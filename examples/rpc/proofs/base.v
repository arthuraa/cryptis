From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown saved_prop.
From cryptis Require Import cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn conn.
From cryptis.examples.rpc Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class rpcGpreS Σ := RpcGPreS {
  #[local] rpcGpreS_meta :: metaGS Σ;
  #[local] rpcGpreS_call_pred ::
    savedPredG Σ (sign_key * sign_key * sess_info * term);
  #[local] rpcGpreS_resp_pred ::
    savedPredG Σ (sign_key * sign_key * sess_info * term * term);
  #[local] rpcGpreS_last_call ::
    inG Σ (dfrac_agreeR (leibnizO (namespace * term)));
}.

Class rpcGS Σ := RpcGS {
  #[local] rpc_inG :: rpcGpreS Σ;
  rpc_call_name : gname;
  rpc_resp_name : gname;
}.

Definition rpcΣ := #[
  metaΣ;
  savedPredΣ (sign_key * sign_key * sess_info * term);
  savedPredΣ (sign_key * sign_key * sess_info * term * term);
  GFunctor (dfrac_agreeR (leibnizO (namespace * term)))].

Global Instance subG_rpcGpreS Σ : subG rpcΣ Σ → rpcGpreS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ, !rpcGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (skI skR : sign_key) (kS t : term) (ts : list term).
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types (ok : Prop) (failed : bool).
Implicit Types si : sess_info.
Implicit Types φ : sign_key → sign_key → sess_info → term → iProp.
Implicit Types ψ : sign_key → sign_key → sess_info → term → term → iProp.
Implicit Types ξ : term → iProp.

Definition resp_pred_token si N t : iProp :=
  term_own (si_init_share si) (rpcN.@"resp_saved_pred")
    (to_dfrac_agree (DfracOwn (1 / 2)) ((N, t) : leibnizO _)).

Lemma resp_pred_token_alloc si E :
  ↑rpcN.@"resp_saved_pred" ⊆ E →
  term_token (si_init_share si) E ==∗
  resp_pred_token si rpcN (TInt 0) ∗
  resp_pred_token si rpcN (TInt 0) ∗
  term_token (si_init_share si) (E ∖ ↑rpcN.@"resp_saved_pred").
Proof.
iIntros "% token".
iMod (term_own_alloc (rpcN.@"resp_saved_pred")
        (to_dfrac_agree (DfracOwn 1)
           ((rpcN, TInt 0) : leibnizO _)) with "token")
  as "[own token]" => //. iFrame "token".
rewrite -Qp.half_half -dfrac_op_own dfrac_agree_op.
iDestruct "own" as "[own1 own2]". by iFrame.
Qed.

Lemma resp_pred_token_agree si N₁ N₂ t₁ t₂ :
  resp_pred_token si N₁ t₁ -∗
  resp_pred_token si N₂ t₂ -∗
  ⌜N₁ = N₂ ∧ t₁ = t₂⌝.
Proof.
iIntros "own1 own2".
iDestruct (term_own_valid_2 with "own1 own2") as "%valid".
rewrite dfrac_agree_op_valid_L in valid.
by case: valid => _ [-> ->].
Qed.

Lemma resp_pred_token_update si N t N₁ N₂ t₁ t₂ :
  resp_pred_token si N₁ t₁ -∗
  resp_pred_token si N₂ t₂ ==∗
  resp_pred_token si N t ∗ resp_pred_token si N t.
Proof.
iIntros "own1 own2".
iMod (term_own_update_2 with "own1 own2") as "own".
{ apply: (dfrac_agree_update_2 _ _ _ _ ((N, t) : leibnizO _)).
  by rewrite dfrac_op_own Qp.half_half. }
by iDestruct "own" as "[??]"; iFrame.
Qed.

Definition rpc_token E : iProp :=
  gmeta_token rpc_call_name E ∗
  gmeta_token rpc_resp_name E.

Definition rpc_pred N φ ψ : iProp :=
  nown rpc_call_name N
    (saved_pred DfracDiscarded (λ '(skI, skR, si, t), φ skI skR si t)) ∗
  nown rpc_resp_name N
    (saved_pred DfracDiscarded (λ '(skI, skR, si, t, t'), ψ skI skR si t t')).

Lemma rpc_pred_set N φ ψ E :
  ↑N ⊆ E →
  rpc_token E ==∗ rpc_pred N φ ψ ∗ rpc_token (E ∖ ↑N).
Proof.
iIntros "%sub [call resp]".
iMod (nown_alloc N (saved_pred DfracDiscarded (λ '(skI, skR, si, ts), φ skI skR si ts)) with "call") as "[#φ call]" => //.
iMod (nown_alloc N (saved_pred DfracDiscarded (λ '(skI, skR, si, ts, ts'), ψ skI skR si ts ts')) with "resp") as "[#ψ resp]" => //.
iFrame. iModIntro. iSplit; eauto.
Qed.

Lemma rpc_token_difference E1 E2 :
  E1 ⊆ E2 →
  rpc_token E2 ⊣⊢ rpc_token E1 ∗ rpc_token (E2 ∖ E1).
Proof.
move=> sub. rewrite /rpc_token.
rewrite (gmeta_token_difference _ _ _ sub).
rewrite (gmeta_token_difference _ _ _ sub).
by iSplit; iIntros "((?&?)&(?&?))"; iFrame.
Qed.

Lemma rpc_token_drop E1 E2 :
  E1 ⊆ E2 →
  rpc_token E2 -∗ rpc_token E1.
Proof.
iIntros "%sub [call resp]".
iSplitL "call"; iApply gmeta_token_drop; eauto.
Qed.

Lemma rpc_pred_agree N φ₁ φ₂ ψ₁ ψ₂ :
  rpc_pred N φ₁ ψ₁ -∗
  rpc_pred N φ₂ ψ₂ -∗
  ▷ ((∀ skI skR si t,    φ₁ skI skR si t ≡ φ₂ skI skR si t) ∗
     (∀ skI skR si t t', ψ₁ skI skR si t t' ≡ ψ₂ skI skR si t t')).
Proof.
iIntros "#[Nφ₁ Nψ₁] #[Nφ₂ Nψ₂]".
iPoseProof (nown_valid_2 with "Nφ₁ Nφ₂") as "#vφ".
iPoseProof (nown_valid_2 with "Nψ₁ Nψ₂") as "#vψ".
rewrite !saved_pred_op_validI.
iDestruct "vφ" as "[_ #vφ]".
iDestruct "vψ" as "[_ #vψ]".
iSplit.
- iIntros "%skI %skR %si %t".
  by iSpecialize ("vφ" $! (skI, skR, si, t)).
- iIntros "%skI %skR %si %t %t'".
  by iSpecialize ("vψ" $! (skI, skR, si, t, t')).
Qed.

Definition rpc_msg_pred skI skR si rl t : iProp :=
  if rl is Init then
    ∃ N t' φ ψ,
      ⌜t = Spec.tag (Tag N) t'⌝ ∗
      rpc_pred N φ ψ ∗ φ skI skR si t' ∗
      resp_pred_token si N t'
  else ∃ N t₀ φ ψ,
      rpc_pred N φ ψ ∗ ψ skI skR si t₀ t ∗
      resp_pred_token si N t₀.

Local Definition ps := {| Conn.msg_inv := rpc_msg_pred |}.

Definition client_connected kI kR cs : iProp :=
  Conn.connected ps kI kR Init cs ∗
  release_token (si_init_share cs) ∗
  (public (si_key cs) ∨
  resp_pred_token cs rpcN (TInt 0) ∗
  resp_pred_token cs rpcN (TInt 0)).

Lemma client_connected_ok skI skR cs :
  client_connected skI skR cs -∗
  secret skI -∗
  secret skR -∗
  minted skI -∗
  minted skR -∗
  ◇ □ ¬ compromised_session Init cs.
Proof.
iIntros "(conn & _)".
by iApply (Conn.connected_ok with "conn").
Qed.

Lemma client_connected_keys kI kR cs :
  client_connected kI kR cs -∗
  ⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝.
Proof.
iIntros "(conn & _)".
by iPoseProof (Conn.connected_keyE with "conn") as "(-> & -> & _)".
Qed.

Lemma client_connected_failure skI skR cs :
  client_connected skI skR cs -∗
  public (si_key cs) -∗
  ◇ GenConn.failure skI skR.
Proof.
iIntros "(conn & rel & _) fail".
by iApply (Conn.connected_failure with "conn rel fail").
Qed.

Definition server_connected skI skR cs : iProp :=
  Conn.connected ps skI skR Resp cs ∗
  release_token (si_resp_share cs).

Lemma server_connected_ok skI skR cs :
  server_connected skI skR cs -∗
  secret skI -∗
  secret skR -∗
  minted skI -∗
  minted skR -∗
  ◇ □ ¬ compromised_session Resp cs.
Proof.
iIntros "(conn & _)".
by iApply (Conn.connected_ok with "conn").
Qed.

Lemma server_connected_keys skI skR cs :
  server_connected skI skR cs -∗
  ⌜skI = si_init cs⌝ ∗ ⌜skR = si_resp cs⌝.
Proof.
iIntros "(conn & _)".
by iPoseProof (Conn.connected_keyE with "conn") as "(-> & -> & _)".
Qed.

Definition ctx : iProp :=
  rpc_pred
    (rpcN.@"close")
    (λ _ _ si _, released (si_init_share si))
    (λ _ _ _ _ _, False)%I ∗
  Conn.ctx rpcN ps.

End Defs.

Arguments rpcGS Σ : clear implicits.

Lemma ctx_alloc `{!heapGS Σ, !cryptisGS Σ, !iso_dhGS Σ,
                  !GenConn.connGS Σ, Hrpc : !rpcGpreS Σ} E :
  ↑rpcN ⊆ E →
  Conn.pre_ctx -∗
  iso_dh_token E ==∗ ∃ H : rpcGS Σ,
  ctx ∗
  iso_dh_token (E ∖ ↑rpcN) ∗
  rpc_token (⊤ ∖ ↑rpcN).
Proof.
iIntros "% #? iso_tok".
iMod gmeta_token_alloc as (γcall) "rpc_tok_call".
iMod gmeta_token_alloc as (γresp) "rpc_tok_resp".
pose Hrpc' := RpcGS Hrpc γcall γresp. iExists Hrpc'.
iMod (Conn.ctx_alloc with "[//] iso_tok") as "[#? tok]" => //.
iFrame.
iAssert (rpc_token ⊤) with "[rpc_tok_call rpc_tok_resp]" as "rpc_tok".
{ by iFrame. }
rewrite (rpc_token_difference (E1 := ↑rpcN)) //.
iDestruct "rpc_tok" as "[rpc_tok ?]". iFrame.
iMod (rpc_pred_set (N := rpcN.@"close") with "rpc_tok") as "[??]";
  first solve_ndisj.
by iFrame.
Qed.
