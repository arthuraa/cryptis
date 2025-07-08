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
From cryptis Require Import cryptis primitives tactics.
From cryptis Require Import role iso_dh conn.
From cryptis.rpc Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Props.

Class rpcGS Σ := RpcGS {
  rpcGS_pred  : savedPredG Σ (list term);
}.

Local Existing Instance rpcGS_pred.

Definition rpcΣ := #[
  savedPredΣ (list term)
].

Global Instance subG_rpcGS Σ : subG rpcΣ Σ → rpcGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !rpcGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (skI skR : sign_key) (kS t : term) (ts : list term).
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types (ok : Prop) (failed : bool).
Implicit Types si : sess_info.

Definition resp_pred_token si φ : iProp :=
  term_own (si_init_share si) (rpcN.@"resp_pred")
    (saved_pred (DfracOwn (1 / 2)) φ).

Lemma resp_pred_token_alloc si E :
  ↑rpcN.@"resp_pred" ⊆ E →
  term_token (si_init_share si) E ==∗
  resp_pred_token si (λ _, False%I) ∗
  resp_pred_token si (λ _, False%I) ∗
  term_token (si_init_share si) (E ∖ ↑rpcN.@"resp_pred").
Proof.
iIntros "% token".
iMod (term_own_alloc (rpcN.@"resp_pred")
        (saved_pred (DfracOwn 1) (λ _, False%I)) with "token")
  as "[own token]" => //. iFrame "token".
rewrite -Qp.half_half -dfrac_op_own saved_pred_op.
iDestruct "own" as "[own1 own2]". by iFrame.
Qed.

Lemma resp_pred_token_agree si φ ψ :
  resp_pred_token si φ -∗
  resp_pred_token si ψ -∗
  □ ∀ x, ▷ (φ x ≡ ψ x).
Proof.
iIntros "own1 own2".
iPoseProof (term_own_valid_2 with "own1 own2") as "#valid".
rewrite saved_pred_op_validI. iDestruct "valid" as "[_ #?]".
by iModIntro.
Qed.

Lemma resp_pred_token_update si φ1 φ2 ψ :
  resp_pred_token si φ1 -∗
  resp_pred_token si φ2 ==∗
  resp_pred_token si ψ ∗ resp_pred_token si ψ.
Proof.
iIntros "own1 own2".
iMod (term_own_update_2 with "own1 own2") as "own".
apply: (saved_pred_update_2 _ _ _ _ ψ).
{ by rewrite dfrac_op_own Qp.half_half. }
by iDestruct "own" as "[??]"; iFrame.
Qed.

Definition client_connected kI kR cs : iProp :=
  Conn.connected kI kR Init cs ∗
  release_token (si_init_share cs) ∗
  (compromised_session Init cs ∨
  resp_pred_token cs (λ _, False%I) ∗
  resp_pred_token cs (λ _, False%I)).

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

Definition server_connected skI skR cs : iProp :=
  Conn.connected skI skR Resp cs ∗
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

Definition call_pred φ ψ :=
  Conn.conn_pred Init (λ skI skR si ts,
    resp_pred_token si (ψ skI skR si ts) ∗
    φ skI skR si ts
  )%I.

Definition rpc N φ ψ :=
  senc_pred N (call_pred φ ψ).

Lemma rpc_alloc N φ ψ E :
  ↑N ⊆ E →
  seal_pred_token SENC E ==∗
  rpc N φ ψ ∗ seal_pred_token SENC (E ∖ ↑N).
Proof. exact: seal_pred_set. Qed.

Definition resp_pred skI skR si ts : iProp :=
  ∃ ψ, resp_pred_token si ψ ∗ ψ ts.

Definition error_pred skI skR si ts : iProp := True.

Definition close_pred :=
  call_pred (λ _ _ si _, released (si_init_share si))
    (λ _ _ _ _ _, False)%I.

Definition ctx : iProp :=
  senc_pred (rpcN.@"resp") (Conn.conn_pred Resp resp_pred) ∗
  senc_pred (rpcN.@"error") (Conn.conn_pred Resp error_pred) ∗
  senc_pred (rpcN.@"close") close_pred ∗
  iso_dh_ctx.

Lemma ctx_alloc E :
  ↑rpcN ⊆ E →
  seal_pred_token SENC E -∗
  iso_dh_ctx ==∗
  ctx ∗ seal_pred_token SENC (E ∖ ↑rpcN).
Proof.
iIntros "%sub token #?".
rewrite (seal_pred_token_difference _ (↑rpcN)); try solve_ndisj.
iDestruct "token" as "[token ?]". iFrame.
iMod (senc_pred_set (N := rpcN.@"resp") with "token")
  as "[resp token]"; try solve_ndisj.
iFrame.
iMod (senc_pred_set (N := rpcN.@"error") with "token")
  as "[error token]"; try solve_ndisj.
iFrame.
iMod (senc_pred_set (N := rpcN.@"close") with "token")
  as "[init token]"; try solve_ndisj.
Qed.

Ltac solve_ctx :=
  iIntros "ctx"; repeat (
    try solve [iApply "ctx"];
    iDestruct "ctx" as "[H ctx]";
    first [iApply "H" | iClear "H"]
  ).

Lemma ctx_resp :
  ctx -∗
  senc_pred (rpcN.@"resp") (Conn.conn_pred Resp resp_pred).
Proof. solve_ctx. Qed.

Lemma ctx_error :
  ctx -∗
  senc_pred (rpcN.@"error") (Conn.conn_pred Resp error_pred).
Proof. solve_ctx. Qed.

Lemma ctx_close :
  ctx -∗
  senc_pred (rpcN.@"close") close_pred.
Proof. solve_ctx. Qed.

Lemma ctx_conn_ctx : ctx -∗ iso_dh_ctx.
Proof. solve_ctx. Qed.

End Defs.

End Props.

Arguments Props.rpcGS Σ : clear implicits.
