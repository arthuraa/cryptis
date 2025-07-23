From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac numbers.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis primitives tactics role.
From cryptis Require Import saved_prop.
From cryptis.examples Require Import iso_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation connN := (nroot.@"conn").

Record state := State {
  cs_si   :> sess_info;
  cs_ts   :  loc;
  cs_chan :  val;
  cs_role :  role;
}.

Definition cs_share cs := si_share_of (cs_role cs) cs.

#[global]
Instance cs_repr : Repr state :=
  λ s, (#(cs_ts s), si_key s, cs_chan s, repr (cs_role s))%V.

Definition countR := authR max_natUR.

Class connGS Σ := ConnGS {
  connGS_count  : inG Σ countR;
  connGS_pred   : savedPredG Σ (sign_key * sign_key * sess_info * role * term);
}.

Local Existing Instance connGS_count.
Local Existing Instance connGS_pred.

Definition connΣ := #[
  GFunctor countR;
  savedPredΣ (sign_key * sign_key * sess_info * role * term)
].

Global Instance subG_connGS Σ : subG connΣ Σ → connGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !connGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : state).
Implicit Types (kS t : term) (ts : list term).
Implicit Types (skI skR : sign_key).
Implicit Types n m : nat.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types (ok : Prop) (failed : bool).
Implicit Types si : sess_info.
Implicit Types (φ : sign_key → sign_key → sess_info → role → term → iProp).
Implicit Types (ψ : role → term → iProp).

Definition failure skI skR : iProp :=
   public skI ∨ public skR.

Definition wf_sess_info rl si : iProp :=
  minted (si_key si) ∗
  session rl si.

#[global]
Instance wf_sess_info_persistent rl si : Persistent (wf_sess_info rl si).
Proof. apply _. Qed.

Definition never_connected skI skR : iProp :=
  term_token skR (↑connN.@"server".@skI).

Lemma never_connected_switch skI skR Q : ⊢ switch (never_connected skI skR) Q.
Proof. apply term_token_switch. Qed.

Definition received_auth si rl n : iProp :=
  term_own (si_share_of rl si) (connN.@"received") (● MaxNat n).

Definition received_frag si rl n : iProp :=
  term_own (si_share_of rl si) (connN.@"received") (◯ MaxNat n).

Lemma received_update si rl n :
  received_auth si rl n ==∗
  received_auth si rl (S n) ∗ received_frag si rl (S n).
Proof.
rewrite /received_auth /received_frag -term_own_op.
iApply term_own_update.
apply: auth_update_alloc.
apply: max_nat_local_update => /=; lia.
Qed.

Lemma received_alloc si rl E :
  ↑connN.@"received" ⊆ E →
  term_token (si_share_of rl si) E ==∗
  received_auth si rl 0 ∗
  term_token (si_share_of rl si) (E ∖ ↑connN.@"received").
Proof.
iIntros "% token".
iMod (term_own_alloc (connN.@"received") (● MaxNat 0)
       with "token") as "[own token]" => //.
- by rewrite auth_auth_valid.
- by iFrame.
Qed.

Lemma escrow_received n P si rl :
  P ={⊤}=∗
  escrow nroot (received_auth si rl n) (P ∗ received_auth si rl (S n)).
Proof.
iIntros "P".
iMod (inv_alloc nroot _ (P ∨ received_frag si rl (S n))%I with "[P]") as "#I".
{ by eauto. }
rewrite /escrow. iIntros "!> !> %E %sub recv".
iInv nroot as "[HP|>recv']".
- iMod (received_update with "recv") as "[recv #frag]".
  iModIntro. iSplitR; iFrame; by eauto.
- iPoseProof (term_own_valid_2 with "recv recv'") as "%valid".
  rewrite auth_both_valid_discrete max_nat_included in valid.
  case: valid => /= ? _; lia.
Qed.

Definition conn_msg_pred φ gb : iProp :=
  □ (∀ si rl t,
        term_pred gb (iso_dhN.@"res".@"pred")
          (si_init si, si_resp si, si, rl, t)
          ↔ ▷ φ (si_init si) (si_resp si) si rl t).

Definition conn_init_pred φ ψ gb : iProp :=
  conn_msg_pred φ gb ∗ ψ Init gb.

Definition connected skI skR φ rl cs : iProp :=
  ⌜si_init cs = skI⌝ ∗
  ⌜si_resp cs = skR⌝ ∗
  ⌜cs_role cs = rl⌝ ∗
  channel (cs_chan cs) ∗
  wf_sess_info (cs_role cs) cs ∗
  (compromised_session rl cs ∨
     conn_msg_pred φ (si_resp_share cs)) ∗
  ∃ n m, cs_ts cs ↦∗ [ #n; #m ] ∗ received_auth cs (cs_role cs) m.

Lemma connected_channel skI skR φ rl cs :
  connected skI skR φ rl cs -∗
  channel (cs_chan cs).
Proof. by iIntros "(_ & _ & _ & ? & _)". Qed.

Lemma connected_public_key skI skR φ rl cs :
  connected skI skR φ rl cs -∗
  release_token (si_share_of rl cs) -∗
  public (si_key cs) -∗
  ◇ compromised_session rl cs.
Proof.
iIntros "conn rel #p_k".
iPoseProof "conn" as "(_ & _ & <- & _ & #sess & _)".
iDestruct "sess" as "(#? & #sess)".
by iApply (session_compromised with "[] [//] rel").
Qed.

Lemma connected_released_session skI skR φ rl cs :
  connected skI skR φ rl cs -∗
  □ (▷ released_session cs → public (si_key cs)).
Proof.
iIntros "(_ & _ & _ & _ & #sess & _)".
by iDestruct "sess" as "(_ & ? & sess)".
Qed.

Lemma connected_keyE skI skR φ rl cs :
  connected skI skR φ rl cs -∗
  ⌜skI = si_init cs⌝ ∗ ⌜skR = si_resp cs⌝ ∗ ⌜rl = cs_role cs⌝.
Proof. by iIntros "(-> & -> & -> & _)". Qed.

Lemma connected_ok skI skR φ rl cs :
  connected skI skR φ rl cs -∗
  secret skI -∗
  secret skR -∗
  minted skI -∗
  minted skR -∗
  ◇ □ ¬ compromised_session rl cs.
Proof.
iIntros "(<- & <- & <- & _ & #sess & _ & % & % & _ & _)
          s_kI s_kR #signI #signR".
iDestruct "sess" as "(m_k & sess)".
by iApply (session_not_compromised with "[//] s_kI s_kR").
Qed.

Definition conn_pred kS t : iProp :=
  ∃ si rl n t',
    let rl' := TInt (if rl is Init then 1 else 0) in
    ⌜kS = si_key si⌝ ∗
    ⌜t = Spec.of_list [rl'; TInt n; t']⌝ ∗
    public t' ∗
    escrow nroot (received_auth si (swap_role rl) n)
      (term_pred (si_resp_share si) (iso_dhN.@"res".@"pred")
         (si_init si, si_resp si, si, rl, t')
       ∗ received_auth si (swap_role rl) (S n)).

Lemma session_failed_failure rl si :
  compromised_session rl si  ⊢ failure (si_init si) (si_resp si).
Proof. by iIntros "(#failed & _)". Qed.

Definition pre_ctx `{!iso_dhGS Σ} : iProp :=
  iso_dh_ctx ∗
  senc_pred connN conn_pred.

Lemma pre_ctx_alloc `{!iso_dhGS Σ} E :
  ↑connN ⊆ E →
  iso_dh_ctx -∗
  seal_pred_token SENC E ==∗
  pre_ctx ∗ seal_pred_token SENC (E ∖ ↑connN).
Proof.
iIntros "% #? tok". iFrame "#". by iApply seal_pred_set.
Qed.

Definition ctx `{!iso_dhGS Σ} N φ ψ : iProp :=
  pre_ctx ∗
  iso_dh_pred N (conn_init_pred φ ψ).

Lemma ctx_alloc `{!iso_dhGS Σ} N φ ψ E :
  ↑N ⊆ E →
  pre_ctx -∗
  iso_dh_token E ==∗
  ctx N φ ψ ∗ iso_dh_token (E ∖ ↑N).
Proof.
iIntros "% #ctx tok". iFrame "#".
by iApply iso_dh_pred_set.
Qed.

End Defs.

Arguments connGS Σ : clear implicits.
