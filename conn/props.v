From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis primitives tactics.
From cryptis Require Import role iso_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Props.

Record state := State {
  cs_si   :> sess_info;
  cs_ts   :  loc;
  cs_role :  role;
}.

Definition cs_share cs := si_share_of (cs_role cs) cs.

#[global]
Instance cs_repr : Repr state :=
  λ s, (#(cs_ts s), si_key s)%V.

Definition clockR := dfrac_agreeR natO.
Definition countR := authR max_natUR.

Class connGS Σ := ConnGS {
  connGS_clock  : inG Σ clockR;
  connGS_count  : inG Σ countR;
}.

Local Existing Instance connGS_clock.
Local Existing Instance connGS_count.

Definition connΣ := #[
  GFunctor clockR;
  GFunctor countR
].

Global Instance subG_connGS Σ : subG connΣ Σ → connGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !connGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : state).
Implicit Types (kI kR kS t : term) (ts : list term).
Implicit Types n m : nat.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types (ok : Prop) (failed : bool).
Implicit Types si : sess_info.

Variable N : namespace.

Definition failure kI kR : iProp :=
  compromised_key kI ∨ compromised_key kR.

Definition wf_sess_info rl si : iProp :=
  minted (si_key si) ∗
  senc_key (si_key si) ∗
  session rl si.

#[global]
Instance wf_sess_info_persistent rl si : Persistent (wf_sess_info rl si).
Proof. apply _. Qed.

Definition never_connected kI kR : iProp :=
  term_token kR (↑N.@"server".@kI).

Lemma never_connected_switch kI kR Q : ⊢ switch (never_connected kI kR) Q.
Proof. apply term_token_switch. Qed.

Definition clock kI kR n :=
  term_own kI (N.@"client".@kR.@"clock") (to_frac_agree (1 / 2) n).

Lemma clock_alloc kI kR E :
  ↑N.@"client".@kR.@"clock" ⊆ E →
  term_token kI E ==∗
  clock kI kR 0 ∗
  clock kI kR 0 ∗
  term_token kI (E ∖ ↑N.@"client".@kR.@"clock").
Proof.
iIntros "%sub token".
iMod (term_own_alloc (N.@"client".@kR.@"clock") (to_frac_agree 1 0)
       with "token") as "[own token]" => //.
iFrame. rewrite -Qp.half_half frac_agree_op.
iDestruct "own" as "[??]". by iFrame.
Qed.

Lemma clock_agree kI kR n m :
  clock kI kR n -∗
  clock kI kR m -∗
  ⌜n = m⌝.
Proof.
iIntros "own1 own2".
iPoseProof (term_own_valid_2 with "own1 own2") as "%valid".
rewrite frac_agree_op_valid_L in valid.
by case: valid.
Qed.

Lemma clock_update p kI kR n m :
  clock kI kR n -∗
  clock kI kR m ==∗
  clock kI kR p ∗ clock kI kR p.
Proof.
iIntros "own1 own2".
rewrite /clock.
iMod (term_own_update_2 with "own1 own2") as "[own1 own2]".
{ apply: (frac_agree_update_2 _ _ _ _ p).
  by rewrite Qp.half_half. }
by iFrame.
Qed.

Definition received_auth si rl n : iProp :=
  term_own (si_share_of rl si) (isoN.@"received") (● MaxNat n).

Definition received_frag si rl n : iProp :=
  term_own (si_share_of rl si) (isoN.@"received") (◯ MaxNat n).

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
  ↑isoN.@"received" ⊆ E →
  term_token (si_share_of rl si) E ==∗
  received_auth si rl 0 ∗
  term_token (si_share_of rl si) (E ∖ ↑isoN.@"received").
Proof.
iIntros "% token".
iMod (term_own_alloc (isoN.@"received") (● MaxNat 0)
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

Definition connected kI kR rl cs n m : iProp :=
  ⌜si_init cs = kI⌝ ∗
  ⌜si_resp cs = kR⌝ ∗
  ⌜cs_role cs = rl⌝ ∗
  wf_sess_info (cs_role cs) cs ∗
  cs_ts cs ↦∗ [ #n; #m ] ∗
  received_auth cs (cs_role cs) m.

Lemma connected_keyE kI kR rl cs n m :
  connected kI kR rl cs n m -∗
  ⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝ ∗ ⌜rl = cs_role cs⌝.
Proof. by iIntros "(-> & -> & -> & _)". Qed.

Lemma connected_ok kI kR rl cs n m :
  connected kI kR rl cs n m -∗
  secret kI -∗
  secret kR -∗
  sign_key kI -∗
  sign_key kR -∗
  ◇ □ ¬ compromised_session rl cs.
Proof.
iIntros "(<- & <- & <- & #sess & _ & _) s_kI s_kR #signI #signR".
iDestruct "sess" as "(m_k & s_k & sess)".
by iApply (session_not_compromised with "[//] s_kI s_kR").
Qed.

Definition conn_pred rl φ kS t : iProp :=
  ∃ si n ts,
    ⌜kS = si_key si⌝ ∗
    ⌜t = Spec.of_list (TInt n :: ts)⌝ ∗
    ([∗ list] t' ∈ ts, public t') ∗
    escrow nroot
      (received_auth si (swap_role rl) n)
      (φ (si_init si) (si_resp si) si n ts ∗ received_auth si (swap_role rl) (S n)).

Lemma session_failed_failure rl si :
  compromised_session rl si  ⊢ failure (si_init si) (si_resp si).
Proof. by iIntros "(#failed & _)". Qed.

Definition ctx : iProp :=
  iso_dh_ctx N.

Lemma ctx_alloc E :
  ↑N ⊆ E →
  seal_pred_token E ==∗
  ctx ∗ seal_pred_token (E ∖ ↑N).
Proof.
iIntros "%sub token".
rewrite (seal_pred_token_difference (↑N));
  try solve_ndisj.
iDestruct "token" as "[token ?]". iFrame.
iMod (iso_dh_ctx_alloc N with "token")
  as "#iso_dh"; try solve_ndisj.
Qed.

Ltac solve_ctx :=
  iIntros "ctx"; repeat (
    try solve [iApply "ctx"];
    iDestruct "ctx" as "[H ctx]";
    first [iApply "H" | iClear "H"]
  ).

Lemma ctx_iso_dh_ctx : ctx -∗ iso_dh_ctx N.
Proof. solve_ctx. Qed.

End Defs.

End Props.

Arguments Props.connGS Σ : clear implicits.
