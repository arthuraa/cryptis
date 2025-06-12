From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac numbers.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis primitives tactics.
From cryptis Require Import role iso_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation connN := (nroot.@"conn").

Module Props.

Record state := State {
  cs_si   :> sess_info;
  cs_ts   :  loc;
  cs_chan :  val;
  cs_role :  role;
}.

Definition cs_share cs := si_share_of (cs_role cs) cs.

#[global]
Instance cs_repr : Repr state :=
  λ s, (#(cs_ts s), si_key s, cs_chan s)%V.

Definition countR := authR max_natUR.

Class connGS Σ := ConnGS {
  connGS_count  : inG Σ countR;
}.

Local Existing Instance connGS_count.

Definition connΣ := #[
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
  term_token kR (↑connN.@"server".@kI).

Lemma never_connected_switch kI kR Q : ⊢ switch (never_connected kI kR) Q.
Proof. apply term_token_switch. Qed.

Lemma public_sencE N rl si t φ :
  public (TSeal (TKey Seal (si_key si)) (Spec.tag (Tag N) t)) -∗
  seal_pred N φ -∗
  wf_sess_info rl si -∗
  ▷ □ (public (si_key si) ∗ public t ∨ φ (si_key si) t).
Proof.
iIntros "#p_m #Nφ #(_ & s_key & sess)".
iDestruct (public_TSealE with "[//] [//]") as "{p_m} [[p_key p_m]|p_m]".
- iPoseProof ("s_key" with "p_key") as "{p_key} >p_key". by eauto.
- iDestruct "p_m" as "[#p_m _]". by eauto.
Qed.

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

Definition connected kI kR rl cs : iProp :=
  ⌜si_init cs = kI⌝ ∗
  ⌜si_resp cs = kR⌝ ∗
  ⌜cs_role cs = rl⌝ ∗
  channel (cs_chan cs) ∗
  wf_sess_info (cs_role cs) cs ∗
  ∃ n m, cs_ts cs ↦∗ [ #n; #m ] ∗ received_auth cs (cs_role cs) m.

Lemma connected_channel kI kR rl cs :
  connected kI kR rl cs -∗
  channel (cs_chan cs).
Proof. by iIntros "(_ & _ & _ & ? & _)". Qed.

Lemma connected_public_key kI kR rl cs kt :
  connected kI kR rl cs -∗
  release_token (si_share_of rl cs) -∗
  public (TKey kt (si_key cs)) -∗
  ◇ compromised_session rl cs.
Proof.
iIntros "conn rel #p_k".
iPoseProof "conn" as "(_ & _ & <- & _ & #sess & _)".
iDestruct "sess" as "(#? & #s_key & #sess)".
iPoseProof (senc_key_compromised_keyI with "s_key p_k") as "{p_k} p_k".
iPoseProof (senc_key_compromised_keyE with "s_key p_k") as "{p_k} >p_k".
by iApply session_compromised.
Qed.

Lemma connected_released_session kI kR rl cs :
  connected kI kR rl cs -∗
  □ (▷ released_session cs → public (si_key cs)).
Proof.
iIntros "(_ & _ & _ & _ & #sess & _)".
by iDestruct "sess" as "(_ & _ & ? & sess)".
Qed.

Lemma connected_keyE kI kR rl cs :
  connected kI kR rl cs -∗
  ⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝ ∗ ⌜rl = cs_role cs⌝.
Proof. by iIntros "(-> & -> & -> & _)". Qed.

Lemma connected_ok kI kR rl cs :
  connected kI kR rl cs -∗
  secret kI -∗
  secret kR -∗
  sign_key kI -∗
  sign_key kR -∗
  ◇ □ ¬ compromised_session rl cs.
Proof.
iIntros "(<- & <- & <- & _ & #sess & % & % & _ & _) s_kI s_kR #signI #signR".
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
      (φ (si_init si) (si_resp si) si ts ∗
       received_auth si (swap_role rl) (S n)).

Lemma session_failed_failure rl si :
  compromised_session rl si  ⊢ failure (si_init si) (si_resp si).
Proof. by iIntros "(#failed & _)". Qed.

End Defs.

End Props.

Arguments Props.connGS Σ : clear implicits.
