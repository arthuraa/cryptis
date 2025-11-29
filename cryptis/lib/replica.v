From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree gmap.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation replicaG Σ A :=
  (inG Σ (dfrac_agreeR (leibnizO A))).

Notation replicaΣ A :=
  (GFunctor (dfrac_agreeR (leibnizO A))).

Section Updates.

Context `{!heapGS Σ, !cryptisGS Σ, !replicaG Σ A}.

Implicit Types (kI kR : term) (N : namespace).

Definition replica kI kR N (s : string) (a : A) : iProp Σ :=
  term_own kI (N.@"client".@kR.@"replica".@s)
    (to_frac_agree (1 / 2) (a : leibnizO A)).

Lemma replica_alloc kI kR N s a E :
  ↑N.@"client".@kR.@"replica".@s ⊆ E →
  term_token kI E ==∗
  replica kI kR N s a ∗
  replica kI kR N s a ∗
  term_token kI (E ∖ ↑N.@"client".@kR.@"replica".@s).
Proof.
iIntros "%sub token".
iMod (term_own_alloc (N.@"client".@kR.@"replica".@s)
        (to_frac_agree 1 (a : leibnizO A)) with "token")
  as "[own token]" => //.
iFrame. rewrite -Qp.half_half frac_agree_op.
iDestruct "own" as "[??]". by iFrame.
Qed.

Lemma replica_agree kI kR N s a1 a2 :
  replica kI kR N s a1 -∗
  replica kI kR N s a2 -∗
  ⌜a1 = a2⌝.
Proof.
iIntros "own1 own2".
iPoseProof (term_own_valid_2 with "own1 own2") as "%valid".
rewrite frac_agree_op_valid_L in valid.
by case: valid.
Qed.

Lemma replica_update a kI kR N s a1 a2 :
  replica kI kR N s a1 -∗
  replica kI kR N s a2 ==∗
  replica kI kR N s a ∗ replica kI kR N s a.
Proof.
iIntros "own1 own2". rewrite /replica.
iMod (term_own_update_2 with "own1 own2") as "[own1 own2]".
{ apply: (frac_agree_update_2 _ _ _ _ (a : leibnizO A)).
  by rewrite Qp.half_half. }
by iFrame.
Qed.

Definition never_connected kI kR N : iProp Σ :=
  term_token kR (↑N.@"server".@kI).

Lemma first_connection kI kR N :
  never_connected kI kR N ==∗ □ ¬ never_connected kI kR N.
Proof.
iIntros "token".
iMod (term_meta_set _ () with "token") as "#meta"; eauto.
iIntros "!> !> contra".
by iDestruct (term_meta_token with "contra meta") as "[]".
Qed.

Definition rep_main  kI kR N (a : A) : iProp Σ := replica kI kR N "main" a.
Definition rep_copy' kI kR N (a : A) : iProp Σ := replica kI kR N "copy" a.

Definition rep_sync kI kR N a0 a : iProp Σ :=
  rep_main  kI kR N a ∗
  rep_copy' kI kR N a ∗
  (⌜a = a0⌝ ∗ rep_copy' kI kR N a0 ∨ □ ¬ never_connected kI kR N).

Definition rep_update kI kR N a0 a a' : iProp Σ :=
  rep_main kI kR N a' ∗
  rep_copy' kI kR N a ∗
  (⌜a = a0⌝ ∗ rep_copy' kI kR N a0 ∨ □ ¬ never_connected kI kR N).

Definition rep_copy kI kR N a0 a : iProp Σ :=
  ⌜a = a0⌝ ∗ never_connected kI kR N ∨
  rep_copy' kI kR N a ∗ □ ¬ never_connected kI kR N.

Lemma rep_main_sync kI kR N a0 a a' :
  rep_main kI kR N a -∗
  rep_sync kI kR N a0 a' -∗
  ⌜a = a'⌝.
Proof.
iIntros "c1 (c2 & _)". iApply (replica_agree with "c1 c2").
Qed.

Lemma rep_main_alloc kI kR N a0 E :
  ↑N.@"client".@kR.@"replica" ⊆ E →
  term_token kI E ==∗
  rep_main kI kR N a0 ∗ rep_sync kI kR N a0 a0 ∗
  term_token kI (E ∖ ↑N.@"client".@kR.@"replica").
Proof.
iIntros "%sub token".
iMod (replica_alloc _ a0 (s := "main") with "token")
  as "(? & ? & token)"; first solve_ndisj.
iFrame.
iMod (replica_alloc _ a0 (s := "copy") with "token")
  as "(c1 & c2 & token)"; first solve_ndisj.
iModIntro. iFrame.
iSplitL "c1".
- iLeft. by iFrame.
- iApply (term_token_drop with "token"). solve_ndisj.
Qed.

Lemma rep_copy_alloc kI kR N a0 E :
  ↑N.@"server".@kI ⊆ E →
  term_token kR E ==∗
  rep_copy kI kR N a0 a0 ∗ term_token kR (E ∖ ↑N.@"server".@kI).
Proof.
iIntros "%sub token".
rewrite term_token_difference //. iDestruct "token" as "[??]".
iFrame. iModIntro. iLeft. by iFrame.
Qed.

Lemma rep_main_update a' kI kR N a0 a :
  rep_main kI kR N a -∗
  rep_sync kI kR N a0 a ==∗
  rep_main kI kR N a' ∗
  rep_update kI kR N a0 a a'.
Proof.
iIntros "client1 (client2 & server1 & ?)".
iFrame.
iMod (replica_update a' with "client1 client2") as "[??]".
by iFrame.
Qed.

Lemma rep_copy_update kI kR N a0 a1 a2 a' :
  rep_copy kI kR N a0 a1 -∗
  rep_update kI kR N a0 a2 a' ==∗
  ⌜a1 = a2⌝ ∗
  rep_copy kI kR N a0 a' ∗
  rep_sync kI kR N a0 a'.
Proof.
iIntros "server upd".
iDestruct "server" as "[(-> & never)|(s1 & #first1)]";
iDestruct "upd" as "(c1 & s2 & [(-> & s3)| #first2])".
- iMod (first_connection with "never") as "#first".
  iMod (replica_update a' with "s2 s3") as "[s2 s3]".
  iModIntro. iSplit => //. iFrame.
  iSplitL "s2".
  + iRight. by iSplit; iFrame.
  + by iRight.
- by iPoseProof ("first2" with "never") as "[]".
- iPoseProof (replica_agree with "s1 s2") as "<-".
  iMod (replica_update a' with "s1 s2") as "[s1 s2]".
  iModIntro. iFrame. iSplit => //. iSplitL "s1".
  + by iRight; iFrame.
  + by iRight.
- iPoseProof (replica_agree with "s1 s2") as "<-".
  iMod (replica_update a' with "s1 s2") as "[s1 s2]".
  iModIntro. iFrame. iSplit => //.
  iSplitL; last by eauto.
  iRight. by iFrame.
Qed.

End Updates.
