From stdpp Require Import base gmap.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.base_logic Require Import iprop own.
From iris.proofmode Require Import tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation versionUR A := (authR (max_prefix_listUR A)).
Notation versionG Σ A := (inG Σ (versionUR A)).
Notation versionΣ A := (GFunctor (versionUR A)).

Section Version.

Variables (Σ : gFunctors) (A : ofe).

Notation iProp := (iProp Σ).

Context `{!versionG Σ A}.

Implicit Types (x y z : A) (xs ys zs : list A).

Definition version_auth_def γ dq n x : iProp := ∃ xs,
  own γ (●{dq} to_max_prefix_list (xs ++ [x]) ⋅
         ◯     to_max_prefix_list (xs ++ [x])) ∗
  ⌜n = length xs⌝.
Definition version_auth_aux : seal version_auth_def. by eexists. Qed.
Definition version_auth := unseal version_auth_aux.
Lemma version_auth_unseal : version_auth = version_auth_def.
Proof. exact: seal_eq. Qed.

Definition version_frag_def γ n t : iProp := ∃ ts,
  own γ (◯ to_max_prefix_list (ts ++ [t])) ∗
  ⌜n = length ts⌝.
Definition version_frag_aux : seal version_frag_def. by eexists. Qed.
Definition version_frag := unseal version_frag_aux.
Lemma version_frag_unseal : version_frag = version_frag_def.
Proof. exact: seal_eq. Qed.

Lemma version_alloc x : ⊢ |==> ∃ γ, version_auth γ (DfracOwn 1) 0 x.
Proof.
rewrite version_auth_unseal.
iMod (own_alloc (● to_max_prefix_list [x] ⋅
                 ◯ to_max_prefix_list [x])) as "[%γ own]".
  rewrite auth_both_valid; split; eauto.
  by apply to_max_prefix_list_valid.
iModIntro. iExists γ, []. rewrite /=. iFrame. by eauto.
Qed.

(* FIXME: What if A is not discrete? *)
Lemma version_auth_dfrac_op `{OfeDiscrete A} γ dq1 dq2 n x :
  version_auth γ (dq1 ⋅ dq2) n x ⊣⊢
  version_auth γ dq1 n x ∗ version_auth γ dq2 n x.
Proof.
rewrite version_auth_unseal. iSplit.
- iIntros "(%xs & [[own1 own2] #own'] & %en)".
  iSplitL "own1".
  + iExists xs. rewrite own_op. by iFrame; iSplit.
  + iExists xs. rewrite own_op. by iFrame; iSplit.
- iIntros "[v1 v2]".
  iDestruct "v1" as "(%xs1 & [own1 #own1'] & %en1)".
  iDestruct "v2" as "(%xs2 & [own2 #own2'] & %en2)".
  iPoseProof (own_valid_2 with "own1 own2") as "%valid".
  have {}valid := auth_auth_dfrac_op_inv _ _ _ _ valid.
  have e := to_max_prefix_list_inj _ _ valid.
  have : take n (xs1 ++ [x]) ≡ take n (xs2 ++ [x]) by rewrite e.
  rewrite !take_app_alt // => <- {xs2 en2 valid e}.
  iExists xs1. rewrite own_op auth_auth_dfrac_op own_op. iFrame.
  by iSplit.
Qed.

Lemma version_auth_discard γ dq n x :
  version_auth γ dq n x ==∗
  version_auth γ DfracDiscarded n x.
Proof.
rewrite version_auth_unseal.
iIntros "(%xs & [own #own'] & %en)".
iExists xs. rewrite own_op. do 2!iSplitL => //.
iApply (own_update with "own").
apply auth_update_auth_persist.
Qed.

#[global]
Instance version_auth_from_sep `{OfeDiscrete A} γ dq1 dq2 n x :
  FromSep (version_auth γ (dq1 ⋅ dq2) n x)
          (version_auth γ dq1 n x)
          (version_auth γ dq2 n x).
Proof. by rewrite /FromSep version_auth_dfrac_op. Qed.

#[global]
Instance version_auth_into_sep `{OfeDiscrete A} γ dq1 dq2 n x :
  IntoSep (version_auth γ (dq1 ⋅ dq2) n x)
          (version_auth γ dq1 n x)
          (version_auth γ dq2 n x).
Proof. by rewrite /IntoSep version_auth_dfrac_op. Qed.

#[global]
Instance version_auth_timeless γ dq n x `{OfeDiscrete A} :
  Timeless (version_auth γ dq n x).
Proof. rewrite version_auth_unseal. apply _. Qed.

#[global]
Instance version_auth_discarded_persistent γ n x :
  Persistent (version_auth γ DfracDiscarded n x).
Proof.
rewrite version_auth_unseal /version_auth_def.
apply: bi.exist_persistent => xs.
Qed.

#[global]
Instance version_frag_persistent γ n x : Persistent (version_frag γ n x).
Proof. rewrite version_frag_unseal. apply _. Qed.

#[global]
Instance version_frag_timeless γ n x `{OfeDiscrete A} :
  Timeless (version_frag γ n x).
Proof. rewrite version_frag_unseal. apply _. Qed.

Lemma version_auth_frag γ dq n x : version_auth γ dq n x -∗ version_frag γ n x.
Proof.
rewrite version_auth_unseal version_frag_unseal.
iDestruct 1 as "(%xs & [own1 #own2] & %nE)".
iExists xs; eauto.
Qed.

Lemma version_update y γ n x :
  version_auth γ (DfracOwn 1) n x ==∗ version_auth γ (DfracOwn 1) (S n) y.
Proof.
rewrite version_auth_unseal.
iDestruct 1 as "(%xs & own & ->)".
iMod (own_update with "own") as "own".
  eapply auth_update.
  apply (max_prefix_list_local_update _ ((xs ++ [x]) ++ [y])).
  by exists [y].
iModIntro.
iExists (xs ++ [x]). rewrite own_op app_length plus_comm. iFrame.
by iPureIntro.
Qed.

(* FIXME: What if A is not discrete? *)
Lemma version_auth_agree `{OfeDiscrete A} γ dq1 dq2 n m x y :
  version_auth γ dq1 n x -∗
  version_auth γ dq2 m y -∗
  ⌜n = m ∧ x ≡ y⌝.
Proof.
rewrite version_auth_unseal.
iIntros "(%xs & [own_x _] & %e1)".
iIntros "(%ys & [own_y _] & %e2)".
iPoseProof (own_valid_2 with "own_x own_y") as "%valid".
have {}valid := auth_auth_dfrac_op_inv _ _ _ _ valid.
have e := to_max_prefix_list_inj _ _ valid.
have elen : length (xs ++ [x]) = length (ys ++ [y]) by rewrite e.
have enm : n = m by rewrite e1 e2 !app_length /= in elen *; lia.
iSplit => //.
have ex : last (xs ++ [x]) = Some x by rewrite last_snoc.
have ey : last (ys ++ [y]) = Some y by rewrite last_snoc.
iAssert (Some x ≡ Some y)%I as "e".
  by rewrite -ex -ey e.
by rewrite option_equivI; iPoseProof "e" as "%".
Qed.

(* FIXME: What if A is not discrete? *)
Lemma version_auth_frag_agree `{OfeDiscrete A} γ dq n x y :
  version_auth γ dq n x -∗
  version_frag γ    n y -∗
  x ≡ y.
Proof.
rewrite version_auth_unseal version_frag_unseal.
iIntros "(%xs & [own_x _] & %e1)".
iIntros "(%ys & own_y & %e2)".
iPoseProof (own_valid_2 with "own_x own_y") as "%valid".
rewrite auth_both_dfrac_valid_discrete in valid.
case: valid => [] _ [] incl _.
rewrite to_max_prefix_list_included in incl.
case: incl => zs e.
have e' : drop (length (xs ++ [x])) (xs ++ [x]) ≡
          drop (length (xs ++ [x])) ((ys ++ [y]) ++ zs).
  by rewrite -e.
rewrite drop_all drop_app_alt ?app_length -?e1 -?e2 // in e'.
rewrite -e' app_nil_r in e.
have ex : last (xs ++ [x]) = Some x by rewrite last_snoc.
have ey : last (ys ++ [y]) = Some y by rewrite last_snoc.
iAssert (Some x ≡ Some y)%I as "e".
  by rewrite -ex -ey e.
by rewrite option_equivI.
Qed.

(* FIXME: What if A is not discrete? *)
Lemma version_auth_frag_num `{OfeDiscrete A} γ dq n m x y :
  version_auth γ dq n x -∗
  version_frag γ    m y -∗
  ⌜m ≤ n⌝.
Proof.
rewrite version_auth_unseal version_frag_unseal.
iIntros "(%xs & [own_x _] & %e1)".
iIntros "(%ys & own_y & %e2)".
iPoseProof (own_valid_2 with "own_x own_y") as "%valid".
rewrite auth_both_dfrac_valid_discrete to_max_prefix_list_included in valid.
case: valid => [] _ [] [zs e] _.
iPureIntro.
have : length (ys ++ [y]) ≤ length (xs ++ [x]).
  rewrite e !app_length; lia.
rewrite !app_length -e1 -e2 /=; lia.
Qed.

(* FIXME: What if A is not discrete? *)
Lemma version_frag_agree `{OfeDiscrete A} γ n x y :
  version_frag γ n x -∗
  version_frag γ n y -∗
  x ≡ y.
Proof.
rewrite version_frag_unseal.
iIntros "(%xs & #own_xs & %e1)".
iIntros "(%ys & #own_ys & %e2)".
iPoseProof (own_valid_2 with "own_xs own_ys") as "%valid".
rewrite auth_frag_op_valid to_max_prefix_list_op_valid in valid.
enough (e : xs ++ [x] ≡ ys ++ [y]).
  assert (e' : last (xs ++ [x]) ≡ last (ys ++ [y])) by rewrite e //.
  rewrite !last_snoc in e'.
  by inversion e'.
case: valid => [] [l e].
- assert (e' : take (S n) ((xs ++ [x]) ++ l) ≡ take (S n) (ys ++ [y])).
    by rewrite e.
  rewrite take_app_alt ?app_length /= 1?Nat.add_comm -?e1 // in e' *.
  rewrite take_ge ?app_length /= 1?Nat.add_comm -?e2 // in e'.
- assert (e' : take (S n) ((ys ++ [y]) ++ l) ≡ take (S n) (xs ++ [x])).
    by rewrite e.
  rewrite take_app_alt ?app_length /= 1?Nat.add_comm -?e2 // in e' *.
  by rewrite take_ge ?app_length /= 1?Nat.add_comm -?e1 // in e'.
Qed.

End Version.

Arguments version_auth {Σ A _}.
Arguments version_frag {Σ A _}.
Arguments version_alloc {Σ A _} x.
Arguments version_update {Σ A _} y.
