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

Section Version.

Variables (Σ : gFunctors) (A : ofe).

Notation iProp := (iProp Σ).

Context `{!versionG Σ A}.

Implicit Types (x y z : A) (xs ys zs : list A).

Definition version_auth γ dq n x : iProp := ∃ xs,
  own γ (●{dq} to_max_prefix_list (xs ++ [x]) ⋅
         ◯     to_max_prefix_list (xs ++ [x])) ∗
  ⌜n = length xs⌝.

Definition version_frag γ n t : iProp := ∃ ts,
  own γ (◯ to_max_prefix_list (ts ++ [t])) ∗
  ⌜n = length ts⌝.

Lemma version_alloc x : ⊢ |==> ∃ γ, version_auth γ (DfracOwn 1) 0 x.
Proof.
iMod (own_alloc (● to_max_prefix_list [x] ⋅
                 ◯ to_max_prefix_list [x])) as "[%γ own]".
  rewrite auth_both_valid; split; eauto.
  by apply to_max_prefix_list_valid.
iModIntro. iExists γ, []. rewrite /=. iFrame. by eauto.
Qed.

#[global]
Instance version_frag_persistent γ n x : Persistent (version_frag γ n x).
Proof. apply _. Qed.

Lemma version_auth_frag γ dq n x : version_auth γ dq n x -∗ version_frag γ n x.
Proof.
iDestruct 1 as "(%xs & [own1 #own2] & %nE)".
iExists xs; eauto.
Qed.

Lemma version_update γ n x y :
  version_auth γ (DfracOwn 1) n x ==∗ version_auth γ (DfracOwn 1) (n + 1) y.
Proof.
iDestruct 1 as "(%xs & own & ->)".
iMod (own_update with "own") as "own".
  eapply auth_update.
  apply (max_prefix_list_local_update _ ((xs ++ [x]) ++ [y])).
  by exists [y].
iModIntro. rewrite plus_comm /=.
iExists (xs ++ [x]). rewrite own_op app_length. iFrame.
iPureIntro. simpl. lia.
Qed.

(* FIXME: What if A is not discrete? *)
Lemma version_auth_agree `{OfeDiscrete A} γ dq1 dq2 n x y :
  version_auth γ dq1 n x -∗
  version_auth γ dq2 n y -∗
  x ≡ y.
Proof.
iIntros "(%xs & [own_x _] & %e1)".
iIntros "(%ys & [own_y _] & %e2)".
iPoseProof (own_valid_2 with "own_x own_y") as "%valid".
have {}valid := auth_auth_dfrac_op_inv _ _ _ _ valid.
have e := to_max_prefix_list_inj _ _ valid.
have ex : last (xs ++ [x]) = Some x by rewrite last_snoc.
have ey : last (ys ++ [y]) = Some y by rewrite last_snoc.
iAssert (Some x ≡ Some y)%I as "e".
  by rewrite -ex -ey e.
by rewrite option_equivI.
Qed.

(* FIXME: What if A is not discrete? *)
Lemma version_auth_frag_agree `{OfeDiscrete A} γ dq n x y :
  version_auth γ dq n x -∗
  version_frag γ    n y -∗
  x ≡ y.
Proof.
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

End Version.
