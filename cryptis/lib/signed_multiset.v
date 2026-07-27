(** Signed multisets over a type [T] equipped with a decidable total order [R]
    and a fixed-point-free involution [i : T -> T] (i.e. [i (i x) = x] and
    [i x <> x]).  Elements [x] and [i x] are mutual inverses: they cancel.

    A signed multiset is represented by a [list T].  Its "signed count" at [x] is

        count_sms x X = count_mem x X - count_mem (i x) X   (in Z),

    so that [count_sms (i x) X = - count_sms x X].  A list is well-formed
    ([wf_sms]) when it is sorted and no element occurs together with its inverse
    ([invs_canceled]).  [to] normalises an arbitrary list by cancelling inverse
    pairs and sorting; it is the canonical form for the signed counts:

      (1) [wf (to X)] always holds;
      (2) [to X = to Y <-> forall x, count x X = count x Y]. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import sorting list numbers.
From Stdlib Require Import ZArith Lia.
From cryptis.lib Require Import list_sort.

Module SMS.

Section SignedMultiset.

Context {T : Type} `{EqDecision T}.
Context (R : relation T)
  `{!RelDecision R, !Transitive R, !Total R, !AntiSymm (=@{T}) R}.
Context (i : T -> T) (iK : forall x, i (i x) = x) (iN : forall x, i x <> x).

Implicit Types (x y z : T) (X Y : list T).

(** ** Definitions *)

Definition count x X : Z :=
  (Z.of_nat (count_mem x X) - Z.of_nat (count_mem (i x) X))%Z.

(** [invs_canceled X] : no element of [X] occurs together with its inverse. *)
Definition invs_canceled X : bool :=
  forallb (fun x => bool_decide (i x ∉ X)) X.

Definition wf X : bool :=
  bool_decide (StronglySorted R X) && invs_canceled X.

(** [insert x X] adds [x] to [X], cancelling against an occurrence of [i x] if
    one is present; [cancel] cancels all inverse pairs of a list. *)
Definition insert x X : list T :=
  if bool_decide (i x ∈ X) then rem (i x) X else x :: X.

Definition cancel : list T -> list T := foldr insert [].

Definition to X : list T := merge_sort R (cancel X).

(** ** The involution *)

Lemma i_inj z x : i z = i x -> z = x.
Proof. move=> e; by rewrite -(iK z) e iK. Qed.

Lemma bool_decide_ii z x : bool_decide (i z = i x) = bool_decide (z = x).
Proof.
apply: bool_decide_ext; split.
- exact: i_inj.
- by move=> ->.
Qed.

Lemma bool_decide_ix z x : bool_decide (i z = x) = bool_decide (z = i x).
Proof.
apply: bool_decide_ext; split.
- by move=> e; rewrite -(iK z) e.
- by move=> e; rewrite e iK.
Qed.

(** ** Signed counts *)

Lemma count_Permutation z X Y : X ≡ₚ Y -> count z X = count z Y.
Proof.
move=> e; rewrite /count.
by rewrite (count_mem_Permutation z X Y e) (count_mem_Permutation (i z) X Y e).
Qed.

Lemma count_cons z x X :
  count z (x :: X) =
  (count z X + Z.b2z (bool_decide (z = x))
             - Z.b2z (bool_decide (i z = x)))%Z.
Proof. rewrite /count /=; case_bool_decide; case_bool_decide; simpl; lia. Qed.

(** Cancelling one [i x] against [x] leaves every signed count unchanged:
    [insert] behaves like consing as far as [count_sms] is concerned. *)

Lemma count_insert z x X : count z (insert x X) = count z (x :: X).
Proof.
rewrite /insert; case_bool_decide as Hin; last done.
have e : count z X = count z (i x :: rem (i x) X)
  by apply: count_Permutation; exact: rem_Permutation Hin.
rewrite (count_cons z (i x) (rem (i x) X)) in e.
rewrite (count_cons z x X) (bool_decide_ii z x) in e *.
rewrite (bool_decide_ix z x); lia.
Qed.

Lemma cancel_cons x X : cancel (x :: X) = insert x (cancel X).
Proof. reflexivity. Qed.

Lemma count_cancel z X : count z (cancel X) = count z X.
Proof.
elim: X => [//|x X IH].
by rewrite cancel_cons count_insert
           (count_cons z x (cancel X)) (count_cons z x X) IH.
Qed.

Lemma count_to z X : count z (to X) = count z X.
Proof.
rewrite /to (count_Permutation z _ _ (merge_sort_Permutation R (cancel X))).
exact: count_cancel.
Qed.

(** ** Cancellation removes all inverse pairs *)

Lemma invs_canceledP X : invs_canceled X <-> (forall x, x ∈ X -> i x ∉ X).
Proof.
rewrite /invs_canceled forallb_True list.Forall_forall; split => H x xX; move: (H x xX).
- exact: bool_decide_unpack.
- exact: bool_decide_pack.
Qed.

Lemma invs_canceled_Permutation X Y : X ≡ₚ Y -> invs_canceled X = invs_canceled Y.
Proof.
move=> e; apply: eq_bool_prop_intro.
rewrite !invs_canceledP; split => H x.
- rewrite -e; exact: (H x).
- rewrite e; exact: (H x).
Qed.

Lemma invs_canceled_insert x X : invs_canceled X -> invs_canceled (insert x X).
Proof.
rewrite !invs_canceledP => H y.
rewrite /insert; case_bool_decide as Hin.
- move=> yin iyin.
  exact: (H y (elem_of_rem yin) (elem_of_rem iyin)).
- rewrite elem_of_cons => -[-> | yX].
  + rewrite elem_of_cons => -[ixx | ixX].
    * exact: (iN x ixx).
    * exact: (Hin ixX).
  + rewrite elem_of_cons => -[iyx | iyX].
    * apply: Hin.
      have -> : i x = y by rewrite -iyx iK.
      exact: yX.
    * exact: (H y yX iyX).
Qed.

Lemma invs_canceled_cancel X : invs_canceled (cancel X).
Proof.
elim: X => [|x X IH].
- by rewrite /invs_canceled /cancel /=.
- rewrite cancel_cons; by apply: invs_canceled_insert.
Qed.

(** If [invs_canceled X], the plain multiplicity is recovered from the
    signed count. *)
Lemma count_mem_of_invs_canceled z X :
  invs_canceled X -> Z.of_nat (count_mem z X) = Z.max 0 (count z X).
Proof.
move=> /invs_canceledP H; rewrite /count.
case: (decide (z ∈ X)) => zX.
- rewrite (proj1 (not_elem_of_count_mem (i z) X) (H z zX)); lia.
- rewrite (proj1 (not_elem_of_count_mem z X) zX); lia.
Qed.

(** ** Main results *)

Lemma wf_to X : wf (to X).
Proof.
rewrite /wf /to andb_True; split.
- apply: bool_decide_pack; exact: merge_sort_sorted.
- rewrite (invs_canceled_Permutation _ _ (merge_sort_Permutation R (cancel X))).
  exact: invs_canceled_cancel.
Qed.

Lemma to_eq X Y :
  to X = to Y <-> (forall x, count x X = count x Y).
Proof.
split.
- move=> e x.
  by rewrite -(count_to x X) -(count_to x Y) e.
- move=> Hc; rewrite /to.
  apply: merge_sort_Permutation_eq; apply: Permutation_count_mem => z.
  apply: Nat2Z.inj.
  rewrite (count_mem_of_invs_canceled z (cancel X) (invs_canceled_cancel X)).
  rewrite (count_mem_of_invs_canceled z (cancel Y) (invs_canceled_cancel Y)).
  by rewrite !count_cancel (Hc z).
Qed.

End SignedMultiset.

End SMS.
