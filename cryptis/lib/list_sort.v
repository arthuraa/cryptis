(** Small generic list utilities on top of stdpp, used to canonicalise lists
    with [merge_sort]:

    - [rem x l] removes the *first* occurrence of [x] from [l] (like mathcomp's
      [seq.rem]), parameterised by an [EqDecision] instance.  stdpp has no
      first-occurrence removal (its [list_difference] removes *all* matches, and
      the multiset view [elem_of_Permutation] is only existential), so we define
      it here.

    - lemmas relating [merge_sort R] (for an arbitrary decidable total order [R])
      to membership, [Forall], length and sortedness. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import sorting list.

Section Rem.
Context {A : Type} `{EqDecision A}.
Implicit Types (x z : A) (l : list A).

Fixpoint rem x l : list A :=
  match l with
  | [] => []
  | y :: l => if bool_decide (x = y) then l else y :: rem x l
  end.

Lemma elem_of_rem {z x l} : z ∈ rem x l -> z ∈ l.
Proof.
elim: l => [|a l IH] //=.
case_bool_decide as H.
- move=> ?; exact: list_elem_of_further.
- rewrite !elem_of_cons; move=> [->|/IH ?]; by [left|right].
Qed.

End Rem.

Section MergeSort.
Context {A : Type} (R : relation A)
  `{!RelDecision R, !Transitive R, !Total R, !AntiSymm (=@{A}) R}.
Implicit Types (x : A) (l : list A) (P : A -> Prop).

Lemma elem_of_merge_sort x l : x ∈ merge_sort R l ↔ x ∈ l.
Proof. by rewrite (merge_sort_Permutation R l). Qed.

Lemma Forall_merge_sort P l : Forall P (merge_sort R l) ↔ Forall P l.
Proof. by rewrite (merge_sort_Permutation R l). Qed.

Lemma length_merge_sort l : length (merge_sort R l) = length l.
Proof. by rewrite (merge_sort_Permutation R l). Qed.

Lemma merge_sort_sorted l : StronglySorted R (merge_sort R l).
Proof. apply: StronglySorted_merge_sort. Qed.

Lemma merge_sort_id l : StronglySorted R l -> merge_sort R l = l.
Proof.
move=> H.
exact: (StronglySorted_unique R (merge_sort R l) l
          (merge_sort_sorted l) H (merge_sort_Permutation R l)).
Qed.

End MergeSort.
