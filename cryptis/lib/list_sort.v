(** Small generic list utilities on top of stdpp, used to canonicalise lists
    with [merge_sort]:

    - [rem x l] removes the *first* occurrence of [x] from [l] (like mathcomp's
      [seq.rem]), parameterised by an [EqDecision] instance.  stdpp has no
      first-occurrence removal (its [list_difference] removes *all* matches, and
      the multiset view [elem_of_Permutation] is only existential), so we define
      it here.

    - [count_mem x l] counts the occurrences of [x] in [l] (like mathcomp's
      [count_mem]).  stdpp has no list-counting function, so we define it and
      prove the multiset characterisation of permutations
      ([Permutation_count_mem]): two lists are a permutation of each other iff
      every element occurs equally often.

    - lemmas relating [merge_sort R] (for an arbitrary decidable total order [R])
      to membership, [Forall], length and sortedness. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import sorting list numbers.
From Stdlib Require Import Lia.

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

Lemma rem_submseteq x l : rem x l ⊆+ l.
Proof.
elim: l => [|a l IH] /=.
- exact: submseteq_nil_l.
- case_bool_decide as H.
  + apply: submseteq_cons; reflexivity.
  + by apply: submseteq_skip.
Qed.

Lemma length_rem x l : x ∈ l -> length (rem x l) = length l - 1.
Proof.
elim: l => [|a l IH] Hin; first by move: Hin; rewrite elem_of_nil.
move: Hin; rewrite /= elem_of_cons => Hin.
case_bool_decide as H; first by simpl; lia.
have Hin' : x ∈ l by case: Hin => [E|//]; rewrite E in H.
rewrite /= (IH Hin').
case: l Hin' {IH Hin} => [|b l'] Hin'; first by move: Hin'; rewrite elem_of_nil.
by simpl; lia.
Qed.

End Rem.

Section Count.
Context {A : Type} `{EqDecision A}.
Implicit Types (x y z : A) (l : list A).

Fixpoint count_mem x l : nat :=
  match l with
  | [] => 0
  | y :: l => (if bool_decide (x = y) then 1 else 0) + count_mem x l
  end.

Lemma count_mem_app x l1 l2 :
  count_mem x (l1 ++ l2) = count_mem x l1 + count_mem x l2.
Proof. elim: l1 => [|a l1 IH] //=. rewrite IH; lia. Qed.

Lemma count_mem_Permutation x l1 l2 :
  l1 ≡ₚ l2 -> count_mem x l1 = count_mem x l2.
Proof.
move=> H; elim: H => //=.
- move=> y l l' _ IH; lia.
- move=> y z l; lia.
- move=> l l' l'' _ IH1 _ IH2; lia.
Qed.

Lemma elem_of_count_mem x l : x ∈ l <-> count_mem x l ≠ 0.
Proof.
elim: l => [|a l IH] /=.
- rewrite elem_of_nil; split=> [[]|]; lia.
- rewrite elem_of_cons IH; case_bool_decide as H; split.
  + move=> _; lia.
  + move=> _; by left.
  + by move=> [E|Hc]; [rewrite E in H | lia].
  + move=> Hc; by right.
Qed.

Lemma not_elem_of_count_mem x l : x ∉ l <-> count_mem x l = 0.
Proof. rewrite elem_of_count_mem; split; [move=> H|move=> -> H]; lia. Qed.

Lemma count_mem_rem x y l :
  count_mem x (rem y l) = count_mem x l - (if bool_decide (x = y) then 1 else 0).
Proof.
elim: l => [|a l IH] /=; first lia.
case E: (bool_decide (y = a)).
- move/bool_decide_eq_true_1 in E; rewrite E /=.
  case_bool_decide as Hxa; lia.
- move/bool_decide_eq_false_1 in E; rewrite /= IH /=.
  case_bool_decide as Hxa; case_bool_decide as Hxy; try lia.
  exfalso; apply: E; congruence.
Qed.

Lemma rem_Permutation {x l} : x ∈ l -> l ≡ₚ x :: rem x l.
Proof.
elim: l => [|a l IH]; first by rewrite elem_of_nil.
rewrite elem_of_cons /= => Hin.
case_bool_decide as Hxa.
- by rewrite Hxa.
- have Hin' : x ∈ l by case: Hin => [E|//]; rewrite E in Hxa.
  etrans; [apply: perm_skip; exact: (IH Hin') | apply: Permutation_swap].
Qed.

Lemma Permutation_count_mem l1 l2 :
  (forall x, count_mem x l1 = count_mem x l2) -> l1 ≡ₚ l2.
Proof.
elim: l1 l2 => [|a l1 IH] l2 H.
- suff -> : l2 = [] by [].
  case: l2 H => [//|b l2] H.
  move: (H b) => /=; rewrite bool_decide_eq_true_2 //; lia.
- have Ha : a ∈ l2.
  { apply/elem_of_count_mem. move: (H a) => /=.
    rewrite bool_decide_eq_true_2 //; lia. }
  rewrite (rem_Permutation Ha); apply: perm_skip.
  apply: IH => x; rewrite (count_mem_rem x a l2).
  move: (H x) => /=; case_bool_decide as Hxa; lia.
Qed.

End Count.

Lemma fmap_rem {A B} `{EqDecision A} `{EqDecision B} (f : A -> B) x l :
  (forall a b, f a = f b -> a = b) ->
  f <$> rem x l = rem (f x) (f <$> l).
Proof.
move=> finj; elim: l => [//|y l IH] /=.
case_bool_decide as Hxy; case_bool_decide as Hfxy.
- done.
- exfalso; apply: Hfxy; by rewrite Hxy.
- exfalso; apply: Hxy; exact: (finj _ _ Hfxy).
- by rewrite fmap_cons IH.
Qed.

Lemma count_mem_fmap {A B} `{EqDecision A} `{EqDecision B} (f : A -> B) x l :
  (forall a b, f a = f b -> a = b) ->
  count_mem (f x) (f <$> l) = count_mem x l.
Proof.
move=> finj; elim: l => [//|y l IH] /=; rewrite IH.
rewrite (bool_decide_ext (f x = f y) (x = y)) //.
split; [exact: finj | by move=> ->].
Qed.

Section SumList.
Context {A : Type} (f : A -> nat).

Lemma sum_list_with_Permutation l1 l2 :
  l1 ≡ₚ l2 -> sum_list_with f l1 = sum_list_with f l2.
Proof.
move=> H; elim: H => //=.
- move=> x l l' _ IH; lia.
- move=> x y l; lia.
- move=> l l' l'' _ IH1 _ IH2; lia.
Qed.

End SumList.

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

Lemma merge_sort_Permutation_eq l1 l2 :
  l1 ≡ₚ l2 -> merge_sort R l1 = merge_sort R l2.
Proof.
move=> H; apply: (StronglySorted_unique R);
  [exact: merge_sort_sorted | exact: merge_sort_sorted |].
by rewrite !(merge_sort_Permutation R).
Qed.

Lemma merge_sort_eq_Permutation l1 l2 :
  merge_sort R l1 = merge_sort R l2 -> l1 ≡ₚ l2.
Proof.
move=> H. by rewrite -(merge_sort_Permutation R l1) H merge_sort_Permutation.
Qed.

End MergeSort.

Section MergeSortFmap.
Context {A B} (RA : relation A) (RB : relation B)
  `{!RelDecision RA, !Transitive RA, !Total RA,
    !RelDecision RB, !Transitive RB, !Total RB, !@AntiSymm B (=) RB}.

Lemma merge_sort_fmap (f : A -> B) (Hf : forall x y, RA x y <-> RB (f x) (f y)) l :
  f <$> merge_sort RA l = merge_sort RB (f <$> l).
Proof.
apply: (StronglySorted_unique RB).
- apply: (StronglySorted_fmap f RA RB).
  + move=> x y HR; exact: (proj1 (Hf x y) HR).
  + exact: (StronglySorted_merge_sort RA l).
- exact: (StronglySorted_merge_sort RB (f <$> l)).
- rewrite (merge_sort_Permutation RB (f <$> l)).
  by rewrite (merge_sort_Permutation RA l).
Qed.

End MergeSortFmap.
