(** Finite multisets over a type [T] ordered by a [Lexico] instance.

    [mset T] is a list sorted by [le], the reflexive closure of [lexico], so
    each multiset has one representation: equality is Leibniz ([count_inj]),
    and [elements] returns the sorted list.  HeapLang code can compute that
    order; stdpp's [gmultiset] would need [Countable T] and order elements by
    their encodings.

    [count x X] is the multiplicity of [x] in [X], and [of_list] sorts a list
    into a multiset.  [mset_solver] proves equations between multisets built
    from [∅], [{[+ x +]}], [⊎], [∖] and [of_list] by comparing counts. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import sorting list numbers proof_irrel.
From Stdlib Require Import Lia.
From cryptis.lib Require Import list_sort.

Module MSet.

(** ** The order of a [Lexico] type

    Sorting needs a total order: [le] is the reflexive closure of the strict
    [lexico]. *)

Section Order.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Definition le : relation T := λ x y, x = y ∨ lexico x y.

#[global] Instance le_dec : RelDecision le :=
  λ x y, decide (x = y ∨ lexico x y).

#[global] Instance le_trans : Transitive le.
Proof.
move=> x y z [->|xy] [<-|yz]; [by left|by right|by right|].
by right; trans y.
Qed.

#[global] Instance le_total : Total le.
Proof.
move=> x y; case: (trichotomy lexico x y) => [xy|[->|yx]].
- by left; right.
- by left; left.
- by right; right.
Qed.

#[global] Instance le_antisymm : AntiSymm (=) le.
Proof.
move=> x y [//|xy] [//|yx]; exfalso.
by apply: (irreflexivity lexico x); trans y.
Qed.

End Order.

(** ** Multisets *)

Section MultiSet.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Implicit Types (x y z : T) (l : list T).

Definition wf l : bool := bool_decide (StronglySorted le l).

Record mset := mk { car : list T; wf_car : wf car }.

Implicit Types (X Y W : mset).

Definition of_list l : mset :=
  mk (merge_sort le l) (bool_decide_pack _ (merge_sort_sorted le l)).

Definition count x X : nat := count_mem x (car X).

#[global] Arguments count : simpl never.

#[global] Instance empty_instance : Empty mset := of_list [].
#[global] Instance singleton_instance : SingletonMS T mset :=
  λ x, of_list [x].
#[global] Instance disj_union_instance : DisjUnion mset :=
  λ X Y, of_list (car X ++ car Y).
#[global] Instance difference_instance : Difference mset :=
  λ X Y, of_list (foldr rem (car X) (car Y)).
#[global] Instance elements_instance : Elements T mset := car.
#[global] Instance elem_of_instance : ElemOf T mset := λ x X, x ∈ car X.
#[global] Instance elem_of_dec x X : Decision (x ∈ X) := decide (x ∈ car X).
#[global] Instance disjoint_instance : Disjoint mset :=
  λ X Y, car X ## car Y.
#[global] Instance disjoint_dec : RelDecision (##@{mset}) :=
  λ X Y, decide (car X ## car Y).

Lemma car_inj X Y : car X = car Y → X = Y.
Proof.
case: X Y => [l1 w1] [l2 w2] /= e; subst l2.
by rewrite (proof_irrel w1 w2).
Qed.

#[global] Instance eq_dec : EqDecision mset := λ X Y,
  match decide (car X = car Y) with
  | left e => left (car_inj X Y e)
  | right n => right (λ e, n (f_equal car e))
  end.

Lemma elements_sorted X : StronglySorted le (elements X).
Proof. exact: bool_decide_unpack _ (wf_car X). Qed.

Lemma count_mem_elements x X : count_mem x (elements X) = count x X.
Proof. done. Qed.

Lemma count_inj X Y : (∀ x, count x X = count x Y) → X = Y.
Proof.
move=> e; apply: car_inj; apply: (StronglySorted_unique le).
- exact: elements_sorted.
- exact: elements_sorted.
- exact: (Permutation_count_mem _ _ e).
Qed.

(** *** Lists *)

Lemma elements_of_list l : elements (of_list l) ≡ₚ l.
Proof. exact: merge_sort_Permutation. Qed.

Lemma count_of_list x l : count x (of_list l) = count_mem x l.
Proof. exact: (count_mem_Permutation x _ _ (elements_of_list l)). Qed.

Lemma elem_of_of_list x l : x ∈ of_list l ↔ x ∈ l.
Proof. exact: elem_of_merge_sort. Qed.

Lemma of_list_elements X : of_list (elements X) = X.
Proof. apply: car_inj; exact: (merge_sort_id le _ (elements_sorted X)). Qed.

#[global] Instance of_list_proper : Proper ((≡ₚ) ==> (=)) of_list.
Proof.
move=> l1 l2 e; apply: count_inj => x; rewrite !count_of_list.
exact: count_mem_Permutation.
Qed.

(** *** Counts *)

#[local] Lemma count_mem_foldr_rem x l1 l2 :
  count_mem x (foldr rem l1 l2) = count_mem x l1 - count_mem x l2.
Proof.
elim: l2 => [|y l2 IH] /=; first lia.
rewrite count_mem_rem IH; case_bool_decide; simpl; lia.
Qed.

Lemma count_empty x : count x ∅ = 0.
Proof. done. Qed.

Lemma count_singleton x y :
  count x {[+ y +]} = if bool_decide (x = y) then 1 else 0.
Proof.
have -> : count x {[+ y +]} = count_mem x [y] by [].
by rewrite /= Nat.add_0_r.
Qed.

Lemma count_disj_union x X Y : count x (X ⊎ Y) = count x X + count x Y.
Proof.
have -> : X ⊎ Y = of_list (elements X ++ elements Y) by [].
by rewrite count_of_list count_mem_app.
Qed.

Lemma count_difference x X Y : count x (X ∖ Y) = count x X - count x Y.
Proof.
have -> : X ∖ Y = of_list (foldr rem (elements X) (elements Y)) by [].
by rewrite count_of_list count_mem_foldr_rem.
Qed.

(** *** Membership *)

Lemma elem_of_elements x X : x ∈ elements X ↔ x ∈ X.
Proof. done. Qed.

Lemma elem_of_count x X : x ∈ X ↔ 0 < count x X.
Proof.
rewrite -elem_of_elements elem_of_count_mem count_mem_elements; lia.
Qed.

Lemma not_elem_of_count x X : x ∉ X ↔ count x X = 0.
Proof. rewrite elem_of_count; lia. Qed.

Lemma not_elem_of_empty x : x ∉ (∅ : mset).
Proof. by rewrite not_elem_of_count. Qed.

Lemma elem_of_singleton x y : x ∈ ({[+ y +]} : mset) ↔ x = y.
Proof. exact: list_elem_of_singleton. Qed.

Lemma elem_of_disj_union x X Y : x ∈ X ⊎ Y ↔ x ∈ X ∨ x ∈ Y.
Proof. rewrite !elem_of_count count_disj_union; lia. Qed.

Lemma elem_of_difference x X Y : x ∈ X ∖ Y ↔ count x Y < count x X.
Proof. rewrite elem_of_count count_difference; lia. Qed.

(** *** Elements *)

Lemma elements_empty : elements (∅ : mset) = [].
Proof. done. Qed.

Lemma elements_singleton x : elements ({[+ x +]} : mset) = [x].
Proof. done. Qed.

Lemma elements_disj_union X Y : elements (X ⊎ Y) ≡ₚ elements X ++ elements Y.
Proof. exact: elements_of_list. Qed.

Lemma elements_empty_inv X : elements X = [] → X = ∅.
Proof. by move=> e; rewrite -(of_list_elements X) e. Qed.

(** *** Disjointness *)

Lemma disjoint_count X Y : X ## Y ↔ ∀ x, count x X = 0 ∨ count x Y = 0.
Proof.
have e x W : x ∈ car W ↔ 0 < count x W := elem_of_count x W.
split=> d x.
- by have := d x; rewrite !e; lia.
- by move=> /e ? /e ?; have := d x; lia.
Qed.

Lemma difference_disjoint X Y : X ∖ Y ## Y ∖ X.
Proof. apply/disjoint_count => x; rewrite !count_difference; lia. Qed.

End MultiSet.

Arguments mset T {_ _ _ _}.

Ltac mset_solver :=
  apply: count_inj => ?;
  rewrite ?(count_empty, count_singleton, count_disj_union, count_difference,
            count_of_list, count_mem_app) /=;
  repeat case_bool_decide; subst; simpl; lia.

(** ** Laws *)

Section Laws.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Implicit Types (x : T) (l : list T) (X Y W : mset T).

#[global] Instance disj_union_comm : Comm (=@{mset T}) (⊎).
Proof. move=> X Y; mset_solver. Qed.

#[global] Instance disj_union_assoc : Assoc (=@{mset T}) (⊎).
Proof. move=> X Y W; mset_solver. Qed.

#[global] Instance disj_union_left_id : LeftId (=@{mset T}) ∅ (⊎).
Proof. move=> X; mset_solver. Qed.

#[global] Instance disj_union_right_id : RightId (=@{mset T}) ∅ (⊎).
Proof. move=> X; mset_solver. Qed.

Lemma of_list_nil : of_list [] = (∅ : mset T).
Proof. done. Qed.

Lemma of_list_app l1 l2 : of_list (l1 ++ l2) = of_list l1 ⊎ of_list l2.
Proof. mset_solver. Qed.

Lemma of_list_cons x l : of_list (x :: l) = {[+ x +]} ⊎ of_list l.
Proof. mset_solver. Qed.

Lemma mset_ind (P : mset T → Prop) :
  P ∅ → (∀ x X, P X → P ({[+ x +]} ⊎ X)) → ∀ X, P X.
Proof.
move=> P0 PS X; rewrite -(of_list_elements X).
elim: (elements X) => [|x l IH]; first exact: P0.
by rewrite of_list_cons; apply: PS.
Qed.

End Laws.

End MSet.
