(** Finite multisets over a type [T] ordered by a [Lexico] instance.

    [mset T] is a list sorted by [le], the reflexive closure of [lexico], so
    each multiset has one representation: equality is Leibniz ([count_inj]),
    and [elements] returns the sorted list.  HeapLang code can compute that
    order; stdpp's [gmultiset] would need [Countable T] and order elements by
    their encodings.

    [count x X] is the multiplicity of [x] in [X], and [of_list] sorts a list
    into a multiset.  [mset_solver] proves equations between multisets built
    from [∅], [{[+ x +]}], [⊎], [∖] and [of_list] by comparing counts.
    Multisets are themselves ordered by their sorted lists, so they can be
    elements of multisets and signed multisets, as the monomials of
    [Poly.poly] are.  The operations are locked, since computing with them in
    proofs is slow; [unlock] exposes their definitions. *)

From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From stdpp Require Import sorting list numbers proof_irrel lexico.
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

lock Definition of_list l : mset :=
  mk (merge_sort le l) (bool_decide_pack _ (merge_sort_sorted le l)).

lock Definition count x X : nat := count_mem x (car X).

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
#[global] Instance subseteq_instance : SubsetEq mset :=
  λ X Y, ∀ x, count x X ≤ count x Y.
#[global] Instance size_instance : Size mset := λ X, length (car X).

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

#[global] Instance lexico_instance : Lexico mset :=
  λ X Y, lexico (car X) (car Y).

#[global] Instance lexico_strict : StrictOrder (@lexico mset _).
Proof.
split; first by move=> X; exact: (irreflexivity lexico (car X)).
move=> X Y W; exact: (@transitivity _ (@lexico (list T) _) _).
Qed.

#[global] Instance lexico_trichotomyT : TrichotomyT (@lexico mset _).
Proof.
refine (λ X Y,
  match trichotomyT lexico (car X) (car Y) with
  | inleft (left p) => inleft (left p)
  | inleft (right e) => inleft (right _)
  | inright p => inright p
  end).
abstract (exact: car_inj e).
Defined.

Lemma elements_sorted X : StronglySorted le (elements X).
Proof. exact: bool_decide_unpack _ (wf_car X). Qed.

Lemma count_mem_elements x X : count_mem x (elements X) = count x X.
Proof. by rewrite [count]unlock. Qed.

Lemma count_inj X Y : (∀ x, count x X = count x Y) → X = Y.
Proof.
move=> e; apply: car_inj; apply: (StronglySorted_unique le).
- exact: elements_sorted.
- exact: elements_sorted.
- by apply: Permutation_count_mem => x; rewrite !count_mem_elements.
Qed.

(** *** Lists *)

Lemma elements_of_list_sort l : elements (of_list l) = merge_sort le l.
Proof. by rewrite [of_list]unlock. Qed.

Lemma elements_of_list l : elements (of_list l) ≡ₚ l.
Proof. rewrite elements_of_list_sort; exact: merge_sort_Permutation. Qed.

Lemma count_of_list x l : count x (of_list l) = count_mem x l.
Proof.
rewrite -count_mem_elements.
exact: (count_mem_Permutation x _ _ (elements_of_list l)).
Qed.

Lemma elem_of_of_list x l : x ∈ of_list l ↔ x ∈ l.
Proof. rewrite [of_list]unlock; exact: elem_of_merge_sort. Qed.

Lemma of_list_elements X : of_list (elements X) = X.
Proof.
apply: car_inj; rewrite [of_list]unlock.
exact: (merge_sort_id le _ (elements_sorted X)).
Qed.

#[global] Instance of_list_proper : Proper ((≡ₚ) ==> (=)) of_list.
Proof.
move=> l1 l2 e; apply: count_inj => x; rewrite !count_of_list.
exact: count_mem_Permutation.
Qed.

Lemma elements_empty : elements (∅ : mset) = [].
Proof. by rewrite (_ : ∅ = of_list []) // [of_list]unlock. Qed.

Lemma elements_singleton x : elements ({[+ x +]} : mset) = [x].
Proof. by rewrite (_ : {[+ x +]} = of_list [x]) // [of_list]unlock. Qed.

Lemma car_empty : car (∅ : mset) = [].
Proof. exact: elements_empty. Qed.

Lemma car_singleton x : car ({[+ x +]} : mset) = [x].
Proof. exact: elements_singleton. Qed.

(** *** Counts *)

#[local] Lemma count_mem_foldr_rem x l1 l2 :
  count_mem x (foldr rem l1 l2) = count_mem x l1 - count_mem x l2.
Proof.
elim: l2 => [|y l2 IH] /=; first lia.
rewrite count_mem_rem IH; case_bool_decide; simpl; lia.
Qed.

Lemma count_empty x : count x ∅ = 0.
Proof. exact: count_of_list x []. Qed.

Lemma count_singleton x y :
  count x {[+ y +]} = if bool_decide (x = y) then 1 else 0.
Proof.
have -> : count x {[+ y +]} = count_mem x [y] by exact: count_of_list.
by rewrite /= Nat.add_0_r.
Qed.

Lemma count_disj_union x X Y : count x (X ⊎ Y) = count x X + count x Y.
Proof.
have -> : X ⊎ Y = of_list (elements X ++ elements Y) by [].
by rewrite count_of_list count_mem_app !count_mem_elements.
Qed.

Lemma count_difference x X Y : count x (X ∖ Y) = count x X - count x Y.
Proof.
have -> : X ∖ Y = of_list (foldr rem (elements X) (elements Y)) by [].
by rewrite count_of_list count_mem_foldr_rem !count_mem_elements.
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
Proof. by rewrite not_elem_of_count count_empty. Qed.

Lemma elem_of_singleton x y : x ∈ ({[+ y +]} : mset) ↔ x = y.
Proof.
rewrite -elem_of_elements elements_singleton; exact: list_elem_of_singleton.
Qed.

Lemma elem_of_disj_union x X Y : x ∈ X ⊎ Y ↔ x ∈ X ∨ x ∈ Y.
Proof. rewrite !elem_of_count count_disj_union; lia. Qed.

Lemma elem_of_difference x X Y : x ∈ X ∖ Y ↔ count x Y < count x X.
Proof. rewrite elem_of_count count_difference; lia. Qed.

(** *** Elements *)

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

Lemma difference_disjoint_l X Y : X ## Y → X ∖ Y = X.
Proof.
move=> /disjoint_count d; apply: count_inj => x.
by rewrite count_difference; have := d x; lia.
Qed.

Lemma of_list_disjoint l1 l2 : l1 ## l2 → of_list l1 ## of_list l2.
Proof.
by move=> d x /elem_of_of_list h1 /elem_of_of_list h2; exact: d x h1 h2.
Qed.

Lemma elements_of_list_wf l : wf l → elements (of_list l) = l.
Proof.
by rewrite [of_list]unlock => /bool_decide_unpack; exact: merge_sort_id.
Qed.

(** *** Inclusion *)

#[global] Instance subseteq_preorder : PreOrder (⊆@{mset}).
Proof.
split; first by move=> X x.
by move=> X Y W h1 h2 x; move: (h1 x) (h2 x); lia.
Qed.

Lemma subseteq_count X Y : X ⊆ Y ↔ ∀ x, count x X ≤ count x Y.
Proof. done. Qed.

Lemma elem_of_subseteq x X Y : X ⊆ Y → x ∈ X → x ∈ Y.
Proof. by rewrite !elem_of_count => /(_ x); lia. Qed.

Lemma singleton_subseteq x X : {[+ x +]} ⊆ X ↔ x ∈ X.
Proof.
rewrite elem_of_count; split.
- by move=> /(_ x); rewrite count_singleton bool_decide_eq_true_2 //; lia.
- by move=> h y; rewrite count_singleton; case_bool_decide; subst; lia.
Qed.

(** *** Size *)

Lemma size_elements X : size X = length (elements X).
Proof. done. Qed.

Lemma size_singleton x : size ({[+ x +]} : mset) = 1.
Proof. by rewrite size_elements elements_singleton. Qed.

Lemma size_disj_union X Y : size (X ⊎ Y) = size X + size Y.
Proof.
rewrite !size_elements (Permutation_length (elements_disj_union X Y)).
exact: length_app.
Qed.

Lemma subseteq_size X Y : X ⊆ Y → size X ≤ size Y.
Proof.
move=> h; have -> : Y = X ⊎ (Y ∖ X).
  apply: count_inj => x; rewrite count_disj_union count_difference.
  by have := h x; lia.
rewrite size_disj_union; lia.
Qed.

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

(** ** The graded order

    [glt] compares multisets by size, and multisets of equal size by
    [lexico].  Unlike [lexico] (where [∅] comes before [{[+ y +]}], but
    [{[+ y +]}] after [{[+ x; y +]}] when [x] comes before [y]), it is
    compatible with [⊎] ([glt_disj_union_l]): on multisets of equal size,
    [lexico] compares counts from the least element up ([lexico_count]).
    [gmin_list] picks the least multiset of a list. *)

Section Graded.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Implicit Types (x y : T) (l : list T) (X Y Z : mset T).

Lemma count_mem_below x l : (∀ y, y ∈ l → lexico x y) → count_mem x l = 0.
Proof.
elim: l => [//|y l IH] h /=.
have nxy : x ≠ y.
  by move=> e; apply: (irreflexivity lexico x); apply: h; rewrite e; left.
rewrite (bool_decide_eq_false_2 _ nxy) IH //.
by move=> z zl; apply: h; right.
Qed.

Lemma count_mem_below_sorted x a l :
  StronglySorted le (a :: l) → lexico x a → count_mem x (a :: l) = 0.
Proof.
move=> s xa; have [_ h] := StronglySorted_inv s.
apply: count_mem_below => z /elem_of_cons [->|zl] //.
case: (proj1 (list.Forall_forall _ _) h z zl) => [<-|az] //.
by trans a.
Qed.

Lemma lexico_cons a b l1 l2 :
  lexico (a :: l1) (b :: l2) ↔ lexico a b ∨ a = b ∧ lexico l1 l2.
Proof. done. Qed.

Lemma lexico_count_mem l1 l2 :
  StronglySorted le l1 → StronglySorted le l2 → length l1 = length l2 →
  lexico l1 l2 ↔
  ∃ x, (∀ y, lexico y x → count_mem y l1 = count_mem y l2) ∧
       count_mem x l2 < count_mem x l1.
Proof.
elim: l1 l2 => [|a l1 IH] [|b l2] s1 s2 len.
- split=> [h|[x [_ c]]]; first by case: h.
  by move: c => /=; lia.
- by move: len => /=; lia.
- by move: len => /=; lia.
- have t1 := proj1 (StronglySorted_inv s1).
  have t2 := proj1 (StronglySorted_inv s2).
  have len' : length l1 = length l2 by case: len.
  rewrite lexico_cons.
  case: (trichotomy lexico a b) => [ab|[eab|ba]].
  + split=> _; last by left.
    exists a; split.
    * move=> y ya; have yb : lexico y b by trans a.
      by rewrite (count_mem_below_sorted y a l1 s1 ya)
        (count_mem_below_sorted y b l2 s2 yb).
    * rewrite (count_mem_below_sorted a b l2 s2 ab) /=.
      by rewrite bool_decide_eq_true_2 //; lia.
  + subst b; rewrite (IH l2 t1 t2 len'); split.
    * case=> [/(irreflexivity lexico a) []|[_ [x [hx cx]]]].
      exists x; split; last by rewrite /=; lia.
      by move=> y /hx /= ->.
    * case=> x [hx cx]; right; split=> //; exists x; split.
        by move=> y /hx /=; lia.
      by move: cx => /=; lia.
  + split.
      case=> [ab|[eab _]].
        by case: (irreflexivity lexico a); trans b.
      by subst b; case: (irreflexivity lexico a).
    case=> x [hx cx].
    case: (trichotomy lexico x b) => [xb|[exb|bx]].
    * have xa : lexico x a by trans b.
      by move: cx; rewrite (count_mem_below_sorted x a l1 s1 xa); lia.
    * subst x.
      by move: cx; rewrite (count_mem_below_sorted b a l1 s1 ba); lia.
    * have := hx b bx; rewrite (count_mem_below_sorted b a l1 s1 ba) /=.
      by rewrite bool_decide_eq_true_2.
Qed.

Lemma lexico_count X Y :
  size X = size Y →
  lexico X Y ↔
  ∃ x, (∀ y, lexico y x → count y X = count y Y) ∧ count x Y < count x X.
Proof.
move=> e.
have sX : StronglySorted le (car X) := bool_decide_unpack _ (wf_car X).
have sY : StronglySorted le (car Y) := bool_decide_unpack _ (wf_car Y).
split.
- move=> /(lexico_count_mem _ _ sX sY e) [x [hx cx]]; exists x; split.
  + by move=> y /hx; rewrite -!count_mem_elements.
  + by rewrite -!count_mem_elements.
- move=> [x [hx cx]]; apply/(lexico_count_mem _ _ sX sY e).
  exists x; split.
  + by move=> y /hx; rewrite -!count_mem_elements.
  + by move: cx; rewrite -!count_mem_elements.
Qed.

Definition glt X Y : Prop := size X < size Y ∨ size X = size Y ∧ lexico X Y.

#[global] Instance glt_dec : RelDecision glt.
Proof. move=> X Y; rewrite /glt; apply _. Defined.

Lemma glt_irrefl X : ¬ glt X X.
Proof. by case=> [|[_ /(irreflexivity lexico X)]]; lia. Qed.

Lemma glt_trans X Y Z : glt X Y → glt Y Z → glt X Z.
Proof.
rewrite /glt => -[h1|[e1 l1]] [h2|[e2 l2]]; try by left; lia.
by right; split; [lia|trans Y].
Qed.

Lemma glt_total X Y : glt X Y ∨ X = Y ∨ glt Y X.
Proof.
rewrite /glt; case: (Nat.lt_trichotomy (size X) (size Y)) => [h|[e|h]].
- by left; left.
- case: (trichotomy lexico X Y) => [l|[->|l]].
  + by left; right.
  + by right; left.
  + by right; right; right; split.
- by right; right; left.
Qed.

Lemma glt_disj_union_l Z X Y : glt X Y → glt (Z ⊎ X) (Z ⊎ Y).
Proof.
rewrite /glt !size_disj_union => -[h|[e l]]; first by left; lia.
right; split; first lia.
have e' : size (Z ⊎ X) = size (Z ⊎ Y) by rewrite !size_disj_union; lia.
apply/(lexico_count _ _ e').
have [x [hx cx]] := proj1 (lexico_count _ _ e) l.
exists x; split.
- by move=> y /hx; rewrite !count_disj_union => ->.
- by rewrite !count_disj_union; lia.
Qed.

Lemma glt_disj_union_r Z X Y : glt X Y → glt (X ⊎ Z) (Y ⊎ Z).
Proof. by rewrite !(comm (⊎) _ Z); exact: glt_disj_union_l. Qed.

Fixpoint gmin_list (ms : list (mset T)) : option (mset T) :=
  match ms with
  | [] => None
  | X :: ms =>
    Some (if gmin_list ms is Some Y then if bool_decide (glt Y X) then Y else X
          else X)
  end.

Lemma gmin_list_spec ms X :
  gmin_list ms = Some X → X ∈ ms ∧ ∀ Y, Y ∈ ms → Y = X ∨ glt X Y.
Proof.
elim: ms X => [//|Z ms IH] X /=.
case E: (gmin_list ms) => [Y|] [<-].
- have [Yl hY] := IH Y E.
  case: bool_decide_reflect => [YZ|nYZ].
  + split; first by right.
    move=> W /elem_of_cons [->|Wl]; first by right.
    by case: (hY W Wl) => [->|YW]; [left|right].
  + split; first by left.
    move=> W /elem_of_cons [->|Wl]; first by left.
    case: (glt_total Z Y) => [ZY|[eZY|YZ]]; last by case: nYZ.
    * by case: (hY W Wl) => [->|YW]; right => //; exact: glt_trans ZY YW.
    * by subst Y; exact: hY.
- have -> : ms = [] by clear IH; case: ms E.
  split; first by left.
  by move=> W /elem_of_cons [->|/elem_of_nil []]; left.
Qed.

Lemma gmin_list_None ms : gmin_list ms = None → ms = [].
Proof. by case: ms. Qed.

Lemma glt_unique (ms : list (mset T)) X Y :
  X ∈ ms → (∀ W, W ∈ ms → W = X ∨ glt X W) →
  Y ∈ ms → (∀ W, W ∈ ms → W = Y ∨ glt Y W) → X = Y.
Proof.
move=> Xm hX Ym hY.
case: (hX Y Ym) => [//|XY]; case: (hY X Xm) => [//|YX].
by case: (glt_irrefl X); exact: glt_trans XY YX.
Qed.

End Graded.

(** ** Binding and mapping *)

Section Bind.

Context {T U : Type}.
Context `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Implicit Types (x : T) (y : U) (X Y : mset T).

lock Definition bind (f : T → mset U) X : mset U :=
  of_list (elements X ≫= λ x, elements (f x)).

lock Definition map (f : T → U) X : mset U := of_list (f <$> elements X).

Lemma count_bind y f X :
  count y (bind f X) = sum_list_with (λ x, count y (f x)) (elements X).
Proof.
rewrite [bind]unlock count_of_list; elim: (elements X) => [|x l IH] //=.
by rewrite count_mem_app IH count_mem_elements.
Qed.

Lemma bind_empty f : bind f ∅ = ∅.
Proof.
by apply: count_inj => y; rewrite count_bind elements_empty count_empty.
Qed.

Lemma bind_singleton f x : bind f {[+ x +]} = f x.
Proof.
apply: count_inj => y; rewrite count_bind elements_singleton /=; lia.
Qed.

Lemma bind_disj_union f X Y : bind f (X ⊎ Y) = bind f X ⊎ bind f Y.
Proof.
apply: count_inj => y; rewrite count_disj_union !count_bind.
rewrite (sum_list_with_Permutation _ _ _ (elements_disj_union X Y)).
exact: sum_list_with_app.
Qed.

Lemma bind_ext f g X : (∀ x, x ∈ X → f x = g x) → bind f X = bind g X.
Proof.
move=> e; apply: count_inj => y; rewrite !count_bind.
have {}e x : x ∈ elements X → f x = g x by move=> /elem_of_elements /e.
elim: (elements X) e => [|x l IH] e //=.
rewrite (e x (list_elem_of_here _ _)) IH // => x' x'l.
exact: e x' (list_elem_of_further _ _ _ x'l).
Qed.

Lemma bind_empty_r X : bind (λ _, ∅ : mset U) X = ∅.
Proof.
apply: count_inj => y; rewrite count_bind count_empty.
by elim: (elements X) => [|x l IH] //=; rewrite count_empty IH.
Qed.

Lemma elem_of_bind f X y : y ∈ bind f X ↔ ∃ x, x ∈ X ∧ y ∈ f x.
Proof.
rewrite [bind]unlock elem_of_of_list list_elem_of_bind.
by split=> -[x [h1 h2]]; exists x; split.
Qed.

Lemma count_map_inj f x X :
  (∀ a b, f a = f b → a = b) → count (f x) (map f X) = count x X.
Proof.
move=> finj; rewrite [map]unlock count_of_list -count_mem_elements.
exact: count_mem_fmap.
Qed.

Lemma elements_map_perm f X : elements (map f X) ≡ₚ f <$> elements X.
Proof. rewrite [map]unlock; exact: elements_of_list. Qed.

Lemma elem_of_map f X y : y ∈ map f X ↔ ∃ x, y = f x ∧ x ∈ X.
Proof. by rewrite [map]unlock elem_of_of_list list_elem_of_fmap. Qed.

Lemma map_empty f : map f ∅ = ∅.
Proof. by rewrite [map]unlock elements_empty. Qed.

Lemma map_singleton f x : map f {[+ x +]} = {[+ f x +]}.
Proof. by rewrite [map]unlock elements_singleton. Qed.

Lemma map_disj_union f X Y : map f (X ⊎ Y) = map f X ⊎ map f Y.
Proof.
apply: count_inj => y; rewrite [map]unlock count_disj_union !count_of_list.
rewrite -count_mem_app -fmap_app; apply: count_mem_Permutation.
apply: fmap_Permutation; exact: elements_disj_union.
Qed.

Lemma bind_singletons f X : bind (λ x, {[+ f x +]}) X = map f X.
Proof.
apply: count_inj => y; rewrite count_bind [map]unlock count_of_list.
elim: (elements X) => [|x l IH] //=.
by rewrite count_singleton IH.
Qed.

Lemma bind_of_list f l :
  bind f (of_list l) = of_list (l ≫= λ x, elements (f x)).
Proof.
apply: count_inj => y; rewrite count_bind count_of_list.
rewrite (sum_list_with_Permutation _ _ _ (elements_of_list l)).
by elim: l => [|x l IH] //=; rewrite count_mem_app IH count_mem_elements.
Qed.

Lemma map_of_list f l : map f (of_list l) = of_list (f <$> l).
Proof.
apply: count_inj => y; rewrite [map]unlock !count_of_list.
apply: count_mem_Permutation; apply: fmap_Permutation; exact: elements_of_list.
Qed.

Lemma elements_map f X :
  (∀ a b, le a b → le (f a) (f b)) → elements (map f X) = f <$> elements X.
Proof.
move=> mono; rewrite [map]unlock; apply: elements_of_list_wf.
apply: bool_decide_pack.
apply: (StronglySorted_fmap f le le) => //; exact: elements_sorted.
Qed.

Lemma map_disjoint f X Y :
  (∀ a b, f a = f b → a = b) → X ## Y → map f X ## map f Y.
Proof.
move=> finj d y /elem_of_map [a [-> aX]] /elem_of_map [b [eb bY]].
by apply: (d a aX); rewrite (finj _ _ eb).
Qed.

End Bind.

Lemma map_map {T U V : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    `{EqDecision U, Lexico U, !StrictOrder (@lexico U _),
      !TrichotomyT (@lexico U _)}
    `{EqDecision V, Lexico V, !StrictOrder (@lexico V _),
      !TrichotomyT (@lexico V _)}
    (f : T → U) (g : U → V) (X : mset T) :
  map g (map f X) = map (λ x, g (f x)) X.
Proof.
apply: count_inj => z; rewrite ![map]unlock !count_of_list.
apply: count_mem_Permutation; transitivity (g <$> (f <$> elements X)).
- apply: fmap_Permutation; exact: elements_of_list.
- by rewrite -list_fmap_compose.
Qed.

End MSet.
