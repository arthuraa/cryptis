(** Signed multisets over a type [T] ordered by a [Lexico] instance.

    [sms T] is the free abelian group on [T]: [∅] is its unit, [⊎] its
    operation, [inv] its inverse and [{[+ x +]}] its generators.  [count x s]
    is the signed multiplicity of [x] in [s], and equality is Leibniz
    ([count_inj]) and decidable.  [bind] substitutes signed multisets for
    elements, and [filter] keeps the elements that satisfy a predicate.
    [sms_ind] is the induction principle: a signed multiset is built from [∅]
    by adding or removing one element at a time.  A signed multiset of pairs
    is a finite map ([FMap.fmap]) from first components to signed multisets
    of second components: [curry] and [uncurry] are inverse ([curryK],
    [uncurryK]).

    A signed multiset is a pair of disjoint multisets ([MSet.mset]): its
    positive occurrences [pos s] and its negative ones [neg s].  [make X Y]
    has the positive occurrences [X] and the negative ones [Y]; its sides are
    [to X Y], which cancels the common occurrences by taking [X ∖ Y] and
    [Y ∖ X].  [inv] swaps the sides, so no element needs an inverse.  The
    operations are locked, since computing with them in proofs is slow;
    [unlock] exposes their definitions. *)

From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From stdpp Require Import list numbers proof_irrel sorting.
From Stdlib Require Import ZArith Lia.
From cryptis.lib Require Import list_sort fmap mset.

Module SMS.

Section SignedMultiset.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Implicit Types (x y z : T) (X Y : MSet.mset T).

Definition to X Y : MSet.mset T * MSet.mset T := (X ∖ Y, Y ∖ X).

Lemma to_disjoint X Y : (to X Y).1 ## (to X Y).2.
Proof. exact: MSet.difference_disjoint. Qed.

Record sms := mk {
  pos : MSet.mset T;
  neg : MSet.mset T;
  pos_neg_disjoint : bool_decide (pos ## neg);
}.

Implicit Types (s : sms).

#[local] Lemma disjoint_swap X Y : X ## Y → Y ## X.
Proof. by move=> d x xY xX; exact: d x xX xY. Qed.

lock Definition make X Y :=
  mk (to X Y).1 (to X Y).2 (bool_decide_pack _ (to_disjoint X Y)).
lock Definition inv s :=
  mk (neg s) (pos s)
     (bool_decide_pack _
        (disjoint_swap _ _ (bool_decide_unpack _ (pos_neg_disjoint s)))).
lock Definition count x s : Z :=
  (Z.of_nat (MSet.count x (pos s)) - Z.of_nat (MSet.count x (neg s)))%Z.

#[global] Instance empty_instance : Empty sms := make ∅ ∅.
#[global] Instance singleton_instance : SingletonMS T sms :=
  λ x, make {[+ x +]} ∅.
#[global] Instance disj_union_instance : DisjUnion sms :=
  λ s1 s2, make (pos s1 ⊎ pos s2) (neg s1 ⊎ neg s2).
#[global] Instance elements_instance : Elements T sms :=
  λ s, elements (pos s) ++ elements (neg s).
#[global] Instance elem_of_instance : ElemOf T sms :=
  λ x s, x ∈ pos s ∨ x ∈ neg s.
#[global] Instance elem_of_dec x s : Decision (x ∈ s) :=
  decide (x ∈ pos s ∨ x ∈ neg s).

Lemma sms_eq s1 s2 : pos s1 = pos s2 → neg s1 = neg s2 → s1 = s2.
Proof.
case: s1 s2 => [P1 N1 w1] [P2 N2 w2] /= eP eN; subst.
by rewrite (proof_irrel w1 w2).
Qed.

#[global] Instance eq_dec : EqDecision sms := λ s1 s2,
  match decide ((pos s1, neg s1) = (pos s2, neg s2)) with
  | left e => left (sms_eq s1 s2 (f_equal fst e) (f_equal snd e))
  | right n => right (λ e, n (f_equal (λ s, (pos s, neg s)) e))
  end.

Lemma pos_neg_disj s : pos s ## neg s.
Proof. exact: (bool_decide_unpack _ (pos_neg_disjoint s)). Qed.

#[local] Lemma count_pos_neg x s :
  MSet.count x (pos s) = 0 ∨ MSet.count x (neg s) = 0.
Proof. exact: (proj1 (MSet.disjoint_count _ _) (pos_neg_disj s) x). Qed.

Lemma countE x s : count x s =
  (Z.of_nat (MSet.count x (pos s)) - Z.of_nat (MSet.count x (neg s)))%Z.
Proof. by rewrite [count]unlock. Qed.

Lemma count_pos_max x s :
  Z.of_nat (MSet.count x (pos s)) = Z.max 0 (count x s).
Proof. rewrite countE; have := count_pos_neg x s; lia. Qed.

Lemma count_neg_max x s :
  Z.of_nat (MSet.count x (neg s)) = Z.max 0 (- count x s).
Proof. rewrite countE; have := count_pos_neg x s; lia. Qed.

Lemma count_inj s1 s2 : (∀ z, count z s1 = count z s2) → s1 = s2.
Proof.
move=> e; apply: sms_eq; apply: MSet.count_inj => z; apply: Nat2Z.inj.
- by rewrite !count_pos_max e.
- by rewrite !count_neg_max e.
Qed.

Lemma pos_make X Y : pos (make X Y) = X ∖ Y.
Proof. by rewrite [make]unlock. Qed.

Lemma neg_make X Y : neg (make X Y) = Y ∖ X.
Proof. by rewrite [make]unlock. Qed.

Lemma count_make z X Y :
  count z (make X Y) =
  (Z.of_nat (MSet.count z X) - Z.of_nat (MSet.count z Y))%Z.
Proof. rewrite countE pos_make neg_make !MSet.count_difference; lia. Qed.

Lemma make_eq X Y X' Y' : X ⊎ Y' = X' ⊎ Y → make X Y = make X' Y'.
Proof.
move=> e; apply: count_inj => z; rewrite !count_make.
have := f_equal (MSet.count z) e; rewrite !MSet.count_disj_union; lia.
Qed.

Lemma make_pos_neg s : make (pos s) (neg s) = s.
Proof.
apply: sms_eq; rewrite ?pos_make ?neg_make; apply: MSet.count_inj => z;
  rewrite MSet.count_difference; have := count_pos_neg z s; lia.
Qed.

Lemma singleton_make x : {[+ x +]} = make {[+ x +]} ∅.
Proof. done. Qed.

Lemma pos_singleton x : pos {[+ x +]} = {[+ x +]}.
Proof. rewrite singleton_make pos_make; MSet.mset_solver. Qed.

Lemma neg_singleton x : neg {[+ x +]} = ∅.
Proof. rewrite singleton_make neg_make; MSet.mset_solver. Qed.

Lemma pos_empty : pos ∅ = ∅.
Proof.
by rewrite (_ : ∅ = make ∅ ∅) // pos_make; MSet.mset_solver.
Qed.

Lemma neg_empty : neg ∅ = ∅.
Proof.
by rewrite (_ : ∅ = make ∅ ∅) // neg_make; MSet.mset_solver.
Qed.

Lemma pos_inv s : pos (inv s) = neg s.
Proof. by rewrite [inv]unlock. Qed.

Lemma neg_inv s : neg (inv s) = pos s.
Proof. by rewrite [inv]unlock. Qed.

Lemma elements_pos_neg s : elements s = elements (pos s) ++ elements (neg s).
Proof. done. Qed.

Lemma elem_of_pos_neg x s : x ∈ s ↔ x ∈ pos s ∨ x ∈ neg s.
Proof. done. Qed.

(** *** Counts *)

Lemma count_empty z : count z ∅ = 0%Z.
Proof. by rewrite count_make MSet.count_empty. Qed.

Lemma count_singleton z x : count z {[+ x +]} = Z.b2z (bool_decide (z = x)).
Proof.
rewrite count_make MSet.count_singleton MSet.count_empty.
by case_bool_decide.
Qed.

Lemma count_disj_union z s1 s2 :
  count z (s1 ⊎ s2) = (count z s1 + count z s2)%Z.
Proof. rewrite count_make !MSet.count_disj_union !countE; lia. Qed.

Lemma count_inv z s : count z (inv s) = (- count z s)%Z.
Proof. rewrite !countE pos_inv neg_inv; lia. Qed.

Lemma disj_union_make X1 Y1 X2 Y2 :
  make X1 Y1 ⊎ make X2 Y2 = make (X1 ⊎ X2) (Y1 ⊎ Y2).
Proof.
apply: count_inj => z; rewrite count_disj_union !count_make.
rewrite !MSet.count_disj_union; lia.
Qed.

Lemma make_singleton_l x X Y : make ({[+ x +]} ⊎ X) Y = {[+ x +]} ⊎ make X Y.
Proof.
apply: count_inj => z; rewrite count_disj_union count_singleton !count_make.
rewrite MSet.count_disj_union MSet.count_singleton.
case_bool_decide; simpl; lia.
Qed.

Lemma make_singleton_r y X Y :
  make X ({[+ y +]} ⊎ Y) = inv {[+ y +]} ⊎ make X Y.
Proof.
apply: count_inj => z; rewrite count_disj_union count_inv count_singleton.
rewrite !count_make MSet.count_disj_union MSet.count_singleton.
case_bool_decide; simpl; lia.
Qed.

Lemma inv_make X Y : inv (make X Y) = make Y X.
Proof. apply: count_inj => z; rewrite count_inv !count_make; lia. Qed.

(** *** Group laws *)

#[global] Instance disj_union_comm : Comm (=@{sms}) (⊎).
Proof. move=> s1 s2; apply: count_inj => z; rewrite !count_disj_union; lia. Qed.

#[global] Instance disj_union_assoc : Assoc (=@{sms}) (⊎).
Proof.
move=> s1 s2 s3; apply: count_inj => z; rewrite !count_disj_union; lia.
Qed.

#[global] Instance disj_union_left_id : LeftId (=@{sms}) ∅ (⊎).
Proof.
move=> s; apply: count_inj => z; rewrite count_disj_union count_empty; lia.
Qed.

#[global] Instance disj_union_right_id : RightId (=@{sms}) ∅ (⊎).
Proof.
move=> s; apply: count_inj => z; rewrite count_disj_union count_empty; lia.
Qed.

Lemma disj_union_inv_r s : s ⊎ inv s = ∅.
Proof.
apply: count_inj => z; rewrite count_disj_union count_inv count_empty; lia.
Qed.

Lemma invK s : inv (inv s) = s.
Proof. apply: count_inj => z; rewrite !count_inv; lia. Qed.

(** *** Elements *)

Lemma elem_of_elements x s : x ∈ elements s ↔ x ∈ s.
Proof.
rewrite elements_pos_neg elem_of_app !MSet.elem_of_elements.
reflexivity.
Qed.

Lemma elem_of_count x s : x ∈ s ↔ count x s ≠ 0%Z.
Proof.
rewrite elem_of_pos_neg !MSet.elem_of_count countE.
have := count_pos_neg x s; lia.
Qed.

Lemma not_elem_of_count x s : x ∉ s → count x s = 0%Z.
Proof. by rewrite elem_of_count; lia. Qed.

Lemma count_pos x s : (0 < count x s)%Z ↔ x ∈ pos s.
Proof. rewrite MSet.elem_of_count countE; have := count_pos_neg x s; lia. Qed.

Lemma count_neg x s : (count x s < 0)%Z ↔ x ∈ neg s.
Proof. rewrite MSet.elem_of_count countE; have := count_pos_neg x s; lia. Qed.

Lemma elem_of_pos x s : x ∈ pos s → x ∈ s.
Proof. by move=> ?; left. Qed.

Lemma elem_of_neg x s : x ∈ neg s → x ∈ s.
Proof. by move=> ?; right. Qed.

Lemma count_mem_elements x s :
  Z.of_nat (count_mem x (elements s)) = Z.abs (count x s).
Proof.
rewrite elements_pos_neg count_mem_app !MSet.count_mem_elements countE.
have := count_pos_neg x s; lia.
Qed.

Lemma elements_empty : elements (∅ : sms) = [].
Proof.
rewrite elements_pos_neg (_ : ∅ = make ∅ ∅) // pos_make neg_make.
by rewrite (_ : ∅ ∖ ∅ = ∅) ?MSet.elements_empty //; MSet.mset_solver.
Qed.

Lemma elements_empty_inv s : elements s = [] → s = ∅.
Proof.
move=> Hs; apply: count_inj => z; rewrite count_empty.
by apply: not_elem_of_count; rewrite -elem_of_elements Hs => /elem_of_nil.
Qed.

Lemma max_or_empty (f : T → Z) s :
  (∃ x, x ∈ s ∧ ∀ y, y ∈ s → (f y ≤ f x)%Z) ∨ s = ∅.
Proof.
destruct (elements s) as [|w l] eqn:E.
  by right; exact: elements_empty_inv.
left; enough (∃ x, x ∈ w :: l ∧ ∀ y, y ∈ w :: l → (f y ≤ f x)%Z)
  as [x [x_in x_max]].
  by exists x; split=> [|y]; rewrite -elem_of_elements E //; exact: x_max.
clear E; elim: l w => [|b l IH] w.
  by exists w; split=> [|y /list_elem_of_singleton ->]; [left|lia].
have [m [m_in m_max]] := IH b.
case: (Z.le_ge_cases (f w) (f m)) => [le|ge].
  by exists m; split=> [|y /elem_of_cons [->|/m_max]]; [right| |].
by exists w; split=> [|y /elem_of_cons [->|/m_max]]; [left|lia|lia].
Qed.

Lemma elements_singleton x : elements ({[+ x +]} : sms) = [x].
Proof.
by rewrite elements_pos_neg pos_singleton neg_singleton MSet.elements_singleton
  MSet.elements_empty.
Qed.

Lemma elements_inv s : elements (inv s) ≡ₚ elements s.
Proof.
rewrite !elements_pos_neg pos_inv neg_inv; exact: Permutation_app_comm.
Qed.

Lemma elements_disj_union s1 s2 :
  pos s1 ## neg s2 → neg s1 ## pos s2 →
  elements (s1 ⊎ s2) ≡ₚ elements s1 ++ elements s2.
Proof.
move=> d12 d21; apply: Permutation_count_mem => z; apply: Nat2Z.inj.
rewrite count_mem_app Nat2Z.inj_add !count_mem_elements count_disj_union.
have ? : ¬ (0 < count z s1 ∧ count z s2 < 0)%Z.
  by case=> /count_pos ? /count_neg ?; exact: (d12 z).
have ? : ¬ (count z s1 < 0 ∧ 0 < count z s2)%Z.
  by case=> /count_neg ? /count_pos ?; exact: (d21 z).
lia.
Qed.

Lemma elem_of_disj_union {x s1 s2} : x ∈ s1 ⊎ s2 → x ∈ s1 ∨ x ∈ s2.
Proof.
rewrite !elem_of_count count_disj_union.
case: (decide (count x s1 = 0%Z)) => ?; [right|left]; lia.
Qed.

Lemma elem_of_singleton x y : x ∈ ({[+ y +]} : sms) ↔ x = y.
Proof.
by rewrite -elem_of_elements elements_singleton list_elem_of_singleton.
Qed.

Lemma pos_make_empty_r X : pos (make X ∅) = X.
Proof. rewrite pos_make; MSet.mset_solver. Qed.

Lemma neg_make_empty_r X : neg (make X ∅) = ∅.
Proof. rewrite neg_make; MSet.mset_solver. Qed.

Lemma elements_make_empty_r X : elements (make X ∅) = elements X.
Proof.
rewrite elements_pos_neg pos_make_empty_r neg_make_empty_r.
by rewrite MSet.elements_empty app_nil_r.
Qed.

Lemma elem_of_make_empty_r x X : x ∈ make X ∅ ↔ x ∈ X.
Proof.
rewrite elem_of_pos_neg pos_make_empty_r neg_make_empty_r.
split; last by left.
by case=> // h; case: (MSet.not_elem_of_empty x h).
Qed.

Lemma elem_of_make {x X Y} : x ∈ make X Y → x ∈ X ∨ x ∈ Y.
Proof.
rewrite elem_of_pos_neg pos_make neg_make !MSet.elem_of_difference.
by case=> ?; [left|right]; apply/MSet.elem_of_count; lia.
Qed.

(** *** Induction *)

Lemma sms_ind (P : sms → Prop) :
  P ∅ →
  (∀ x s, P s → P ({[+ x +]} ⊎ s)) →
  (∀ x s, P s → P (inv {[+ x +]} ⊎ s)) →
  ∀ s, P s.
Proof.
move=> P0 Ppos Pneg s; rewrite -(make_pos_neg s).
move: (pos s) (neg s) => X Y.
elim/(MSet.mset_ind (T := T)): Y => [|y Y IHY].
  elim/(MSet.mset_ind (T := T)): X => [|x X IHX]; first exact: P0.
  by rewrite make_singleton_l; apply: Ppos.
by rewrite make_singleton_r; apply: Pneg.
Qed.

End SignedMultiset.

Arguments sms T {_ _ _ _}.

(** ** Binding

    [bind f s] substitutes [f x] for each element [x] of [s]: [sms] is the free
    abelian group, and [bind] its monadic bind ([bind_singleton], [bind_unit],
    [bind_bind]).  It is additive in [f] as well as in [s], and binds over two
    signed multisets commute ([bind_comm]). *)

Section Bind.

Context {T U : Type}.
Context `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Implicit Types (x : T) (X Y : MSet.mset T) (s : sms T).

lock Definition bind (f : T → sms U) s : sms U :=
  make
    (MSet.bind (λ x, pos (f x)) (pos s) ⊎ MSet.bind (λ x, neg (f x)) (neg s))
    (MSet.bind (λ x, neg (f x)) (pos s) ⊎ MSet.bind (λ x, pos (f x)) (neg s)).

lock Definition map (f : T → U) s : sms U := bind (λ x, {[+ f x +]}) s.

Lemma count_bind (z : U) f s :
  count z (bind f s) =
  (Z.of_nat (MSet.count z (MSet.bind (λ x, pos (f x)) (pos s))) +
   Z.of_nat (MSet.count z (MSet.bind (λ x, neg (f x)) (neg s))) -
   Z.of_nat (MSet.count z (MSet.bind (λ x, neg (f x)) (pos s))) -
   Z.of_nat (MSet.count z (MSet.bind (λ x, pos (f x)) (neg s))))%Z.
Proof. rewrite [bind]unlock count_make !MSet.count_disj_union; lia. Qed.

(** When a single element [x0] of [s] contributes to [z], the count of [z]
    is that contribution times the count of [x0]. *)
Lemma count_bind_single (z : U) f s x0 :
  (∀ x, x ∈ s → x ≠ x0 → count z (f x) = 0%Z) →
  count z (bind f s) = (count x0 s * count z (f x0))%Z.
Proof.
move=> h.
have Z0 x : x ∈ s → x ≠ x0 →
    MSet.count z (pos (f x)) = 0 ∧ MSet.count z (neg (f x)) = 0.
  move=> xs nx; have := h x xs nx; rewrite countE.
  have := count_pos_neg z (f x); lia.
have S (X : MSet.mset T) (g : T → MSet.mset U) :
    (∀ x, x ∈ X → x ∈ s) → (∀ x, x ∈ s → x ≠ x0 → MSet.count z (g x) = 0) →
    MSet.count z (MSet.bind g X) = MSet.count x0 X * MSet.count z (g x0).
  move=> hX hg; rewrite MSet.count_bind -MSet.count_mem_elements.
  have hl : ∀ x, x ∈ elements X → x ≠ x0 → MSet.count z (g x) = 0.
    by move=> x /MSet.elem_of_elements /hX xs; exact: hg.
  elim: (elements X) hl => [//|x l IH] hl /=.
  have hl' : ∀ y, y ∈ l → y ≠ x0 → MSet.count z (g y) = 0.
    by move=> y yl; apply: hl; right.
  rewrite (IH hl'); case: bool_decide_reflect => [->|nx]; first lia.
  by rewrite (hl x (list_elem_of_here _ _) (λ e, nx (eq_sym e))); lia.
have Pp : ∀ x, x ∈ pos s → x ∈ s by move=> x; exact: elem_of_pos.
have Pn : ∀ x, x ∈ neg s → x ∈ s by move=> x; exact: elem_of_neg.
have Zp : ∀ x, x ∈ s → x ≠ x0 → MSet.count z (pos (f x)) = 0.
  by move=> x xs nx; case: (Z0 x xs nx).
have Zn : ∀ x, x ∈ s → x ≠ x0 → MSet.count z (neg (f x)) = 0.
  by move=> x xs nx; case: (Z0 x xs nx).
rewrite count_bind (S _ _ Pp Zp) (S _ _ Pn Zn) (S _ _ Pp Zn) (S _ _ Pn Zp).
rewrite !countE !Nat2Z.inj_mul; ring.
Qed.

(** [bind] ignores the cancellations of [make]. *)
Lemma bind_make f X Y :
  bind f (make X Y) =
  make (MSet.bind (λ x, pos (f x)) X ⊎ MSet.bind (λ x, neg (f x)) Y)
       (MSet.bind (λ x, neg (f x)) X ⊎ MSet.bind (λ x, pos (f x)) Y).
Proof.
have eX : X = (X ∖ Y) ⊎ (X ∖ (X ∖ Y)) by MSet.mset_solver.
have eY : Y = (Y ∖ X) ⊎ (X ∖ (X ∖ Y)) by MSet.mset_solver.
apply: count_inj => z; rewrite count_bind count_make pos_make neg_make.
have cX g : MSet.count z (MSet.bind g X) =
    MSet.count z (MSet.bind g (X ∖ Y)) +
    MSet.count z (MSet.bind g (X ∖ (X ∖ Y))).
  by rewrite -MSet.count_disj_union -MSet.bind_disj_union -eX.
have cY g : MSet.count z (MSet.bind g Y) =
    MSet.count z (MSet.bind g (Y ∖ X)) +
    MSet.count z (MSet.bind g (X ∖ (X ∖ Y))).
  by rewrite -MSet.count_disj_union -MSet.bind_disj_union -eY.
rewrite !MSet.count_disj_union (cX (λ x, pos (f x))) (cX (λ x, neg (f x))).
rewrite (cY (λ x, pos (f x))) (cY (λ x, neg (f x))); lia.
Qed.

Lemma bind_make_singleton_l f x X Y :
  bind f (make ({[+ x +]} ⊎ X) Y) = f x ⊎ bind f (make X Y).
Proof.
apply: count_inj => z; rewrite count_disj_union !bind_make !count_make.
by rewrite !MSet.bind_disj_union !MSet.bind_singleton
  !MSet.count_disj_union !countE; lia.
Qed.

Lemma bind_make_singleton_r f y X Y :
  bind f (make X ({[+ y +]} ⊎ Y)) = inv (f y) ⊎ bind f (make X Y).
Proof.
apply: count_inj => z; rewrite count_disj_union count_inv !bind_make.
by rewrite !count_make !MSet.bind_disj_union !MSet.bind_singleton
  !MSet.count_disj_union !countE; lia.
Qed.

Lemma elem_of_bind {f s} {y : U} : y ∈ bind f s → ∃ x, x ∈ s ∧ y ∈ f x.
Proof.
rewrite [bind]unlock => /elem_of_make.
rewrite !MSet.elem_of_disj_union !MSet.elem_of_bind.
by case=> [[]|[]] [x [xs yx]]; exists x; split; first [by left|by right].
Qed.

Lemma bind_singleton f x : bind f {[+ x +]} = f x.
Proof.
rewrite singleton_make bind_make !MSet.bind_singleton !MSet.bind_empty.
by rewrite !(right_id ∅ (⊎)) make_pos_neg.
Qed.

Lemma bind_empty f : bind f ∅ = ∅.
Proof. by rewrite bind_make !MSet.bind_empty !(left_id ∅ (⊎)). Qed.

Lemma bind_disj_union f s1 s2 : bind f (s1 ⊎ s2) = bind f s1 ⊎ bind f s2.
Proof.
rewrite bind_make; apply: count_inj => z.
rewrite count_make count_disj_union !count_bind !MSet.bind_disj_union.
rewrite !MSet.count_disj_union; lia.
Qed.

Lemma bind_inv f s : bind f (inv s) = inv (bind f s).
Proof.
apply: count_inj => z; rewrite count_inv !count_bind pos_inv neg_inv; lia.
Qed.

Lemma bind_ext f g s : (∀ x, x ∈ s → f x = g x) → bind f s = bind g s.
Proof.
move=> e; rewrite [bind]unlock.
have eb W : (∀ x, x ∈ W → x ∈ s) →
    MSet.bind (λ x, pos (f x)) W = MSet.bind (λ x, pos (g x)) W ∧
    MSet.bind (λ x, neg (f x)) W = MSet.bind (λ x, neg (g x)) W.
  by move=> sub; split; apply: MSet.bind_ext => x /sub /e ->.
have [-> ->] := eb (pos s) (λ x h, or_introl h).
by have [-> ->] := eb (neg s) (λ x h, or_intror h).
Qed.

Lemma bind_disj_union_l (f g : T → sms U) s :
  bind (λ x, f x ⊎ g x) s = bind f s ⊎ bind g s.
Proof.
elim/(sms_ind (T := T)): s => [|x s IH|x s IH];
  rewrite ?bind_empty ?bind_disj_union ?bind_inv ?bind_singleton ?IH;
  apply: count_inj => z;
  rewrite !(count_disj_union, count_inv, count_empty); lia.
Qed.

Lemma bind_inv_l (f : T → sms U) s :
  bind (λ x, inv (f x)) s = inv (bind f s).
Proof.
elim/(sms_ind (T := T)): s => [|x s IH|x s IH];
  rewrite ?bind_empty ?bind_disj_union ?bind_inv ?bind_singleton ?IH;
  apply: count_inj => z;
  rewrite !(count_disj_union, count_inv, count_empty); lia.
Qed.

Lemma bind_empty_l s : bind (λ _, ∅ : sms U) s = ∅.
Proof.
elim/(sms_ind (T := T)): s => [|x s IH|x s IH];
  rewrite ?bind_empty ?bind_disj_union ?bind_inv ?bind_singleton ?IH;
  apply: count_inj => z;
  rewrite !(count_disj_union, count_inv, count_empty); lia.
Qed.

Lemma map_make f X Y : map f (make X Y) = make (MSet.map f X) (MSet.map f Y).
Proof.
rewrite [map]unlock bind_make.
have ep W : MSet.bind (λ x, pos {[+ f x +]}) W = MSet.map f W.
  rewrite -MSet.bind_singletons; apply: MSet.bind_ext => x _.
  exact: pos_singleton.
have en W : MSet.bind (λ x, neg {[+ f x +]}) W = ∅.
  rewrite -(MSet.bind_empty_r W); apply: MSet.bind_ext => x _.
  exact: neg_singleton.
by rewrite !ep !en (right_id ∅ (⊎)) (left_id ∅ (⊎)).
Qed.

Lemma map_pos_neg f s :
  map f s = make (MSet.map f (pos s)) (MSet.map f (neg s)).
Proof. by rewrite -{1}(make_pos_neg s) map_make. Qed.

Lemma count_map_inj f x s :
  (∀ a b, f a = f b → a = b) → count (f x) (map f s) = count x s.
Proof.
move=> finj; rewrite map_pos_neg count_make.
by rewrite !(MSet.count_map_inj f x _ finj) countE.
Qed.

Lemma elem_of_map {f s} {y : U} : y ∈ map f s → ∃ x, y = f x ∧ x ∈ s.
Proof.
rewrite map_pos_neg => /elem_of_make.
by case=> /MSet.elem_of_map [x [-> xs]]; exists x; split=> //; [left|right].
Qed.

Lemma elements_map_inj f s :
  (∀ a b, f a = f b → a = b) → elements (map f s) ≡ₚ f <$> elements s.
Proof.
move=> finj; apply: Permutation_count_mem => y; apply: Nat2Z.inj.
rewrite count_mem_elements.
case: (decide (y ∈ map f s)) => [/elem_of_map [x [-> x_s]]|ny].
  by rewrite count_map_inj // count_mem_fmap // count_mem_elements.
rewrite (not_elem_of_count _ _ ny) (proj1 (not_elem_of_count_mem _ _)) //.
move=> /list_elem_of_fmap [x [ex x_s]]; apply: ny; rewrite ex.
by rewrite elem_of_count count_map_inj // -elem_of_count -elem_of_elements.
Qed.

Lemma elements_map_mono f s :
  (∀ a b, f a = f b → a = b) → (∀ a b, MSet.le a b → MSet.le (f a) (f b)) →
  elements (map f s) = f <$> elements s.
Proof.
move=> finj mono.
have dm : MSet.map f (pos s) ## MSet.map f (neg s).
  exact: MSet.map_disjoint finj (pos_neg_disj s).
rewrite map_pos_neg elements_pos_neg pos_make neg_make.
rewrite MSet.difference_disjoint_l // MSet.difference_disjoint_l.
  by move=> y h1 h2; exact: dm y h2 h1.
by rewrite !MSet.elements_map // -fmap_app.
Qed.

Lemma map_singleton f x : map f {[+ x +]} = {[+ f x +]}.
Proof. rewrite [map]unlock; exact: bind_singleton. Qed.

Lemma map_empty f : map f ∅ = ∅.
Proof. rewrite [map]unlock; exact: bind_empty. Qed.

Lemma map_disj_union f s1 s2 : map f (s1 ⊎ s2) = map f s1 ⊎ map f s2.
Proof. rewrite [map]unlock; exact: bind_disj_union. Qed.

Lemma map_ext f g s : (∀ x, x ∈ s → f x = g x) → map f s = map g s.
Proof. by move=> fg; rewrite [map]unlock; apply: bind_ext => x /fg ->. Qed.

Lemma map_inv f s : map f (inv s) = inv (map f s).
Proof. rewrite [map]unlock; exact: bind_inv. Qed.

Lemma pos_map_inj (f : T → U) s :
  (∀ a b, f a = f b → a = b) →
  pos (map f s) = MSet.map f (pos s) ∧ neg (map f s) = MSet.map f (neg s).
Proof.
move=> finj; have d := MSet.map_disjoint f _ _ finj (pos_neg_disj s).
rewrite map_pos_neg pos_make neg_make.
rewrite MSet.difference_disjoint_l // MSet.difference_disjoint_l //.
by move=> y h1 h2; exact: d y h2 h1.
Qed.

End Bind.

Lemma map_map {T U V : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    `{EqDecision U, Lexico U, !StrictOrder (@lexico U _),
      !TrichotomyT (@lexico U _)}
    `{EqDecision V, Lexico V, !StrictOrder (@lexico V _),
      !TrichotomyT (@lexico V _)}
    (f : T → U) (g : U → V) (s : sms T) :
  map g (map f s) = map (λ x, g (f x)) s.
Proof.
rewrite [map f s]map_pos_neg map_make !MSet.map_map.
by rewrite [map (λ x, g (f x)) s]map_pos_neg.
Qed.

Lemma bind_map {T U V : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    `{EqDecision U, Lexico U, !StrictOrder (@lexico U _),
      !TrichotomyT (@lexico U _)}
    `{EqDecision V, Lexico V, !StrictOrder (@lexico V _),
      !TrichotomyT (@lexico V _)}
    (f : U → sms V) (g : T → U) (s : sms T) :
  bind f (map g s) = bind (λ x, f (g x)) s.
Proof.
elim/(sms_ind (T := T)): s => [|x s IH|x s IH].
- by rewrite map_empty !bind_empty.
- by rewrite map_disj_union map_singleton !bind_disj_union !bind_singleton IH.
- by rewrite map_disj_union map_inv map_singleton !bind_disj_union !bind_inv
    !bind_singleton IH.
Qed.

Lemma map_bind {T U V : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    `{EqDecision U, Lexico U, !StrictOrder (@lexico U _),
      !TrichotomyT (@lexico U _)}
    `{EqDecision V, Lexico V, !StrictOrder (@lexico V _),
      !TrichotomyT (@lexico V _)}
    (f : U → V) (g : T → sms U) (s : sms T) :
  map f (bind g s) = bind (λ x, map f (g x)) s.
Proof.
elim/(sms_ind (T := T)): s => [|x s IH|x s IH].
- by rewrite !bind_empty map_empty.
- by rewrite !bind_disj_union !bind_singleton map_disj_union IH.
- by rewrite !bind_disj_union !bind_inv !bind_singleton map_disj_union
    map_inv IH.
Qed.

Lemma bind_unit {T : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    (s : sms T) :
  bind (λ x, {[+ x +]}) s = s.
Proof.
elim/(sms_ind (T := T)): s => [|x s IH|x s IH].
- exact: bind_empty.
- by rewrite bind_disj_union bind_singleton IH.
- by rewrite bind_disj_union bind_inv bind_singleton IH.
Qed.

Lemma map_id_ext {T : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    (f : T → T) (s : sms T) :
  (∀ x, x ∈ s → f x = x) → map f s = s.
Proof.
move=> fs; rewrite [map]unlock -[RHS]bind_unit.
by apply: bind_ext => x /fs ->.
Qed.

Lemma bind_bind {T U V : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    `{EqDecision U, Lexico U, !StrictOrder (@lexico U _),
      !TrichotomyT (@lexico U _)}
    `{EqDecision V, Lexico V, !StrictOrder (@lexico V _),
      !TrichotomyT (@lexico V _)}
    (f : U → sms V) (g : T → sms U) (s : sms T) :
  bind f (bind g s) = bind (λ x, bind f (g x)) s.
Proof.
elim/(sms_ind (T := T)): s => [|x s IH|x s IH].
- by rewrite !bind_empty.
- by rewrite !bind_disj_union !bind_singleton IH.
- by rewrite !bind_disj_union !bind_inv !bind_singleton IH.
Qed.

Lemma bind_comm {T U V : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    `{EqDecision U, Lexico U, !StrictOrder (@lexico U _),
      !TrichotomyT (@lexico U _)}
    `{EqDecision V, Lexico V, !StrictOrder (@lexico V _),
      !TrichotomyT (@lexico V _)}
    (f : T → U → sms V) (s : sms T) (r : sms U) :
  bind (λ x, bind (f x) r) s = bind (λ y, bind (λ x, f x y) s) r.
Proof.
elim/(sms_ind (T := T)): s => [|x s IH|x s IH].
- rewrite bind_empty -{1}(bind_empty_l r); apply: bind_ext => y _.
  by rewrite bind_empty.
- rewrite bind_disj_union bind_singleton IH -bind_disj_union_l.
  apply: bind_ext => y _.
  by rewrite bind_disj_union bind_singleton.
- rewrite bind_disj_union bind_inv bind_singleton IH.
  rewrite -bind_inv_l -bind_disj_union_l; apply: bind_ext => y _.
  by rewrite bind_disj_union bind_inv bind_singleton.
Qed.

(** ** Filtering *)

Section Filter.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Implicit Types (z : T) (s : sms T).

lock Definition filter (P : T → Prop) `{!∀ x, Decision (P x)} s : sms T :=
  bind (λ x, if bool_decide (P x) then {[+ x +]} else ∅) s.

Lemma count_filter (P : T → Prop) `{!∀ x, Decision (P x)} z s :
  count z (filter P s) = if bool_decide (P z) then count z s else 0%Z.
Proof.
have cz x : count z (if bool_decide (P x) then {[+ x +]} else ∅)
            = if bool_decide (P z) then Z.b2z (bool_decide (z = x)) else 0%Z.
  case: (decide (z = x)) => [<-|ne].
    by case: (bool_decide (P z)); rewrite ?count_singleton ?count_empty.
  rewrite (bool_decide_eq_false_2 (z = x)) //.
  by case: (bool_decide (P x)); case: (bool_decide (P z));
    rewrite ?count_singleton ?count_empty ?bool_decide_eq_false_2.
rewrite [filter]unlock; elim/(sms_ind (T := T)): s => [|x s IH|x s IH].
- by rewrite bind_empty count_empty; case: (bool_decide (P z)).
- rewrite bind_disj_union bind_singleton !count_disj_union cz IH.
  by rewrite count_singleton; case: (bool_decide (P z)).
- rewrite bind_disj_union bind_inv bind_singleton !count_disj_union.
  rewrite count_inv cz IH count_inv count_singleton.
  by case: (bool_decide (P z)); lia.
Qed.

End Filter.

Section Curry.

Context {T U : Type}.
Context `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Implicit Types (k : T) (v : U) (P : sms (T * U)).
Implicit Types (m : FMap.fmap T (sms U) ∅).

Definition curry_add k (s : sms U) m : FMap.fmap T (sms U) ∅ :=
  <[k := m !!! k ⊎ s]> m.

Definition curry_list (f : U → sms U) (ps : list (T * U)) m :=
  foldr (λ p m, curry_add p.1 (f p.2) m) m ps.

lock Definition curry P : FMap.fmap T (sms U) ∅ :=
  curry_list (λ v, {[+ v +]}) (elements (pos P))
    (curry_list (λ v, inv {[+ v +]}) (elements (neg P)) ∅).

Definition uncurry_list (l : list (T * sms U)) : sms (T * U) :=
  foldr (λ p s, map (λ v, (p.1, v)) p.2 ⊎ s) ∅ l.

lock Definition uncurry m : sms (T * U) := uncurry_list (FMap.to_list m).

Lemma curryE P :
  curry P =
  curry_list (λ v, {[+ v +]}) (elements (pos P))
    (curry_list (λ v, inv {[+ v +]}) (elements (neg P)) ∅).
Proof. by rewrite [curry]unlock. Qed.

Lemma lookup_curry_add k k' s m :
  curry_add k' s m !!! k =
  if bool_decide (k = k') then m !!! k ⊎ s else m !!! k.
Proof.
rewrite /curry_add FMap.lookup_insert.
by case: (bool_decide_reflect (k = k')) => [->|].
Qed.

Lemma count_curry_list (c : Z) f ps m k v :
  (∀ u, count v (f u) = c * Z.b2z (bool_decide (v = u)))%Z →
  count v (curry_list f ps m !!! k) =
  (count v (m !!! k) + c * Z.of_nat (count_mem (k, v) ps))%Z.
Proof.
move=> fP; elim: ps => [|[k' u] ps IH] /=; first lia.
rewrite lookup_curry_add.
case: (bool_decide_reflect (k = k')) => [<-|nk].
- rewrite count_disj_union IH fP.
  case: (bool_decide_reflect (v = u)) => [<-|nv].
  + rewrite bool_decide_eq_true_2 //=; lia.
  + rewrite bool_decide_eq_false_2 /=; [by case|lia].
- rewrite IH bool_decide_eq_false_2 /=; [by case|lia].
Qed.

Lemma count_curry P k v : count v (curry P !!! k) = count (k, v) P.
Proof.
have cp u : count v {[+ u +]} = (1 * Z.b2z (bool_decide (v = u)))%Z.
  by rewrite count_singleton; lia.
have cn u : count v (inv {[+ u +]}) = (-1 * Z.b2z (bool_decide (v = u)))%Z.
  by rewrite count_inv count_singleton; lia.
rewrite curryE (count_curry_list _ _ _ _ _ _ cp).
rewrite (count_curry_list _ _ _ _ _ _ cn) FMap.lookup_empty count_empty.
rewrite !MSet.count_mem_elements countE; lia.
Qed.

Lemma count_uncurry_list l k v :
  StronglySorted lexico (FMap.keys l) →
  count (k, v) (uncurry_list l) = count v (FMap.lookup_list ∅ k l).
Proof.
elim: l => [|[k' s] l IH] /=; first by rewrite !count_empty.
move=> /StronglySorted_cons [lb sl].
rewrite count_disj_union IH //.
case: (bool_decide_reflect (k = k')) => [->|nk].
- have inj : ∀ a b : U, (k', a) = (k', b) → a = b by move=> ?? [].
  rewrite (count_map_inj (λ v, (k', v)) v s inj).
  rewrite FMap.lookup_list_lexico // count_empty; lia.
- rewrite not_elem_of_count /=; last lia.
  by move=> /elem_of_map [u [[/nk]]].
Qed.

Lemma count_uncurry m k v : count (k, v) (uncurry m) = count v (m !!! k).
Proof.
rewrite [uncurry]unlock count_uncurry_list.
  by rewrite FMap.keys_fmap; exact: FMap.to_list_sorted.
by rewrite FMap.lookupE FMap.to_listE.
Qed.

Lemma curryK P : uncurry (curry P) = P.
Proof. apply: count_inj => -[k v]; by rewrite count_uncurry count_curry. Qed.

Lemma uncurryK m : curry (uncurry m) = m.
Proof.
apply: FMap.lookup_inj => k; apply: count_inj => v.
by rewrite count_curry count_uncurry.
Qed.

Lemma elem_of_curry P k v : v ∈ curry P !!! k ↔ (k, v) ∈ P.
Proof. by rewrite !elem_of_count count_curry. Qed.

Lemma elem_of_uncurry m k v : (k, v) ∈ uncurry m ↔ v ∈ m !!! k.
Proof. by rewrite !elem_of_count count_uncurry. Qed.

Lemma curry_singleton k v : curry {[+ (k, v) +]} = {[k := {[+ v +]}]}.
Proof.
apply: FMap.lookup_inj => k'; rewrite FMap.lookup_singleton.
(* Both sides compute to the same count, so plain [rewrite] would also hit the
   right-hand side. *)
apply: count_inj => v'; rewrite {1}count_curry {1}count_singleton.
case: (bool_decide_reflect (k' = k)) => [->|nk] /=.
- rewrite count_singleton.
  case: (bool_decide_reflect (v' = v)) => [->|nv].
  + by rewrite bool_decide_eq_true_2.
  + by rewrite bool_decide_eq_false_2 //; case.
- by rewrite count_empty bool_decide_eq_false_2 //; case.
Qed.

End Curry.

(* Tactics that reduce a goal to head normal form, such as ssreflect's [apply:],
   would otherwise unfold [curry] through all its map updates. *)

End SMS.
