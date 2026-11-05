From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import base gmap.
From cryptis Require Import term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Extended exponents

    An extended exponent ([eexp]) is a formal sum of exponents: a signed
    multiset of terms, read additively.  [∅] is zero, [⊎] is addition and
    [SMS.inv] is negation.  The exponents themselves are the monomials, and
    [emul] multiplies two sums monomial by monomial with [TMul], so extended
    exponents form a commutative ring ([emul_comm]).

    Group terms form a module over this ring.  [epow t s] raises [t] to the sum
    [s], the product of the powers of [t] by the monomials of [s], so that
    [epow (epow t s) r = epow t (emul s r)] ([epowA]).  Conversely, [log g t]
    reads off the exponent of the base [g] in [t]: the sum of the exponents [e]
    of the group factors [g^e] of [t].  The logarithms are linear ([log_TGMul2],
    [log_epow]), and they determine a term ([log_inj]); in particular, a term
    other than [1] has a logarithm other than [0] ([log_neq0]).

    An equation between terms thus becomes an equation between their
    logarithms, which we analyze with degrees.  The degree [deg h s] of [s] in
    an atom [h] is the interval spanned by the numbers of occurrences of [h]
    in the monomials of [s], or [None] if [s] is [0].  Degrees add up when
    multiplying ([deg_emul]), since extended exponents have no zero divisors
    ([emul_neq0]).  For the same reason, nonzero factors cancel ([emul_injr]),
    so raising to a nonzero sum is injective in the base ([epow_injl]).
    Adding two sums joins their degrees when their bounds differ, since
    nothing cancels then ([deg_disj_union_apart]).  Three facts make degrees
    useful:

    - The logarithms of a term have degree 0 in any atom at least as big as
      the term ([deg_log_small]), and in any atom with a subterm that the term
      lacks ([deg_log_fresh]).

    - Parts of different degrees can be compared separately ([deg_split]).

    - Leading parts do not cancel: two different shifts of a nonzero sum cannot
      agree up to terms of a single degree ([emul_lead]). *)

Abbreviation eexp := tsms.

Implicit Types (g h t u e m : term) (s r : eexp) (k d : Z).

(** ** The ring of extended exponents *)

(** The product of [s] and [r]: every monomial of [s] times every monomial of
    [r]. *)
Definition emul s r : eexp :=
  SMS.bind (λ e, SMS.map (λ m, TMul {[+ m; e +]}) s) r.

Lemma emul1 s e : emul s {[+ e +]} = SMS.map (λ m, TMul {[+ m; e +]}) s.
Proof. exact: SMS.bind_singleton. Qed.

Lemma emul_singleton e1 e2 :
  emul {[+ e1 +]} {[+ e2 +]} = {[+ TMul {[+ e1; e2 +]} +]}.
Proof. by rewrite emul1 SMS.map_singleton. Qed.

Lemma emul_empty_l r : emul ∅ r = ∅.
Proof.
rewrite /emul -[RHS](SMS.bind_empty_l r); apply: SMS.bind_ext => e _.
exact: SMS.map_empty.
Qed.

Lemma emul_disj_union_l s1 s2 r : emul (s1 ⊎ s2) r = emul s1 r ⊎ emul s2 r.
Proof.
rewrite /emul -SMS.bind_disj_union_l; apply: SMS.bind_ext => e _.
exact: SMS.map_disj_union.
Qed.

Lemma emul_disj_union_r s r1 r2 : emul s (r1 ⊎ r2) = emul s r1 ⊎ emul s r2.
Proof. exact: SMS.bind_disj_union. Qed.

Lemma emul_empty_r s : emul s ∅ = ∅.
Proof. exact: SMS.bind_empty. Qed.

Lemma emul_inv_r s r : emul s (SMS.inv r) = SMS.inv (emul s r).
Proof. exact: SMS.bind_inv. Qed.

Lemma emul_comm s r : emul s r = emul r s.
Proof.
rewrite /emul /SMS.map SMS.bind_comm; apply: SMS.bind_ext => m _.
by apply: SMS.bind_ext => e _; rewrite (comm (⊎) {[+ e +]}).
Qed.

Lemma emul1A s e1 e2 :
  emul (emul s {[+ e1 +]}) {[+ e2 +]} = emul s {[+ TMul {[+ e1; e2 +]} +]}.
Proof.
rewrite !emul1 SMS.map_map; apply: SMS.map_ext => m _.
apply: count_inj => x _; rewrite !count_TMul2; lia.
Qed.

#[local] Lemma TMulK m e : TMul {[+ TMul {[+ m; e +]}; TInv e +]} = m.
Proof. apply: count_inj => x _; rewrite !count_TMul2 count_TInv; lia. Qed.

#[local] Lemma TMulKV m e : TMul {[+ TMul {[+ m; TInv e +]}; e +]} = m.
Proof. apply: count_inj => x _; rewrite !count_TMul2 count_TInv; lia. Qed.

Lemma count_emul1 s e m :
  SMS.count m (emul s {[+ e +]}) = SMS.count (TMul {[+ m; TInv e +]}) s.
Proof.
have inj m1 m2 : TMul {[+ m1; e +]} = TMul {[+ m2; e +]} → m1 = m2.
  by move=> E; rewrite -(TMulK m1 e) E TMulK.
rewrite emul1 -{1}(TMulKV m e).
exact: (SMS.count_map_inj (λ m', TMul {[+ m'; e +]}) _ s inj).
Qed.

Lemma emul1_inj s r e : emul s {[+ e +]} = emul r {[+ e +]} → s = r.
Proof.
move=> E; apply: SMS.count_inj => m.
by rewrite -(TMulK m e) -!count_emul1 E.
Qed.

Lemma emul1_eq0 s e : emul s {[+ e +]} = ∅ → s = ∅.
Proof. by move=> E; apply: (emul1_inj (e := e)); rewrite E emul_empty_l. Qed.

(** ** Exponentiation by extended exponents *)

Definition epow t s : term := TGMul (SMS.map (TExp t) s).

Lemma epow2 t e1 e2 :
  epow t {[+ e1; e2 +]} = TGMul {[+ TExp t e1; TExp t e2 +]}.
Proof. by rewrite /epow SMS.map_disj_union !SMS.map_singleton. Qed.

Lemma epow_unit s : epow (TGMul ∅) s = TGMul ∅.
Proof.
apply/gtunitP; rewrite /epow gfactors_TGMul SMS.bind_map.
rewrite -[RHS](SMS.bind_empty_l s); apply: SMS.bind_ext => e _.
by rewrite TExp_gunit gfactors_TGMul_empty.
Qed.

#[local] Lemma TGMul_bind (f : term → eexp) s :
  TGMul (SMS.bind f s) = TGMul (SMS.map (λ x, TGMul (f x)) s).
Proof.
apply: gfactors_inj; rewrite !gfactors_TGMul SMS.bind_bind SMS.bind_map.
by apply: SMS.bind_ext => x _; rewrite gfactors_TGMul.
Qed.

Lemma epowA t s r : epow (epow t s) r = epow t (emul s r).
Proof.
rewrite /epow /emul SMS.map_bind TGMul_bind; congr TGMul.
apply: SMS.map_ext => e _.
rewrite TExp_TGMul !SMS.map_map; congr TGMul; apply: SMS.map_ext => m _.
by rewrite /= TExpA.
Qed.

(** ** Logarithms *)

(** The exponent of the base [g] in [t]. *)
Definition log g t : eexp :=
  SMS.bind (λ u, if bool_decide (base u = g) then {[+ expo u +]} else ∅)
    (gfactors t).

(** The coefficient of [e] in [log g t] is the multiplicity of [g^e] in [t]. *)
Lemma count_log g e t :
  negb (is_exp g) → negb (is_gmul g) →
  SMS.count e (log g t) = gcount (TExp g e) t.
Proof.
move=> gNX gNm.
have inj : ∀ e1 e2, TExp g e1 = TExp g e2 → e1 = e2.
  move=> e1 e2; exact: TExp_injr (Ngmul_neq_unit gNm).
rewrite -(SMS.count_map_inj (TExp g) e (log g t) inj) /log SMS.map_bind.
have -> : SMS.bind (λ u, SMS.map (TExp g)
            (if bool_decide (base u = g) then {[+ expo u +]} else ∅))
            (gfactors t)
          = SMS.filter (λ u, base u = g) (gfactors t).
  rewrite /SMS.filter; apply: SMS.bind_ext => u _.
  case: (bool_decide_reflect (base u = g)) => [<-|_].
  - by rewrite SMS.map_singleton TExp_base_expo.
  - exact: SMS.map_empty.
rewrite SMS.count_filter base_TExp // base_expN //.
by rewrite bool_decide_eq_true_2.
Qed.

Lemma log_inj t1 t2 : (∀ g, log g t1 = log g t2) → t1 = t2.
Proof.
move=> e; apply: gcount_inj => u Nu.
have bNX := base_Nexp u.
have bNm : negb (is_gmul (base u)) by rewrite is_gmul_base.
by rewrite -(TExp_base_expo u) -!(count_log _ _ bNX bNm) e.
Qed.

Lemma log_TGMul g s : log g (TGMul s) = SMS.bind (log g) s.
Proof. by rewrite /log gfactors_TGMul SMS.bind_bind. Qed.

Lemma log_unit g : log g (TGMul ∅) = ∅.
Proof. by rewrite log_TGMul SMS.bind_empty. Qed.

Lemma log_TGMul2 g t1 t2 : log g (TGMul {[+ t1; t2 +]}) = log g t1 ⊎ log g t2.
Proof. by rewrite log_TGMul SMS.bind_disj_union !SMS.bind_singleton. Qed.

Lemma log_eq0 t : (∀ g, log g t = ∅) → t = TGMul ∅.
Proof. by move=> e; apply: log_inj => g; rewrite e log_unit. Qed.

Lemma log_neq0 t : t ≠ TGMul ∅ → ∃ g, log g t ≠ ∅.
Proof.
move=> /gfactors_nonempty [u u_t]; exists (base u) => e.
have Nu := Ngmul_gfactors _ _ u_t.
have bNX := base_Nexp u.
have bNm : negb (is_gmul (base u)) by rewrite is_gmul_base.
have : gcount u t ≠ 0%Z by apply/gcount_neq0.
by rewrite -(TExp_base_expo u) -(count_log _ _ bNX bNm) e SMS.count_empty.
Qed.

Lemma log_TExp g t e : log g (TExp t e) = emul (log g t) {[+ e +]}.
Proof.
rewrite emul1 /log gfactors_TExp SMS.bind_map SMS.map_bind.
apply: SMS.bind_ext => u u_t; have Nu := Ngmul_gfactors _ _ u_t.
rewrite base_TExp // expo_TExp //.
case: (bool_decide (base u = g)).
- by rewrite SMS.map_singleton.
- by rewrite SMS.map_empty.
Qed.

Lemma log_epow g t s : log g (epow t s) = emul (log g t) s.
Proof.
rewrite /epow log_TGMul SMS.bind_map /emul.
by apply: SMS.bind_ext => e _; rewrite log_TExp emul1.
Qed.

Lemma log_atom g u :
  negb (is_exp u) → negb (is_gmul u) →
  log g u = if bool_decide (u = g) then {[+ TMul ∅ +]} else ∅.
Proof.
move=> uNX uNm.
by rewrite /log gfactors_Ngmul // SMS.bind_singleton base_expN // expo_expN.
Qed.

Lemma log_TExp_atom g u e :
  negb (is_exp u) → negb (is_gmul u) →
  log g (TExp u e) = if bool_decide (u = g) then {[+ e +]} else ∅.
Proof.
move=> uNX uNm; rewrite log_TExp log_atom //.
case: (bool_decide (u = g)); last exact: emul_empty_l.
by rewrite emul_singleton TMul_unit_l.
Qed.

(** ** Degrees

    Degrees are intervals of integers: [Some (a, b)] stands for the integers
    from [a] to [b], and [None] for the empty interval.  They are ordered by
    inclusion ([⊑]), joined by their convex hull ([⊔]) and added pointwise
    ([+] in [deg_scope]). *)

#[export] Instance deg_sqsubseteq : SqSubsetEq (option (Z * Z)) := λ I J,
  match I, J with
  | None, _ => True
  | Some _, None => False
  | Some (a1, b1), Some (a2, b2) => (a2 ≤ a1 ∧ b1 ≤ b2)%Z
  end.

#[export] Instance deg_join : Join (option (Z * Z)) := λ I J,
  match I, J with
  | None, _ => J
  | _, None => I
  | Some (a1, b1), Some (a2, b2) => Some (Z.min a1 a2, Z.max b1 b2)
  end.

Definition dadd (I J : option (Z * Z)) : option (Z * Z) :=
  match I, J with
  | Some (a1, b1), Some (a2, b2) => Some (a1 + a2, b1 + b2)%Z
  | _, _ => None
  end.

Declare Scope deg_scope.
Delimit Scope deg_scope with deg.
Infix "+" := dadd : deg_scope.

Lemma Some_sqsubseteq a1 b1 a2 b2 :
  Some (a1, b1) ⊑ Some (a2, b2) ↔ (a2 ≤ a1 ∧ b1 ≤ b2)%Z.
Proof. done. Qed.

#[export] Instance deg_sqsubseteq_preorder : PreOrder (⊑@{option (Z * Z)}).
Proof.
split.
- by case=> [[a b]|] //; rewrite Some_sqsubseteq; lia.
- case=> [[a1 b1]|] [[a2 b2]|] [[a3 b3]|] //=; rewrite !Some_sqsubseteq; lia.
Qed.

Lemma join_Some a1 b1 a2 b2 :
  Some (a1, b1) ⊔ Some (a2, b2) = Some (Z.min a1 a2, Z.max b1 b2).
Proof. done. Qed.

Lemma join_None_r i : i ⊔ None = i.
Proof. by case: i => [[]|]. Qed.

#[local] Fixpoint ldeg h (l : list term) : option (Z * Z) :=
  if l is m :: l then Some (count h m, count h m) ⊔ ldeg h l else None.

(** The degree of [s] in [h]: the interval spanned by [count h m] over the
    monomials [m] of [s]. *)
Definition deg h s : option (Z * Z) := ldeg h (elements s).

#[local] Lemma ldeg_spec h l :
  match ldeg h l with
  | Some (a, b) =>
      (∀ m, m ∈ l → a ≤ count h m ≤ b)%Z ∧
      (∃ m, m ∈ l ∧ count h m = a) ∧ (∃ m, m ∈ l ∧ count h m = b)
  | None => l = []
  end.
Proof.
elim: l => [|m l IH] //=; move: IH.
case: (ldeg h l) => [[a b] [hb [[m1 [m1_l e1]] [m2 [m2_l e2]]]]|->];
  rewrite ?join_Some ?join_None_r /=.
- split; [|split].
  + by move=> m' /elem_of_cons [->|/hb]; lia.
  + case: (Z.le_ge_cases (count h m) a) => ?.
      by exists m; split; [left|lia].
    by exists m1; split; [right|lia].
  + case: (Z.le_ge_cases b (count h m)) => ?.
      by exists m; split; [left|lia].
    by exists m2; split; [right|lia].
- split; [|split]; try by exists m; split; [left|].
  by move=> m' /list_elem_of_singleton ->; lia.
Qed.

#[local] Lemma deg_spec h s :
  match deg h s with
  | Some (a, b) =>
      (∀ m, m ∈ s → a ≤ count h m ≤ b)%Z ∧
      (∃ m, m ∈ s ∧ count h m = a) ∧ (∃ m, m ∈ s ∧ count h m = b)
  | None => s = ∅
  end.
Proof.
rewrite /deg; pose proof (ldeg_spec h (elements s)) as H.
destruct (ldeg h (elements s)) as [[a b]|]; first exact H.
exact: SMS.elements_empty_inv H.
Qed.

Lemma deg_le h s a b :
  deg h s ⊑ Some (a, b) ↔ ∀ m, m ∈ s → (a ≤ count h m ≤ b)%Z.
Proof.
have := deg_spec h s.
case: (deg h s) => [[a' b'] [hb [[m1 [m1_s e1]] [m2 [m2_s e2]]]]|->].
- rewrite Some_sqsubseteq; split; first by move=> ? m /hb; lia.
  by move=> H; have := H _ m1_s; have := H _ m2_s; lia.
- split=> // _ m /SMS.elem_of_count; rewrite SMS.count_empty.
  by move=> /(_ eq_refl).
Qed.

Lemma deg_eq_None h s : deg h s = None ↔ s = ∅.
Proof.
split=> [|->]; last by rewrite /deg SMS.elements_empty.
by have := deg_spec h s; case: (deg h s) => [[a b] _|].
Qed.

Lemma deg_empty h : deg h ∅ = None.
Proof. by apply/deg_eq_None. Qed.

Lemma deg_Some h s a b :
  deg h s = Some (a, b) ↔
  (∀ m, m ∈ s → a ≤ count h m ≤ b)%Z ∧
  (∃ m, m ∈ s ∧ count h m = a) ∧ (∃ m, m ∈ s ∧ count h m = b).
Proof.
split=> [E|[hb [[m1 [m1_s e1]] [m2 [m2_s e2]]]]].
  by have := deg_spec h s; rewrite E.
have := deg_spec h s.
case: (deg h s) => [[a' b'] [hb' [[m3 [m3_s e3]] [m4 [m4_s e4]]]]|E].
- have := hb _ m3_s; have := hb _ m4_s; have := hb' _ m1_s.
  have := hb' _ m2_s; move=> ? ? ? ?; do 2 f_equal; lia.
- move: m1_s; rewrite E SMS.elem_of_count SMS.count_empty.
  by move=> /(_ eq_refl).
Qed.

Lemma deg_bounds h s a b : deg h s = Some (a, b) → (a ≤ b)%Z.
Proof. by case/deg_Some => hb [[m [m_s <-]] _]; have := hb _ m_s; lia. Qed.

Lemma deg_singleton h e : deg h {[+ e +]} = Some (count h e, count h e).
Proof. by rewrite /deg SMS.elements_singleton /= ?join_None_r. Qed.

(* Unfolding [deg] while unifying computes over the elements of sums. *)
#[global] Opaque deg.

Lemma deg_count h s a b m :
  deg h s ⊑ Some (a, b) → (count h m < a ∨ b < count h m)%Z →
  SMS.count m s = 0%Z.
Proof. by move=> /deg_le hs out; apply: SMS.not_elem_of_count => /hs; lia. Qed.

#[local] Lemma deg_ext h s r : (∀ m, m ∈ s ↔ m ∈ r) → deg h s = deg h r.
Proof.
move=> sr; have := deg_spec h s; have := deg_spec h r.
case: (deg h r) => [[a b] [hb [[m1 [m1_r e1]] [m2 [m2_r e2]]]] _|r0].
  apply/deg_Some; split; [|split].
  - by move=> m /sr /hb.
  - by exists m1; rewrite sr.
  - by exists m2; rewrite sr.
case: (deg h s) => [[a b] [_ [[m [m_s _]] _]]|//].
by move: m_s; rewrite sr r0 SMS.elem_of_count SMS.count_empty => /(_ eq_refl).
Qed.

Lemma deg_inv h s : deg h (SMS.inv s) = deg h s.
Proof.
apply: deg_ext => m; rewrite !SMS.elem_of_count SMS.count_inv.
by split; lia.
Qed.

(** *** Sums *)

#[local] Lemma elem_of_disj_union_l m s r : m ∈ s → m ∉ r → m ∈ s ⊎ r.
Proof.
move=> m_s m_r; apply/SMS.elem_of_count; rewrite SMS.count_disj_union.
by rewrite (SMS.not_elem_of_count _ _ m_r) Z.add_0_r -SMS.elem_of_count.
Qed.

Lemma deg_le_disj_union h s r a b :
  deg h s ⊑ Some (a, b) → deg h r ⊑ Some (a, b) →
  deg h (s ⊎ r) ⊑ Some (a, b).
Proof.
by rewrite !deg_le => hs hr m /SMS.elem_of_disj_union [/hs|/hr].
Qed.

(** No cancellation occurs when the bounds of the two sums differ. *)
Lemma deg_disj_union_apart h s r :
  (∀ a1 b1 a2 b2, deg h s = Some (a1, b1) → deg h r = Some (a2, b2) →
     a1 ≠ a2 ∧ b1 ≠ b2) →
  deg h (s ⊎ r) = deg h s ⊔ deg h r.
Proof.
move=> apart.
case Es: (deg h s) => [[a1 b1]|]; last first.
  by move/deg_eq_None: Es => ->; rewrite (left_id ∅ (⊎)).
case Er: (deg h r) => [[a2 b2]|]; last first.
  by move/deg_eq_None: Er => ->; rewrite (right_id ∅ (⊎)) Es join_None_r.
have [na nb] := apart _ _ _ _ Es Er.
move/deg_Some: Es => [hs [[m1 [m1_s e1]] [m2 [m2_s e2]]]].
move/deg_Some: Er => [hr [[m3 [m3_r e3]] [m4 [m4_r e4]]]].
rewrite join_Some; apply/deg_Some; split; [|split].
- by move=> m /SMS.elem_of_disj_union [/hs|/hr]; lia.
- case: (Z.lt_total a1 a2) => [lt|[//|lt]].
    exists m1; split; last lia.
    by apply: elem_of_disj_union_l m1_s _ => /hr; lia.
  exists m3; split; last lia.
  by rewrite (comm (⊎)); apply: elem_of_disj_union_l m3_r _ => /hs; lia.
- case: (Z.lt_total b1 b2) => [lt|[//|lt]].
    exists m4; split; last lia.
    by rewrite (comm (⊎)); apply: elem_of_disj_union_l m4_r _ => /hs; lia.
  exists m2; split; last lia.
  by apply: elem_of_disj_union_l m2_s _ => /hr; lia.
Qed.

Lemma deg_split h a b s1 s2 r1 r2 :
  deg h s1 ⊑ Some (a, a) → deg h r1 ⊑ Some (a, a) →
  deg h s2 ⊑ Some (b, b) → deg h r2 ⊑ Some (b, b) → a ≠ b →
  s1 ⊎ s2 = r1 ⊎ r2 → s2 = r2.
Proof.
move=> hs1 hr1 hs2 hr2 ab E; apply: SMS.count_inj => m.
move/(f_equal (SMS.count m)): E; rewrite !SMS.count_disj_union.
case: (decide (count h m = b)) => e.
- by rewrite (deg_count hs1) ?(deg_count hr1); lia.
- by rewrite (deg_count hs2) ?(deg_count hr2); lia.
Qed.

(** *** Products *)

Lemma deg_le_emul h s r a1 b1 a2 b2 :
  deg h s ⊑ Some (a1, b1) → deg h r ⊑ Some (a2, b2) →
  deg h (emul s r) ⊑ Some (a1 + a2, b1 + b2)%Z.
Proof.
rewrite !deg_le => hs hr m.
case/SMS.elem_of_bind => e [e_r /SMS.elem_of_map [m' [-> m'_s]]].
by rewrite count_TMul2; have := hs _ m'_s; have := hr _ e_r; lia.
Qed.

#[local] Definition dpart h k s : eexp := SMS.filter (λ m, count h m = k) s.

#[local] Lemma count_dpart h k s m :
  SMS.count m (dpart h k s)
  = if bool_decide (count h m = k) then SMS.count m s else 0%Z.
Proof. by rewrite /dpart SMS.count_filter. Qed.

#[local] Lemma elem_of_dpart h k s m :
  m ∈ dpart h k s ↔ m ∈ s ∧ count h m = k.
Proof.
rewrite !SMS.elem_of_count count_dpart.
case: (bool_decide_reflect (count h m = k)) => H; first tauto.
by split=> [/(_ eq_refl)|[_ /H]].
Qed.

#[local] Lemma dpart_neq0 h k s m : m ∈ s → count h m = k → dpart h k s ≠ ∅.
Proof.
move=> m_s e /(f_equal (SMS.count m)).
rewrite count_dpart bool_decide_eq_true_2 // SMS.count_empty.
by move: m_s; rewrite SMS.elem_of_count.
Qed.

#[local] Lemma dpart_empty h k : dpart h k ∅ = ∅.
Proof. exact: SMS.bind_empty. Qed.

#[local] Lemma dpart_bind h k (f : term → eexp) r :
  dpart h k (SMS.bind f r) = SMS.bind (λ e, dpart h k (f e)) r.
Proof. by rewrite /dpart /SMS.filter SMS.bind_bind. Qed.

#[local] Lemma bind_dpart h k (f : term → eexp) r :
  SMS.bind f (dpart h k r)
  = SMS.bind (λ e, if bool_decide (count h e = k) then f e else ∅) r.
Proof.
rewrite /dpart /SMS.filter SMS.bind_bind; apply: SMS.bind_ext => e _.
by case: bool_decide; rewrite ?SMS.bind_singleton ?SMS.bind_empty.
Qed.

#[local] Lemma dpart_emul1 h k s e :
  dpart h k (emul s {[+ e +]}) = emul (dpart h (k - count h e) s) {[+ e +]}.
Proof.
apply: SMS.count_inj => m; rewrite count_dpart !count_emul1 count_dpart.
rewrite count_TMul2 count_TInv.
case: (bool_decide_reflect (count h m = k)) => ?;
  case: (bool_decide_reflect (_ = _)) => ? //; lia.
Qed.

#[local] Lemma dpart_emul h a b s r :
  (∀ m e, m ∈ s → e ∈ r → count h m + count h e = a + b → count h e = b)%Z →
  dpart h (a + b) (emul s r) = emul (dpart h a s) (dpart h b r).
Proof.
move=> uniq; rewrite {1}/emul dpart_bind [RHS]/emul bind_dpart.
apply: SMS.bind_ext => e e_r; rewrite -!emul1 dpart_emul1.
case: (bool_decide_reflect (count h e = b)) => [<-|ne].
  by rewrite Z.add_simpl_r.
rewrite -[RHS](emul_empty_l {[+ e +]}); congr emul.
apply: SMS.count_inj => m; rewrite count_dpart SMS.count_empty.
case: (bool_decide_reflect (_ = _)) => // c.
by apply: SMS.not_elem_of_count => m_s; apply: ne; apply: uniq m_s e_r _; lia.
Qed.

#[local] Lemma count_emul_mono s r m e :
  (∀ m', m' ∈ s → m' = m) →
  SMS.count (TMul {[+ m; e +]}) (emul s r) = (SMS.count m s * SMS.count e r)%Z.
Proof.
move=> Hs.
have key x : SMS.count (TMul {[+ m; e +]}) (emul s {[+ x +]})
             = (SMS.count m s * SMS.count e {[+ x +]})%Z.
  rewrite count_emul1 SMS.count_singleton.
  case: (bool_decide_reflect (e = x)) => [<-|ne] /=.
    by rewrite TMulK Z.mul_1_r.
  rewrite Z.mul_0_r; apply: SMS.not_elem_of_count => /Hs E; apply: ne.
  apply: count_inj => y _; move/(f_equal (count y)): E.
  rewrite !count_TMul2 count_TInv; lia.
elim/(SMS.sms_ind (T := term)): r => [|x r IH|x r IH].
- by rewrite emul_empty_r !SMS.count_empty Z.mul_0_r.
- by rewrite emul_disj_union_r !SMS.count_disj_union key IH; ring.
- rewrite emul_disj_union_r emul_inv_r !SMS.count_disj_union !SMS.count_inv.
  by rewrite key IH; ring.
Qed.

#[local] Lemma sms_witness s : s ≠ ∅ → ∃ m, m ∈ s.
Proof.
move=> ns; destruct (elements s) as [|m l] eqn:E.
  by case: ns; exact: SMS.elements_empty_inv.
by exists m; rewrite -SMS.elem_of_elements E; left.
Qed.

(* The monomials of [s] have the same number of occurrences of every atom
   outside of [L]. *)
#[local] Definition agree (L : list term) s :=
  ∀ m1 m2 a, m1 ∈ s → m2 ∈ s → negb (is_mul a) → a ∉ L →
    count a m1 = count a m2.

#[local] Lemma agree_dpart a L k s : agree (a :: L) s → agree L (dpart a k s).
Proof.
move=> hs m1 m2 x /elem_of_dpart [m1_s e1] /elem_of_dpart [m2_s e2] Nx xL.
case: (decide (x = a)) => [->|xa]; first lia.
by apply: hs => //; case/elem_of_cons.
Qed.

(* Induction on the atoms [L] in which monomials may differ: the highest parts
   in the first atom have one atom less to differ in. *)
#[local] Lemma emul_neq0_agree L s r :
  agree L s → agree L r → s ≠ ∅ → r ≠ ∅ → emul s r ≠ ∅.
Proof.
elim: L s r => [|a L IH] s r hs hr ns nr.
  have [m m_s] := sms_witness ns; have [e e_r] := sms_witness nr.
  have Hs m' : m' ∈ s → m' = m.
    move=> m'_s; apply: count_inj => x Nx.
    exact: hs _ _ _ m'_s m_s Nx (not_elem_of_nil x).
  move=> /(f_equal (SMS.count (TMul {[+ m; e +]}))).
  rewrite count_emul_mono // SMS.count_empty.
  by move: m_s e_r; rewrite !SMS.elem_of_count; nia.
have := deg_spec a r; have := deg_spec a s.
case: (deg a s) => [[a1 b1]|//]; case: (deg a r) => [[a2 b2]|//].
move=> [bs [_ [ms [ms_s ems]]]] [br [_ [mr [mr_r emr]]]] E.
apply: (IH (dpart a b1 s) (dpart a b2 r)).
- exact: agree_dpart.
- exact: agree_dpart.
- exact: dpart_neq0 ms_s ems.
- exact: dpart_neq0 mr_r emr.
rewrite -dpart_emul ?E ?dpart_empty //.
by move=> m e /bs ? /br ?; lia.
Qed.

(** Extended exponents have no zero divisors. *)
Lemma emul_neq0 s r : s ≠ ∅ → r ≠ ∅ → emul s r ≠ ∅.
Proof.
set L := (elements s ++ elements r) ≫= λ m, elements (factors m).
have ag q : (∀ m, m ∈ q → m ∈ elements s ++ elements r) → agree L q.
  move=> sub m1 m2 a m1_q m2_q _ aL.
  have z m : m ∈ q → count a m = 0%Z.
    move=> m_q; apply: not_elem_of_count => a_m; apply: aL.
    by apply/list_elem_of_bind; exists m; split; last exact: sub.
  by rewrite !z.
move=> ns nr; apply: (emul_neq0_agree _ _ ns nr); apply: ag => m m_q;
  apply/elem_of_app; by [left|right].
Qed.

Lemma emul_injr s r1 r2 : s ≠ ∅ → emul s r1 = emul s r2 → r1 = r2.
Proof.
move=> ns E; apply: SMS.count_inj => m.
case: (decide (SMS.count m (r1 ⊎ SMS.inv r2) = 0%Z)) => [|nz].
  by rewrite SMS.count_disj_union SMS.count_inv; lia.
have nr : r1 ⊎ SMS.inv r2 ≠ ∅.
  by move=> E'; apply: nz; rewrite E' SMS.count_empty.
case: (emul_neq0 ns nr).
by rewrite emul_disj_union_r emul_inv_r E SMS.disj_union_inv_r.
Qed.

Lemma epow_injl s t1 t2 : s ≠ ∅ → epow t1 s = epow t2 s → t1 = t2.
Proof.
move=> ns E; apply: log_inj => g; apply: (emul_injr ns).
by rewrite !(emul_comm s) -!log_epow E.
Qed.

Lemma deg_emul h s r : deg h (emul s r) = (deg h s + deg h r)%deg.
Proof.
have := deg_spec h r; have := deg_spec h s.
case: (deg h s) => [[a1 b1] Hs|->]; last by rewrite emul_empty_l deg_empty.
case: (deg h r) => [[a2 b2] Hr|->]; last by rewrite emul_empty_r deg_empty.
move: Hs Hr => [hs [[m1 [m1_s e1]] [m2 [m2_s e2]]]].
move=> [hr [[m3 [m3_r e3]] [m4 [m4_r e4]]]] /=.
have part a b : (∀ m e, m ∈ s → e ∈ r →
                   count h m + count h e = a + b → count h e = b)%Z →
    (∃ m, m ∈ s ∧ count h m = a) → (∃ e, e ∈ r ∧ count h e = b) →
    ∃ m, m ∈ emul s r ∧ count h m = (a + b)%Z.
  move=> uniq [m [m_s em]] [e [e_r ee]].
  have /sms_witness [m' /elem_of_dpart [? ?]] :
      dpart h (a + b) (emul s r) ≠ ∅.
    rewrite dpart_emul //.
    exact: emul_neq0 (dpart_neq0 m_s em) (dpart_neq0 e_r ee).
  by exists m'.
apply/deg_Some; split; [|split].
- move=> m /SMS.elem_of_bind [e [e_r /SMS.elem_of_map [m' [-> m'_s]]]].
  by rewrite count_TMul2; have := hs _ m'_s; have := hr _ e_r; lia.
- apply: part; [|by exists m1|by exists m3].
  by move=> m e /hs ? /hr ?; lia.
- apply: part; [|by exists m2|by exists m4].
  by move=> m e /hs ? /hr ?; lia.
Qed.

Lemma deg_emul_point h s r a b k :
  deg h r = Some (a, b) → (a < b)%Z → deg h (emul s r) ⊑ Some (k, k) →
  s = ∅.
Proof.
move=> Er lt; case Es: (deg h s) => [[a' b']|]; last by move/deg_eq_None: Es.
rewrite deg_emul Es Er /= Some_sqsubseteq => - [? ?]; exfalso.
by have := deg_bounds Es; lia.
Qed.

(** Leading parts do not cancel: two different shifts of a nonzero sum differ
    by a sum of degrees spanning more than one integer. *)
Lemma emul_lead h β e1 e2 r1 r2 k :
  deg h r1 ⊑ Some (k, k) → deg h r2 ⊑ Some (k, k) →
  count h e1 ≠ count h e2 →
  r1 ⊎ emul β {[+ e1 +]} = r2 ⊎ emul β {[+ e2 +]} → β = ∅.
Proof.
move=> hr1 hr2 ne E.
case Eβ: (deg h β) => [[a b]|]; last by move/deg_eq_None: Eβ.
have ab := deg_bounds Eβ; exfalso.
have E' : emul β {[+ e1 +]} ⊎ SMS.inv (emul β {[+ e2 +]}) = r2 ⊎ SMS.inv r1.
  apply: SMS.count_inj => m; move/(f_equal (SMS.count m)): E.
  rewrite !SMS.count_disj_union !SMS.count_inv; lia.
have : deg h (r2 ⊎ SMS.inv r1) ⊑ Some (k, k).
  by apply: deg_le_disj_union; rewrite ?deg_inv.
rewrite -E' deg_disj_union_apart deg_inv !deg_emul Eβ !deg_singleton /=.
  by rewrite ?join_Some ?Some_sqsubseteq; lia.
move=> ? ? ? ?; rewrite ?deg_inv ?deg_emul ?Eβ ?deg_singleton /=.
by move=> - [<- <-] [<- <-]; lia.
Qed.

(** *** Degrees of logarithms *)

#[local] Lemma deg_log0 h g t :
  (∀ u, u ∈ gfactors t → count h (expo u) = 0%Z) →
  deg h (log g t) ⊑ Some (0, 0)%Z.
Proof.
move=> H; apply/deg_le => m /SMS.elem_of_bind [u [u_t]].
case: (bool_decide (base u = g));
  last by rewrite SMS.elem_of_count SMS.count_empty.
by move=> /SMS.elem_of_singleton ->; rewrite H //; lia.
Qed.

Lemma deg_log_small h t :
  tsize t ≤ tsize h → ∀ g, deg h (log g t) ⊑ Some (0, 0)%Z.
Proof.
move=> le g; apply: deg_log0 => u u_t.
exact: count_expo_gfactors_big u_t le.
Qed.

Lemma deg_log_fresh n h t :
  subterm n h → ¬ subterm n t → ∀ g, deg h (log g t) ⊑ Some (0, 0)%Z.
Proof.
move=> n_h n_t g; apply: deg_log0 => u u_t.
apply: not_elem_of_count => h_u; apply: n_t.
apply: (subterm_gfactors u_t); transitivity h => //.
exact: subterm_exps h_u.
Qed.
