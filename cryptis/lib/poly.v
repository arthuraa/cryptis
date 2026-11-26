(** Polynomials with integer coefficients over a type [T] ordered by a
    [Lexico] instance.

    A monomial is a multiset of variables ([MSet.mset T]): [∅] is the constant
    monomial and [{[+ x; x; y +]}] is [x²y].  A polynomial [poly T] wraps a
    signed multiset of monomials ([SMS.sms (MSet.mset T)]): the signed
    multiplicity of a monomial is its coefficient ([coeff]), and equality is
    Leibniz ([coeff_inj]) and decidable.

    [add] and [opp] are the group operations of the signed multiset, and [mul]
    multiplies every monomial of one polynomial by every monomial of the other
    by adding up their variables.  Polynomials form a commutative ring with
    [zero] and [one] ([poly_ring_theory]), and [p + q], [p - q], [p * q] and
    [- p] denote the ring operations in [poly_scope], delimited by [%P].
    [mono m] is the monomial [m] with coefficient [1], [const z] is the
    constant [z], and [poly_ind] builds a polynomial by adding or subtracting
    one monomial at a time.  [map f p] renames the variables of [p].

    [gcd p q] computes a greatest common divisor one variable at a time, and
    [div] computes exact quotients.  [cancel p q] divides [p] and [q] by
    [gcd p q] to remove their common factors.  [cancel_spec] proves that it
    only divides out a common factor.  [poly_gcd.v] proves that [gcd] is a
    greatest common divisor, that [div] is exact, and that [cancel] leaves no
    common factor besides [1] and [-1] and maps equal fractions to the same
    pair.  The operations are locked, since computing with them in proofs is
    slow; [unlock] exposes their definitions. *)

From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From stdpp Require Import list numbers.
From Stdlib Require Import ZArith Lia Ring.
From cryptis.lib Require Import mset sms.

Module Poly.

Section Polynomial.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Implicit Types (x : T) (m n : MSet.mset T).

Record poly := mk { car : SMS.sms (MSet.mset T) }.

Implicit Types (p q r : poly).

lock Definition coeff m p : Z := SMS.count m (car p).

lock Definition mono m : poly := mk {[+ m +]}.
lock Definition zero : poly := mk ∅.
lock Definition one : poly := mono ∅.
lock Definition var x : poly := mono {[+ x +]}.
lock Definition add p q : poly := mk (car p ⊎ car q).
lock Definition opp p : poly := mk (SMS.inv (car p)).
lock Definition mul p q : poly :=
  mk (SMS.bind (λ m, SMS.map (λ n, m ⊎ n) (car q)) (car p)).

Lemma coeffE m p : coeff m p = SMS.count m (car p).
Proof. by rewrite [coeff]unlock. Qed.

Lemma car_mono m : car (mono m) = {[+ m +]}.
Proof. by rewrite [mono]unlock. Qed.

Lemma car_zero : car zero = ∅.
Proof. by rewrite [zero]unlock. Qed.

Lemma oneE : one = mono ∅.
Proof. by rewrite [one]unlock. Qed.

Lemma varE x : var x = mono {[+ x +]}.
Proof. by rewrite [var]unlock. Qed.

Lemma car_add p q : car (add p q) = car p ⊎ car q.
Proof. by rewrite [add]unlock. Qed.

Lemma car_opp p : car (opp p) = SMS.inv (car p).
Proof. by rewrite [opp]unlock. Qed.

Lemma car_mul p q :
  car (mul p q) = SMS.bind (λ m, SMS.map (λ n, m ⊎ n) (car q)) (car p).
Proof. by rewrite [mul]unlock. Qed.

Lemma car_inj p q : car p = car q → p = q.
Proof. by case: p q => [s1] [s2] /= ->. Qed.

Lemma coeff_inj p q : (∀ m, coeff m p = coeff m q) → p = q.
Proof.
by move=> e; apply: car_inj; apply: SMS.count_inj => m; rewrite -!coeffE.
Qed.

#[global] Instance eq_dec : EqDecision poly := λ p q,
  match decide (car p = car q) with
  | left e => left (car_inj p q e)
  | right n => right (λ e, n (f_equal car e))
  end.

(** *** Coefficients *)

Lemma coeff_mono m n : coeff m (mono n) = Z.b2z (bool_decide (m = n)).
Proof. rewrite coeffE car_mono; exact: SMS.count_singleton. Qed.

Lemma coeff_zero m : coeff m zero = 0%Z.
Proof. rewrite coeffE car_zero; exact: SMS.count_empty. Qed.

Lemma coeff_one m : coeff m one = Z.b2z (bool_decide (m = ∅)).
Proof. rewrite oneE; exact: coeff_mono. Qed.

Lemma coeff_var m x : coeff m (var x) = Z.b2z (bool_decide (m = {[+ x +]})).
Proof. rewrite varE; exact: coeff_mono. Qed.

Lemma coeff_add m p q : coeff m (add p q) = (coeff m p + coeff m q)%Z.
Proof. rewrite !coeffE car_add; exact: SMS.count_disj_union. Qed.

Lemma coeff_opp m p : coeff m (opp p) = (- coeff m p)%Z.
Proof. rewrite !coeffE car_opp; exact: SMS.count_inv. Qed.

Lemma coeff_mono_eq m n : coeff m (mono n) ≠ 0%Z ↔ m = n.
Proof. rewrite coeff_mono; case_bool_decide; naive_solver. Qed.

Lemma coeff_neq0_elem m p : coeff m p ≠ 0%Z ↔ m ∈ car p.
Proof. by rewrite coeffE SMS.elem_of_count. Qed.

Lemma one_neq0 : one ≠ zero.
Proof.
move=> /(f_equal (coeff ∅)).
by rewrite coeff_one coeff_zero bool_decide_eq_true_2.
Qed.

(** *** Addition *)

#[global] Instance add_comm : Comm (=@{poly}) add.
Proof. move=> p q; apply: coeff_inj => m; rewrite !coeff_add; lia. Qed.

#[global] Instance add_assoc : Assoc (=@{poly}) add.
Proof. move=> p q r; apply: coeff_inj => m; rewrite !coeff_add; lia. Qed.

#[global] Instance add_left_id : LeftId (=@{poly}) zero add.
Proof. move=> p; apply: coeff_inj => m; rewrite coeff_add coeff_zero; lia. Qed.

#[global] Instance add_right_id : RightId (=@{poly}) zero add.
Proof. move=> p; apply: coeff_inj => m; rewrite coeff_add coeff_zero; lia. Qed.

Lemma add_opp_r p : add p (opp p) = zero.
Proof.
apply: coeff_inj => m; rewrite coeff_add coeff_opp coeff_zero; lia.
Qed.

Lemma opp_opp p : opp (opp p) = p.
Proof. apply: coeff_inj => m; rewrite !coeff_opp; lia. Qed.

Lemma opp_zero : opp zero = zero.
Proof. by apply: coeff_inj => m; rewrite coeff_opp coeff_zero. Qed.

(** *** Multiplication *)

Lemma car_mul_mono m p : car (mul (mono m) p) = SMS.map (λ n, m ⊎ n) (car p).
Proof. by rewrite car_mul car_mono SMS.bind_singleton. Qed.

Lemma mul_mono m n : mul (mono m) (mono n) = mono (m ⊎ n).
Proof. by apply: car_inj; rewrite car_mul_mono !car_mono SMS.map_singleton. Qed.

#[global] Instance mul_comm : Comm (=@{poly}) mul.
Proof.
move=> p q; apply: car_inj; rewrite !car_mul ![SMS.map]unlock.
rewrite (SMS.bind_comm (λ m n, {[+ m ⊎ n +]})).
apply: SMS.bind_ext => n _; apply: SMS.bind_ext => m _ /=.
by rewrite (comm (⊎)).
Qed.

#[global] Instance mul_assoc : Assoc (=@{poly}) mul.
Proof.
move=> p q r; apply: car_inj; rewrite !car_mul SMS.bind_bind.
apply: SMS.bind_ext => m _ /=; rewrite SMS.map_bind SMS.bind_map.
apply: SMS.bind_ext => n _ /=; rewrite SMS.map_map.
by apply: SMS.map_ext => k _; rewrite (assoc (⊎)).
Qed.

#[global] Instance mul_left_id : LeftId (=@{poly}) one mul.
Proof.
move=> p; apply: car_inj; rewrite car_mul oneE car_mono SMS.bind_singleton.
by apply: SMS.map_id_ext => n _; rewrite (left_id ∅ (⊎)).
Qed.

#[global] Instance mul_right_id : RightId (=@{poly}) one mul.
Proof.
move=> p; apply: car_inj; rewrite car_mul oneE car_mono -[RHS]SMS.bind_unit.
apply: SMS.bind_ext => m _ /=.
by rewrite SMS.map_singleton (right_id ∅ (⊎)).
Qed.

#[global] Instance mul_left_absorb : LeftAbsorb (=@{poly}) zero mul.
Proof.
by move=> p; apply: car_inj; rewrite car_mul car_zero SMS.bind_empty.
Qed.

#[global] Instance mul_right_absorb : RightAbsorb (=@{poly}) zero mul.
Proof.
move=> p; apply: car_inj.
rewrite car_mul car_zero -[RHS](SMS.bind_empty_l (car p)).
by apply: SMS.bind_ext => m _ /=; rewrite SMS.map_empty.
Qed.

Lemma mul_add_l p q r : mul (add p q) r = add (mul p r) (mul q r).
Proof. by apply: car_inj; rewrite !(car_mul, car_add) SMS.bind_disj_union. Qed.

Lemma mul_add_r p q r : mul p (add q r) = add (mul p q) (mul p r).
Proof.
apply: car_inj; rewrite !(car_mul, car_add) -SMS.bind_disj_union_l.
by apply: SMS.bind_ext => m _ /=; rewrite SMS.map_disj_union.
Qed.

Lemma mul_opp_l p q : mul (opp p) q = opp (mul p q).
Proof. by apply: car_inj; rewrite !(car_mul, car_opp) SMS.bind_inv. Qed.

Lemma mul_opp_r p q : mul p (opp q) = opp (mul p q).
Proof. by rewrite (comm mul) mul_opp_l (comm mul). Qed.

(** *** Induction *)

Lemma poly_ind (P : poly → Prop) :
  P zero →
  (∀ m p, P p → P (add (mono m) p)) →
  (∀ m p, P p → P (add (opp (mono m)) p)) →
  ∀ p, P p.
Proof.
move=> P0 Ppos Pneg [s].
elim/(SMS.sms_ind (T := MSet.mset T)): s => [|m s IH|m s IH].
- by rewrite (_ : mk ∅ = zero) //; apply: car_inj; rewrite car_zero.
- rewrite (_ : mk ({[+ m +]} ⊎ s) = add (mono m) (mk s)).
    by apply: car_inj; rewrite car_add car_mono.
  exact: Ppos m (mk s) IH.
- rewrite (_ : mk (SMS.inv {[+ m +]} ⊎ s) = add (opp (mono m)) (mk s)).
    by apply: car_inj; rewrite car_add car_opp car_mono.
  exact: Pneg m (mk s) IH.
Qed.

Lemma poly_ind_add (P : poly → Prop) :
  P zero → (∀ m, P (mono m)) → (∀ p q, P p → P q → P (add p q)) →
  (∀ p, P p → P (opp p)) → ∀ p, P p.
Proof.
move=> P0 Pm Padd Popp; elim/poly_ind => [//|m p IH|m p IH].
- exact: Padd (Pm m) IH.
- exact: Padd (Popp _ (Pm m)) IH.
Qed.

(** *** Constants and subtraction *)

lock Definition const (n : Z) : poly :=
  mk (SMS.make (MSet.of_list (replicate (Z.to_nat n) ∅))
               (MSet.of_list (replicate (Z.to_nat (- n)) ∅))).

lock Definition sub p q : poly := add p (opp q).

Lemma subE p q : sub p q = add p (opp q).
Proof. by rewrite [sub]unlock. Qed.

Lemma coeff_const m z :
  coeff m (const z) = if bool_decide (m = ∅) then z else 0%Z.
Proof.
have e k : MSet.count m (MSet.of_list (replicate k ∅)) =
           if bool_decide (m = ∅) then k else 0.
  rewrite MSet.count_of_list.
  by elim: k => [|k IH] /=; rewrite ?IH; case_bool_decide.
rewrite coeffE [const]unlock /= SMS.count_make !e; case_bool_decide; lia.
Qed.

Lemma coeff_sub m p q : coeff m (sub p q) = (coeff m p - coeff m q)%Z.
Proof. rewrite subE coeff_add coeff_opp; lia. Qed.

(** *** Ring structure *)

(* [ring] finds a ring by its exact carrier, and [poly T] for a variable [T]
   exists only where [T] is bound, so clients declare the ring in their own
   sections. *)
Lemma poly_ring_theory : ring_theory zero one add mul sub opp eq.
Proof.
split.
- exact: (left_id zero add).
- exact: (comm add).
- move=> a b c; exact: (assoc add).
- exact: (left_id one mul).
- exact: (comm mul).
- move=> a b c; exact: (assoc mul).
- exact: mul_add_l.
- exact: subE.
- exact: add_opp_r.
Qed.

Add Ring poly_ring : poly_ring_theory.

Lemma const_add a b : const (a + b) = add (const a) (const b).
Proof.
by apply: coeff_inj => m; rewrite coeff_add !coeff_const; case_bool_decide.
Qed.

Lemma const_opp a : const (- a) = opp (const a).
Proof.
by apply: coeff_inj => m; rewrite coeff_opp !coeff_const; case_bool_decide.
Qed.

Lemma const_zero : const 0 = zero.
Proof.
by apply: coeff_inj => m; rewrite coeff_const coeff_zero; case_bool_decide.
Qed.

Lemma const_one : const 1 = one.
Proof.
by apply: coeff_inj => m; rewrite coeff_const coeff_one; case_bool_decide.
Qed.

Lemma const_mul a b : const (a * b) = mul (const a) (const b).
Proof.
induction a as [|a IH|a IH] using Z.peano_ind.
- by rewrite Z.mul_0_l const_zero (left_absorb zero mul).
- rewrite Z.mul_succ_l const_add IH (_ : Z.succ a = a + 1)%Z //.
  by rewrite const_add const_one; ring.
- rewrite Z.mul_pred_l (_ : Z.pred a = a + - (1))%Z //.
  rewrite (_ : (a * b - b = a * b + - b)%Z) //.
  by rewrite !const_add !const_opp IH const_one; ring.
Qed.

Lemma const_inj a b : const a = const b → a = b.
Proof.
move=> /(f_equal (coeff ∅)); rewrite !coeff_const.
by rewrite bool_decide_eq_true_2.
Qed.

(** *** Polynomials in one variable

    A polynomial is a polynomial in [x] whose coefficients do not contain
    [x]: [coeffx x k p] is the coefficient of [x^k] and [lcx x p] the leading
    one. *)

lock Definition vpow x k : MSet.mset T := MSet.of_list (replicate k x).

lock Definition deg x p : nat := max_list (MSet.count x <$> elements (car p)).

lock Definition coeffx x k p : poly :=
  mk (SMS.bind (λ m, if bool_decide (MSet.count x m = k)
                     then {[+ m ∖ vpow x k +]} else ∅) (car p)).

lock Definition lcx x p : poly := coeffx x (deg x p) p.

lock Definition vars p : list T := remove_dups (elements (car p) ≫= elements).

Lemma vpowE x k : vpow x k = MSet.of_list (replicate k x).
Proof. by rewrite [vpow]unlock. Qed.

Lemma degE x p : deg x p = max_list (MSet.count x <$> elements (car p)).
Proof. by rewrite [deg]unlock. Qed.

Lemma car_coeffx x k p :
  car (coeffx x k p) =
  SMS.bind (λ m, if bool_decide (MSet.count x m = k)
                 then {[+ m ∖ vpow x k +]} else ∅) (car p).
Proof. by rewrite [coeffx]unlock. Qed.

Lemma varsE p : vars p = remove_dups (elements (car p) ≫= elements).
Proof. by rewrite [vars]unlock. Qed.

Lemma elem_of_vars x p : x ∈ vars p ↔ ∃ m, m ∈ car p ∧ x ∈ m.
Proof.
rewrite varsE elem_of_remove_dups list_elem_of_bind.
split=> -[m [xm mp]]; exists m; split=> //; exact/SMS.elem_of_elements.
Qed.

Lemma lcxE x p : lcx x p = coeffx x (deg x p) p.
Proof. by rewrite [lcx]unlock. Qed.

(** *** Greatest common divisors

    The gcd is computed one variable at a time: the gcd of two polynomials
    in [x] is the gcd of their contents, the gcds of their coefficients
    computed over the remaining variables, times the gcd of their primitive
    parts, computed by a pseudo-remainder sequence.  Pseudo-remainders scale
    by leading coefficients instead of dividing by them, since coefficients
    do not form a field.  [ops vs] holds the gcd and the exact division of
    polynomials over the variables [vs].  Fuels are written [n + 1] rather
    than [S n] so that [simpl] does not unfold the loops. *)

Fixpoint prem_loop x b d l fuel r : poly :=
  match fuel with
  | O => r
  | S fuel =>
      if bool_decide (r = zero) || (deg x r <? d)%nat then r else
      let t := mul (lcx x r) (mono (vpow x (deg x r - d))) in
      prem_loop x b d l fuel (sub (mul l r) (mul t b))
  end.

lock Definition prem x a b : poly :=
  prem_loop x b (deg x b) (lcx x b) (deg x a + 1) a.

Fixpoint div_loop x (dv : poly → poly → poly) g d l fuel r q :=
  match fuel with
  | O => q
  | S fuel =>
      if bool_decide (r = zero) then q else
      let c := mul (dv (lcx x r) l) (mono (vpow x (deg x r - d))) in
      div_loop x dv g d l fuel (sub r (mul c g)) (add q c)
  end.

lock Definition div_lvl x dv p g : poly :=
  div_loop x dv g (deg x g) (lcx x g) (deg x p + 1) p zero.

lock Definition cont x (gc : poly → poly → poly) p : poly :=
  foldr gc zero ((λ k, coeffx x k p) <$> seq 0 (deg x p + 1)).

Fixpoint prs x gc dv fuel a b : poly :=
  match fuel with
  | O => a
  | S fuel =>
      if bool_decide (b = zero) then a else
      let r := prem x a b in
      prs x gc dv fuel b (div_lvl x dv r (cont x gc r))
  end.

lock Definition gcd_lvl x gc dv p q : poly :=
  if bool_decide (p = zero) then q else
  if bool_decide (q = zero) then p else
  let cp := cont x gc p in
  let cq := cont x gc q in
  let a := div_lvl x dv p cp in
  let b := div_lvl x dv q cq in
  let g := if (deg x a <? deg x b)%nat then prs x gc dv (deg x a + 2) b a
           else prs x gc dv (deg x b + 2) a b in
  mul (gc cp cq) g.

Fixpoint ops (vs : list T) :
    (poly → poly → poly) * (poly → poly → poly) :=
  match vs with
  | [] => (λ p q, const (Z.gcd (coeff ∅ p) (coeff ∅ q)),
           λ p q, const (Z.quot (coeff ∅ p) (coeff ∅ q)))
  | x :: vs => let o := ops vs in (gcd_lvl x o.1 o.2, div_lvl x o.2)
  end.

lock Definition gcd p q : poly :=
  (ops (remove_dups (vars p ++ vars q))).1 p q.

lock Definition div p q : poly := (ops (remove_dups (vars p ++ vars q))).2 p q.

Lemma premE x a b :
  prem x a b = prem_loop x b (deg x b) (lcx x b) (deg x a + 1) a.
Proof. by rewrite [prem]unlock. Qed.

Lemma div_lvlE x dv p g :
  div_lvl x dv p g = div_loop x dv g (deg x g) (lcx x g) (deg x p + 1) p zero.
Proof. by rewrite [div_lvl]unlock. Qed.

Lemma contE x gc p :
  cont x gc p = foldr gc zero ((λ k, coeffx x k p) <$> seq 0 (deg x p + 1)).
Proof. by rewrite [cont]unlock. Qed.

Lemma gcdE p q : gcd p q = (ops (remove_dups (vars p ++ vars q))).1 p q.
Proof. by rewrite [gcd]unlock. Qed.

Lemma divE p q : div p q = (ops (remove_dups (vars p ++ vars q))).2 p q.
Proof. by rewrite [div]unlock. Qed.

(** *** Cancelling common factors

    [cancel p q] divides [p] and [q] by [gcd p q], and fixes the sign by
    making the coefficient of the least monomial of the second component
    positive ([first_neg]).  Monomials are compared by [MSet.glt], which is
    compatible with products, so this sign is multiplicative
    ([first_neg_mul]).  The divisions are checked, so [cancel] is sound
    however [gcd] behaves. *)

lock Definition first_neg p : bool :=
  match MSet.gmin_list (elements (SMS.pos (car p) ⊎ SMS.neg (car p))) with
  | Some m => bool_decide (coeff m p < 0)%Z
  | None => false
  end.

lock Definition cancel_with g p q p' q' : poly * poly :=
  if bool_decide (mul g p' = p ∧ mul g q' = q) then
    if first_neg q' then (opp p', opp q') else (p', q')
  else (p, q).

lock Definition cancel p q : poly * poly :=
  let g := gcd p q in cancel_with g p q (div p g) (div q g).

Lemma cancel_spec p q :
  ∃ g, p = mul g (cancel p q).1 ∧ q = mul g (cancel p q).2.
Proof.
rewrite [cancel]unlock /=; move: (gcd p q) => g.
move: (div p g) (div q g) => p' q'.
rewrite [cancel_with]unlock /=.
case: bool_decide_reflect => [[ep eq]|_]; last first.
  by exists one; rewrite !(left_id one mul).
case: (first_neg q'); last by exists g.
by exists (opp g); rewrite /= !mul_opp_l !mul_opp_r !opp_opp.
Qed.

Lemma elem_of_monos p m :
  m ∈ elements (SMS.pos (car p) ⊎ SMS.neg (car p)) ↔ m ∈ car p.
Proof.
by rewrite MSet.elem_of_elements MSet.elem_of_disj_union SMS.elem_of_pos_neg.
Qed.

Lemma first_neg_spec p :
  p ≠ zero →
  ∃ m, m ∈ car p ∧ (∀ n, n ∈ car p → n = m ∨ MSet.glt m n) ∧
       first_neg p = bool_decide (coeff m p < 0)%Z.
Proof.
move=> np; rewrite [first_neg]unlock.
case E: (MSet.gmin_list _) => [m|].
- have [ml hm] := MSet.gmin_list_spec _ _ E.
  exists m; split; first exact/elem_of_monos.
  by split=> // n /elem_of_monos; exact: hm.
- exfalso; apply: np; apply: car_inj; rewrite car_zero.
  apply: SMS.count_inj => m; rewrite SMS.count_empty.
  apply: SMS.not_elem_of_count => /elem_of_monos.
  by rewrite (MSet.gmin_list_None _ E) => /elem_of_nil.
Qed.

Lemma first_neg_zero : first_neg zero = false.
Proof.
rewrite [first_neg]unlock car_zero SMS.pos_empty SMS.neg_empty.
by rewrite (left_id ∅ (⊎)) MSet.elements_empty.
Qed.

Lemma glt_min_unique (s : SMS.sms (MSet.mset T)) m m' :
  m ∈ s → (∀ n, n ∈ s → n = m ∨ MSet.glt m n) →
  m' ∈ s → (∀ n, n ∈ s → n = m' ∨ MSet.glt m' n) → m = m'.
Proof.
move=> ms hm ms' hm'.
case: (hm m' ms') => [->//|lt1]; case: (hm' m ms) => [//|lt2].
by case: (MSet.glt_irrefl m); exact: MSet.glt_trans lt1 lt2.
Qed.

Lemma first_neg_opp p : p ≠ zero → first_neg (opp p) = negb (first_neg p).
Proof.
move=> np.
have np' : opp p ≠ zero.
  move=> e; apply: np; apply: coeff_inj => n.
  by have := f_equal (coeff n) e; rewrite coeff_opp !coeff_zero; lia.
have E n : n ∈ car (opp p) ↔ n ∈ car p.
  by rewrite car_opp !SMS.elem_of_count SMS.count_inv; lia.
have [m [mp [hm ->]]] := first_neg_spec _ np.
have [m' [mp' [hm' ->]]] := first_neg_spec _ np'.
have em : m' = m.
  apply: (glt_min_unique (car p)) => //; first exact/E.
  by move=> n /E; exact: hm'.
rewrite em coeff_opp.
have nz := proj2 (coeff_neq0_elem m p) mp.
by case: bool_decide_reflect; case: bool_decide_reflect; lia.
Qed.

Lemma first_neg_mono m : first_neg (mono m) = false.
Proof.
have nm : mono m ≠ zero.
  move=> /(f_equal (coeff m)); rewrite coeff_mono coeff_zero.
  by rewrite (bool_decide_eq_true_2 (m = m)).
have [n [+ [_ ->]]] := first_neg_spec _ nm.
rewrite car_mono => /SMS.elem_of_singleton ->.
by rewrite coeff_mono (bool_decide_eq_true_2 (m = m)).
Qed.

Lemma first_neg_opp_mono m : first_neg (opp (mono m)) = true.
Proof.
have nm : mono m ≠ zero.
  move=> /(f_equal (coeff m)); rewrite coeff_mono coeff_zero.
  by rewrite (bool_decide_eq_true_2 (m = m)).
by rewrite (first_neg_opp _ nm) first_neg_mono.
Qed.

(** The least monomial of a product is the product of the least monomials,
    and nothing cancels it. *)
Lemma coeff_mul_min p q mp mq :
  mp ∈ car p → (∀ n, n ∈ car p → n = mp ∨ MSet.glt mp n) →
  mq ∈ car q → (∀ n, n ∈ car q → n = mq ∨ MSet.glt mq n) →
  coeff (mp ⊎ mq) (mul p q) = (coeff mp p * coeff mq q)%Z ∧
  ∀ n, n ∈ car (mul p q) → n = mp ⊎ mq ∨ MSet.glt (mp ⊎ mq) n.
Proof.
move=> pp hp qq hq.
have strict m n' : m ∈ car p → n' ∈ car q → m ≠ mp ∨ n' ≠ mq →
    MSet.glt (mp ⊎ mq) (m ⊎ n').
  move=> mc nc ne.
  case: (hp m mc) => [em|lt1]; case: (hq n' nc) => [en|lt2].
  - by case: ne.
  - by rewrite em; exact: MSet.glt_disj_union_l.
  - by rewrite en; exact: MSet.glt_disj_union_r.
  - apply: MSet.glt_trans (MSet.glt_disj_union_r _ _ _ lt1) _.
    exact: MSet.glt_disj_union_l.
have inj : ∀ a b, mp ⊎ a = mp ⊎ b → a = b.
  move=> a b e; apply: MSet.count_inj => x.
  by have := f_equal (MSet.count x) e; rewrite !MSet.count_disj_union; lia.
split.
- have Z m : m ∈ car p → m ≠ mp →
      SMS.count (mp ⊎ mq) (SMS.map (λ n, m ⊎ n) (car q)) = 0%Z.
    move=> mc nm; apply: SMS.not_elem_of_count.
    move=> /SMS.elem_of_map [n' [e nc]].
    have := strict m n' mc nc (or_introl nm); rewrite -e.
    exact: MSet.glt_irrefl.
  rewrite !coeffE car_mul (SMS.count_bind_single _ _ _ _ Z).
  by rewrite (SMS.count_map_inj (λ n, mp ⊎ n) mq (car q) inj).
- move=> n; rewrite car_mul => /SMS.elem_of_bind [m [mc /SMS.elem_of_map]].
  move=> [n' [-> nc]].
  case: (decide (m = mp ∧ n' = mq)) => [[-> ->]|ne]; first by left.
  right; apply: strict => //.
  by case: (decide (m = mp)) => [em|]; [right => en; apply: ne|left].
Qed.

Lemma sign_mul (a b : Z) : a ≠ 0%Z → b ≠ 0%Z →
  bool_decide (a * b < 0)%Z =
  xorb (bool_decide (a < 0)%Z) (bool_decide (b < 0)%Z).
Proof.
move=> na nb.
case: (Z.lt_ge_cases a 0) => ha; case: (Z.lt_ge_cases b 0) => hb.
- have hab : ¬ (a * b < 0)%Z by nia.
  by rewrite (bool_decide_eq_false_2 _ hab) (bool_decide_eq_true_2 _ ha)
    (bool_decide_eq_true_2 _ hb).
- have hab : (a * b < 0)%Z by nia.
  have hb' : ¬ (b < 0)%Z by lia.
  by rewrite (bool_decide_eq_true_2 _ hab) (bool_decide_eq_true_2 _ ha)
    (bool_decide_eq_false_2 _ hb').
- have hab : (a * b < 0)%Z by nia.
  have ha' : ¬ (a < 0)%Z by lia.
  by rewrite (bool_decide_eq_true_2 _ hab) (bool_decide_eq_false_2 _ ha')
    (bool_decide_eq_true_2 _ hb).
- have hab : ¬ (a * b < 0)%Z by nia.
  have ha' : ¬ (a < 0)%Z by lia.
  have hb' : ¬ (b < 0)%Z by lia.
  by rewrite (bool_decide_eq_false_2 _ hab) (bool_decide_eq_false_2 _ ha')
    (bool_decide_eq_false_2 _ hb').
Qed.

Lemma first_neg_mul p q :
  p ≠ zero → q ≠ zero →
  first_neg (mul p q) = xorb (first_neg p) (first_neg q).
Proof.
move=> np nq.
have [mp [pp [hp ->]]] := first_neg_spec _ np.
have [mq [qq [hq ->]]] := first_neg_spec _ nq.
have [ec hm] := coeff_mul_min _ _ _ _ pp hp qq hq.
have cp := proj2 (coeff_neq0_elem _ _) pp.
have cq := proj2 (coeff_neq0_elem _ _) qq.
have cpq : coeff (mp ⊎ mq) (mul p q) ≠ 0%Z by rewrite ec; nia.
have m_in := proj1 (coeff_neq0_elem _ _) cpq.
have npq : mul p q ≠ zero.
  by move=> e; apply: cpq; rewrite e coeff_zero.
have [m [mpq [hmpq ->]]] := first_neg_spec _ npq.
have -> : m = mp ⊎ mq.
  exact: (glt_min_unique (car (mul p q))).
by rewrite ec sign_mul.
Qed.

Lemma mono_pm_inj a b : mono a = mono b ∨ mono a = opp (mono b) → a = b.
Proof.
move=> e; have : coeff a (mono a) ≠ 0%Z.
  by rewrite coeff_mono (bool_decide_eq_true_2 (a = a)).
case: e => ->; first by move/coeff_mono_eq.
by rewrite coeff_opp => h; apply/coeff_mono_eq; lia.
Qed.

End Polynomial.

Arguments poly T {_ _ _ _}.

(** ** Renaming variables

    [map f p] renames the variables of [p] with [f].  It is a ring morphism,
    and it is injective when [f] is ([map_inj]). *)

Section Map.

Context {T U : Type}.
Context `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Implicit Types (f : T → U) (p q : poly T).

lock Definition map f p : poly U := mk (SMS.map (MSet.map f) (car p)).

Lemma car_map f p : car (map f p) = SMS.map (MSet.map f) (car p).
Proof. by rewrite [map]unlock. Qed.

Lemma map_zero f : map f zero = zero.
Proof. by apply: car_inj; rewrite car_map !car_zero SMS.map_empty. Qed.

Lemma map_mono f m : map f (mono m) = mono (MSet.map f m).
Proof. by apply: car_inj; rewrite car_map !car_mono SMS.map_singleton. Qed.

Lemma map_one f : map f one = one.
Proof. by rewrite !oneE map_mono MSet.map_empty. Qed.

Lemma map_var f x : map f (var x) = var (f x).
Proof. by rewrite !varE map_mono MSet.map_singleton. Qed.

Lemma map_add f p q : map f (add p q) = add (map f p) (map f q).
Proof. by apply: car_inj; rewrite !(car_map, car_add) SMS.map_disj_union. Qed.

Lemma map_opp f p : map f (opp p) = opp (map f p).
Proof. by apply: car_inj; rewrite !(car_map, car_opp) SMS.map_inv. Qed.

Lemma map_sub f p q : map f (sub p q) = sub (map f p) (map f q).
Proof. by rewrite !subE map_add map_opp. Qed.

Lemma map_mul f p q : map f (mul p q) = mul (map f p) (map f q).
Proof.
apply: car_inj; rewrite !(car_map, car_mul).
rewrite SMS.map_bind SMS.bind_map; apply: SMS.bind_ext => m _ /=.
rewrite !SMS.map_map; apply: SMS.map_ext => n _.
exact: MSet.map_disj_union.
Qed.

Lemma map_const f z : map f (const z) = const z.
Proof.
apply: car_inj; rewrite car_map ![const]unlock /= SMS.map_make.
by rewrite !MSet.map_of_list !fmap_replicate MSet.map_empty.
Qed.

Lemma coeff_map_inj f m p :
  (∀ a b, f a = f b → a = b) → coeff (MSet.map f m) (map f p) = coeff m p.
Proof.
move=> finj; rewrite !coeffE car_map.
apply: (SMS.count_map_inj (MSet.map f)) => X Y e.
apply: MSet.count_inj => x.
by rewrite -(MSet.count_map_inj f x X finj) e MSet.count_map_inj.
Qed.

Lemma map_inj f p q :
  (∀ a b, f a = f b → a = b) → map f p = map f q → p = q.
Proof.
move=> finj e; apply: coeff_inj => m.
by rewrite -!(coeff_map_inj _ m _ finj) e.
Qed.

End Map.

Lemma map_map {T U V : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    `{EqDecision U, Lexico U, !StrictOrder (@lexico U _),
      !TrichotomyT (@lexico U _)}
    `{EqDecision V, Lexico V, !StrictOrder (@lexico V _),
      !TrichotomyT (@lexico V _)}
    (f : T → U) (g : U → V) (p : poly T) :
  map g (map f p) = map (λ x, g (f x)) p.
Proof.
apply: car_inj; rewrite !car_map SMS.map_map; apply: SMS.map_ext => m _.
exact: MSet.map_map.
Qed.

Lemma map_id_ext {T : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    (f : T → T) (p : poly T) :
  (∀ m x, m ∈ car p → x ∈ m → f x = x) → map f p = p.
Proof.
move=> fp; apply: car_inj; rewrite car_map.
apply: SMS.map_id_ext => m m_s.
rewrite -[RHS]MSet.of_list_elements [MSet.map]unlock; congr MSet.of_list.
rewrite -[RHS]list_fmap_id; apply: list_fmap_ext => i x hx.
apply: (fp m x m_s); rewrite -MSet.elem_of_elements.
exact: list_elem_of_lookup_2 hx.
Qed.

End Poly.

Declare Scope poly_scope.
Delimit Scope poly_scope with P.
Infix "+" := Poly.add : poly_scope.
Infix "-" := Poly.sub : poly_scope.
Infix "*" := Poly.mul : poly_scope.
Notation "- p" := (Poly.opp p) : poly_scope.
