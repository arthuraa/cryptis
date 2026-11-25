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
    one monomial at a time.

    [gcd p q] computes a greatest common divisor one variable at a time, and
    [div] computes exact quotients.  [cancel p q] divides [p] and [q] by
    [gcd p q] to remove their common factors.  [cancel_spec] proves that it
    only divides out a common factor.  [poly_gcd.v] proves that [gcd] is a
    greatest common divisor, that [div] is exact, and that [cancel] leaves no
    common factor besides [1] and [-1] and maps equal fractions to the same
    pair. *)

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

Definition coeff m p : Z := SMS.count m (car p).

Definition mono m : poly := mk {[+ m +]}.
Definition zero : poly := mk ∅.
Definition one : poly := mono ∅.
Definition var x : poly := mono {[+ x +]}.
Definition add p q : poly := mk (car p ⊎ car q).
Definition opp p : poly := mk (SMS.inv (car p)).
Definition mul p q : poly :=
  mk (SMS.bind (λ m, SMS.map (λ n, m ⊎ n) (car q)) (car p)).

Lemma car_inj p q : car p = car q → p = q.
Proof. by case: p q => [s1] [s2] /= ->. Qed.

Lemma coeff_inj p q : (∀ m, coeff m p = coeff m q) → p = q.
Proof. by move=> e; apply: car_inj; apply: SMS.count_inj. Qed.

#[global] Instance eq_dec : EqDecision poly := λ p q,
  match decide (car p = car q) with
  | left e => left (car_inj p q e)
  | right n => right (λ e, n (f_equal car e))
  end.

(** *** Coefficients *)

Lemma coeff_mono m n : coeff m (mono n) = Z.b2z (bool_decide (m = n)).
Proof. exact: SMS.count_singleton. Qed.

Lemma coeff_zero m : coeff m zero = 0%Z.
Proof. exact: SMS.count_empty. Qed.

Lemma coeff_one m : coeff m one = Z.b2z (bool_decide (m = ∅)).
Proof. exact: coeff_mono. Qed.

Lemma coeff_var m x : coeff m (var x) = Z.b2z (bool_decide (m = {[+ x +]})).
Proof. exact: coeff_mono. Qed.

Lemma coeff_add m p q : coeff m (add p q) = (coeff m p + coeff m q)%Z.
Proof. exact: SMS.count_disj_union. Qed.

Lemma coeff_opp m p : coeff m (opp p) = (- coeff m p)%Z.
Proof. exact: SMS.count_inv. Qed.

Lemma coeff_mono_eq m n : coeff m (mono n) ≠ 0%Z ↔ m = n.
Proof. rewrite coeff_mono; case_bool_decide; naive_solver. Qed.

Lemma coeff_neq0_elem m p : coeff m p ≠ 0%Z ↔ m ∈ car p.
Proof. by rewrite SMS.elem_of_count. Qed.

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

Lemma mul_mono m n : mul (mono m) (mono n) = mono (m ⊎ n).
Proof. by rewrite /mul /= SMS.bind_singleton /= SMS.map_singleton. Qed.

#[global] Instance mul_comm : Comm (=@{poly}) mul.
Proof.
move=> p q; apply: car_inj; rewrite /mul /=.
rewrite (SMS.bind_comm (λ m n, {[+ m ⊎ n +]})).
apply: SMS.bind_ext => n _; apply: SMS.bind_ext => m _ /=.
by rewrite (comm (⊎)).
Qed.

#[global] Instance mul_assoc : Assoc (=@{poly}) mul.
Proof.
move=> p q r; apply: car_inj; rewrite /mul /= SMS.bind_bind.
apply: SMS.bind_ext => m _ /=; rewrite SMS.map_bind SMS.bind_map.
apply: SMS.bind_ext => n _ /=; rewrite SMS.map_map.
by apply: SMS.map_ext => k _; rewrite (assoc (⊎)).
Qed.

#[global] Instance mul_left_id : LeftId (=@{poly}) one mul.
Proof.
move=> p; apply: car_inj; rewrite /mul /= SMS.bind_singleton.
by apply: SMS.map_id_ext => n _; rewrite (left_id ∅ (⊎)).
Qed.

#[global] Instance mul_right_id : RightId (=@{poly}) one mul.
Proof.
move=> p; apply: car_inj; rewrite /mul /= -[RHS]SMS.bind_unit.
apply: SMS.bind_ext => m _ /=.
by rewrite SMS.map_singleton (right_id ∅ (⊎)).
Qed.

#[global] Instance mul_left_absorb : LeftAbsorb (=@{poly}) zero mul.
Proof. by move=> p; apply: car_inj; rewrite /mul /= SMS.bind_empty. Qed.

#[global] Instance mul_right_absorb : RightAbsorb (=@{poly}) zero mul.
Proof.
move=> p; apply: car_inj; rewrite /mul /= -[RHS](SMS.bind_empty_l (car p)).
by apply: SMS.bind_ext => m _ /=; rewrite SMS.map_empty.
Qed.

Lemma mul_add_l p q r : mul (add p q) r = add (mul p r) (mul q r).
Proof. by apply: car_inj; rewrite /mul /= SMS.bind_disj_union. Qed.

Lemma mul_add_r p q r : mul p (add q r) = add (mul p q) (mul p r).
Proof.
apply: car_inj; rewrite /mul /= -SMS.bind_disj_union_l.
by apply: SMS.bind_ext => m _ /=; rewrite SMS.map_disj_union.
Qed.

Lemma mul_opp_l p q : mul (opp p) q = opp (mul p q).
Proof. by apply: car_inj; rewrite /mul /= SMS.bind_inv. Qed.

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
- exact: P0.
- exact: Ppos m (mk s) IH.
- exact: Pneg m (mk s) IH.
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

Definition const (n : Z) : poly :=
  mk (SMS.make (MSet.of_list (replicate (Z.to_nat n) ∅))
               (MSet.of_list (replicate (Z.to_nat (- n)) ∅))).

Definition sub p q : poly := add p (opp q).

Lemma coeff_const m z :
  coeff m (const z) = if bool_decide (m = ∅) then z else 0%Z.
Proof.
have e k : MSet.count m (MSet.of_list (replicate k ∅)) =
           if bool_decide (m = ∅) then k else 0.
  rewrite MSet.count_of_list.
  by elim: k => [|k IH] /=; rewrite ?IH; case_bool_decide.
rewrite /coeff SMS.count_make !e; case_bool_decide; lia.
Qed.

Lemma coeff_sub m p q : coeff m (sub p q) = (coeff m p - coeff m q)%Z.
Proof. rewrite coeff_add coeff_opp; lia. Qed.

(** *** Ring structure *)

(* [Add Ring] does not outlive its section, so clients declare the ring from
   this theory in their own sections. *)
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
- done.
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
Proof. done. Qed.

Lemma const_one : const 1 = one.
Proof. done. Qed.

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

Definition vpow x k : MSet.mset T := MSet.of_list (replicate k x).

Definition deg x p : nat := max_list (MSet.count x <$> elements (car p)).

Definition coeffx x k p : poly :=
  mk (SMS.bind (λ m, if bool_decide (MSet.count x m = k)
                     then {[+ m ∖ vpow x k +]} else ∅) (car p)).

Definition lcx x p : poly := coeffx x (deg x p) p.

Definition vars p : list T := remove_dups (elements (car p) ≫= elements).

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

Definition prem x a b : poly :=
  prem_loop x b (deg x b) (lcx x b) (deg x a + 1) a.

Fixpoint div_loop x (dv : poly → poly → poly) g d l fuel r q :=
  match fuel with
  | O => q
  | S fuel =>
      if bool_decide (r = zero) then q else
      let c := mul (dv (lcx x r) l) (mono (vpow x (deg x r - d))) in
      div_loop x dv g d l fuel (sub r (mul c g)) (add q c)
  end.

Definition div_lvl x dv p g : poly :=
  div_loop x dv g (deg x g) (lcx x g) (deg x p + 1) p zero.

Definition cont x (gc : poly → poly → poly) p : poly :=
  foldr gc zero ((λ k, coeffx x k p) <$> seq 0 (deg x p + 1)).

Fixpoint prs x gc dv fuel a b : poly :=
  match fuel with
  | O => a
  | S fuel =>
      if bool_decide (b = zero) then a else
      let r := prem x a b in
      prs x gc dv fuel b (div_lvl x dv r (cont x gc r))
  end.

Definition gcd_lvl x gc dv p q : poly :=
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

Definition gcd p q : poly := (ops (remove_dups (vars p ++ vars q))).1 p q.

Definition div p q : poly := (ops (remove_dups (vars p ++ vars q))).2 p q.

(** *** Cancelling common factors

    [cancel p q] divides [p] and [q] by [gcd p q], and fixes the sign by
    making the first coefficient of the second component positive.  The
    divisions are checked, so [cancel] is sound however [gcd] behaves. *)

Definition first_neg p : bool :=
  match elements (SMS.pos (car p) ⊎ SMS.neg (car p)) with
  | m :: _ => bool_decide (coeff m p < 0)%Z
  | [] => false
  end.

Definition cancel_with g p q p' q' : poly * poly :=
  if bool_decide (mul g p' = p ∧ mul g q' = q) then
    if first_neg q' then (opp p', opp q') else (p', q')
  else (p, q).

Definition cancel p q : poly * poly :=
  let g := gcd p q in cancel_with g p q (div p g) (div q g).

Lemma cancel_spec p q :
  ∃ g, p = mul g (cancel p q).1 ∧ q = mul g (cancel p q).2.
Proof.
rewrite /cancel; move: (gcd p q) => g; move: (div p g) (div q g) => p' q'.
rewrite /cancel_with; case: bool_decide_reflect => [[ep eq]|_]; last first.
  by exists one; rewrite !(left_id one mul).
case: (first_neg q'); last by exists g.
by exists (opp g); rewrite /= !mul_opp_l !mul_opp_r !opp_opp.
Qed.

End Polynomial.

Arguments poly T {_ _ _ _}.

End Poly.

Declare Scope poly_scope.
Delimit Scope poly_scope with P.
Infix "+" := Poly.add : poly_scope.
Infix "-" := Poly.sub : poly_scope.
Infix "*" := Poly.mul : poly_scope.
Notation "- p" := (Poly.opp p) : poly_scope.
