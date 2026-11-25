(** Polynomials with integer coefficients over a type [T] ordered by a
    [Lexico] instance.

    A monomial is a multiset of variables ([MSet.mset T]): [∅] is the constant
    monomial and [{[+ x; x; y +]}] is [x²y].  A polynomial [poly T] wraps a
    signed multiset of monomials ([SMS.sms (MSet.mset T)]): the signed
    multiplicity of a monomial is its coefficient ([coeff]), and equality is
    Leibniz ([coeff_inj]).

    [add] and [opp] are the group operations of the signed multiset, and [mul]
    multiplies every monomial of one polynomial by every monomial of the other
    by adding up their variables.  Polynomials form a commutative ring with
    [zero] and [one].  [mono m] is the monomial [m] with coefficient [1], and
    [poly_ind] builds a polynomial by adding or subtracting one monomial at a
    time. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list numbers.
From Stdlib Require Import ZArith Lia.
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

End Polynomial.

Arguments poly T {_ _ _ _}.

End Poly.
