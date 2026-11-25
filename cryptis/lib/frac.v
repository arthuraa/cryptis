(** Rational functions with integer coefficients over a type [T] ordered by
    a [Lexico] instance.

    A rational function [f : frac T] is a fraction [num f / den f] of
    polynomials kept in the canonical form of [Poly.cancel]: [den f] is
    nonzero ([den_neq0]), the only common divisors of [num f] and [den f]
    are units ([num_den_coprime]), and [den f] is not [Poly.first_neg]
    ([den_first_neg]).  Hence equal rational functions are represented by
    the same fraction ([frac_eq]).

    [make p q] puts [p / q] in canonical form, and [add], [mul] and [inv]
    are computed with it.  [of_poly] is the canonical injection of
    polynomials, an injective ring morphism ([of_poly_inj], [of_poly_add],
    [of_poly_mul]).  As in mathcomp, inversion and division are total:
    [inv zero = zero] ([inv_zero]) and [div f zero = zero] ([div_zero]), and
    [make p q = div (of_poly p) (of_poly q)] ([make_div]).  The operations
    form a field ([frac_field_theory]), and [f + g], [f - g], [f * g],
    [f / g], [- f] and [/ f] denote them in [frac_scope], delimited by
    [%F]. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list numbers proof_irrel.
From Stdlib Require Import ZArith Lia Ring Field.
From cryptis.lib Require Import mset sms poly poly_gcd.

Module Frac.

Section Frac.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Local Abbreviation poly := (Poly.poly T).

Add Ring poly_ring : (Poly.poly_ring_theory (T := T)).

Implicit Types (p q : poly).

Definition wf p q : bool :=
  bool_decide (q ≠ Poly.zero ∧ Poly.cancel p q = (p, q)).

Record frac := mk { num : poly; den : poly; wf_num_den : wf num den }.

Implicit Types (f g h : frac).

Lemma num_den_inj f g : num f = num g → den f = den g → f = g.
Proof.
case: f g => [p1 q1 w1] [p2 q2 w2] /= ep eq; subst.
by rewrite (proof_irrel w1 w2).
Qed.

#[global] Instance eq_dec : EqDecision frac := λ f g,
  match decide ((num f, den f) = (num g, den g)) with
  | left e => left (num_den_inj f g (f_equal fst e) (f_equal snd e))
  | right n => right (λ e, n (f_equal (λ f, (num f, den f)) e))
  end.

(** *** Canonical form *)

Lemma den_neq0 f : den f ≠ Poly.zero.
Proof. exact: proj1 (bool_decide_unpack _ (wf_num_den f)). Qed.

Lemma cancel_num_den f : Poly.cancel (num f) (den f) = (num f, den f).
Proof. exact: proj2 (bool_decide_unpack _ (wf_num_den f)). Qed.

Lemma num_den_coprime f u :
  PolyGcd.dvd u (num f) → PolyGcd.dvd u (den f) → PolyGcd.dvd u Poly.one.
Proof.
have := PolyGcd.cancel_coprime (num f) (den f) u (or_intror (den_neq0 f)).
by rewrite cancel_num_den.
Qed.

Lemma den_first_neg f : Poly.first_neg (den f) = false.
Proof.
have := PolyGcd.cancel_first_neg (num f) (den f) (den_neq0 f).
by rewrite cancel_num_den.
Qed.

(* ssreflect's [apply:] diverges on [bool_decide_pack]; plain [apply] does
   not. *)
Lemma wf_cancel p q :
  q ≠ Poly.zero → wf (Poly.cancel p q).1 (Poly.cancel p q).2.
Proof.
move=> nq; apply bool_decide_pack; split.
  exact: PolyGcd.cancel_den_neq0.
apply: PolyGcd.cancel_id.
- exact: PolyGcd.cancel_den_neq0.
- by move=> u; apply: PolyGcd.cancel_coprime; right.
- exact: PolyGcd.cancel_first_neg.
Qed.

Lemma wf_of_poly p : wf p Poly.one.
Proof.
apply bool_decide_pack; split; first exact: Poly.one_neq0.
apply: PolyGcd.cancel_id; first exact: Poly.one_neq0.
- by move=> u _.
- done.
Qed.

Lemma wf_opp f : wf (- num f)%P (den f).
Proof.
apply bool_decide_pack; split; first exact: den_neq0.
apply: PolyGcd.cancel_id; [exact: den_neq0| |exact: den_first_neg].
move=> u un ud; apply: (num_den_coprime f) => //.
by rewrite -(Poly.opp_opp (num f)); apply: PolyGcd.dvd_opp.
Qed.

(** *** Operations *)

Definition of_poly p : frac := mk p Poly.one (wf_of_poly p).
Definition zero : frac := of_poly Poly.zero.
Definition one : frac := of_poly Poly.one.

Definition make p q : frac :=
  match decide (q = Poly.zero) with
  | left _ => zero
  | right nq => mk _ _ (wf_cancel p q nq)
  end.

Definition opp f : frac := mk _ _ (wf_opp f).
Definition add f g : frac :=
  make (num f * den g + num g * den f)%P (den f * den g)%P.
Definition sub f g : frac := add f (opp g).
Definition mul f g : frac := make (num f * num g)%P (den f * den g)%P.
Definition inv f : frac := make (den f) (num f).
Definition div f g : frac := mul f (inv g).

(** *** Fractions *)

Lemma make_cancel p q : q ≠ Poly.zero →
  num (make p q) = (Poly.cancel p q).1 ∧ den (make p q) = (Poly.cancel p q).2.
Proof. by move=> nq; rewrite /make; case_decide. Qed.

Lemma make_den0 p : make p Poly.zero = zero.
Proof. by rewrite /make; case_decide. Qed.

Lemma make_spec p q : q ≠ Poly.zero →
  (num (make p q) * q = p * den (make p q))%P.
Proof.
move=> nq; have [-> ->] := make_cancel p q nq.
have [g [Ep Eq]] := Poly.cancel_spec p q.
move: (Poly.cancel p q) Ep Eq => c Ep Eq.
by rewrite Ep Eq; ring.
Qed.

Lemma make_eq p q p' q' : q ≠ Poly.zero → q' ≠ Poly.zero →
  (p * q' = p' * q)%P → make p q = make p' q'.
Proof.
move=> nq nq' e.
have E := proj2 (PolyGcd.cancel_canon p q p' q' nq nq') e.
have [e1 e2] := make_cancel p q nq; have [e1' e2'] := make_cancel p' q' nq'.
by apply: num_den_inj; rewrite ?e1 ?e2 ?e1' ?e2' E.
Qed.

Lemma make_num_den f : make (num f) (den f) = f.
Proof.
have [e1 e2] := make_cancel (num f) (den f) (den_neq0 f).
by apply: num_den_inj; rewrite ?e1 ?e2 cancel_num_den.
Qed.

Lemma frac_eq f g : f = g ↔ (num f * den g = num g * den f)%P.
Proof.
split=> [-> //|e].
rewrite -(make_num_den f) -(make_num_den g).
exact: make_eq (den_neq0 f) (den_neq0 g) e.
Qed.

Lemma frac_ind (P : frac → Prop) :
  (∀ p q, q ≠ Poly.zero → P (make p q)) → ∀ f, P f.
Proof. by move=> h f; rewrite -(make_num_den f); apply: h; apply: den_neq0. Qed.

Lemma of_poly_make p : make p Poly.one = of_poly p.
Proof. exact: make_num_den (of_poly p). Qed.

Lemma make_num0 q : make Poly.zero q = zero.
Proof.
case: (decide (q = Poly.zero)) => [->|nq]; first exact: make_den0.
rewrite /zero -of_poly_make.
apply: make_eq; [done|exact: Poly.one_neq0|ring].
Qed.

Lemma opp_make p q : q ≠ Poly.zero → opp (make p q) = make (- p)%P q.
Proof.
move=> nq; rewrite -[LHS]make_num_den.
apply: make_eq => //; first exact: den_neq0.
have := make_spec p q nq; move: (make p q) => f e.
transitivity (- (num f * q))%P; first by rewrite /=; ring.
by rewrite e /=; ring.
Qed.

Lemma add_make p q p' q' : q ≠ Poly.zero → q' ≠ Poly.zero →
  add (make p q) (make p' q') = make (p * q' + p' * q)%P (q * q')%P.
Proof.
move=> nq nq'; rewrite /add.
have e := make_spec p q nq; have e' := make_spec p' q' nq'.
move: (make p q) (make p' q') e e' => f f' e e'.
apply: make_eq.
- exact: PolyGcd.mul_neq0 (den_neq0 f) (den_neq0 f').
- exact: PolyGcd.mul_neq0.
transitivity (num f * q * (den f' * q') + num f' * q' * (den f * q))%P.
  ring.
by rewrite e e'; ring.
Qed.

Lemma mul_make p q p' q' : q ≠ Poly.zero → q' ≠ Poly.zero →
  mul (make p q) (make p' q') = make (p * p')%P (q * q')%P.
Proof.
move=> nq nq'; rewrite /mul.
have e := make_spec p q nq; have e' := make_spec p' q' nq'.
move: (make p q) (make p' q') e e' => f f' e e'.
apply: make_eq.
- exact: PolyGcd.mul_neq0 (den_neq0 f) (den_neq0 f').
- exact: PolyGcd.mul_neq0.
transitivity (num f * q * (num f' * q'))%P; first ring.
by rewrite e e'; ring.
Qed.

Lemma inv_zero : inv zero = zero.
Proof. exact: make_den0. Qed.

Lemma inv_make p q : q ≠ Poly.zero → inv (make p q) = make q p.
Proof.
move=> nq; case: (decide (p = Poly.zero)) => [->|np].
  by rewrite make_num0 make_den0 inv_zero.
rewrite /inv; have := make_spec p q nq; move: (make p q) => f e.
have nf : num f ≠ Poly.zero.
  move=> ef; rewrite ef (left_absorb Poly.zero Poly.mul) in e.
  case: (PolyGcd.domain _ _ (eq_sym e)) => //; exact: den_neq0.
apply: make_eq => //.
transitivity (p * den f)%P; first ring.
by rewrite -e; ring.
Qed.

(** *** Field laws *)

#[global] Instance add_left_id : LeftId (=@{frac}) zero add.
Proof.
elim/frac_ind=> p q nq.
rewrite /zero -of_poly_make (add_make _ _ _ _ Poly.one_neq0 nq).
apply: make_eq => //; [exact: PolyGcd.mul_neq0 Poly.one_neq0 nq|ring].
Qed.

#[global] Instance add_comm : Comm (=@{frac}) add.
Proof.
elim/frac_ind=> p q nq; elim/frac_ind=> p' q' nq'.
rewrite (add_make _ _ _ _ nq nq') (add_make _ _ _ _ nq' nq).
apply: make_eq; [exact: PolyGcd.mul_neq0|exact: PolyGcd.mul_neq0|ring].
Qed.

#[global] Instance add_assoc : Assoc (=@{frac}) add.
Proof.
elim/frac_ind=> p1 q1 n1; elim/frac_ind=> p2 q2 n2; elim/frac_ind=> p3 q3 n3.
have n12 := PolyGcd.mul_neq0 _ _ n1 n2.
have n23 := PolyGcd.mul_neq0 _ _ n2 n3.
rewrite (add_make _ _ _ _ n2 n3) (add_make _ _ _ _ n1 n23).
rewrite (add_make _ _ _ _ n1 n2) (add_make _ _ _ _ n12 n3).
apply: make_eq; [exact: PolyGcd.mul_neq0|exact: PolyGcd.mul_neq0|ring].
Qed.

Lemma add_opp_r f : add f (opp f) = zero.
Proof.
elim/frac_ind: f => p q nq.
rewrite (opp_make _ _ nq) (add_make _ _ _ _ nq nq) -(make_num0 (q * q)%P).
apply: make_eq; [exact: PolyGcd.mul_neq0|exact: PolyGcd.mul_neq0|ring].
Qed.

#[global] Instance mul_left_id : LeftId (=@{frac}) one mul.
Proof.
elim/frac_ind=> p q nq.
rewrite /one -of_poly_make (mul_make _ _ _ _ Poly.one_neq0 nq).
apply: make_eq => //; [exact: PolyGcd.mul_neq0 Poly.one_neq0 nq|ring].
Qed.

#[global] Instance mul_comm : Comm (=@{frac}) mul.
Proof.
elim/frac_ind=> p q nq; elim/frac_ind=> p' q' nq'.
rewrite (mul_make _ _ _ _ nq nq') (mul_make _ _ _ _ nq' nq).
apply: make_eq; [exact: PolyGcd.mul_neq0|exact: PolyGcd.mul_neq0|ring].
Qed.

#[global] Instance mul_assoc : Assoc (=@{frac}) mul.
Proof.
elim/frac_ind=> p1 q1 n1; elim/frac_ind=> p2 q2 n2; elim/frac_ind=> p3 q3 n3.
have n12 := PolyGcd.mul_neq0 _ _ n1 n2.
have n23 := PolyGcd.mul_neq0 _ _ n2 n3.
rewrite (mul_make _ _ _ _ n2 n3) (mul_make _ _ _ _ n1 n23).
rewrite (mul_make _ _ _ _ n1 n2) (mul_make _ _ _ _ n12 n3).
apply: make_eq; [exact: PolyGcd.mul_neq0|exact: PolyGcd.mul_neq0|ring].
Qed.

Lemma mul_add_l f g h : mul (add f g) h = add (mul f h) (mul g h).
Proof.
elim/frac_ind: f => p1 q1 n1; elim/frac_ind: g => p2 q2 n2.
elim/frac_ind: h => p3 q3 n3.
have n12 := PolyGcd.mul_neq0 _ _ n1 n2.
have n13 := PolyGcd.mul_neq0 _ _ n1 n3.
have n23 := PolyGcd.mul_neq0 _ _ n2 n3.
rewrite (add_make _ _ _ _ n1 n2) (mul_make _ _ _ _ n12 n3).
rewrite (mul_make _ _ _ _ n1 n3) (mul_make _ _ _ _ n2 n3).
rewrite (add_make _ _ _ _ n13 n23).
apply: make_eq; [exact: PolyGcd.mul_neq0|exact: PolyGcd.mul_neq0|ring].
Qed.

Lemma one_neq0 : one ≠ zero.
Proof. by move=> /(f_equal num); exact: Poly.one_neq0. Qed.

Lemma mul_inv_l f : f ≠ zero → mul (inv f) f = one.
Proof.
elim/frac_ind: f => p q nq nf.
have np : p ≠ Poly.zero by move=> ep; apply: nf; rewrite ep make_num0.
rewrite (inv_make _ _ nq) (mul_make _ _ _ _ np nq) /one -of_poly_make.
apply: make_eq; [exact: PolyGcd.mul_neq0|exact: Poly.one_neq0|ring].
Qed.

Lemma div_zero f : div f zero = zero.
Proof.
elim/frac_ind: f => p q nq; rewrite /div inv_zero -(make_num0 Poly.one).
rewrite (mul_make _ _ _ _ nq Poly.one_neq0).
apply: make_eq; first exact: PolyGcd.mul_neq0 nq Poly.one_neq0.
- exact: Poly.one_neq0.
- ring.
Qed.

Lemma frac_ring_theory : ring_theory zero one add mul sub opp eq.
Proof.
split.
- exact: (left_id zero add).
- exact: (comm add).
- move=> f g h; exact: (assoc add).
- exact: (left_id one mul).
- exact: (comm mul).
- move=> f g h; exact: (assoc mul).
- exact: mul_add_l.
- done.
- exact: add_opp_r.
Qed.

(* [Add Field] does not outlive its section, so clients declare the field from
   this theory in their own sections. *)
Lemma frac_field_theory : field_theory zero one add mul sub opp div inv eq.
Proof.
split.
- exact: frac_ring_theory.
- exact: one_neq0.
- done.
- exact: mul_inv_l.
Qed.

(** *** Polynomials *)

Lemma of_poly_inj p q : of_poly p = of_poly q → p = q.
Proof. by move=> /(f_equal num). Qed.

Lemma of_poly_add p q : of_poly (p + q)%P = add (of_poly p) (of_poly q).
Proof.
rewrite -!of_poly_make (add_make _ _ _ _ Poly.one_neq0 Poly.one_neq0).
apply: make_eq; first exact: Poly.one_neq0.
- exact: PolyGcd.mul_neq0 Poly.one_neq0 Poly.one_neq0.
- ring.
Qed.

Lemma of_poly_mul p q : of_poly (p * q)%P = mul (of_poly p) (of_poly q).
Proof.
rewrite -!of_poly_make (mul_make _ _ _ _ Poly.one_neq0 Poly.one_neq0).
apply: make_eq; first exact: Poly.one_neq0.
- exact: PolyGcd.mul_neq0 Poly.one_neq0 Poly.one_neq0.
- ring.
Qed.

Lemma make_div p q : make p q = div (of_poly p) (of_poly q).
Proof.
rewrite /div -!of_poly_make (inv_make _ _ Poly.one_neq0).
case: (decide (q = Poly.zero)) => [->|nq].
  rewrite !make_den0 -(make_num0 Poly.one).
  rewrite (mul_make _ _ _ _ Poly.one_neq0 Poly.one_neq0).
  apply: make_eq; first exact: Poly.one_neq0.
  - exact: PolyGcd.mul_neq0 Poly.one_neq0 Poly.one_neq0.
  - ring.
rewrite (mul_make _ _ _ _ Poly.one_neq0 nq).
apply: make_eq => //; first exact: PolyGcd.mul_neq0 Poly.one_neq0 nq.
ring.
Qed.

End Frac.

Arguments frac T {_ _ _ _}.

End Frac.

Declare Scope frac_scope.
Delimit Scope frac_scope with F.
Infix "+" := Frac.add : frac_scope.
Infix "-" := Frac.sub : frac_scope.
Infix "*" := Frac.mul : frac_scope.
Infix "/" := Frac.div : frac_scope.
Notation "- f" := (Frac.opp f) : frac_scope.
Notation "/ f" := (Frac.inv f) : frac_scope.
