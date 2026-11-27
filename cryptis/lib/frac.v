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
    [%F].

    [vars f] lists the variables of [f], [over vs f] says that they are
    among [vs] and [all_vars P f] that they satisfy [P].  [valuation x f] is
    the [x]-adic valuation of [f].  [mono_num f] and [mono_den f] say that
    the numerator or the denominator of [f] is a monomial, and [laurent f]
    that both are, i.e. that [f] is a Laurent monomial.  [map f r]
    renames variables, [eval φ p] substitutes [φ x] for every variable [x] of
    a polynomial (a ring morphism), and [bind φ r] substitutes in a fraction
    by dividing the evaluated numerator by the evaluated denominator.  The
    operations are locked, since computing with them in proofs is slow;
    [unlock] exposes their definitions. *)

From elpi.apps Require Import locker.
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
- by rewrite Poly.oneE Poly.first_neg_mono.
Qed.

Lemma wf_opp f : wf (- num f)%P (den f).
Proof.
apply bool_decide_pack; split; first exact: den_neq0.
apply: PolyGcd.cancel_id; [exact: den_neq0| |exact: den_first_neg].
move=> u un ud; apply: (num_den_coprime f) => //.
by rewrite -(Poly.opp_opp (num f)); apply: PolyGcd.dvd_opp.
Qed.

(** *** Operations *)

lock Definition of_poly p : frac := mk p Poly.one (wf_of_poly p).
lock Definition zero : frac := of_poly Poly.zero.
lock Definition one : frac := of_poly Poly.one.

lock Definition make p q : frac :=
  match decide (q = Poly.zero) with
  | left _ => zero
  | right nq => mk _ _ (wf_cancel p q nq)
  end.

lock Definition opp f : frac := mk _ _ (wf_opp f).
lock Definition add f g : frac :=
  make (num f * den g + num g * den f)%P (den f * den g)%P.
lock Definition sub f g : frac := add f (opp g).
lock Definition mul f g : frac := make (num f * num g)%P (den f * den g)%P.
lock Definition inv f : frac := make (den f) (num f).
lock Definition div f g : frac := mul f (inv g).

Lemma num_of_poly p : num (of_poly p) = p.
Proof. by rewrite [of_poly]unlock. Qed.

Lemma den_of_poly p : den (of_poly p) = Poly.one.
Proof. by rewrite [of_poly]unlock. Qed.

Lemma zeroE : zero = of_poly Poly.zero.
Proof. by rewrite [zero]unlock. Qed.

Lemma oneE : one = of_poly Poly.one.
Proof. by rewrite [one]unlock. Qed.

Lemma num_zero : num zero = Poly.zero.
Proof. by rewrite zeroE num_of_poly. Qed.

Lemma den_zero : den zero = Poly.one.
Proof. by rewrite zeroE den_of_poly. Qed.

Lemma num_one : num one = Poly.one.
Proof. by rewrite oneE num_of_poly. Qed.

Lemma den_one : den one = Poly.one.
Proof. by rewrite oneE den_of_poly. Qed.

Lemma num_opp f : num (opp f) = (- num f)%P.
Proof. by rewrite [opp]unlock. Qed.

Lemma den_opp f : den (opp f) = den f.
Proof. by rewrite [opp]unlock. Qed.

Lemma addE f g :
  add f g = make (num f * den g + num g * den f)%P (den f * den g)%P.
Proof. by rewrite [add]unlock. Qed.

Lemma subE f g : sub f g = add f (opp g).
Proof. by rewrite [sub]unlock. Qed.

Lemma mulE f g : mul f g = make (num f * num g)%P (den f * den g)%P.
Proof. by rewrite [mul]unlock. Qed.

Lemma invE f : inv f = make (den f) (num f).
Proof. by rewrite [inv]unlock. Qed.

Lemma divE f g : div f g = mul f (inv g).
Proof. by rewrite [div]unlock. Qed.

(** *** Fractions *)

Lemma make_cancel p q : q ≠ Poly.zero →
  num (make p q) = (Poly.cancel p q).1 ∧ den (make p q) = (Poly.cancel p q).2.
Proof. by move=> nq; rewrite [make]unlock; case_decide. Qed.

Lemma make_den0 p : make p Poly.zero = zero.
Proof. by rewrite [make]unlock; case_decide. Qed.

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
Proof.
by have := make_num_den (of_poly p); rewrite num_of_poly den_of_poly.
Qed.

Lemma make_num0 q : make Poly.zero q = zero.
Proof.
case: (decide (q = Poly.zero)) => [->|nq]; first exact: make_den0.
rewrite !zeroE -of_poly_make.
apply: make_eq; [done|exact: Poly.one_neq0|ring].
Qed.

Lemma make_neq0 p q : p ≠ Poly.zero → q ≠ Poly.zero → make p q ≠ zero.
Proof.
move=> np nq e; have := make_spec p q nq; rewrite e num_zero => E.
case: (PolyGcd.domain p (den zero)); first by rewrite -E; ring.
- exact: np.
- exact: den_neq0.
Qed.

Lemma opp_make p q : q ≠ Poly.zero → opp (make p q) = make (- p)%P q.
Proof.
move=> nq; rewrite -[LHS]make_num_den.
apply: make_eq => //; first exact: den_neq0.
have := make_spec p q nq; move: (make p q) => f e.
rewrite num_opp den_opp.
transitivity (- (num f * q))%P; first ring.
by rewrite e; ring.
Qed.

Lemma add_make p q p' q' : q ≠ Poly.zero → q' ≠ Poly.zero →
  add (make p q) (make p' q') = make (p * q' + p' * q)%P (q * q')%P.
Proof.
move=> nq nq'; rewrite !addE.
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
move=> nq nq'; rewrite !mulE.
have e := make_spec p q nq; have e' := make_spec p' q' nq'.
move: (make p q) (make p' q') e e' => f f' e e'.
apply: make_eq.
- exact: PolyGcd.mul_neq0 (den_neq0 f) (den_neq0 f').
- exact: PolyGcd.mul_neq0.
transitivity (num f * q * (num f' * q'))%P; first ring.
by rewrite e e'; ring.
Qed.

Lemma inv_zero : inv zero = zero.
Proof. by rewrite invE num_zero make_den0. Qed.

Lemma inv_make p q : q ≠ Poly.zero → inv (make p q) = make q p.
Proof.
move=> nq; case: (decide (p = Poly.zero)) => [->|np].
  by rewrite make_num0 make_den0 inv_zero.
rewrite !invE; have := make_spec p q nq; move: (make p q) => f e.
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
rewrite !zeroE -of_poly_make (add_make _ _ _ _ Poly.one_neq0 nq).
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
rewrite !oneE -of_poly_make (mul_make _ _ _ _ Poly.one_neq0 nq).
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
Proof.
by move=> /(f_equal num); rewrite num_one num_zero; exact: Poly.one_neq0.
Qed.

Lemma mul_inv_l f : f ≠ zero → mul (inv f) f = one.
Proof.
elim/frac_ind: f => p q nq nf.
have np : p ≠ Poly.zero by move=> ep; apply: nf; rewrite ep make_num0.
rewrite (inv_make _ _ nq) (mul_make _ _ _ _ np nq) !oneE -of_poly_make.
apply: make_eq; [exact: PolyGcd.mul_neq0|exact: Poly.one_neq0|ring].
Qed.

Lemma div_zero f : div f zero = zero.
Proof.
elim/frac_ind: f => p q nq; rewrite !divE inv_zero -(make_num0 Poly.one).
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
- exact: subE.
- exact: add_opp_r.
Qed.

(* [field] finds a field by its exact carrier, and [frac T] for a variable [T]
   exists only where [T] is bound, so clients declare the field in their own
   sections. *)
Lemma frac_field_theory : field_theory zero one add mul sub opp div inv eq.
Proof.
split.
- exact: frac_ring_theory.
- exact: one_neq0.
- exact: divE.
- exact: mul_inv_l.
Qed.

(** *** Polynomials *)

Lemma of_poly_inj p q : of_poly p = of_poly q → p = q.
Proof. by move=> /(f_equal num); rewrite !num_of_poly. Qed.

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
rewrite !divE -!of_poly_make (inv_make _ _ Poly.one_neq0).
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

Lemma of_poly_opp p : of_poly (- p)%P = opp (of_poly p).
Proof.
by apply: num_den_inj; rewrite ?num_opp ?den_opp ?num_of_poly ?den_of_poly.
Qed.

Lemma opp_opp f : opp (opp f) = f.
Proof. by apply: num_den_inj; rewrite ?num_opp ?den_opp ?Poly.opp_opp. Qed.

Lemma opp_zero : opp zero = zero.
Proof. by rewrite !zeroE -of_poly_opp Poly.opp_zero. Qed.

Lemma mul_zero_l f : mul zero f = zero.
Proof.
elim/frac_ind: f => p q nq.
rewrite {1}zeroE -of_poly_make (mul_make _ _ _ _ Poly.one_neq0 nq).
by rewrite (left_absorb Poly.zero Poly.mul) make_num0.
Qed.

(** *** Variables *)

(** [over vs f]: the variables of [f] are among [vs]. *)
Definition over (vs : list T) f :=
  PolyGcd.over vs (num f) ∧ PolyGcd.over vs (den f).

Lemma over_make vs p q :
  PolyGcd.over vs p → PolyGcd.over vs q → over vs (make p q).
Proof.
move=> op oq; case: (decide (q = Poly.zero)) => [->|nq].
  rewrite make_den0 /over num_zero den_zero.
  split; [exact: PolyGcd.over_zero|exact: PolyGcd.over_one].
have [e1 e2] := make_cancel p q nq; rewrite /over e1 e2.
have [g [Ep Eq]] := Poly.cancel_spec p q.
have ng : g ≠ Poly.zero.
  by move=> eg; apply: nq; rewrite Eq eg (left_absorb Poly.zero Poly.mul).
split.
- by apply: (PolyGcd.over_quot _ g) => //; rewrite -Ep.
- by apply: (PolyGcd.over_quot _ g) => //; rewrite -Eq.
Qed.

Lemma over_of_poly vs p : PolyGcd.over vs p → over vs (of_poly p).
Proof.
by move=> op; rewrite /over num_of_poly den_of_poly; split=> //;
  exact: PolyGcd.over_one.
Qed.

Lemma over_zero vs : over vs zero.
Proof. rewrite zeroE; exact: over_of_poly (PolyGcd.over_zero vs). Qed.

Lemma over_one vs : over vs one.
Proof. rewrite oneE; exact: over_of_poly (PolyGcd.over_one vs). Qed.

Lemma over_opp vs f : over vs f → over vs (opp f).
Proof.
by case=> on od; rewrite /over num_opp den_opp; split=> //;
  exact: PolyGcd.over_opp.
Qed.

Lemma over_add vs f g : over vs f → over vs g → over vs (add f g).
Proof.
move=> [nf df] [ng dg]; rewrite addE; apply: over_make.
- by apply: PolyGcd.over_add; apply: PolyGcd.over_mul.
- exact: PolyGcd.over_mul.
Qed.

Lemma over_mul vs f g : over vs f → over vs g → over vs (mul f g).
Proof.
by move=> [nf df] [ng dg]; rewrite mulE; apply: over_make;
  apply: PolyGcd.over_mul.
Qed.

Lemma over_inv vs f : over vs f → over vs (inv f).
Proof. by move=> [nf df]; rewrite invE; apply: over_make. Qed.

Lemma over_sub vs f g : over vs f → over vs g → over vs (sub f g).
Proof.
by move=> hf hg; rewrite subE; apply: over_add => //; apply: over_opp.
Qed.

Lemma over_div vs f g : over vs f → over vs g → over vs (div f g).
Proof.
by move=> hf hg; rewrite divE; apply: over_mul => //; apply: over_inv.
Qed.

Lemma over_elem vs f m x :
  over vs f → m ∈ Poly.car (num f) ∨ m ∈ Poly.car (den f) → x ∈ m → x ∈ vs.
Proof.
move=> [on od] mf xm; case: (decide (x ∈ vs)) => // nx; exfalso.
have cx : 0 < MSet.count x m by apply/MSet.elem_of_count.
case: mf => /(proj2 (Poly.coeff_neq0_elem _ _)) mf.
- have := PolyGcd.count_le_deg x m (num f) mf.
  by rewrite (on x nx); lia.
- have := PolyGcd.count_le_deg x m (den f) mf.
  by rewrite (od x nx); lia.
Qed.

(** *** Variables and valuations

    [valuation x f] is the [x]-adic valuation of [f]: the multiplicity of [x] in
    the monomial content of the numerator minus that of the denominator.  It is
    additive on nonzero fractions ([valuation_mul]). *)

lock Definition var x : frac := of_poly (Poly.var x).

Lemma varE x : var x = of_poly (Poly.var x).
Proof. by rewrite [var]unlock. Qed.

Lemma var_neq0 x : var x ≠ zero.
Proof. rewrite varE zeroE => /of_poly_inj; exact: PolyGcd.var_neq0. Qed.

Lemma num_eq0 f : num f = Poly.zero → f = zero.
Proof.
move=> e.
have : PolyGcd.dvd (den f) Poly.one.
  apply: num_den_coprime; last exact: PolyGcd.dvd_refl.
  by rewrite e; exact: PolyGcd.dvd_zero.
case/PolyGcd.unit_pm1 => ed.
  by apply: num_den_inj; rewrite ?e ?ed ?num_zero ?den_zero.
have := den_first_neg f.
rewrite ed Poly.first_neg_opp; first exact: Poly.one_neq0.
by rewrite Poly.oneE Poly.first_neg_mono.
Qed.

Lemma num_neq0 f : f ≠ zero → num f ≠ Poly.zero.
Proof. by move=> nf e; apply: nf; apply: num_eq0. Qed.

Lemma mul_neq0 f g : f ≠ zero → g ≠ zero → mul f g ≠ zero.
Proof.
move=> nf ng; rewrite mulE; apply: make_neq0; apply: PolyGcd.mul_neq0;
  by [apply: num_neq0|apply: den_neq0].
Qed.

Lemma make_coprime p q : q ≠ Poly.zero →
  (∀ u, PolyGcd.dvd u p → PolyGcd.dvd u q → PolyGcd.dvd u Poly.one) →
  Poly.first_neg q = false → num (make p q) = p ∧ den (make p q) = q.
Proof.
move=> nq cop fq; have [-> ->] := make_cancel p q nq.
by rewrite PolyGcd.cancel_id.
Qed.

Lemma make_cross p q p' q' : q ≠ Poly.zero → q' ≠ Poly.zero →
  make p q = make p' q' → (p * q' = p' * q)%P.
Proof.
move=> nq nq' e.
have E1 := make_spec p q nq; have E2 := make_spec p' q' nq'.
rewrite -e in E2; move: (make p q) E1 E2 => r E1 E2.
apply: (PolyGcd.mul_cancel_l (den r)); first exact: den_neq0.
transitivity (num r * q * q')%P; first by rewrite E1; ring.
transitivity (num r * q' * q)%P; first ring.
by rewrite E2; ring.
Qed.

Lemma inv_one : inv one = one.
Proof. by rewrite oneE -of_poly_make (inv_make _ _ Poly.one_neq0). Qed.

Lemma inv_inv f : inv (inv f) = f.
Proof.
case: (decide (f = zero)) => [->|nf]; first by rewrite !inv_zero.
by rewrite [inv f]invE inv_make; [exact: num_neq0|exact: make_num_den].
Qed.

lock Definition valuation x f : Z :=
  (Z.of_nat (MSet.count x (PolyGcd.content (num f))) -
   Z.of_nat (MSet.count x (PolyGcd.content (den f))))%Z.

Lemma valuationE x f : valuation x f =
  (Z.of_nat (MSet.count x (PolyGcd.content (num f))) -
   Z.of_nat (MSet.count x (PolyGcd.content (den f))))%Z.
Proof. by rewrite [valuation]unlock. Qed.

Lemma valuation_make x p q : p ≠ Poly.zero → q ≠ Poly.zero →
  valuation x (make p q) =
  (Z.of_nat (MSet.count x (PolyGcd.content p)) -
   Z.of_nat (MSet.count x (PolyGcd.content q)))%Z.
Proof.
move=> np nq.
have nm : num (make p q) ≠ Poly.zero by apply: num_neq0; exact: make_neq0.
have nd := den_neq0 (make p q).
have := f_equal (λ r, MSet.count x (PolyGcd.content r)) (make_spec p q nq).
rewrite /= !PolyGcd.content_mul // !MSet.count_disj_union valuationE; lia.
Qed.

Lemma valuation_of_poly x p :
  valuation x (of_poly p) = Z.of_nat (MSet.count x (PolyGcd.content p)).
Proof.
rewrite !valuationE num_of_poly den_of_poly Poly.oneE PolyGcd.content_mono.
rewrite MSet.count_empty; lia.
Qed.

Lemma valuation_zero x : valuation x zero = 0%Z.
Proof. by rewrite zeroE valuation_of_poly PolyGcd.content_zero MSet.count_empty.
  Qed.

Lemma valuation_one x : valuation x one = 0%Z.
Proof.
by rewrite oneE valuation_of_poly Poly.oneE PolyGcd.content_mono
  MSet.count_empty.
Qed.

Lemma valuation_var x y :
  valuation x (var y) = if bool_decide (x = y) then 1%Z else 0%Z.
Proof.
rewrite varE valuation_of_poly Poly.varE PolyGcd.content_mono
  MSet.count_singleton.
by case: bool_decide.
Qed.

Lemma valuation_mul x f g : f ≠ zero → g ≠ zero →
  valuation x (mul f g) = (valuation x f + valuation x g)%Z.
Proof.
move=> nf ng; have nnf := num_neq0 _ nf; have nng := num_neq0 _ ng.
have ndf := den_neq0 f; have ndg := den_neq0 g.
rewrite !mulE valuation_make; try exact: PolyGcd.mul_neq0.
rewrite !PolyGcd.content_mul // !MSet.count_disj_union !valuationE; lia.
Qed.

Lemma valuation_inv x f : valuation x (inv f) = (- valuation x f)%Z.
Proof.
case: (decide (f = zero)) => [->|nf]; first by rewrite inv_zero valuation_zero.
have nd := den_neq0 f; have nn := num_neq0 _ nf.
rewrite !invE valuation_make // !valuationE; lia.
Qed.

(** ** Variables *)

Definition vars f : list T := Poly.vars (num f) ++ Poly.vars (den f).

Lemma car_num_var x : Poly.car (num (of_poly (Poly.var x))) = {[+ {[+ x +]} +]}.
Proof. by rewrite num_of_poly Poly.varE Poly.car_mono. Qed.

Lemma car_den_of_poly p : Poly.car (den (of_poly p)) = {[+ ∅ +]}.
Proof. by rewrite den_of_poly Poly.oneE Poly.car_mono. Qed.

Lemma vars_over vs f y : over vs f → y ∈ vars f → y ∈ vs.
Proof.
move=> o; rewrite /vars elem_of_app !Poly.elem_of_vars.
by case=> -[m [mr ym]]; apply: (over_elem _ _ m y o ltac:(tauto) ym).
Qed.

Lemma over_vars_sub vs f : (∀ x, x ∈ vars f → x ∈ vs) → over vs f.
Proof.
move=> sub; split; apply: PolyGcd.over_mono (PolyGcd.over_vars _) => x xv;
  apply: sub; apply/elem_of_app; by [left|right].
Qed.

Lemma vars_one y : y ∉ vars one.
Proof.
rewrite /vars num_one den_one elem_of_app.
rewrite !Poly.elem_of_vars Poly.oneE Poly.car_mono.
case=> -[m [/SMS.elem_of_singleton -> e]];
  by case: (MSet.not_elem_of_empty _ e).
Qed.

Lemma vars_zero y : y ∉ vars zero.
Proof.
rewrite /vars num_zero den_zero elem_of_app.
rewrite !Poly.elem_of_vars Poly.car_zero Poly.oneE Poly.car_mono.
case=> -[m [mz ym]].
  by move/SMS.elem_of_count: mz; rewrite SMS.count_empty.
move/SMS.elem_of_singleton: mz ym => -> e.
by case: (MSet.not_elem_of_empty _ e).
Qed.

Lemma vars_mul f g y : y ∈ vars (mul f g) → y ∈ vars f ∨ y ∈ vars g.
Proof.
set vs := vars f ++ vars g.
have o1 : over vs f.
  by apply: over_vars_sub => z zf; apply/elem_of_app; left.
have o2 : over vs g.
  by apply: over_vars_sub => z zg; apply/elem_of_app; right.
by move=> /(vars_over _ _ _ (over_mul _ _ _ o1 o2)) /elem_of_app.
Qed.

(** [all_vars P f]: every variable of [f] satisfies [P]. *)
Definition all_vars (P : T → Prop) f : Prop :=
  ∀ m x, m ∈ Poly.car (num f) ∨ m ∈ Poly.car (den f) → x ∈ m → P x.

Lemma all_vars_iff (P : T → Prop) f :
  all_vars P f ↔ ∀ x, x ∈ vars f → P x.
Proof.
rewrite /all_vars /vars; split.
- move=> h x /elem_of_app
    [/Poly.elem_of_vars [m [mr xm]]|/Poly.elem_of_vars [m [mr xm]]];
    apply: (h m x) => //; by [left|right].
- move=> h m x [mr|mr] xm; apply: h; apply/elem_of_app;
    [left|right]; apply/Poly.elem_of_vars; by exists m.
Qed.

Lemma all_vars_over (P : T → Prop) vs f :
  over vs f → (∀ x, x ∈ vs → P x) → all_vars P f.
Proof. move=> o h m x mr xm; apply: h; exact: over_elem o mr xm. Qed.

Lemma all_vars_op2 (P : T → Prop) (op : frac → frac → frac) f g :
  (∀ vs f g, over vs f → over vs g → over vs (op f g)) →
  all_vars P f → all_vars P g → all_vars P (op f g).
Proof.
move=> hop /all_vars_iff h1 /all_vars_iff h2.
apply: (all_vars_over _ (vars f ++ vars g)).
- by apply: hop; apply: over_vars_sub => x xv; apply/elem_of_app;
    [left|right].
- by move=> x /elem_of_app [/h1|/h2].
Qed.

Lemma all_vars_op1 (P : T → Prop) (op : frac → frac) f :
  (∀ vs f, over vs f → over vs (op f)) → all_vars P f → all_vars P (op f).
Proof.
move=> hop /all_vars_iff h; apply: (all_vars_over _ (vars f)) => //.
by apply: hop; apply: over_vars_sub.
Qed.

Lemma all_vars_add P f g :
  all_vars P f → all_vars P g → all_vars P (add f g).
Proof. exact: all_vars_op2 over_add. Qed.

Lemma all_vars_mul P f g :
  all_vars P f → all_vars P g → all_vars P (mul f g).
Proof. exact: all_vars_op2 over_mul. Qed.

Lemma all_vars_sub P f g :
  all_vars P f → all_vars P g → all_vars P (sub f g).
Proof. exact: all_vars_op2 over_sub. Qed.

Lemma all_vars_div P f g :
  all_vars P f → all_vars P g → all_vars P (div f g).
Proof. exact: all_vars_op2 over_div. Qed.

Lemma all_vars_opp P f : all_vars P f → all_vars P (opp f).
Proof. exact: all_vars_op1 over_opp. Qed.

Lemma all_vars_inv P f : all_vars P f → all_vars P (inv f).
Proof. exact: all_vars_op1 over_inv. Qed.

Lemma all_vars_zero P : all_vars P zero.
Proof.
apply: (all_vars_over _ []); first exact: over_zero.
by move=> x /elem_of_nil.
Qed.

Lemma all_vars_one P : all_vars P one.
Proof.
apply: (all_vars_over _ []); first exact: over_one.
by move=> x /elem_of_nil.
Qed.

Lemma all_vars_impl (P Q : T → Prop) f :
  (∀ x, P x → Q x) → all_vars P f → all_vars Q f.
Proof. by move=> PQ h m x mr xm; apply: PQ; apply: h mr xm. Qed.

Lemma all_vars_var (P : T → Prop) x : P x → all_vars P (var x).
Proof.
move=> Px m y; rewrite varE car_num_var car_den_of_poly.
move=> [/SMS.elem_of_singleton ->|/SMS.elem_of_singleton ->].
- by move=> /MSet.elem_of_singleton ->.
- by move=> ym; case: (MSet.not_elem_of_empty y).
Qed.

Lemma all_vars_of_poly P p :
  (∀ m x, m ∈ Poly.car p → x ∈ m → P x) → all_vars P (of_poly p).
Proof.
move=> h m x; rewrite num_of_poly den_of_poly Poly.oneE Poly.car_mono.
case=> [mp|/SMS.elem_of_singleton ->]; first exact: h.
by move=> e; case: (MSet.not_elem_of_empty _ e).
Qed.

Lemma all_vars_make_mono P f n :
  n ∈ Poly.car (num f) → all_vars P f →
  all_vars P (make (Poly.mono n) (den f)).
Proof.
move=> nf /all_vars_iff af; apply: (all_vars_over _ (vars f)) => //.
apply: over_make.
- apply: PolyGcd.over_intro => m x; rewrite Poly.car_mono.
  move=> /SMS.elem_of_singleton -> xn.
  by apply/elem_of_app; left; apply/Poly.elem_of_vars; exists n.
- apply: PolyGcd.over_mono (PolyGcd.over_vars _) => x xv.
  by apply/elem_of_app; right.
Qed.

Lemma num_car_neq0 f m : m ∈ Poly.car (num f) → f ≠ zero.
Proof.
move=> mf e; move: mf; rewrite e num_zero Poly.car_zero.
by move=> /SMS.elem_of_count; rewrite SMS.count_empty.
Qed.

Lemma den_vars_neq0 f y : y ∈ Poly.vars (den f) → f ≠ zero.
Proof. by move=> yf e; move: yf; rewrite e den_zero => /(Poly.vars_one y). Qed.

Lemma num_car_exists f : f ≠ zero → ∃ m, m ∈ Poly.car (num f).
Proof.
move=> nf; destruct (elements (Poly.car (num f))) as [|m l] eqn:E.
  exfalso; apply: nf; apply: num_eq0; apply: Poly.car_inj.
  by rewrite Poly.car_zero; exact: SMS.elements_empty_inv.
by exists m; apply/SMS.elem_of_elements; rewrite E; left.
Qed.

(** ** Monomial numerators and denominators

    A Laurent monomial ([laurent]) has monomials as numerator and as
    denominator. *)

Definition mono_num f : Prop := ∃ n, num f = Poly.mono n.

Definition mono_den f : Prop := ∃ Q, den f = Poly.mono Q.

Definition laurent f : Prop := ∃ n Q, num f = Poly.mono n ∧ den f = Poly.mono Q.

(** Reducing [P / Q] for a monomial [Q] cancels a monomial [K]. *)
Lemma make_mono_den P Q :
  ∃ Q' K, den (make P (Poly.mono Q)) = Poly.mono Q' ∧
          Q = K ⊎ Q' ∧
          P = Poly.mul (Poly.mono K) (num (make P (Poly.mono Q))).
Proof.
have nq := PolyGcd.mono_neq0 Q.
have [e1 e2] := make_cancel P (Poly.mono Q) nq.
have [g [EP EQ]] := Poly.cancel_spec P (Poly.mono Q).
rewrite -e1 in EP; rewrite -e2 in EQ.
move: (make P (Poly.mono Q)) EP EQ => f EP EQ.
have [Q' [_ hd]] := PolyGcd.dvd_mono (den f) Q
  ltac:(by exists g; rewrite EQ (comm Poly.mul)).
have {}hd : den f = Poly.mono Q'.
  case: hd => // e; have := den_first_neg f.
  by rewrite e Poly.first_neg_opp_mono.
have [K [_ hg]] := PolyGcd.dvd_mono g Q ltac:(by exists (den f)).
exists Q', K; split=> //.
case: hg => eg; rewrite eg in EP EQ.
- rewrite hd Poly.mul_mono in EQ.
  by split=> //; apply: Poly.mono_pm_inj; left.
- exfalso.
  have E : Poly.mono Q = Poly.opp (Poly.mono (K ⊎ Q')).
    by rewrite EQ hd -Poly.mul_mono; ring.
  have EQ' := Poly.mono_pm_inj Q (K ⊎ Q') (or_intror E).
  by apply: (Poly.mono_neq_opp Q); rewrite {1}E EQ'.
Qed.

Lemma mono_den_zero : mono_den zero.
Proof. by exists ∅; rewrite den_zero Poly.oneE. Qed.

Lemma mono_den_one : mono_den one.
Proof. by exists ∅; rewrite den_one Poly.oneE. Qed.

Lemma mono_den_opp f : mono_den f → mono_den (opp f).
Proof. by case=> Q e; exists Q; rewrite den_opp. Qed.

Lemma mono_den_add f g : mono_den f → mono_den g → mono_den (add f g).
Proof.
move=> [Q1 e1] [Q2 e2]; rewrite addE e1 e2 Poly.mul_mono.
set P := (_ + _)%P.
by have [Q' [_ [hd _]]] := make_mono_den P (Q1 ⊎ Q2); exists Q'.
Qed.

Lemma mono_den_mul f g : mono_den f → mono_den g → mono_den (mul f g).
Proof.
move=> [Q1 e1] [Q2 e2]; rewrite mulE e1 e2 Poly.mul_mono.
have [Q' [_ [hd _]]] :=
  make_mono_den (Poly.mul (num f) (num g)) (Q1 ⊎ Q2).
by exists Q'.
Qed.

Lemma mono_num_neq0 f : mono_num f → f ≠ zero.
Proof.
case=> n en e; move: en; rewrite e num_zero => e'.
exact: (PolyGcd.mono_neq0 _ (eq_sym e')).
Qed.

Lemma laurent_mono_num f : laurent f → mono_num f.
Proof. by case=> n [Q [en _]]; exists n. Qed.

Lemma laurent_mono_den f : laurent f → mono_den f.
Proof. by case=> n [Q [_ eQ]]; exists Q. Qed.

Lemma laurent_neq0 f : laurent f → f ≠ zero.
Proof. by move=> /laurent_mono_num; exact: mono_num_neq0. Qed.

Lemma laurent_make_mono n Q : laurent (make (Poly.mono n) (Poly.mono Q)).
Proof.
have [Q' [K [hd [_ hP]]]] := make_mono_den (Poly.mono n) Q.
move: (make _ _) hd hP => f hd hP.
have [n' [_ hn]] := PolyGcd.dvd_mono (num f) n
  ltac:(by exists (Poly.mono K); rewrite hP (comm Poly.mul)).
exists n', Q'; split=> //.
case: hn => // e; exfalso; rewrite e in hP.
have E : Poly.mono n = Poly.opp (Poly.mono (K ⊎ n')).
  by rewrite hP -Poly.mul_mono; ring.
have En := Poly.mono_pm_inj n (K ⊎ n') (or_intror E).
by apply: (Poly.mono_neq_opp n); rewrite {1}E En.
Qed.

Lemma laurent_one : laurent one.
Proof. by exists ∅, ∅; rewrite num_one den_one Poly.oneE. Qed.

Lemma laurent_var x : laurent (var x).
Proof.
exists {[+ x +]}, ∅.
by rewrite varE num_of_poly den_of_poly Poly.varE Poly.oneE.
Qed.

Lemma laurent_mul f g : laurent f → laurent g → laurent (mul f g).
Proof.
move=> [n1 [Q1 [e1 f1]]] [n2 [Q2 [e2 f2]]].
by rewrite mulE e1 f1 e2 f2 !Poly.mul_mono; exact: laurent_make_mono.
Qed.

Lemma laurent_inv f : laurent f → laurent (inv f).
Proof.
move=> [n [Q [e e']]].
rewrite -(make_num_den f) e e' (inv_make _ _ (PolyGcd.mono_neq0 Q)).
exact: laurent_make_mono.
Qed.

Lemma make_mono_canon m D :
  D ≠ Poly.zero → Poly.first_neg D = false →
  ∃ K, K ⊆ m ∧ num (make (Poly.mono m) D) = Poly.mono (m ∖ K) ∧
       (Poly.mono K * den (make (Poly.mono m) D))%P = D.
Proof.
move=> nD fD.
have [e1 e2] := make_cancel (Poly.mono m) D nD.
have [g [EP EQ]] := Poly.cancel_spec (Poly.mono m) D.
rewrite -e1 in EP; rewrite -e2 in EQ.
set f := make (Poly.mono m) D in EP EQ *.
have [h [hm hg]] := PolyGcd.dvd_mono g m ltac:(by exists (num f)).
have nden := den_neq0 f.
have nh : Poly.mono h ≠ Poly.zero := PolyGcd.mono_neq0 h.
case: hg => eg; last first.
  exfalso; move: fD; rewrite EQ eg.
  have nh' : (- Poly.mono h)%P ≠ Poly.zero.
    move=> e; apply: nh.
    by rewrite -(Poly.opp_opp (Poly.mono h)) e Poly.opp_zero.
  rewrite (Poly.first_neg_mul _ _ nh' nden) (den_first_neg f).
  by rewrite Poly.first_neg_opp_mono.
exists h; split=> //; split; last by rewrite -eg.
apply: (PolyGcd.mul_cancel_l (Poly.mono h)) => //.
rewrite -eg -EP eg Poly.mul_mono; congr Poly.mono.
apply: MSet.count_inj => x; rewrite MSet.count_disj_union MSet.count_difference.
have := proj1 (MSet.subseteq_count _ _) hm x; lia.
Qed.

Lemma content_den_missing f a :
  f ≠ zero → a ∈ PolyGcd.content (den f) →
  ∃ m, m ∈ Poly.car (num f) ∧ a ∉ m.
Proof.
move=> nf aD.
case: (decide (Exists (λ m, MSet.count a m = 0)
                      (elements (Poly.car (num f))))).
  case/Exists_exists=> m [mN am]; exists m; split.
    apply/SMS.elem_of_elements; by [|apply/list_elem_of_In].
  exact/MSet.not_elem_of_count.
move=> no; exfalso.
have nN : num f ≠ Poly.zero := num_neq0 _ nf.
have aN : a ∈ PolyGcd.content (num f).
  apply/MSet.singleton_subseteq; apply: PolyGcd.sub_content nN _ => m mN.
  apply/MSet.singleton_subseteq; apply/MSet.elem_of_count.
  case: (decide (MSet.count a m = 0)) => [am|]; last lia.
  case: no; apply/Exists_exists; exists m; split=> //.
  have me : m ∈ elements (Poly.car (num f)) by apply/SMS.elem_of_elements.
  by [|apply/list_elem_of_In].
have dN : PolyGcd.dvd (Poly.var a) (num f).
  exact/PolyGcd.var_dvd_content.
have dD : PolyGcd.dvd (Poly.var a) (den f).
  by apply/PolyGcd.var_dvd_content => //; exact: den_neq0.
have ne := MSet.empty_neq_singleton a.
case: (PolyGcd.unit_pm1 _ (num_den_coprime _ _ dN dD)).
- move=> /(f_equal (Poly.coeff ∅)); rewrite Poly.coeff_var Poly.coeff_one.
  by rewrite bool_decide_eq_false_2 // bool_decide_eq_true_2.
- move=> /(f_equal (Poly.coeff ∅)).
  rewrite Poly.coeff_var Poly.coeff_opp Poly.coeff_one.
  by rewrite bool_decide_eq_false_2 // bool_decide_eq_true_2.
Qed.

Lemma den_make_divisor p q :
  q ≠ Poly.zero → ∃ k, k ≠ Poly.zero ∧ q = (k * den (make p q))%P.
Proof.
move=> nq; have [_ e2] := make_cancel p q nq.
have [k [_ EQ]] := Poly.cancel_spec p q; rewrite -e2 in EQ.
exists k; split=> // ek; apply: nq; rewrite EQ ek.
exact: (left_absorb Poly.zero Poly.mul).
Qed.

Lemma vars_den_add f g y :
  y ∈ Poly.vars (den (add f g)) →
  y ∈ Poly.vars (den f) ∨ y ∈ Poly.vars (den g).
Proof.
rewrite addE => yd.
have nD := PolyGcd.mul_neq0 _ _ (den_neq0 f) (den_neq0 g).
have [h [nh EQ]] := den_make_divisor
  (num f * den g + num g * den f)%P _ nD.
apply: PolyGcd.vars_mul_sub; rewrite EQ; exact: PolyGcd.vars_divisor.
Qed.

Lemma vars_den_mul f g y :
  y ∈ Poly.vars (den (mul f g)) →
  y ∈ Poly.vars (den f) ∨ y ∈ Poly.vars (den g).
Proof.
rewrite mulE => yd.
have nD := PolyGcd.mul_neq0 _ _ (den_neq0 f) (den_neq0 g).
have [h [nh EQ]] := den_make_divisor (num f * num g)%P _ nD.
apply: PolyGcd.vars_mul_sub; rewrite EQ; exact: PolyGcd.vars_divisor.
Qed.

End Frac.

Arguments frac T {_ _ _ _}.

(** ** Renaming variables

    [map f r] renames the variables of [r] with [f], and [map g] undoes it
    when [g] undoes [f] on the variables of [r] ([map_cancel]). *)

Section Map.

Context {T U : Type}.
Context `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Add Ring poly_ring_T : (Poly.poly_ring_theory (T := T)).

lock Definition map (f : T → U) (r : frac T) : frac U :=
  make (Poly.map f (num r)) (Poly.map f (den r)).

Lemma mapE f r : map f r = make (Poly.map f (num r)) (Poly.map f (den r)).
Proof. by rewrite [map]unlock. Qed.

Lemma map_of_poly f p : map f (of_poly p) = of_poly (Poly.map f p).
Proof. by rewrite mapE num_of_poly den_of_poly Poly.map_one of_poly_make. Qed.

Lemma map_zero f : map f zero = zero.
Proof. by rewrite !zeroE map_of_poly Poly.map_zero. Qed.

Lemma map_one f : map f one = one.
Proof. by rewrite !oneE map_of_poly Poly.map_one. Qed.

Lemma map_var f x : map f (var x) = var (f x).
Proof. by rewrite !varE map_of_poly Poly.map_var. Qed.

(** Renaming by an injective function is a field morphism. *)
Section Inj.

Variable f : T → U.
Hypothesis finj : ∀ a b, f a = f b → a = b.

Lemma map_neq0 p : p ≠ Poly.zero → Poly.map f p ≠ Poly.zero.
Proof.
move=> np e; apply: np; apply: (Poly.map_inj f); first exact: finj.
by rewrite e Poly.map_zero.
Qed.

Lemma map_make p q : map f (make p q) = make (Poly.map f p) (Poly.map f q).
Proof.
case: (decide (q = Poly.zero)) => [->|nq].
  by rewrite make_den0 map_zero Poly.map_zero make_den0.
rewrite !mapE; apply: make_eq.
- exact: map_neq0 (den_neq0 _).
- exact: map_neq0.
- by rewrite -!Poly.map_mul make_spec.
Qed.

Lemma map_mul r g : map f (mul r g) = mul (map f r) (map f g).
Proof.
rewrite [mul r g]mulE map_make !Poly.map_mul [map f r]mapE [map f g]mapE.
by rewrite mul_make //; exact: map_neq0 (den_neq0 _).
Qed.

Lemma map_add r g : map f (add r g) = add (map f r) (map f g).
Proof.
rewrite [add r g]addE map_make Poly.map_add !Poly.map_mul.
rewrite [map f r]mapE [map f g]mapE.
by rewrite add_make //; exact: map_neq0 (den_neq0 _).
Qed.

Lemma map_opp r : map f (opp r) = opp (map f r).
Proof.
rewrite [map f (opp r)]mapE num_opp den_opp Poly.map_opp [map f r]mapE.
rewrite opp_make //; exact: map_neq0 (den_neq0 _).
Qed.

Lemma map_inv r : map f (inv r) = inv (map f r).
Proof.
case: (decide (r = zero)) => [->|nr].
  by rewrite inv_zero map_zero inv_zero.
rewrite [inv r]invE map_make [map f r]mapE inv_make //.
exact: map_neq0 (den_neq0 _).
Qed.

Lemma map_sub r g : map f (sub r g) = sub (map f r) (map f g).
Proof. by rewrite !subE map_add map_opp. Qed.

Lemma map_div r g : map f (div r g) = div (map f r) (map f g).
Proof. by rewrite !divE map_mul map_inv. Qed.

Lemma map_inj r g : map f r = map f g → r = g.
Proof.
move=> e; apply/frac_eq; apply: (Poly.map_inj f) => //.
rewrite !Poly.map_mul; move: e; rewrite !mapE.
by apply: make_cross; exact: map_neq0 (den_neq0 _).
Qed.

End Inj.

End Map.

Section MapCancel.

Context {T U : Type}.
Context `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Add Ring poly_ring_T' : (Poly.poly_ring_theory (T := T)).

Lemma map_cancel (f : T → U) (g : U → T) r :
  (∀ m x, m ∈ Poly.car (num r) ∨ m ∈ Poly.car (den r) → x ∈ m →
     g (f x) = x) →
  map g (map f r) = r.
Proof.
move=> gf.
have Q p : p = num r ∨ p = den r → Poly.map g (Poly.map f p) = p.
  move=> ep; rewrite Poly.map_map; apply: Poly.map_id_ext => m x mp xm.
  by apply: (gf m x) => //; case: ep => ?; subst p; [left|right].
have nq : Poly.map f (den r) ≠ Poly.zero.
  move=> e; apply: (den_neq0 r).
  by rewrite -(Q (den r) (or_intror eq_refl)) e Poly.map_zero.
set p := Poly.map f (num r); set q := Poly.map f (den r).
have [c [Ep Eq]] := Poly.cancel_spec p q.
have [e1 e2] := make_cancel p q nq.
rewrite !mapE -/p -/q e1 e2 -[RHS]make_num_den.
move: (Poly.cancel p q) Ep Eq => [p' q'] /= Ep Eq.
have Qp : Poly.map g p = num r by apply: Q; left.
have Qq : Poly.map g q = den r by apply: Q; right.
have nq' : Poly.map g q' ≠ Poly.zero.
  move=> e0; apply: (den_neq0 r).
  by rewrite -Qq Eq Poly.map_mul e0 (right_absorb Poly.zero Poly.mul).
apply: make_eq => //; first exact: den_neq0.
by rewrite -Qp -Qq Ep Eq !Poly.map_mul; ring.
Qed.

End MapCancel.

Lemma map_id {T : Type} `{EqDecision T, Lexico T}
    `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)} (r : frac T) :
  map (λ x, x) r = r.
Proof.
rewrite !mapE !Poly.map_id_ext //; exact: make_num_den.
Qed.

(** ** Substitution

    [eval φ p] substitutes the fraction [φ x] for every variable [x] of the
    polynomial [p]; it is a ring morphism ([eval_add], [eval_mul]).
    [bind φ r] substitutes in a fraction by dividing the evaluated numerator
    by the evaluated denominator, so that substituting variables for
    variables renames them ([bind_var_map]). *)

Section Eval.

Context {T U : Type}.
Context `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Add Ring frac_ring_U : (frac_ring_theory (T := U)).
Add Field frac_field_U : (frac_field_theory (T := U)).

Implicit Types (φ : T → frac U) (p q : Poly.poly T) (m n : MSet.mset T).

lock Definition fsum (l : list (frac U)) : frac U := foldr add zero l.
lock Definition fprod (l : list (frac U)) : frac U := foldr mul one l.

(** The value of a monomial and the sum of the values of a multiset of
    monomials. *)
lock Definition mono_val φ m : frac U := fprod (φ <$> elements m).
lock Definition msum φ (X : MSet.mset (MSet.mset T)) : frac U :=
  fsum (mono_val φ <$> elements X).

lock Definition eval φ p : frac U :=
  sub (msum φ (SMS.pos (Poly.car p))) (msum φ (SMS.neg (Poly.car p))).

lock Definition bind φ (r : frac T) : frac U :=
  div (eval φ (num r)) (eval φ (den r)).

Lemma fsum_nil : fsum [] = zero.
Proof. by rewrite [fsum]unlock. Qed.

Lemma fsum_cons f l : fsum (f :: l) = add f (fsum l).
Proof. by rewrite [fsum]unlock. Qed.

Lemma fprod_nil : fprod [] = one.
Proof. by rewrite [fprod]unlock. Qed.

Lemma fprod_cons f l : fprod (f :: l) = mul f (fprod l).
Proof. by rewrite [fprod]unlock. Qed.

Lemma mono_valE φ m : mono_val φ m = fprod (φ <$> elements m).
Proof. by rewrite [mono_val]unlock. Qed.

Lemma msumE φ X : msum φ X = fsum (mono_val φ <$> elements X).
Proof. by rewrite [msum]unlock. Qed.

Lemma evalE φ p :
  eval φ p =
  sub (msum φ (SMS.pos (Poly.car p))) (msum φ (SMS.neg (Poly.car p))).
Proof. by rewrite [eval]unlock. Qed.

Lemma bindE φ r : bind φ r = div (eval φ (num r)) (eval φ (den r)).
Proof. by rewrite [bind]unlock. Qed.

Lemma fsum_app l1 l2 : fsum (l1 ++ l2) = add (fsum l1) (fsum l2).
Proof.
elim: l1 => [|f l IH] /=; first by rewrite fsum_nil; ring.
by rewrite !fsum_cons IH; ring.
Qed.

Lemma fsum_perm l1 l2 : l1 ≡ₚ l2 → fsum l1 = fsum l2.
Proof.
elim=> [//|f l1' l2' _ IH|f g l|l1' l2' l3 _ IH1 _ IH2].
- by rewrite !fsum_cons IH.
- by rewrite !fsum_cons; ring.
- by rewrite IH1 IH2.
Qed.

Lemma fsum_mul_l c (l : list (frac U)) :
  fsum ((λ f, mul c f) <$> l) = mul c (fsum l).
Proof.
elim: l => [|f l IH] /=; first by rewrite fsum_nil; ring.
by rewrite !fsum_cons IH; ring.
Qed.

Lemma fprod_app l1 l2 : fprod (l1 ++ l2) = mul (fprod l1) (fprod l2).
Proof.
elim: l1 => [|f l IH] /=; first by rewrite fprod_nil; ring.
by rewrite !fprod_cons IH; ring.
Qed.

Lemma fprod_perm l1 l2 : l1 ≡ₚ l2 → fprod l1 = fprod l2.
Proof.
elim=> [//|f l1' l2' _ IH|f g l|l1' l2' l3 _ IH1 _ IH2].
- by rewrite !fprod_cons IH.
- by rewrite !fprod_cons; ring.
- by rewrite IH1 IH2.
Qed.

Lemma mono_val_empty φ : mono_val φ ∅ = one.
Proof. by rewrite !mono_valE MSet.elements_empty fprod_nil. Qed.

Lemma mono_val_singleton φ x : mono_val φ {[+ x +]} = φ x.
Proof.
rewrite !mono_valE MSet.elements_singleton /= fprod_cons fprod_nil; ring.
Qed.

Lemma mono_val_disj_union φ m n :
  mono_val φ (m ⊎ n) = mul (mono_val φ m) (mono_val φ n).
Proof.
rewrite !mono_valE -fprod_app -fmap_app; apply: fprod_perm.
apply: fmap_Permutation; exact: MSet.elements_disj_union.
Qed.

Lemma msum_empty φ : msum φ ∅ = zero.
Proof. by rewrite !msumE MSet.elements_empty fsum_nil. Qed.

Lemma msum_singleton φ m : msum φ {[+ m +]} = mono_val φ m.
Proof.
rewrite !msumE MSet.elements_singleton /= fsum_cons fsum_nil; ring.
Qed.

Lemma msum_disj_union φ X Y : msum φ (X ⊎ Y) = add (msum φ X) (msum φ Y).
Proof.
rewrite !msumE -fsum_app -fmap_app; apply: fsum_perm.
apply: fmap_Permutation; exact: MSet.elements_disj_union.
Qed.

Lemma msum_mul φ m X :
  msum φ (MSet.map (λ n, m ⊎ n) X) = mul (mono_val φ m) (msum φ X).
Proof.
rewrite !msumE -fsum_mul_l -list_fmap_compose; apply: fsum_perm.
transitivity (mono_val φ <$> ((λ n, m ⊎ n) <$> elements X)).
  apply: fmap_Permutation; exact: MSet.elements_map_perm.
rewrite -list_fmap_compose; apply: Permutation_refl'.
apply: list_fmap_ext => i n _ /=; exact: mono_val_disj_union.
Qed.

Lemma eval_make φ X Y :
  eval φ (Poly.mk (SMS.make X Y)) = sub (msum φ X) (msum φ Y).
Proof.
rewrite !evalE SMS.pos_make SMS.neg_make.
have EX : X = (X ∖ Y) ⊎ (X ∖ (X ∖ Y)).
  apply: MSet.count_inj => m.
  rewrite MSet.count_disj_union !MSet.count_difference; lia.
have EY : Y = (Y ∖ X) ⊎ (X ∖ (X ∖ Y)).
  apply: MSet.count_inj => m.
  rewrite MSet.count_disj_union !MSet.count_difference; lia.
rewrite [in RHS]EX [in msum φ Y]EY !msum_disj_union; ring.
Qed.

Lemma eval_add φ p q : eval φ (Poly.add p q) = add (eval φ p) (eval φ q).
Proof.
have -> : Poly.add p q =
    Poly.mk (SMS.make (SMS.pos (Poly.car p) ⊎ SMS.pos (Poly.car q))
                      (SMS.neg (Poly.car p) ⊎ SMS.neg (Poly.car q))).
  by apply: Poly.car_inj; rewrite Poly.car_add.
rewrite eval_make !msum_disj_union !evalE; ring.
Qed.

Lemma eval_opp φ p : eval φ (Poly.opp p) = opp (eval φ p).
Proof. rewrite !evalE Poly.car_opp SMS.pos_inv SMS.neg_inv; ring. Qed.

Lemma eval_zero φ : eval φ Poly.zero = zero.
Proof.
rewrite -(Poly.add_opp_r Poly.zero) eval_add eval_opp; ring.
Qed.

Lemma eval_mono φ m : eval φ (Poly.mono m) = mono_val φ m.
Proof.
have -> : Poly.mono m = Poly.mk (SMS.make {[+ m +]} ∅).
  by apply: Poly.car_inj; rewrite Poly.car_mono.
rewrite eval_make msum_singleton msum_empty; ring.
Qed.

Lemma eval_one φ : eval φ Poly.one = one.
Proof. by rewrite Poly.oneE eval_mono mono_val_empty. Qed.

Lemma eval_var φ x : eval φ (Poly.var x) = φ x.
Proof. by rewrite Poly.varE eval_mono mono_val_singleton. Qed.

Lemma eval_sub φ p q : eval φ (Poly.sub p q) = sub (eval φ p) (eval φ q).
Proof. by rewrite Poly.subE eval_add eval_opp subE. Qed.

Lemma eval_mono_mul φ m q :
  eval φ (Poly.mul (Poly.mono m) q) = mul (mono_val φ m) (eval φ q).
Proof.
have -> : Poly.mul (Poly.mono m) q =
    Poly.mk (SMS.make (MSet.map (λ n, m ⊎ n) (SMS.pos (Poly.car q)))
                      (MSet.map (λ n, m ⊎ n) (SMS.neg (Poly.car q)))).
  by apply: Poly.car_inj; rewrite Poly.car_mul_mono SMS.map_pos_neg.
rewrite eval_make.
rewrite !msum_mul !evalE; ring.
Qed.

Lemma eval_mul φ p q : eval φ (Poly.mul p q) = mul (eval φ p) (eval φ q).
Proof.
elim/(Poly.poly_ind (T := T)): p => [|m p IH|m p IH].
- rewrite (left_absorb Poly.zero Poly.mul) eval_zero.
  by move: (eval φ q) => b; ring.
- rewrite Poly.mul_add_l eval_add eval_mono_mul IH eval_add eval_mono.
  by move: (mono_val φ m) (eval φ p) (eval φ q) => a b c; ring.
- rewrite Poly.mul_add_l Poly.mul_opp_l !eval_add !eval_opp eval_mono_mul IH.
  rewrite eval_mono.
  by move: (mono_val φ m) (eval φ p) (eval φ q) => a b c; ring.
Qed.

Lemma mono_val_var (f : T → U) m :
  mono_val (λ x, of_poly (Poly.var (f x))) m =
  of_poly (Poly.mono (MSet.map f m)).
Proof.
elim/(MSet.mset_ind (T := T)): m => [|x m IH].
  by rewrite mono_val_empty MSet.map_empty oneE Poly.oneE.
rewrite mono_val_disj_union mono_val_singleton IH -of_poly_mul.
by rewrite MSet.map_disj_union MSet.map_singleton -Poly.mul_mono Poly.varE.
Qed.

Lemma eval_var_map (f : T → U) p :
  eval (λ x, of_poly (Poly.var (f x))) p = of_poly (Poly.map f p).
Proof.
elim/(Poly.poly_ind (T := T)): p => [|m p IH|m p IH].
- by rewrite eval_zero Poly.map_zero zeroE.
- rewrite eval_add Poly.map_add of_poly_add IH eval_mono Poly.map_mono.
  by rewrite mono_val_var.
- rewrite eval_add eval_opp Poly.map_add Poly.map_opp !of_poly_add IH.
  by rewrite eval_mono Poly.map_mono mono_val_var of_poly_opp.
Qed.

Lemma bind_var_map (f : T → U) r :
  bind (λ x, of_poly (Poly.var (f x))) r = map f r.
Proof. by rewrite !bindE !eval_var_map !mapE make_div. Qed.

Lemma bind_of_poly φ p : bind φ (of_poly p) = eval φ p.
Proof.
rewrite !bindE num_of_poly den_of_poly.
by rewrite eval_one; move: (eval φ p) => a; field; exact: one_neq0.
Qed.

Lemma eval_ext φ ψ p :
  (∀ m x, m ∈ Poly.car p → x ∈ m → φ x = ψ x) → eval φ p = eval ψ p.
Proof.
move=> h; rewrite !evalE !msumE.
have M s : s = SMS.pos (Poly.car p) ∨ s = SMS.neg (Poly.car p) →
    fsum (mono_val φ <$> elements s) = fsum (mono_val ψ <$> elements s).
  move=> es; congr fsum; apply: list_fmap_ext => i m hm.
  have /MSet.elem_of_elements ms := list_elem_of_lookup_2 _ _ _ hm.
  rewrite !mono_valE; congr fprod.
  apply: list_fmap_ext => j x hx; apply: (h m).
  - by apply/SMS.elem_of_pos_neg; case: es => ?; subst s; [left|right].
  - exact/MSet.elem_of_elements/(list_elem_of_lookup_2 _ _ _ hx).
by rewrite (M _ (or_introl eq_refl)) (M _ (or_intror eq_refl)).
Qed.

Lemma bind_ext φ ψ r :
  (∀ m x, m ∈ Poly.car (num r) ∨ m ∈ Poly.car (den r) → x ∈ m →
     φ x = ψ x) →
  bind φ r = bind ψ r.
Proof.
move=> h; rewrite !bindE.
rewrite (eval_ext φ ψ (num r)); first by move=> m x mr; apply: h; left.
rewrite (eval_ext φ ψ (den r)) //; by move=> m x mr; apply: h; right.
Qed.

(** *** Variables *)

Lemma over_fsum vs l : Forall (over vs) l → over vs (fsum l).
Proof.
elim=> [|f l' hf _ IH]; rewrite ?fsum_nil ?fsum_cons;
  [exact: over_zero|exact: over_add].
Qed.

Lemma over_fprod vs l : Forall (over vs) l → over vs (fprod l).
Proof.
elim=> [|f l' hf _ IH]; rewrite ?fprod_nil ?fprod_cons;
  [exact: over_one|exact: over_mul].
Qed.

Lemma over_eval vs φ p :
  (∀ m x, m ∈ Poly.car p → x ∈ m → over vs (φ x)) → over vs (eval φ p).
Proof.
move=> h; have hm s : s = SMS.pos (Poly.car p) ∨ s = SMS.neg (Poly.car p) →
    over vs (msum φ s).
  move=> es; rewrite msumE; apply: over_fsum.
  apply/Forall_fmap/list.Forall_forall.
  move=> m /MSet.elem_of_elements m_s /=; rewrite mono_valE; apply: over_fprod.
  apply/Forall_fmap/list.Forall_forall => x /MSet.elem_of_elements x_m /=.
  apply: (h m x) => //; apply/SMS.elem_of_pos_neg.
  by case: es => ?; subst s; [left|right].
rewrite evalE; apply: over_sub; apply: hm; by [left|right].
Qed.

Lemma over_bind vs φ r :
  (∀ m x, m ∈ Poly.car (num r) ∨ m ∈ Poly.car (den r) → x ∈ m →
     over vs (φ x)) →
  over vs (bind φ r).
Proof.
move=> h; rewrite bindE; apply: over_div; apply: over_eval => m x mr;
  apply: h; by [left|right].
Qed.

Lemma num_make_mono m (q : Poly.poly T) : q ≠ Poly.zero →
  ∃ n, n ⊆ m ∧ (num (make (Poly.mono m) q) = Poly.mono n ∨
                num (make (Poly.mono m) q) = (- Poly.mono n)%P).
Proof.
move=> nq; have [e1 _] := make_cancel (Poly.mono m) q nq; rewrite e1.
have [g [Ep _]] := Poly.cancel_spec (Poly.mono m) q.
apply: PolyGcd.dvd_mono; exists g; rewrite {1}Ep.
exact: (comm Poly.mul).
Qed.

(** Since [Poly.first_neg] is multiplicative, reducing [m / q] for a monomial
    [m] and a denominator [q] in canonical form leaves a monomial numerator. *)
Lemma num_make_mono_pos m (q : Poly.poly T) :
  q ≠ Poly.zero → Poly.first_neg q = false →
  ∃ n, num (make (Poly.mono m) q) = Poly.mono n.
Proof.
move=> nq fq.
have [n [_ [e|e]]] := num_make_mono m q nq; first by exists n.
exfalso.
have E := make_spec (Poly.mono m) q nq; rewrite e in E.
have nn : (- Poly.mono n)%P ≠ Poly.zero.
  move=> h; apply: (PolyGcd.mono_neq0 n).
  by rewrite -(Poly.opp_opp (Poly.mono n)) h Poly.opp_zero.
have := f_equal Poly.first_neg E.
rewrite (Poly.first_neg_mul _ _ nn nq).
rewrite (Poly.first_neg_mul _ _ (PolyGcd.mono_neq0 m) (den_neq0 _)).
by rewrite Poly.first_neg_opp_mono Poly.first_neg_mono den_first_neg fq.
Qed.

Lemma num_mul_mono r1 r2 n1 n2 :
  num r1 = Poly.mono n1 → num r2 = Poly.mono n2 →
  ∃ n, num (mul r1 r2) = Poly.mono n.
Proof.
move=> e1 e2; rewrite mulE e1 e2 Poly.mul_mono.
apply: num_make_mono_pos.
  by apply: PolyGcd.mul_neq0; exact: den_neq0.
by rewrite Poly.first_neg_mul ?den_first_neg //; exact: den_neq0.
Qed.

Lemma mono_num_mul (f g : frac T) :
  mono_num f → mono_num g → mono_num (mul f g).
Proof. by move=> [n1 e1] [n2 e2]; exact: (num_mul_mono _ _ _ _ e1 e2). Qed.

Lemma all_vars_fsum (P : U → Prop) l :
  Forall (all_vars P) l → all_vars P (fsum l).
Proof.
elim=> [|f l' hf _ IH]; rewrite ?fsum_nil ?fsum_cons;
  [exact: all_vars_zero|exact: all_vars_add].
Qed.

Lemma all_vars_fprod (P : U → Prop) l :
  Forall (all_vars P) l → all_vars P (fprod l).
Proof.
elim=> [|f l' hf _ IH]; rewrite ?fprod_nil ?fprod_cons;
  [exact: all_vars_one|exact: all_vars_mul].
Qed.

Lemma all_vars_bind (P : U → Prop) φ r :
  (∀ x, x ∈ vars r → all_vars P (φ x)) → all_vars P (bind φ r).
Proof.
move=> h; set vs := vars r ≫= (λ x, vars (φ x)).
apply: (all_vars_over _ vs).
- apply: over_bind => m x mr xm.
  have xr : x ∈ vars r.
    rewrite /vars elem_of_app; case: mr => mr; [left|right];
      apply/Poly.elem_of_vars; by exists m.
  apply: over_vars_sub => y yv.
  by apply/list_elem_of_bind; exists x.
- move=> y /list_elem_of_bind [x [yx xr]].
  exact: (proj1 (all_vars_iff _ _) (h x xr)).
Qed.

Lemma mono_den_fsum (l : list (frac U)) :
  Forall mono_den l → mono_den (fsum l).
Proof.
elim: l => [_|f l IH /Forall_cons_iff [hf hl]].
  by rewrite fsum_nil; exact: mono_den_zero.
by rewrite fsum_cons; exact: mono_den_add hf (IH hl).
Qed.

End Eval.

(** ** Signed sums

    [ssum g s] adds up [g x] over a signed multiset [s], subtracting the
    negative elements; it does not depend on how [s] is written
    ([ssum_make]). *)

Section SSum.

Context {A U : Type}.
Context `{EqDecision A, Lexico A}
  `{!StrictOrder (@lexico A _), !TrichotomyT (@lexico A _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Add Ring frac_ring_U' : (frac_ring_theory (T := U)).

Implicit Types (g : A → frac U) (s : SMS.sms A).

lock Definition ssum g s : frac U :=
  sub (fsum (g <$> elements (SMS.pos s))) (fsum (g <$> elements (SMS.neg s))).

Lemma ssumE g s : ssum g s =
  sub (fsum (g <$> elements (SMS.pos s))) (fsum (g <$> elements (SMS.neg s))).
Proof. by rewrite [ssum]unlock. Qed.

Lemma fsum_disj_union g (X Y : MSet.mset A) :
  fsum (g <$> elements (X ⊎ Y)) =
  add (fsum (g <$> elements X)) (fsum (g <$> elements Y)).
Proof.
rewrite -fsum_app -fmap_app; apply: fsum_perm.
apply: fmap_Permutation; exact: MSet.elements_disj_union.
Qed.

Lemma ssum_make g X Y :
  ssum g (SMS.make X Y) =
  sub (fsum (g <$> elements X)) (fsum (g <$> elements Y)).
Proof.
rewrite !ssumE SMS.pos_make SMS.neg_make.
have EX : X = (X ∖ Y) ⊎ (X ∖ (X ∖ Y)).
  apply: MSet.count_inj => x.
  rewrite MSet.count_disj_union !MSet.count_difference; lia.
have EY : Y = (Y ∖ X) ⊎ (X ∖ (X ∖ Y)).
  apply: MSet.count_inj => x.
  rewrite MSet.count_disj_union !MSet.count_difference; lia.
rewrite [in RHS]EX [in fsum (g <$> elements Y)]EY !fsum_disj_union.
by move: (fsum _) (fsum _) (fsum _) => a b c; ring.
Qed.

Lemma ssum_empty g : ssum g ∅ = zero.
Proof.
rewrite (_ : ∅ = SMS.make ∅ ∅) // ssum_make MSet.elements_empty fsum_nil.
ring.
Qed.

Lemma ssum_singleton g x : ssum g {[+ x +]} = g x.
Proof.
rewrite (SMS.singleton_make x) ssum_make MSet.elements_singleton.
rewrite MSet.elements_empty /= fsum_cons !fsum_nil.
by move: (g x) => a; ring.
Qed.

Lemma ssum_disj_union g s1 s2 :
  ssum g (s1 ⊎ s2) = add (ssum g s1) (ssum g s2).
Proof.
change (s1 ⊎ s2) with
  (SMS.make (SMS.pos s1 ⊎ SMS.pos s2) (SMS.neg s1 ⊎ SMS.neg s2)).
rewrite ssum_make !fsum_disj_union !ssumE.
by move: (fsum _) (fsum _) (fsum _) (fsum _) => a b c d; ring.
Qed.

Lemma ssum_inv g s : ssum g (SMS.inv s) = opp (ssum g s).
Proof.
rewrite !ssumE SMS.pos_inv SMS.neg_inv.
by move: (fsum _) (fsum _) => a b; ring.
Qed.

Lemma ssum_ext g h s : (∀ x, x ∈ s → g x = h x) → ssum g s = ssum h s.
Proof.
move=> e; rewrite !ssumE.
have M (X : MSet.mset A) : (∀ x, x ∈ X → g x = h x) →
    fsum (g <$> elements X) = fsum (h <$> elements X).
  move=> eX; congr fsum; apply: list_fmap_ext => i x hx.
  by apply: eX; apply/MSet.elem_of_elements/(list_elem_of_lookup_2 _ _ _ hx).
rewrite (M (SMS.pos s)); first by move=> x xp; apply: e; apply: SMS.elem_of_pos.
by rewrite (M (SMS.neg s)) // => x xn; apply: e; apply: SMS.elem_of_neg.
Qed.

Lemma ssum_mul_r g c s :
  ssum (λ x, mul (g x) c) s = mul (ssum g s) c.
Proof.
elim/(SMS.sms_ind (T := A)): s => [|x s IH|x s IH].
- by rewrite !ssum_empty; ring.
- rewrite !ssum_disj_union !ssum_singleton IH.
  by move: (g x) (ssum g s) => a b; ring.
- rewrite !ssum_disj_union !ssum_inv !ssum_singleton IH.
  by move: (g x) (ssum g s) => a b; ring.
Qed.

Lemma vars_ssum g s y : y ∈ vars (ssum g s) → ∃ u, u ∈ s ∧ y ∈ vars (g u).
Proof.
set vs := elements s ≫= (λ u, vars (g u)).
have F (X : MSet.mset A) : (∀ u, u ∈ X → u ∈ s) →
    over vs (fsum (g <$> elements X)).
  move=> hX; apply: over_fsum; apply/Forall_fmap/list.Forall_forall.
  move=> u /MSet.elem_of_elements /hX us.
  apply: over_vars_sub => z zu; apply/list_elem_of_bind.
  by exists u; split=> //; apply/SMS.elem_of_elements.
have o : over vs (ssum g s).
  rewrite ssumE; apply: over_sub; apply: F => u.
  - exact: SMS.elem_of_pos.
  - exact: SMS.elem_of_neg.
move=> /(vars_over _ _ _ o) /list_elem_of_bind.
by case=> u [yu /SMS.elem_of_elements us]; exists u.
Qed.

Lemma ssum_zero_ext g s : (∀ u, u ∈ s → g u = zero) → ssum g s = zero.
Proof.
move=> h; rewrite (ssum_ext _ (λ _, zero) _ h) ssumE.
have Z (l : list A) : fsum ((λ _ : A, zero) <$> l) = (zero : frac U).
  elim: l => [|u l IH]; first by rewrite fsum_nil.
  by rewrite fmap_cons fsum_cons IH (left_id zero add).
by rewrite !Z subE opp_zero (left_id zero add).
Qed.

Lemma ssum_nonzero g s : ssum g s ≠ zero → ∃ u, u ∈ s ∧ g u ≠ zero.
Proof.
move=> nz.
case: (decide (Exists (λ u, g u ≠ zero) (elements s))).
  case/Exists_exists=> u [us gu]; exists u.
  by split=> //; apply/SMS.elem_of_elements; apply/list_elem_of_In.
move=> no; exfalso; apply: nz; apply: ssum_zero_ext => u us.
case: (decide (g u = zero)) => // gu; case: no; apply/Exists_exists.
by exists u; split=> //; apply/list_elem_of_In/SMS.elem_of_elements.
Qed.

End SSum.

Lemma ssum_bind {A B U : Type}
    `{EqDecision A, Lexico A, !StrictOrder (@lexico A _),
      !TrichotomyT (@lexico A _)}
    `{EqDecision B, Lexico B, !StrictOrder (@lexico B _),
      !TrichotomyT (@lexico B _)}
    `{EqDecision U, Lexico U, !StrictOrder (@lexico U _),
      !TrichotomyT (@lexico U _)}
    (g : B → frac U) (f : A → SMS.sms B) (s : SMS.sms A) :
  ssum g (SMS.bind f s) = ssum (λ x, ssum g (f x)) s.
Proof.
elim/(SMS.sms_ind (T := A)): s => [|x s IH|x s IH].
- by rewrite SMS.bind_empty !ssum_empty.
- by rewrite SMS.bind_disj_union SMS.bind_singleton !ssum_disj_union
    ssum_singleton IH.
- by rewrite SMS.bind_disj_union SMS.bind_inv SMS.bind_singleton
    !ssum_disj_union !ssum_inv ssum_singleton IH.
Qed.

(** ** Field facts *)

Section FracField.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Add Ring frac_ring_F : (frac_ring_theory (T := T)).
Add Field frac_field_F : (frac_field_theory (T := T)).

Implicit Types (f g h : frac T).

Lemma mul_zero_r f : mul f zero = zero.
Proof. by rewrite (comm mul) mul_zero_l. Qed.

Lemma inv_mul f g : inv (mul f g) = mul (inv f) (inv g).
Proof.
case: (decide (f = zero)) => [->|nf].
  by rewrite mul_zero_l inv_zero mul_zero_l.
case: (decide (g = zero)) => [->|ng].
  by rewrite mul_zero_r inv_zero ?mul_zero_r.
by field; split.
Qed.

Lemma div_cancel_r f g h : h ≠ zero → div (mul f h) (mul g h) = div f g.
Proof.
move=> nh; case: (decide (g = zero)) => [->|ng].
  by rewrite mul_zero_l !div_zero.
by field; split.
Qed.

Lemma fprod_neq0 (l : list (frac T)) :
  Forall (λ f, f ≠ zero) l → fprod l ≠ zero.
Proof.
elim=> [|f l' nf _ IH]; rewrite ?fprod_nil ?fprod_cons;
  [exact: one_neq0|exact: mul_neq0].
Qed.

Lemma mul_eq0_l f g : mul f g = zero → g ≠ zero → f = zero.
Proof.
move=> e ng; case: (decide (f = zero)) => // nf.
by case: (mul_neq0 _ _ nf ng).
Qed.

Lemma mul_inj_r f f' g : g ≠ zero → mul f g = mul f' g → f = f'.
Proof.
move=> ng e.
have e0 : mul (sub f f') g = zero.
  transitivity (sub (mul f g) (mul f' g)); first ring.
  by rewrite e; ring.
have e1 := mul_eq0_l _ _ e0 ng.
transitivity (add (sub f f') f'); first ring.
by rewrite e1; ring.
Qed.

End FracField.

(** ** Signed products

    [sprod g s] multiplies [g x] over a signed multiset [s], dividing by the
    negative elements.  Since [s ⊎ s'] cancels opposite elements, it is
    multiplicative only away from zero ([sprod_disj_union]). *)

Section SProd.

Context {A U : Type}.
Context `{EqDecision A, Lexico A}
  `{!StrictOrder (@lexico A _), !TrichotomyT (@lexico A _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Add Ring frac_ring_P : (frac_ring_theory (T := U)).
Add Field frac_field_P : (frac_field_theory (T := U)).

Implicit Types (g : A → frac U) (s : SMS.sms A).

lock Definition sprod g s : frac U :=
  div (fprod (g <$> elements (SMS.pos s))) (fprod (g <$> elements (SMS.neg s))).

Lemma sprodE g s : sprod g s =
  div (fprod (g <$> elements (SMS.pos s))) (fprod (g <$> elements (SMS.neg s))).
Proof. by rewrite [sprod]unlock. Qed.

Lemma fprod_disj_union g (X Y : MSet.mset A) :
  fprod (g <$> elements (X ⊎ Y)) =
  mul (fprod (g <$> elements X)) (fprod (g <$> elements Y)).
Proof.
rewrite -fprod_app -fmap_app; apply: fprod_perm.
apply: fmap_Permutation; exact: MSet.elements_disj_union.
Qed.

Lemma sprod_empty g : sprod g ∅ = one.
Proof.
rewrite sprodE (_ : ∅ = SMS.make ∅ ∅) // SMS.pos_make SMS.neg_make.
rewrite (_ : (∅ : MSet.mset A) ∖ ∅ = ∅); first by MSet.mset_solver.
by rewrite MSet.elements_empty fprod_nil; field; exact: one_neq0.
Qed.

Lemma sprod_pair g x y : sprod g {[+ x; y +]} = mul (g x) (g y).
Proof.
have E : ({[+ x; y +]} : SMS.sms A) = SMS.make ({[+ x +]} ⊎ {[+ y +]}) ∅.
  apply: SMS.count_inj => z.
  rewrite SMS.count_disj_union !SMS.count_singleton SMS.count_make.
  rewrite MSet.count_disj_union !MSet.count_singleton MSet.count_empty.
  by case: bool_decide; case: bool_decide => /=; lia.
rewrite E sprodE SMS.pos_make_empty_r SMS.neg_make_empty_r.
rewrite fprod_disj_union MSet.elements_empty !MSet.elements_singleton /=.
by rewrite !fprod_cons !fprod_nil divE inv_one; ring.
Qed.

Lemma sprod_singleton g x : sprod g {[+ x +]} = g x.
Proof.
rewrite !sprodE SMS.pos_singleton SMS.neg_singleton MSet.elements_singleton.
rewrite MSet.elements_empty /= fprod_cons !fprod_nil.
by move: (g x) => a; field; exact: one_neq0.
Qed.

Lemma sprod_inv g s : sprod g (SMS.inv s) = inv (sprod g s).
Proof.
rewrite !sprodE SMS.pos_inv SMS.neg_inv !divE inv_mul inv_inv.
by move: (fprod _) (fprod _) => a b; ring.
Qed.

Lemma sprod_ext g h s : (∀ x, x ∈ s → g x = h x) → sprod g s = sprod h s.
Proof.
move=> e; rewrite !sprodE.
have M (X : MSet.mset A) : (∀ x, x ∈ X → g x = h x) →
    fprod (g <$> elements X) = fprod (h <$> elements X).
  move=> eX; congr fprod; apply: list_fmap_ext => i x hx.
  by apply: eX; apply/MSet.elem_of_elements/(list_elem_of_lookup_2 _ _ _ hx).
rewrite (M (SMS.pos s)); first by move=> x xp; apply: e; apply: SMS.elem_of_pos.
by rewrite (M (SMS.neg s)) // => x xn; apply: e; apply: SMS.elem_of_neg.
Qed.

Lemma sprod_make g X Y : (∀ x, x ∈ X → x ∈ Y → g x ≠ zero) →
  sprod g (SMS.make X Y) =
  div (fprod (g <$> elements X)) (fprod (g <$> elements Y)).
Proof.
move=> hz; rewrite !sprodE SMS.pos_make SMS.neg_make.
have EX : X = (X ∖ Y) ⊎ (X ∖ (X ∖ Y)).
  apply: MSet.count_inj => x.
  rewrite MSet.count_disj_union !MSet.count_difference; lia.
have EY : Y = (Y ∖ X) ⊎ (X ∖ (X ∖ Y)).
  apply: MSet.count_inj => x.
  rewrite MSet.count_disj_union !MSet.count_difference; lia.
have nI : fprod (g <$> elements (X ∖ (X ∖ Y))) ≠ zero.
  apply: fprod_neq0; apply/list.Forall_forall => f /list_elem_of_fmap.
  move=> [x [-> /MSet.elem_of_elements /MSet.elem_of_difference hx]].
  rewrite !MSet.count_difference in hx.
  by apply: hz; apply/MSet.elem_of_count; lia.
rewrite [in RHS]EX [in fprod (g <$> elements Y)]EY !fprod_disj_union.
by rewrite div_cancel_r.
Qed.

Lemma sprod_disj_union g s1 s2 : (∀ x, x ∈ s1 → x ∈ s2 → g x ≠ zero) →
  sprod g (s1 ⊎ s2) = mul (sprod g s1) (sprod g s2).
Proof.
move=> hz.
change (s1 ⊎ s2) with
  (SMS.make (SMS.pos s1 ⊎ SMS.pos s2) (SMS.neg s1 ⊎ SMS.neg s2)).
rewrite sprod_make.
  move=> x /MSet.elem_of_disj_union hp /MSet.elem_of_disj_union hn.
  have d1 := SMS.pos_neg_disj s1; have d2 := SMS.pos_neg_disj s2.
  case: hp hn => hp [] hn.
  - by case: (d1 x hp hn).
  - by apply: hz; [apply: SMS.elem_of_pos hp|apply: SMS.elem_of_neg hn].
  - by apply: hz; [apply: SMS.elem_of_neg hn|apply: SMS.elem_of_pos hp].
  - by case: (d2 x hp hn).
rewrite !fprod_disj_union !sprodE !divE inv_mul.
by move: (fprod _) (fprod _) (fprod _) (fprod _) => a b c d; ring.
Qed.

Lemma vars_sprod g s y : y ∈ vars (sprod g s) → ∃ u, u ∈ s ∧ y ∈ vars (g u).
Proof.
set vs := elements s ≫= (λ u, vars (g u)).
have F (X : MSet.mset A) : (∀ u, u ∈ X → u ∈ s) →
    over vs (fprod (g <$> elements X)).
  move=> hX; apply: over_fprod; apply/Forall_fmap/list.Forall_forall.
  move=> u /MSet.elem_of_elements /hX us.
  apply: over_vars_sub => z zu; apply/list_elem_of_bind.
  by exists u; split=> //; apply/SMS.elem_of_elements.
have o : over vs (sprod g s).
  rewrite sprodE; apply: over_div; apply: F => u.
  - exact: SMS.elem_of_pos.
  - exact: SMS.elem_of_neg.
move=> /(vars_over _ _ _ o) /list_elem_of_bind.
by case=> u [yu /SMS.elem_of_elements us]; exists u.
Qed.

End SProd.

(** Flattening a signed multiset of signed multisets multiplies the products
    out, unless an element is zero (and could cancel against itself). *)

Section SBind.

Context {A B U : Type}.
Context `{EqDecision A, Lexico A}
  `{!StrictOrder (@lexico A _), !TrichotomyT (@lexico A _)}.
Context `{EqDecision B, Lexico B}
  `{!StrictOrder (@lexico B _), !TrichotomyT (@lexico B _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Add Ring frac_ring_B : (frac_ring_theory (T := U)).

Lemma fprod_mbind (g : B → frac U) (f : A → MSet.mset B) X :
  fprod (g <$> elements (MSet.bind f X)) =
  fprod ((λ x, fprod (g <$> elements (f x))) <$> elements X).
Proof.
elim/(MSet.mset_ind (T := A)): X => [|x X IH].
  by rewrite MSet.bind_empty !MSet.elements_empty.
rewrite MSet.bind_disj_union MSet.bind_singleton !fprod_disj_union IH.
rewrite MSet.elements_singleton fmap_cons fmap_nil fprod_cons fprod_nil.
by move: (fprod _) (fprod _) => a b; ring.
Qed.

Lemma fprod_fmap_div (P N : A → frac U) (l : list A) :
  fprod ((λ x, div (P x) (N x)) <$> l) =
  div (fprod (P <$> l)) (fprod (N <$> l)).
Proof.
elim: l => [|x l IH].
  by rewrite !fmap_nil !fprod_nil divE inv_one; ring.
by rewrite !fmap_cons !fprod_cons IH !divE inv_mul; ring.
Qed.

Lemma sprod_bind (g : B → frac U) (f : A → SMS.sms B) (s : SMS.sms A) :
  (∀ x y, x ∈ s → y ∈ f x → g y ≠ zero) →
  sprod g (SMS.bind f s) = sprod (λ x, sprod g (f x)) s.
Proof.
move=> nz.
set X := MSet.bind (λ x, SMS.pos (f x)) (SMS.pos s) ⊎
         MSet.bind (λ x, SMS.neg (f x)) (SMS.neg s).
set Y := MSet.bind (λ x, SMS.neg (f x)) (SMS.pos s) ⊎
         MSet.bind (λ x, SMS.pos (f x)) (SMS.neg s).
have E : SMS.bind f s = SMS.make X Y.
  by rewrite -{1}(SMS.make_pos_neg s) SMS.bind_make.
have D : ∀ y, y ∈ X → y ∈ Y → g y ≠ zero.
  move=> y /MSet.elem_of_disj_union [] /MSet.elem_of_bind [x [xs yx]] _.
  - by apply: (nz x); [exact: SMS.elem_of_pos xs|exact: SMS.elem_of_pos yx].
  - by apply: (nz x); [exact: SMS.elem_of_neg xs|exact: SMS.elem_of_neg yx].
have S l : fprod ((λ x, sprod g (f x)) <$> l) =
    div (fprod ((λ x, fprod (g <$> elements (SMS.pos (f x)))) <$> l))
        (fprod ((λ x, fprod (g <$> elements (SMS.neg (f x)))) <$> l)).
  rewrite -fprod_fmap_div; congr fprod.
  by apply: list_fmap_ext => i x _; rewrite sprodE.
rewrite E (sprod_make _ _ _ D) /X /Y !fprod_disj_union !fprod_mbind.
rewrite [in RHS]sprodE !S !divE !inv_mul !inv_inv; cbv beta.
by move: (fprod _) (fprod _) (fprod _) (fprod _) => a b c d; ring.
Qed.

End SBind.

(** ** Substituting into variables *)

Section BindVar.

Context {T U : Type}.
Context `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Add Ring poly_ring_V : (Poly.poly_ring_theory (T := T)).
Add Ring frac_ring_V : (frac_ring_theory (T := U)).

Implicit Types (φ : T → frac U) (s : SMS.sms T).

Lemma bind_var φ x : bind φ (var x) = φ x.
Proof. by rewrite !varE bind_of_poly eval_var. Qed.

Lemma fprod_var (X : MSet.mset T) :
  fprod (var <$> elements X) = of_poly (Poly.mono X).
Proof.
transitivity (mono_val var X); first by rewrite mono_valE.
rewrite -eval_mono (_ : var = λ x, of_poly (Poly.var ((λ y : T, y) x))).
  by rewrite [var]unlock.
by rewrite eval_var_map Poly.map_id_ext.
Qed.

Lemma sprod_var_canon s :
  num (sprod var s) = Poly.mono (SMS.pos s) ∧
  den (sprod var s) = Poly.mono (SMS.neg s).
Proof.
rewrite !sprodE !fprod_var -make_div; apply: make_coprime.
- exact: PolyGcd.mono_neq0.
- move=> u /PolyGcd.dvd_mono [m1 [s1 E1]] /PolyGcd.dvd_mono [m2 [s2 E2]].
  have e12 : m1 = m2.
    apply: Poly.mono_pm_inj.
    have opp_inj : ∀ a b : Poly.poly T, (- a)%P = (- b)%P → a = b.
      by move=> a b e; rewrite -(Poly.opp_opp a) e Poly.opp_opp.
    case: E1 => E1; case: E2 => E2; rewrite E1 in E2.
    - by left.
    - by right.
    - by right; rewrite -E2 Poly.opp_opp.
    - by left; apply: opp_inj.
  have m0 : m1 = ∅.
    apply: MSet.count_inj => x; rewrite MSet.count_empty.
    have c1 := proj1 (MSet.subseteq_count _ _) s1 x.
    have c2 := proj1 (MSet.subseteq_count _ _) s2 x.
    rewrite -e12 in c2.
    case: (decide (x ∈ m1)) => hx.
      2: by move: hx; rewrite MSet.elem_of_count; lia.
    exfalso; move/MSet.elem_of_count: hx => hx.
    by apply: (SMS.pos_neg_disj s x); apply/MSet.elem_of_count; lia.
  case: E1 => ->; rewrite m0 -Poly.oneE; first exact: PolyGcd.dvd_refl.
  by exists (- Poly.one)%P; ring.
- exact: Poly.first_neg_mono.
Qed.

Lemma bind_sprod_var φ s : bind φ (sprod var s) = sprod φ s.
Proof.
have [en ed] := sprod_var_canon s.
by rewrite !bindE en ed !eval_mono !mono_valE [sprod φ s]sprodE.
Qed.

(** The polynomial [Σ s]: one monomial per element. *)
lock Definition spoly s : Poly.poly T := Poly.mk (SMS.map (λ x, {[+ x +]}) s).

Lemma eval_spoly φ s : eval φ (spoly s) = ssum φ s.
Proof.
rewrite [spoly]unlock SMS.map_pos_neg eval_make ssumE !msumE.
have M (X : MSet.mset T) :
    fsum (mono_val φ <$> elements (MSet.map (λ x, {[+ x +]}) X)) =
    fsum (φ <$> elements X).
  rewrite (fsum_perm _ (mono_val φ <$> ((λ x, {[+ x +]}) <$> elements X))).
    by apply: fmap_Permutation; exact: MSet.elements_map_perm.
  rewrite -list_fmap_compose; congr fsum; apply: list_fmap_ext => i x _.
  exact: mono_val_singleton.
by rewrite !M.
Qed.

Lemma laurent_sprod_var s : laurent (sprod var s).
Proof.
by have [en ed] := sprod_var_canon s; exists (SMS.pos s), (SMS.neg s).
Qed.

End BindVar.

Lemma ssum_var {T : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)} (s : SMS.sms T) :
  ssum var s = of_poly (spoly s).
Proof.
rewrite -(eval_spoly var) (_ : var = λ x, of_poly (Poly.var ((λ y, y) x))).
  by rewrite [var]unlock.
by rewrite eval_var_map Poly.map_id_ext.
Qed.

Lemma bind_ssum_var {T U : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    `{EqDecision U, Lexico U, !StrictOrder (@lexico U _),
      !TrichotomyT (@lexico U _)} (φ : T → frac U) (s : SMS.sms T) :
  bind φ (ssum var s) = ssum φ s.
Proof. by rewrite ssum_var bind_of_poly eval_spoly. Qed.

(** ** Renaming and substitution *)

Section MapEval.

Context {T U V : Type}.
Context `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.
Context `{EqDecision V, Lexico V}
  `{!StrictOrder (@lexico V _), !TrichotomyT (@lexico V _)}.

Variable g : U → V.
Hypothesis ginj : ∀ a b, g a = g b → a = b.

Lemma map_fsum (l : list (frac U)) : map g (fsum l) = fsum (map g <$> l).
Proof.
elim: l => [|f l IH] /=; first by rewrite !fsum_nil; exact: map_zero.
by rewrite !fsum_cons map_add // IH.
Qed.

Lemma map_fprod (l : list (frac U)) : map g (fprod l) = fprod (map g <$> l).
Proof.
elim: l => [|f l IH] /=; first by rewrite !fprod_nil; exact: map_one.
by rewrite !fprod_cons map_mul // IH.
Qed.

Lemma map_mono_val (φ : T → frac U) m :
  map g (mono_val φ m) = mono_val (λ x, map g (φ x)) m.
Proof. by rewrite !mono_valE map_fprod -list_fmap_compose. Qed.

Lemma map_eval (φ : T → frac U) p :
  map g (eval φ p) = eval (λ x, map g (φ x)) p.
Proof.
have E (X : MSet.mset (MSet.mset T)) :
    (map g ∘ mono_val φ) <$> elements X =
    mono_val (λ x, map g (φ x)) <$> elements X.
  by apply: list_fmap_ext => i m _; exact: map_mono_val.
by rewrite !evalE map_sub // !msumE !map_fsum -!list_fmap_compose !E.
Qed.

Lemma map_bind (φ : T → frac U) r :
  map g (bind φ r) = bind (λ x, map g (φ x)) r.
Proof. by rewrite !bindE map_div // !map_eval. Qed.

Lemma map_sprod (h : T → frac U) s :
  map g (sprod h s) = sprod (λ x, map g (h x)) s.
Proof.
by rewrite !sprodE map_div // !map_fprod -!list_fmap_compose.
Qed.

Lemma map_ssum (h : T → frac U) s :
  map g (ssum h s) = ssum (λ x, map g (h x)) s.
Proof.
by rewrite !ssumE map_sub // !map_fsum -!list_fmap_compose.
Qed.

End MapEval.

(** Renaming the elements of a signed multiset: sums commute with any
    renaming, products with injective ones (which do not cancel). *)

Section SMap.

Context {A B U : Type}.
Context `{EqDecision A, Lexico A}
  `{!StrictOrder (@lexico A _), !TrichotomyT (@lexico A _)}.
Context `{EqDecision B, Lexico B}
  `{!StrictOrder (@lexico B _), !TrichotomyT (@lexico B _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Variable f : A → B.

Lemma fsum_map (g : B → frac U) X :
  fsum (g <$> elements (MSet.map f X)) = fsum ((λ x, g (f x)) <$> elements X).
Proof.
rewrite (fsum_perm _ _ (fmap_Permutation g _ _ (MSet.elements_map_perm f X))).
by rewrite -list_fmap_compose.
Qed.

Lemma fprod_map (g : B → frac U) X :
  fprod (g <$> elements (MSet.map f X)) =
  fprod ((λ x, g (f x)) <$> elements X).
Proof.
rewrite (fprod_perm _ _ (fmap_Permutation g _ _ (MSet.elements_map_perm f X))).
by rewrite -list_fmap_compose.
Qed.

Lemma ssum_map (g : B → frac U) s :
  ssum g (SMS.map f s) = ssum (λ x, g (f x)) s.
Proof. by rewrite SMS.map_pos_neg ssum_make !fsum_map ssumE. Qed.

Lemma sprod_map (g : B → frac U) s :
  (∀ a b, f a = f b → a = b) →
  sprod g (SMS.map f s) = sprod (λ x, g (f x)) s.
Proof.
move=> finj.
have D : ∀ y, y ∈ MSet.map f (SMS.pos s) → y ∈ MSet.map f (SMS.neg s) →
    g y ≠ zero.
  move=> y /MSet.elem_of_map [x1 [-> x1p]] /MSet.elem_of_map [x2 [e x2n]].
  rewrite -(finj _ _ e) in x2n.
  by case: (SMS.pos_neg_disj s x1).
by rewrite SMS.map_pos_neg (sprod_make _ _ _ D) !fprod_map sprodE.
Qed.

End SMap.

(** ** Stripping atoms from monic fractions

    Let [r] have a monomial numerator [M] and denominator [D].  Dividing [r] by
    an atom of [M], multiplying it by an atom of the monomial content of [D],
    or multiplying it by the unit part of [D] yields the expected canonical
    form, because [Poly.first_neg] is multiplicative. *)

Section Strip.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Add Ring poly_ring_S : (Poly.poly_ring_theory (T := T)).

Implicit Types (r : frac T).

Lemma inv_of_poly_canon (U : Poly.poly T) :
  U ≠ Poly.zero → Poly.first_neg U = false →
  num (inv (of_poly U)) = Poly.one ∧ den (inv (of_poly U)) = U.
Proof.
move=> nU fU; rewrite -of_poly_make (inv_make _ _ Poly.one_neq0).
by apply: make_coprime => // u h _.
Qed.

Lemma inv_var_canon x :
  num (inv (var x)) = Poly.one ∧ den (inv (var x)) = Poly.var x.
Proof.
rewrite varE; apply: inv_of_poly_canon; first exact: PolyGcd.var_neq0.
by rewrite Poly.varE Poly.first_neg_mono.
Qed.

Lemma first_neg_unit_part r :
  Poly.first_neg (PolyGcd.unit_part (den r)) = false.
Proof.
have E := PolyGcd.content_unitK (den r).
have nU := PolyGcd.unit_part_neq0 _ (den_neq0 r).
have := den_first_neg r; rewrite -{1}E.
rewrite (Poly.first_neg_mul _ _ (PolyGcd.mono_neq0 _) nU).
by rewrite Poly.first_neg_mono.
Qed.

Lemma mul_inv_var_canon r M a :
  num r = Poly.mono M → a ∈ M →
  num (mul r (inv (var a))) = Poly.mono (M ∖ {[+ a +]}) ∧
  den (mul r (inv (var a))) = den r.
Proof.
move=> eM aM.
have EM : Poly.mono M = (Poly.mono (M ∖ {[+ a +]}) * Poly.var a)%P.
  rewrite Poly.varE Poly.mul_mono; congr Poly.mono.
  apply: MSet.count_inj => x.
  rewrite MSet.count_disj_union MSet.count_difference MSet.count_singleton.
  have := proj1 (MSet.elem_of_count a M) aM.
  by case: bool_decide_reflect => [->|]; lia.
have nq := PolyGcd.mul_neq0 _ _ (den_neq0 r) (PolyGcd.var_neq0 a).
have E : mul r (inv (var a)) = make (Poly.mono (M ∖ {[+ a +]})) (den r).
  rewrite -[r in LHS]make_num_den eM varE -of_poly_make.
  rewrite (inv_make _ _ Poly.one_neq0).
  rewrite (mul_make _ _ _ _ (den_neq0 r) (PolyGcd.var_neq0 a)).
  apply: make_eq nq (den_neq0 r) _.
  by rewrite EM; ring.
rewrite E; apply: make_coprime; first exact: den_neq0.
- move=> u hu hd; apply: (num_den_coprime r) => //.
  rewrite eM EM; apply: PolyGcd.dvd_trans hu _; exact: PolyGcd.dvd_mul_l.
- exact: den_first_neg.
Qed.

Lemma mul_var_content_canon r M c :
  num r = Poly.mono M → c ∈ PolyGcd.content (den r) →
  num (mul r (var c)) = Poly.mono M ∧
  den (mul r (var c)) = PolyGcd.div_mono {[+ c +]} (den r) ∧
  (Poly.mono {[+ c +]} * PolyGcd.div_mono {[+ c +]} (den r))%P = den r.
Proof.
move=> eM cD.
set Dc := PolyGcd.div_mono {[+ c +]} (den r).
have ED : (Poly.mono {[+ c +]} * Dc)%P = den r.
  apply: PolyGcd.unmonoK => n nD; apply/MSet.subseteq_count => x.
  have := proj1 (MSet.subseteq_count _ _) (PolyGcd.content_sub _ _ nD) x.
  have := proj1 (MSet.elem_of_count c _) cD.
  by rewrite MSet.count_singleton; case: bool_decide_reflect => [->|]; lia.
have nDc : Dc ≠ Poly.zero.
  by move=> e; apply: (den_neq0 r); rewrite -ED e; ring.
have E : mul r (var c) = make (Poly.mono M) Dc.
  rewrite -[r in LHS]make_num_den eM varE -of_poly_make.
  rewrite (mul_make _ _ _ _ (den_neq0 r) Poly.one_neq0).
  apply: make_eq (PolyGcd.mul_neq0 _ _ (den_neq0 r) Poly.one_neq0) nDc _.
  by rewrite -ED Poly.varE; ring.
have [en ed] : num (make (Poly.mono M) Dc) = Poly.mono M ∧
               den (make (Poly.mono M) Dc) = Dc.
  apply: make_coprime => //.
  - move=> u hu hd; apply: (num_den_coprime r); first by rewrite eM.
    by rewrite -ED; apply: PolyGcd.dvd_trans hd _; exact: PolyGcd.dvd_mul_r.
  - have := den_first_neg r; rewrite -ED.
    by rewrite (Poly.first_neg_mul _ _ (PolyGcd.mono_neq0 _) nDc)
      Poly.first_neg_mono.
by rewrite E en ed.
Qed.

Lemma mul_unit_part_canon r M :
  num r = Poly.mono M →
  num (mul r (of_poly (PolyGcd.unit_part (den r)))) = Poly.mono M ∧
  den (mul r (of_poly (PolyGcd.unit_part (den r)))) =
  Poly.mono (PolyGcd.content (den r)).
Proof.
move=> eM.
set C := PolyGcd.content (den r); set U := PolyGcd.unit_part (den r).
have ED : (Poly.mono C * U)%P = den r := PolyGcd.content_unitK (den r).
have nU : U ≠ Poly.zero := PolyGcd.unit_part_neq0 _ (den_neq0 r).
have E : mul r (of_poly U) = make (Poly.mono M) (Poly.mono C).
  rewrite -[r in LHS]make_num_den eM -of_poly_make.
  rewrite (mul_make _ _ _ _ (den_neq0 r) Poly.one_neq0).
  apply: make_eq (PolyGcd.mul_neq0 _ _ (den_neq0 r) Poly.one_neq0)
    (PolyGcd.mono_neq0 _) _.
  by rewrite -ED; ring.
rewrite E; apply: make_coprime; first exact: PolyGcd.mono_neq0.
- move=> u hu hd; apply: (num_den_coprime r); first by rewrite eM.
  by rewrite -ED; apply: PolyGcd.dvd_trans hd _; exact: PolyGcd.dvd_mul_l.
- exact: Poly.first_neg_mono.
Qed.

End Strip.

End Frac.

Declare Scope frac_scope.
Delimit Scope frac_scope with F.
Infix "+" := Frac.add : frac_scope.
Infix "-" := Frac.sub : frac_scope.
Infix "*" := Frac.mul : frac_scope.
Infix "/" := Frac.div : frac_scope.
Notation "- f" := (Frac.opp f) : frac_scope.
Notation "/ f" := (Frac.inv f) : frac_scope.
