(** Restricting a polynomial to a secret monomial.

    Given which atoms are public ([pub]), every monomial splits into a secret
    part and a public part ([sec_pubp]).  [restrict σ p] keeps the monomials
    of [p] whose secret part is [σ].  Multiplying by a polynomial over public
    atoms commutes with restriction ([restrict_mul_pub]), so it keeps every
    secret part of the other factor ([restrict_cancel]).  Hence the secret
    parts of the numerator of a sum or product of fractions with public
    denominators come from the numerators of the summands
    ([restrict_add_frac]) or of the first factor ([restrict_mul_frac]). *)

From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From stdpp Require Import list numbers.
From Stdlib Require Import ZArith Lia.
From cryptis.lib Require Import mset sms poly poly_gcd frac.

Module PolyRestrict.

Import Poly.

Section Restrict.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Local Abbreviation poly := (Poly.poly T).

Variable pub : T → bool.

Implicit Types (x y : T) (m n σ : MSet.mset T) (p q d : poly).

Definition sec m : MSet.mset T :=
  MSet.bind (λ x, if pub x then ∅ else {[+ x +]}) m.

Definition pubp m : MSet.mset T :=
  MSet.bind (λ x, if pub x then {[+ x +]} else ∅) m.

Definition over_pub p := ∀ m x, m ∈ car p → x ∈ m → pub x.

lock Definition restrict σ p : poly :=
  mk (SMS.bind (λ m, if bool_decide (sec m = σ) then {[+ m +]} else ∅)
               (car p)).

Lemma car_restrict σ p :
  car (restrict σ p) =
  SMS.bind (λ m, if bool_decide (sec m = σ) then {[+ m +]} else ∅) (car p).
Proof. by rewrite [restrict]unlock. Qed.

Lemma count_sec y m :
  MSet.count y (sec m) = if pub y then 0 else MSet.count y m.
Proof.
elim/MSet.mset_ind: m => [|x m IH].
  by rewrite /sec MSet.bind_empty MSet.count_empty; case: (pub y).
rewrite /sec MSet.bind_disj_union MSet.bind_singleton MSet.count_disj_union.
rewrite -/(sec m) IH MSet.count_disj_union.
case: (decide (y = x)) => [->|ne].
  by case: (pub x); rewrite ?MSet.count_empty.
have c0 : MSet.count y {[+ x +]} = 0.
  by apply/MSet.not_elem_of_count; rewrite MSet.elem_of_singleton.
by case: (pub x); case: (pub y); rewrite ?MSet.count_empty ?c0.
Qed.

Lemma count_pubp y m :
  MSet.count y (pubp m) = if pub y then MSet.count y m else 0.
Proof.
elim/MSet.mset_ind: m => [|x m IH].
  by rewrite /pubp MSet.bind_empty MSet.count_empty; case: (pub y).
rewrite /pubp MSet.bind_disj_union MSet.bind_singleton MSet.count_disj_union.
rewrite -/(pubp m) IH MSet.count_disj_union.
case: (decide (y = x)) => [->|ne].
  by case: (pub x); rewrite ?MSet.count_empty.
have c0 : MSet.count y {[+ x +]} = 0.
  by apply/MSet.not_elem_of_count; rewrite MSet.elem_of_singleton.
by case: (pub x); case: (pub y); rewrite ?MSet.count_empty ?c0.
Qed.

Lemma sec_pubp m : sec m ⊎ pubp m = m.
Proof.
apply: MSet.count_inj => y.
by rewrite MSet.count_disj_union count_sec count_pubp; case: (pub y).
Qed.

Lemma sec_disj_union m n : sec (m ⊎ n) = sec m ⊎ sec n.
Proof. exact: MSet.bind_disj_union. Qed.

Lemma pubp_disj_union m n : pubp (m ⊎ n) = pubp m ⊎ pubp n.
Proof. exact: MSet.bind_disj_union. Qed.

Lemma sec_pub m : (∀ x, x ∈ m → pub x) → sec m = ∅.
Proof.
move=> h; apply: MSet.count_inj => y; rewrite count_sec MSet.count_empty.
case E: (pub y) => //; apply/MSet.not_elem_of_count => /h.
by rewrite E.
Qed.

Lemma pubp_pub m x : x ∈ pubp m → pub x.
Proof.
move=> /MSet.elem_of_count; rewrite count_pubp.
by case: (pub x) => //; lia.
Qed.

Lemma coeff_restrict σ m p :
  coeff m (restrict σ p) =
  if bool_decide (sec m = σ) then coeff m p else 0%Z.
Proof.
rewrite !coeffE car_restrict.
have Z0 : ∀ m', m' ∈ car p → m' ≠ m →
    SMS.count m (if bool_decide (sec m' = σ) then {[+ m' +]} else ∅) = 0%Z.
  move=> m' _ ne; case: bool_decide_reflect => _; last exact: SMS.count_empty.
  by rewrite SMS.count_singleton bool_decide_eq_false_2 // => e; apply: ne.
rewrite (SMS.count_bind_single _ _ _ m Z0).
case: bool_decide_reflect => _; rewrite ?SMS.count_singleton ?SMS.count_empty.
- by rewrite bool_decide_eq_true_2 //=; lia.
- lia.
Qed.

Lemma restrict_neq0 σ p :
  restrict σ p ≠ zero ↔ ∃ m, m ∈ car p ∧ sec m = σ.
Proof.
split.
- move=> nz.
  case: (decide (Exists (λ m, sec m = σ) (elements (car p)))).
    case/Exists_exists=> m [mp e]; exists m; split=> //.
    by apply/SMS.elem_of_elements; apply/list_elem_of_In.
  move=> no; case: nz; apply: coeff_inj => m.
  rewrite coeff_restrict coeff_zero.
  case: bool_decide_reflect => // e.
  case: (decide (coeff m p = 0%Z)) => // /coeff_neq0_elem mp.
  case: no; apply/Exists_exists; exists m; split=> //.
  by apply/list_elem_of_In; apply/SMS.elem_of_elements.
- case=> m [mp e] /(f_equal (coeff m)).
  rewrite coeff_restrict coeff_zero bool_decide_eq_true_2 //.
  by move/coeff_neq0_elem: mp.
Qed.

Lemma restrict_add σ p q :
  restrict σ (p + q)%P = (restrict σ p + restrict σ q)%P.
Proof.
by apply: car_inj; rewrite !(car_restrict, car_add) SMS.bind_disj_union.
Qed.

Lemma restrict_opp σ p : restrict σ (- p)%P = (- restrict σ p)%P.
Proof. by apply: car_inj; rewrite !(car_restrict, car_opp) SMS.bind_inv. Qed.

Lemma restrict_mul_pub σ d p :
  over_pub d → restrict σ (d * p)%P = (d * restrict σ p)%P.
Proof.
move=> hd; apply: car_inj.
rewrite !car_restrict !car_mul !car_restrict SMS.bind_bind.
apply: SMS.bind_ext => m md /=.
rewrite SMS.bind_map SMS.map_bind; apply: SMS.bind_ext => n _ /=.
have -> : sec (m ⊎ n) = sec n.
  by rewrite sec_disj_union (sec_pub m (λ x, hd m x md)) (left_id ∅ (⊎)).
by case: bool_decide; rewrite ?SMS.map_singleton ?SMS.map_empty.
Qed.

Lemma restrict_cancel σ d p q r :
  over_pub d → d ≠ zero → over_pub q → (d * p)%P = (q * r)%P →
  restrict σ p ≠ zero → restrict σ r ≠ zero.
Proof.
move=> hd nd hq e np nr.
have E : (d * restrict σ p)%P = (q * restrict σ r)%P.
  by rewrite -!restrict_mul_pub // e.
move: E; rewrite nr (right_absorb zero mul) => /PolyGcd.domain [] //.
Qed.

Lemma restrict_mul_mono σ m p :
  restrict σ (mono m * p)%P ≠ zero → ∃ n, n ∈ car p ∧ sec m ⊎ sec n = σ.
Proof.
move=> /restrict_neq0 [ν [νp e]]; move: νp; rewrite car_mul_mono.
move=> /SMS.elem_of_map [n [Eν np]].
by exists n; split=> //; rewrite -sec_disj_union -Eν.
Qed.

Lemma over_pub_mul d d' : over_pub d → over_pub d' → over_pub (d * d')%P.
Proof.
move=> hd hd' m x; rewrite car_mul => /SMS.elem_of_bind [m1 [m1d]].
move=> /SMS.elem_of_map [m2 [-> m2d]] /MSet.elem_of_disj_union [].
- exact: hd m1d.
- exact: hd' m2d.
Qed.

Lemma over_pub_vars p : (∀ y, y ∈ Poly.vars p → pub y) → over_pub p.
Proof. by move=> h m x mp xm; apply: h; apply/Poly.elem_of_vars; exists m. Qed.

Lemma vars_over_pub p y : over_pub p → y ∈ Poly.vars p → pub y.
Proof. by move=> h /Poly.elem_of_vars [m [mp ym]]; exact: h mp ym. Qed.

Lemma vars_mul_sub p q y :
  y ∈ Poly.vars (p * q)%P → y ∈ Poly.vars p ∨ y ∈ Poly.vars q.
Proof.
move=> /Poly.elem_of_vars [m]; rewrite car_mul.
case=> /SMS.elem_of_bind [m1 [m1p /SMS.elem_of_map [m2 [-> m2q]]]].
case/MSet.elem_of_disj_union=> ym; [left|right]; apply/Poly.elem_of_vars.
- by exists m1.
- by exists m2.
Qed.

Lemma vars_divisor g s y :
  g ≠ zero → y ∈ Poly.vars s → y ∈ Poly.vars (g * s)%P.
Proof.
move=> ng ys.
have o := PolyGcd.over_quot _ g s (PolyGcd.over_vars (g * s)%P) ng.
case: (decide (y ∈ Poly.vars (g * s)%P)) => // yp.
have d0 := o y yp.
move/Poly.elem_of_vars: ys => [m [ms ym]].
have := PolyGcd.count_le_deg y m s (proj2 (coeff_neq0_elem m s) ms).
have := proj1 (MSet.elem_of_count _ _) ym; lia.
Qed.

Lemma over_pub_divisor g s : g ≠ zero → over_pub (g * s)%P → over_pub s.
Proof.
move=> ng o; apply: over_pub_vars => y ys.
exact: (vars_over_pub _ _ o (vars_divisor _ _ _ ng ys)).
Qed.

End Restrict.

Section Fractions.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Implicit Types (r e : Frac.frac T).

Lemma den_make_divisor (p q : Poly.poly T) :
  q ≠ zero → ∃ g, g ≠ zero ∧ q = (g * Frac.den (Frac.make p q))%P.
Proof.
move=> nq; have [_ e2] := Frac.make_cancel p q nq.
have [g [_ EQ]] := Poly.cancel_spec p q; rewrite -e2 in EQ.
exists g; split=> // eg; apply: nq; rewrite EQ eg.
exact: (left_absorb zero mul).
Qed.

Lemma vars_den_add r1 r2 y :
  y ∈ Poly.vars (Frac.den (Frac.add r1 r2)) →
  y ∈ Poly.vars (Frac.den r1) ∨ y ∈ Poly.vars (Frac.den r2).
Proof.
rewrite Frac.addE => yd.
have nD := PolyGcd.mul_neq0 _ _ (Frac.den_neq0 r1) (Frac.den_neq0 r2).
have [g [ng EQ]] := den_make_divisor
  (Frac.num r1 * Frac.den r2 + Frac.num r2 * Frac.den r1)%P _ nD.
apply: vars_mul_sub; rewrite EQ; exact: vars_divisor.
Qed.

Lemma vars_den_mul r e y :
  y ∈ Poly.vars (Frac.den (Frac.mul r e)) →
  y ∈ Poly.vars (Frac.den r) ∨ y ∈ Poly.vars (Frac.den e).
Proof.
rewrite Frac.mulE => yd.
have nD := PolyGcd.mul_neq0 _ _ (Frac.den_neq0 r) (Frac.den_neq0 e).
have [g [ng EQ]] := den_make_divisor (Frac.num r * Frac.num e)%P _ nD.
apply: vars_mul_sub; rewrite EQ; exact: vars_divisor.
Qed.

Variable pub : T → bool.

Lemma restrict_add_frac σ r1 r2 :
  over_pub pub (Frac.den r1) → over_pub pub (Frac.den r2) →
  restrict pub σ (Frac.num (Frac.add r1 r2)) ≠ zero →
  restrict pub σ (Frac.num r1) ≠ zero ∨ restrict pub σ (Frac.num r2) ≠ zero.
Proof.
move=> o1 o2; rewrite Frac.addE.
set R := (Frac.num r1 * Frac.den r2 + Frac.num r2 * Frac.den r1)%P.
set D := (Frac.den r1 * Frac.den r2)%P.
have nD : D ≠ zero.
  exact: PolyGcd.mul_neq0 _ _ (Frac.den_neq0 r1) (Frac.den_neq0 r2).
have oD : over_pub pub D := over_pub_mul pub _ _ o1 o2.
have [g [ng EQ]] := den_make_divisor R _ nD.
have oQ : over_pub pub (Frac.den (Frac.make R D)).
  by apply: (over_pub_divisor pub _ _ ng); rewrite -EQ.
have E : (D * Frac.num (Frac.make R D))%P = (Frac.den (Frac.make R D) * R)%P.
  by rewrite (comm mul) (Frac.make_spec _ _ nD) (comm mul).
move=> nz; have := restrict_cancel pub σ _ _ _ _ oD nD oQ E nz.
rewrite /R restrict_add ![(Frac.num _ * Frac.den _)%P](comm mul).
rewrite !restrict_mul_pub //.
case: (decide (restrict pub σ (Frac.num r1) = zero)) => [->|]; last by left.
case: (decide (restrict pub σ (Frac.num r2) = zero)) => [->|]; last by right.
by rewrite !(right_absorb zero mul) (left_id zero add).
Qed.

Lemma restrict_mul_frac_num σ r e :
  over_pub pub (Frac.den r) → over_pub pub (Frac.den e) →
  restrict pub σ (Frac.num (Frac.mul r e)) ≠ zero →
  restrict pub σ (Frac.num r * Frac.num e)%P ≠ zero.
Proof.
move=> o1 od; rewrite Frac.mulE.
set R := (Frac.num r * Frac.num e)%P.
set D := (Frac.den r * Frac.den e)%P.
have nD : D ≠ zero := PolyGcd.mul_neq0 _ _ (Frac.den_neq0 r) (Frac.den_neq0 e).
have oD : over_pub pub D := over_pub_mul pub _ _ o1 od.
have [g [ng EQ]] := den_make_divisor R _ nD.
have oQ : over_pub pub (Frac.den (Frac.make R D)).
  by apply: (over_pub_divisor pub _ _ ng); rewrite -EQ.
have E : (D * Frac.num (Frac.make R D))%P = (Frac.den (Frac.make R D) * R)%P.
  by rewrite (comm mul) (Frac.make_spec _ _ nD) (comm mul).
exact: restrict_cancel pub σ _ _ _ _ oD nD oQ E.
Qed.

Lemma restrict_mul_frac σ r e :
  over_pub pub (Frac.den r) → over_pub pub (Frac.num e) →
  over_pub pub (Frac.den e) →
  restrict pub σ (Frac.num (Frac.mul r e)) ≠ zero →
  restrict pub σ (Frac.num r) ≠ zero.
Proof.
move=> o1 on od /(restrict_mul_frac_num _ _ _ o1 od).
rewrite (comm mul) restrict_mul_pub // => h e0; apply: h.
by rewrite e0 (right_absorb zero mul).
Qed.

End Fractions.

End PolyRestrict.
