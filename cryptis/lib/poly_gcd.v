(** Correctness of [Poly.gcd], [Poly.div] and [Poly.cancel].

    [dvd p q] says that [p] divides [q].  [gcd p q] divides [p] and [q]
    ([gcd_dvdl], [gcd_dvdr]), and every common divisor of [p] and [q]
    divides it ([dvd_gcd]).  When [q ≠ 0] divides [p], [div p q] is the
    exact quotient ([div_spec]).  When [p] or [q] is nonzero, every common
    divisor of the two components of [cancel p q] is a unit
    ([cancel_coprime]), and the units are [1] and [-1] ([unit_pm1]).
    [cancel] picks a canonical representative of the fraction [p / q]:
    when [q] and [q'] are nonzero, [cancel p q = cancel p' q'] exactly when
    [p * q' = p' * q] ([cancel_canon]), and the second component is never
    [first_neg] ([cancel_first_neg]).  These representatives are the pairs
    that [cancel] leaves unchanged: [cancel p q = (p, q)] when [q] is
    nonzero, not [first_neg], and has no common divisor with [p] besides
    units ([cancel_id]).

    The proof follows [Poly.ops] one variable at a time ([gcd_spec_cons]).
    At each level, a polynomial is a polynomial in [x] whose coefficients
    are polynomials over the remaining variables ([over]).  Polynomials
    have no zero divisors ([domain]).  The key step is Gauss's lemma
    ([gauss_gen], [prim_dvd_mul]), which ensures that the primitive
    pseudo-remainder sequence keeps the primitive common divisors
    ([prs_spec]). *)

From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From stdpp Require Import list numbers.
From Stdlib Require Import ZArith Lia Ring.
From cryptis.lib Require Import mset sms poly.

Module PolyGcd.

Import Poly.

Section Gcd.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Local Abbreviation poly := (Poly.poly T).

Implicit Types (x y : T) (m n : MSet.mset T) (p q r : poly).

Add Ring poly_ring : (poly_ring_theory (T := T)).

(** ** Coefficients in one variable *)

Lemma count_vpow y x k :
  MSet.count y (vpow x k) = if bool_decide (y = x) then k else 0.
Proof.
rewrite vpowE MSet.count_of_list.
elim: k => [|k IH] /=; first by case_bool_decide.
rewrite IH; case_bool_decide; lia.
Qed.

Ltac mset_solver :=
  apply: MSet.count_inj => ?;
  rewrite ?(MSet.count_empty, MSet.count_singleton, MSet.count_disj_union,
            MSet.count_difference, count_vpow) /=;
  repeat case_bool_decide; subst; simpl; lia.

Lemma coeffx_add x k p q :
  coeffx x k (p + q)%P = (coeffx x k p + coeffx x k q)%P.
Proof.
by apply: car_inj; rewrite !(car_coeffx, car_add) SMS.bind_disj_union.
Qed.

Lemma coeffx_opp x k p : coeffx x k (- p)%P = (- coeffx x k p)%P.
Proof. by apply: car_inj; rewrite !(car_coeffx, car_opp) SMS.bind_inv. Qed.

Lemma coeffx_zero x k : coeffx x k zero = zero.
Proof. by apply: car_inj; rewrite car_coeffx car_zero SMS.bind_empty. Qed.

Lemma coeffx_sub x k p q :
  coeffx x k (p - q)%P = (coeffx x k p - coeffx x k q)%P.
Proof. by rewrite !subE coeffx_add coeffx_opp. Qed.

Lemma coeffx_mono x k m :
  coeffx x k (mono m) =
  if bool_decide (MSet.count x m = k) then mono (m ∖ vpow x k) else zero.
Proof.
apply: car_inj; rewrite car_coeffx car_mono SMS.bind_singleton.
by case_bool_decide; rewrite ?car_mono ?car_zero.
Qed.

Lemma coeff_coeffx x k m p :
  coeff m (coeffx x k p) =
  if bool_decide (MSet.count x m = 0) then coeff (m ⊎ vpow x k) p else 0%Z.
Proof.
have key n : coeff m (coeffx x k (mono n)) =
    if bool_decide (MSet.count x m = 0) then coeff (m ⊎ vpow x k) (mono n)
    else 0%Z.
  rewrite coeffx_mono !coeff_mono.
  case: (bool_decide_reflect (MSet.count x n = k)) => [nk|nk];
  case: (bool_decide_reflect (MSet.count x m = 0)) => [m0|m0];
  rewrite ?coeff_mono ?coeff_zero //.
  - congr Z.b2z; apply: bool_decide_ext; split=> [->|<-]; mset_solver.
  - rewrite bool_decide_eq_false_2 // => e; apply: m0.
    by rewrite e MSet.count_difference count_vpow bool_decide_eq_true_2 //; lia.
  - rewrite bool_decide_eq_false_2 // => e; apply: nk.
    rewrite -e MSet.count_disj_union count_vpow.
    by rewrite bool_decide_eq_true_2 //; lia.
elim/poly_ind: p => [|n p IH|n p IH].
- by rewrite coeffx_zero !coeff_zero; case_bool_decide.
- rewrite coeffx_add !coeff_add IH key; case_bool_decide; lia.
- rewrite coeffx_add coeffx_opp !coeff_add !coeff_opp IH key; case_bool_decide;
    lia.
Qed.

(** *** Degrees *)

Lemma count_le_deg x m p : coeff m p ≠ 0%Z → MSet.count x m ≤ deg x p.
Proof.
move=> h; rewrite degE; apply: max_list_elem_of_le; apply/list_elem_of_fmap.
exists m; split => //; apply/SMS.elem_of_elements; exact/coeff_neq0_elem.
Qed.

Lemma deg_le x p d :
  (∀ m, coeff m p ≠ 0%Z → MSet.count x m ≤ d) → deg x p ≤ d.
Proof.
move=> h; rewrite degE.
case E: (MSet.count x <$> elements (car p)) => [|c cs]; first by simpl; lia.
have : max_list (c :: cs) ∈ c :: cs by apply: max_list_elem_of.
rewrite -E => /list_elem_of_fmap [m [->]].
move=> /SMS.elem_of_elements /coeff_neq0_elem.
exact: h.
Qed.

Lemma deg_witness x p :
  p ≠ zero → ∃ m, coeff m p ≠ 0%Z ∧ MSet.count x m = deg x p.
Proof.
move=> nz; rewrite degE.
case E: (MSet.count x <$> elements (car p)) => [|c cs].
  case: nz; apply: car_inj; rewrite car_zero; apply: SMS.elements_empty_inv.
  by move: E; case: (elements (car p)).
have : max_list (c :: cs) ∈ c :: cs by apply: max_list_elem_of.
rewrite -E => /list_elem_of_fmap [m [e]].
move=> /SMS.elem_of_elements /coeff_neq0_elem.
by exists m.
Qed.

Lemma coeffx_above x k p : deg x p < k → coeffx x k p = zero.
Proof.
move=> lt; apply: coeff_inj => m; rewrite coeff_coeffx coeff_zero.
case_bool_decide => //.
case: (decide (coeff (m ⊎ vpow x k) p = 0%Z)) => // /(count_le_deg x).
rewrite MSet.count_disj_union count_vpow bool_decide_eq_true_2 //; lia.
Qed.

Lemma lcx_neq0 x p : p ≠ zero → lcx x p ≠ zero.
Proof.
move=> /(deg_witness x) [m [cm em]] e.
have c0 : MSet.count x (m ∖ vpow x (deg x p)) = 0.
  by rewrite MSet.count_difference count_vpow bool_decide_eq_true_2 //; lia.
have : coeff (m ∖ vpow x (deg x p)) (lcx x p) ≠ 0%Z.
  rewrite lcxE coeff_coeffx bool_decide_eq_true_2 //.
  by rewrite (_ : m ∖ vpow x (deg x p) ⊎ vpow x (deg x p) = m) //; mset_solver.
by rewrite e coeff_zero.
Qed.

Lemma deg_coeffx x k p : deg x (coeffx x k p) = 0.
Proof.
apply/Nat.le_0_r/deg_le => m; rewrite coeff_coeffx.
by case_bool_decide => // _; lia.
Qed.

Lemma vpow0 x : vpow x 0 = ∅.
Proof. mset_solver. Qed.

Lemma coeffx0_free x s : deg x s = 0 → coeffx x 0 s = s.
Proof.
move=> d0; apply: coeff_inj => m; rewrite coeff_coeffx vpow0.
rewrite (right_id ∅ (⊎)); case_bool_decide => //.
case: (decide (coeff m s = 0%Z)) => // /(count_le_deg x); lia.
Qed.

Lemma diff_empty_r (X : MSet.mset T) : X ∖ ∅ = X.
Proof. mset_solver. Qed.

Lemma coeffx_mul_coeffx0 x k s p :
  coeffx x k (coeffx x 0 s * p)%P = (coeffx x 0 s * coeffx x k p)%P.
Proof.
elim/poly_ind_add: s => [|n|s1 s2 IH1 IH2|s1 IH].
- by rewrite coeffx_zero !(left_absorb zero mul) coeffx_zero.
- elim/poly_ind_add: p => [|m|p1 p2 IH1 IH2|p1 IH].
  + by rewrite coeffx_zero !(right_absorb zero mul) coeffx_zero.
  + rewrite coeffx_mono vpow0 diff_empty_r.
    case: (bool_decide_reflect (MSet.count x n = 0)) => [n0|n0];
      last by rewrite !(left_absorb zero mul) coeffx_zero.
    rewrite mul_mono !coeffx_mono MSet.count_disj_union n0 /=.
    case_bool_decide; last by rewrite (right_absorb zero mul).
    rewrite mul_mono; congr mono; mset_solver.
  + by rewrite mul_add_r !coeffx_add IH1 IH2 mul_add_r.
  + by rewrite mul_opp_r !coeffx_opp IH mul_opp_r.
- by rewrite !coeffx_add !mul_add_l coeffx_add IH1 IH2.
- by rewrite !coeffx_opp !mul_opp_l coeffx_opp IH.
Qed.

Lemma coeffx_mulf x k s p :
  deg x s = 0 → coeffx x k (s * p)%P = (s * coeffx x k p)%P.
Proof. by move=> /coeffx0_free <-; rewrite coeffx_mul_coeffx0. Qed.

Lemma vpow_add x a b : vpow x a ⊎ vpow x b = vpow x (a + b).
Proof. mset_solver. Qed.

Lemma coeffx_shift x k e p :
  coeffx x k (p * mono (vpow x e))%P =
  if bool_decide (e ≤ k) then coeffx x (k - e) p else zero.
Proof.
elim/poly_ind_add: p => [|m|p1 p2 IH1 IH2|p1 IH].
- by rewrite (left_absorb zero mul) !coeffx_zero; case_bool_decide.
- rewrite mul_mono !coeffx_mono MSet.count_disj_union count_vpow.
  rewrite (bool_decide_eq_true_2 (x = x)) //.
  case: (bool_decide_reflect (e ≤ k)) => ek.
  + case: (bool_decide_reflect (MSet.count x m = k - e)) => c.
    * have h : MSet.count x m + e = k by lia.
      rewrite (bool_decide_eq_true_2 _ h); congr mono; mset_solver.
    * have h : MSet.count x m + e ≠ k by lia.
      by rewrite (bool_decide_eq_false_2 _ h).
  + have h : MSet.count x m + e ≠ k by lia.
    by rewrite (bool_decide_eq_false_2 _ h).
- rewrite mul_add_l coeffx_add IH1 IH2; case_bool_decide.
  + by rewrite coeffx_add.
  + by rewrite (left_id zero add).
- rewrite mul_opp_l coeffx_opp IH; case_bool_decide.
  + by rewrite coeffx_opp.
  + exact: opp_zero.
Qed.

Lemma coeffx_vpow x k e :
  coeffx x k (mono (vpow x e)) = if bool_decide (k = e) then one else zero.
Proof.
rewrite coeffx_mono count_vpow (bool_decide_eq_true_2 (x = x)) //.
case: (bool_decide_reflect (k = e)) => ek.
- rewrite (bool_decide_eq_true_2 (e = k)) // oneE; congr mono; mset_solver.
- by rewrite (bool_decide_eq_false_2 (e = k)) //; lia.
Qed.

Lemma deg_zero x : deg x zero = 0.
Proof. by apply/Nat.le_0_r/deg_le => m; rewrite coeff_zero. Qed.

Lemma deg_add_le x p q : deg x (p + q)%P ≤ max (deg x p) (deg x q).
Proof.
apply: deg_le => m; rewrite coeff_add => h.
case: (decide (coeff m p = 0%Z)) => hp.
- have hq : coeff m q ≠ 0%Z by lia.
  have := count_le_deg x m q hq; lia.
- have := count_le_deg x m p hp; lia.
Qed.

Lemma deg_opp x p : deg x (- p)%P = deg x p.
Proof.
apply: Nat.le_antisymm; apply: deg_le => m; rewrite ?coeff_opp => h.
- apply: count_le_deg; lia.
- apply: (count_le_deg x m (- p)%P); rewrite coeff_opp; lia.
Qed.

Lemma deg_sub_le x p q : deg x (p - q)%P ≤ max (deg x p) (deg x q).
Proof. rewrite subE; have := deg_add_le x p (- q)%P; rewrite deg_opp; lia. Qed.

Lemma deg_mul_le x p q : deg x (p * q)%P ≤ deg x p + deg x q.
Proof.
apply: deg_le => m /coeff_neq0_elem.
rewrite car_mul => /SMS.elem_of_bind [a [ap /SMS.elem_of_map [b [-> bq]]]].
rewrite MSet.count_disj_union.
have := count_le_deg x a p (proj2 (coeff_neq0_elem a p) ap).
have := count_le_deg x b q (proj2 (coeff_neq0_elem b q) bq).
lia.
Qed.

Lemma deg_mono x m : deg x (mono m) = MSet.count x m.
Proof.
apply: Nat.le_antisymm.
- by apply: deg_le => n /coeff_mono_eq ->.
- apply: count_le_deg; rewrite coeff_mono bool_decide_eq_true_2 //.
Qed.

Lemma deg_vpow x e : deg x (mono (vpow x e)) = e.
Proof. by rewrite deg_mono count_vpow bool_decide_eq_true_2. Qed.

Lemma deg_one x : deg x one = 0.
Proof. by rewrite oneE deg_mono MSet.count_empty. Qed.

Lemma deg_const x c : deg x (const c) = 0.
Proof.
apply/Nat.le_0_r/deg_le => m; rewrite coeff_const.
case_bool_decide as e; last done.
by rewrite e MSet.count_empty.
Qed.

(** *** Leading coefficients *)

Definition rest x p := (p - lcx x p * mono (vpow x (deg x p)))%P.

Lemma rest_eq x p : p = (lcx x p * mono (vpow x (deg x p)) + rest x p)%P.
Proof. rewrite /rest; ring. Qed.

Lemma deg_lcx x p : deg x (lcx x p) = 0.
Proof. rewrite lcxE; exact: deg_coeffx. Qed.

Lemma coeffx_rest x k p :
  coeffx x k (rest x p) =
  if bool_decide (k = deg x p) then zero else coeffx x k p.
Proof.
rewrite /rest coeffx_sub (coeffx_mulf _ _ _ _ (deg_lcx x p)) coeffx_vpow.
case_bool_decide as e.
- rewrite e (right_id one mul) lcxE; ring.
- rewrite (right_absorb zero mul); ring.
Qed.

Lemma deg_rest x p : rest x p = zero ∨ deg x (rest x p) < deg x p.
Proof.
case: (decide (rest x p = zero)) => [|nz]; [by left|right].
have := lcx_neq0 x (rest x p) nz.
case: (Nat.lt_ge_cases (deg x (rest x p)) (deg x p)) => // le.
rewrite lcxE coeffx_rest; case_bool_decide => //.
have h : deg x p < deg x (rest x p) by lia.
by rewrite (coeffx_above _ _ _ h).
Qed.

Lemma deg_mul0 x s t : deg x s = 0 → deg x t = 0 → deg x (s * t)%P = 0.
Proof. move=> hs ht; have := deg_mul_le x s t; lia. Qed.

(* From here on, unfolding [rest] only slows down unification. *)
Local Opaque rest.

Lemma coeffx_mul_top x p q :
  coeffx x (deg x p + deg x q) (p * q)%P = (lcx x p * lcx x q)%P.
Proof.
set dp := deg x p; set dq := deg x q.
have hX : (mono (vpow x dp) * mono (vpow x dq))%P = mono (vpow x (dp + dq)).
  by rewrite mul_mono vpow_add.
have e : (p * q = lcx x p * lcx x q * mono (vpow x (dp + dq))
              + lcx x p * (rest x q * mono (vpow x dp))
              + lcx x q * (rest x p * mono (vpow x dq))
              + rest x p * rest x q)%P.
  transitivity ((lcx x p * mono (vpow x dp) + rest x p) *
                (lcx x q * mono (vpow x dq) + rest x q))%P.
    by rewrite -!rest_eq.
  rewrite -hX; ring.
have hf := deg_mul0 x _ _ (deg_lcx x p) (deg_lcx x q).
rewrite e !coeffx_add (coeffx_mulf _ _ _ _ hf).
rewrite (coeffx_vpow x (dp + dq) (dp + dq)).
rewrite (bool_decide_eq_true_2 (dp + dq = dp + dq)) // (right_id one mul).
rewrite (coeffx_mulf _ _ _ _ (deg_lcx x p)) (coeffx_mulf _ _ _ _ (deg_lcx x q)).
rewrite (coeffx_shift x (dp + dq) dp (rest x q)).
rewrite (coeffx_shift x (dp + dq) dq (rest x p)).
have h1 : dp ≤ dp + dq by lia.
have h2 : dq ≤ dp + dq by lia.
rewrite (bool_decide_eq_true_2 _ h1) (bool_decide_eq_true_2 _ h2).
have -> : dp + dq - dp = dq by lia.
have -> : dp + dq - dq = dp by lia.
rewrite (coeffx_rest x dq q) (coeffx_rest x dp p).
rewrite (bool_decide_eq_true_2 (dq = deg x q)) //.
rewrite (bool_decide_eq_true_2 (dp = deg x p)) //.
rewrite !(right_absorb zero mul).
have -> : coeffx x (dp + dq) (rest x p * rest x q)%P = zero.
  case: (deg_rest x p) => [->|hp].
    by rewrite (left_absorb zero mul) coeffx_zero.
  case: (deg_rest x q) => [->|hq].
    by rewrite (right_absorb zero mul) coeffx_zero.
  have h : deg x (rest x p * rest x q)%P < dp + dq.
    have := deg_mul_le x (rest x p) (rest x q); lia.
  exact: coeffx_above.
by rewrite !(right_id zero add).
Qed.

Lemma deg_coeffx_le y x k p : y ≠ x → deg y (coeffx x k p) ≤ deg y p.
Proof.
move=> ne; apply: deg_le => m; rewrite coeff_coeffx.
case_bool_decide as c0; last done.
move=> /(count_le_deg y); rewrite MSet.count_disj_union count_vpow.
by rewrite bool_decide_eq_false_2 //; lia.
Qed.

(** *** Variables *)

Definition over (vs : list T) p := ∀ y, y ∉ vs → deg y p = 0.

Lemma over_mono vs vs' p :
  (∀ y, y ∈ vs → y ∈ vs') → over vs p → over vs' p.
Proof. by move=> sub h y yn; apply: h => /sub. Qed.

Lemma over_zero vs : over vs zero.
Proof. by move=> y _; rewrite deg_zero. Qed.

Lemma over_one vs : over vs one.
Proof. by move=> y _; rewrite deg_one. Qed.

Lemma over_const vs c : over vs (const c).
Proof. by move=> y _; rewrite deg_const. Qed.

Lemma over_add vs p q : over vs p → over vs q → over vs (p + q)%P.
Proof.
move=> hp hq y yn; have := deg_add_le y p q; rewrite hp // hq //; lia.
Qed.

Lemma over_opp vs p : over vs p → over vs (- p)%P.
Proof. by move=> hp y yn; rewrite deg_opp hp. Qed.

Lemma over_sub vs p q : over vs p → over vs q → over vs (p - q)%P.
Proof.
move=> hp hq y yn; have := deg_sub_le y p q; rewrite hp // hq //; lia.
Qed.

Lemma over_mul vs p q : over vs p → over vs q → over vs (p * q)%P.
Proof.
move=> hp hq y yn; have := deg_mul_le y p q; rewrite hp // hq //; lia.
Qed.

Lemma over_vpow vs x e : x ∈ vs → over vs (mono (vpow x e)).
Proof.
move=> xin y yn; rewrite deg_mono count_vpow bool_decide_eq_false_2 //.
by move=> e'; apply: yn; rewrite e'.
Qed.

Lemma over_coeffx x vs k p : over (x :: vs) p → over vs (coeffx x k p).
Proof.
move=> hp y yn; case: (decide (y = x)) => [->|ne]; first exact: deg_coeffx.
have h : deg y p = 0 by apply: hp; rewrite elem_of_cons => -[|].
have := deg_coeffx_le y x k p ne; lia.
Qed.

Lemma over_lcx x vs p : over (x :: vs) p → over vs (lcx x p).
Proof. by rewrite lcxE; apply: over_coeffx. Qed.

Lemma over_cons x vs p : over vs p → over (x :: vs) p.
Proof. by apply: over_mono => y yin; apply/elem_of_cons; right. Qed.

Lemma over_free x vs s : over (x :: vs) s → deg x s = 0 → over vs s.
Proof.
move=> hs hx y yn; case: (decide (y = x)) => [->|ne] //.
by apply: hs; rewrite elem_of_cons => -[|].
Qed.

Lemma over_nil p : over [] p → p = const (coeff ∅ p).
Proof.
move=> h; apply: coeff_inj => m; rewrite coeff_const.
case_bool_decide as e; first by rewrite e.
case: (decide (coeff m p = 0%Z)) => // nz; exfalso; apply: e.
apply: MSet.count_inj => y; rewrite MSet.count_empty.
have hy : deg y p = 0 by apply: h; apply: not_elem_of_nil.
have := count_le_deg y m p nz; lia.
Qed.

Lemma over_vars p : over (vars p) p.
Proof.
move=> y yn; case: (decide (deg y p = 0)) => // nd; exfalso; apply: yn.
have nz : p ≠ zero by move=> e; apply: nd; rewrite e deg_zero.
have [m [cm em]] := deg_witness y p nz.
rewrite varsE elem_of_remove_dups; apply/list_elem_of_bind.
exists m; split.
- apply/MSet.elem_of_elements/MSet.elem_of_count; lia.
- by apply/SMS.elem_of_elements/coeff_neq0_elem.
Qed.

(** *** No zero divisors *)

Lemma domain_over vs p q :
  over vs p → over vs q → (p * q)%P = zero → p = zero ∨ q = zero.
Proof.
elim: vs p q => [|x vs IH] p q op oq.
- rewrite (over_nil p op) (over_nil q oq) -const_mul -const_zero.
  by move=> /const_inj /Z.mul_eq_0 [->|->]; [left|right].
- move=> e; case: (decide (p = zero)) => [|np]; [by left|right].
  case: (decide (q = zero)) => // nq; exfalso.
  have : (lcx x p * lcx x q)%P = zero by rewrite -coeffx_mul_top e coeffx_zero.
  move=> /(IH _ _ (over_lcx _ _ _ op) (over_lcx _ _ _ oq)) [].
  + exact: lcx_neq0 _ _ np.
  + exact: lcx_neq0 _ _ nq.
Qed.

Lemma domain p q : (p * q)%P = zero → p = zero ∨ q = zero.
Proof.
apply: (domain_over (vars p ++ vars q)).
- by apply: over_mono (over_vars p) => y yin; apply/elem_of_app; left.
- by apply: over_mono (over_vars q) => y yin; apply/elem_of_app; right.
Qed.

Lemma mul_neq0 p q : p ≠ zero → q ≠ zero → (p * q)%P ≠ zero.
Proof. by move=> np nq /domain []. Qed.

Lemma deg_mul x p q :
  p ≠ zero → q ≠ zero → deg x (p * q)%P = deg x p + deg x q.
Proof.
move=> np nq; apply: Nat.le_antisymm; first exact: deg_mul_le.
case: (Nat.le_gt_cases (deg x p + deg x q) (deg x (p * q)%P)) => // lt.
have : coeffx x (deg x p + deg x q) (p * q)%P ≠ zero.
  by rewrite coeffx_mul_top; apply: mul_neq0; apply: lcx_neq0.
by rewrite (coeffx_above _ _ _ lt).
Qed.

Lemma lcx_zero x : lcx x zero = zero.
Proof. by rewrite lcxE coeffx_zero. Qed.

Lemma lcx_mul x p q : lcx x (p * q)%P = (lcx x p * lcx x q)%P.
Proof.
case: (decide (p = zero)) => [->|np].
  by rewrite (left_absorb zero mul) !lcx_zero (left_absorb zero mul).
case: (decide (q = zero)) => [->|nq].
  by rewrite (right_absorb zero mul) !lcx_zero (right_absorb zero mul).
by rewrite lcxE (deg_mul _ _ _ np nq) coeffx_mul_top.
Qed.

(** *** Divisibility *)

Definition dvd p q := ∃ r, q = (p * r)%P.

Lemma dvd_refl p : dvd p p.
Proof. by exists one; rewrite (right_id one mul). Qed.

Lemma dvd_trans p q r : dvd p q → dvd q r → dvd p r.
Proof. move=> [a ->] [b ->]; exists (a * b)%P; ring. Qed.

Lemma dvd_zero p : dvd p zero.
Proof. by exists zero; rewrite (right_absorb zero mul). Qed.

Lemma dvd_one_l p : dvd one p.
Proof. by exists p; rewrite (left_id one mul). Qed.

Lemma dvd_mulr p q r : dvd p q → dvd p (q * r)%P.
Proof. move=> [a ->]; exists (a * r)%P; ring. Qed.

Lemma dvd_mull p q r : dvd p q → dvd p (r * q)%P.
Proof. move=> [a ->]; exists (r * a)%P; ring. Qed.

Lemma dvd_mul_l p q : dvd p (p * q)%P.
Proof. by exists q. Qed.

Lemma dvd_mul_r p q : dvd q (p * q)%P.
Proof. exists p; ring. Qed.

Lemma dvd_add p q r : dvd p q → dvd p r → dvd p (q + r)%P.
Proof. move=> [a ->] [b ->]; exists (a + b)%P; ring. Qed.

Lemma dvd_opp p q : dvd p q → dvd p (- q)%P.
Proof. move=> [a ->]; exists (- a)%P; ring. Qed.

Lemma dvd_sub p q r : dvd p q → dvd p r → dvd p (q - r)%P.
Proof. move=> [a ->] [b ->]; exists (a - b)%P; ring. Qed.

Lemma dvd_mul2 p q r s : dvd p q → dvd r s → dvd (p * r)%P (q * s)%P.
Proof. move=> [a ->] [b ->]; exists (a * b)%P; ring. Qed.

Lemma dvd_zero_l q : dvd zero q → q = zero.
Proof. by move=> [a ->]; rewrite (left_absorb zero mul). Qed.

Lemma mul_cancel_l c a b : c ≠ zero → (c * a)%P = (c * b)%P → a = b.
Proof.
move=> nc e.
have h : (c * (a - b))%P = zero.
  transitivity (c * a - c * b)%P; first ring.
  by rewrite e; ring.
case/domain: h => // h.
transitivity (a - b + b)%P; first ring.
by rewrite h (left_id zero add).
Qed.

Lemma dvd_cancel_l c a b : c ≠ zero → dvd (c * a)%P (c * b)%P → dvd a b.
Proof.
move=> nc [r e]; exists r; apply: (mul_cancel_l c) => //.
by rewrite e; ring.
Qed.

Lemma dvd_neq0 p q : q ≠ zero → dvd p q → p ≠ zero.
Proof.
by move=> nq [r e] ep; apply: nq; rewrite e ep (left_absorb zero mul).
Qed.

Lemma dvd_deg x p q : q ≠ zero → dvd p q → deg x p ≤ deg x q.
Proof.
move=> nq [r e]; have np : p ≠ zero by apply: (dvd_neq0 p q nq); exists r.
have nr : r ≠ zero.
  by move=> er; apply: nq; rewrite e er (right_absorb zero mul).
by rewrite e deg_mul //; lia.
Qed.

Lemma dvd_over vs p q : over vs q → q ≠ zero → dvd p q → over vs p.
Proof.
move=> oq nq d y yn; have := dvd_deg y p q nq d; rewrite oq //; lia.
Qed.

Lemma over_quot vs g s : over vs (g * s)%P → g ≠ zero → over vs s.
Proof.
move=> o ng; case: (decide (s = zero)) => [->|ns]; first exact: over_zero.
apply: (dvd_over vs s (g * s)%P) => //; last exact: dvd_mul_r.
exact: mul_neq0.
Qed.

Lemma dvd_coeffx x k s p : deg x s = 0 → dvd s p → dvd s (coeffx x k p).
Proof.
by move=> hs [r ->]; rewrite (coeffx_mulf _ _ _ _ hs); apply: dvd_mul_l.
Qed.

Lemma dvd_lcx x s p : deg x s = 0 → dvd s p → dvd s (lcx x p).
Proof. rewrite lcxE; exact: dvd_coeffx. Qed.

Lemma restE x p : rest x p = (p - lcx x p * mono (vpow x (deg x p)))%P.
Proof.
transitivity (lcx x p * mono (vpow x (deg x p)) + rest x p
              - lcx x p * mono (vpow x (deg x p)))%P; first ring.
by rewrite -rest_eq.
Qed.

Lemma over_rest x vs p : over (x :: vs) p → over (x :: vs) (rest x p).
Proof.
move=> op; rewrite restE; apply: over_sub => //; apply: over_mul.
- by apply: over_cons; apply: over_lcx.
- by apply: over_vpow; apply: list_elem_of_here.
Qed.

Lemma lcx_free x s : deg x s = 0 → lcx x s = s.
Proof. by move=> hs; rewrite lcxE hs (coeffx0_free x s hs). Qed.

Lemma dvd_coeffs x s p : (∀ k, dvd s (coeffx x k p)) → dvd s p.
Proof.
move Hn : (deg x p) => n.
elim/lt_wf_ind: n p Hn => n IH p Hn hk.
rewrite (rest_eq x p); apply: dvd_add.
  by apply: dvd_mulr; rewrite lcxE; apply: hk.
case: (deg_rest x p) => [->|lt]; first exact: dvd_zero.
apply: (IH (deg x (rest x p))) => //; first lia.
move=> k; rewrite coeffx_rest; case_bool_decide; [exact: dvd_zero|exact: hk].
Qed.

Lemma deg_lt_top x D p :
  deg x p ≤ D → coeffx x D p = zero → p = zero ∨ deg x p < D.
Proof.
move=> le c0; case: (decide (p = zero)) => [|np]; [by left|right].
case: (Nat.eq_dec (deg x p) D) => [e|ne]; last lia.
by exfalso; apply: (lcx_neq0 x p np); rewrite lcxE e.
Qed.

(** ** One level of the recursion

    Polynomials over [x :: vs] are seen as polynomials in [x] whose
    coefficients are over [vs], where [gc] and [dv] compute gcds and exact
    quotients. *)

Section Level.

Variables (x : T) (vs : list T) (gc dv : poly → poly → poly).
Hypothesis x_vs : x ∉ vs.
Hypothesis gc_dvdl : ∀ s t, over vs s → over vs t → dvd (gc s t) s.
Hypothesis gc_dvdr : ∀ s t, over vs s → over vs t → dvd (gc s t) t.
Hypothesis dvd_gc : ∀ u s t,
  over vs s → over vs t → dvd u s → dvd u t → dvd u (gc s t).
Hypothesis dv_spec : ∀ s t,
  over vs s → over vs t → t ≠ zero → dvd t s → s = (t * dv s t)%P.

Lemma deg_over s : over vs s → deg x s = 0.
Proof. by move=> hs; apply: hs. Qed.

Lemma gc_over s t : over vs s → over vs t → over vs (gc s t).
Proof.
move=> hs ht; case: (decide (s = zero)) => [es|ns].
- case: (decide (t = zero)) => [et|nt].
  + have : dvd zero (gc s t).
      by apply: dvd_gc => //; rewrite ?es ?et; apply: dvd_refl.
    by move=> /dvd_zero_l ->; apply: over_zero.
  + by apply: (dvd_over _ _ _ ht nt); apply: gc_dvdr.
- by apply: (dvd_over _ _ _ hs ns); apply: gc_dvdl.
Qed.

Lemma gc_euclid s a b : over vs s → over vs a → over vs b →
  (∀ u, dvd u s → dvd u b → dvd u one) → dvd s (a * b)%P → dvd s a.
Proof.
move=> os oa ob cop sab.
case: (decide (a = zero)) => [->|na]; first exact: dvd_zero.
have oas : over vs (a * s)%P by apply: over_mul.
have oab : over vs (a * b)%P by apply: over_mul.
have h1 : dvd s (gc (a * s) (a * b))%P.
  by apply: dvd_gc => //; apply: dvd_mul_r.
have [h' Eh] : dvd a (gc (a * s) (a * b))%P.
  by apply: dvd_gc => //; apply: dvd_mul_l.
have hs : dvd h' s.
  by apply: (dvd_cancel_l a) => //; rewrite -Eh; apply: gc_dvdl.
have hb : dvd h' b.
  by apply: (dvd_cancel_l a) => //; rewrite -Eh; apply: gc_dvdr.
apply: (dvd_trans _ _ _ h1); rewrite Eh.
have := dvd_mul2 _ _ _ _ (dvd_refl a) (cop h' hs hb).
by rewrite (right_id one mul).
Qed.

(** *** Contents *)

Lemma foldr_gc_over l : Forall (over vs) l → over vs (foldr gc zero l).
Proof.
elim: l => [|s l IH] /=; first by move=> _; apply: over_zero.
by move=> /Forall_cons_iff [os ol]; apply: gc_over => //; apply: IH.
Qed.

Lemma foldr_gc_dvd l s :
  Forall (over vs) l → s ∈ l → dvd (foldr gc zero l) s.
Proof.
elim: l => [|t l IH] /=; first by move=> _ /elem_of_nil.
move=> /Forall_cons_iff [ot ol] /elem_of_cons [->|sl].
- by apply: gc_dvdl => //; apply: foldr_gc_over.
- apply: (dvd_trans _ (foldr gc zero l)); last exact: IH.
  by apply: gc_dvdr => //; apply: foldr_gc_over.
Qed.

Lemma dvd_foldr_gc l u :
  Forall (over vs) l → Forall (dvd u) l → dvd u (foldr gc zero l).
Proof.
elim: l => [|s l IH] /=; first by move=> _ _; apply: dvd_zero.
move=> /Forall_cons_iff [os ol] /Forall_cons_iff [us ul].
by apply: dvd_gc => //; [apply: foldr_gc_over | apply: IH].
Qed.

Lemma cont_coeffs_over p : over (x :: vs) p →
  Forall (over vs) ((λ k, coeffx x k p) <$> seq 0 (deg x p + 1)).
Proof.
move=> op; apply/list.Forall_forall => s /list_elem_of_fmap [k [-> _]].
exact: over_coeffx.
Qed.

Lemma cont_over p : over (x :: vs) p → over vs (cont x gc p).
Proof.
by move=> op; rewrite contE; apply: foldr_gc_over; apply: cont_coeffs_over.
Qed.

Lemma cont_dvd p k : over (x :: vs) p → dvd (cont x gc p) (coeffx x k p).
Proof.
move=> op; case: (Nat.le_gt_cases k (deg x p)) => [le|lt].
- rewrite contE; apply: foldr_gc_dvd; first exact: cont_coeffs_over.
  apply/list_elem_of_fmap; exists k; split => //.
  apply/elem_of_seq; lia.
- by rewrite (coeffx_above _ _ _ lt); apply: dvd_zero.
Qed.

Lemma dvd_cont u p :
  over (x :: vs) p → (∀ k, dvd u (coeffx x k p)) → dvd u (cont x gc p).
Proof.
move=> op hu; rewrite contE; apply: dvd_foldr_gc; first exact: cont_coeffs_over.
by apply/list.Forall_forall => s /list_elem_of_fmap [k [-> _]].
Qed.

Lemma cont_dvdp p : over (x :: vs) p → dvd (cont x gc p) p.
Proof. by move=> op; apply: dvd_coeffs => k; apply: cont_dvd. Qed.

Lemma dvd_cont_free u p :
  over (x :: vs) p → deg x u = 0 → dvd u p → dvd u (cont x gc p).
Proof. by move=> op hu up; apply: dvd_cont => // k; apply: dvd_coeffx. Qed.

Lemma cont_neq0 p : over (x :: vs) p → p ≠ zero → cont x gc p ≠ zero.
Proof.
move=> op np e; apply: np; apply: dvd_zero_l; rewrite -e; exact: cont_dvdp.
Qed.

(** *** Exact division *)

Lemma div_loop_spec g p : over (x :: vs) g → g ≠ zero →
  ∀ fuel r q s, over (x :: vs) s → r = (g * s)%P → p = (q * g + r)%P →
  (r = zero ∨ deg x r < deg x g + fuel) →
  p = (g * div_loop x dv g (deg x g) (lcx x g) fuel r q)%P.
Proof.
move=> og ng; elim=> [|n IH] r q s os Er Ep hd /=.
- case: (decide (s = zero)) => [es|ns].
    by rewrite Ep Er es (right_absorb zero mul) (right_id zero add); ring.
  exfalso; case: hd => [er|lt].
  + by apply: (mul_neq0 g s) => //; rewrite -Er.
  + have := deg_mul x g s ng ns; rewrite -Er; lia.
- case_bool_decide as er.
    by rewrite Ep er (right_id zero add); ring.
  have ns : s ≠ zero.
    by move=> es; apply: er; rewrite Er es (right_absorb zero mul).
  have or : over (x :: vs) r by rewrite Er; apply: over_mul.
  have nl := lcx_neq0 x g ng.
  have dl : dvd (lcx x g) (lcx x r) by rewrite Er lcx_mul; apply: dvd_mul_l.
  have Edv : dv (lcx x r) (lcx x g) = lcx x s.
    apply: (mul_cancel_l (lcx x g)) => //.
    rewrite -(dv_spec _ _ (over_lcx _ _ _ or) (over_lcx _ _ _ og) nl dl).
    by rewrite Er lcx_mul.
  have Edeg : deg x r - deg x g = deg x s by rewrite Er deg_mul //; lia.
  rewrite Edv Edeg.
  have Er' : (r - lcx x s * mono (vpow x (deg x s)) * g)%P =
             (g * rest x s)%P.
    by rewrite restE Er; ring.
  apply: (IH _ _ (rest x s) (over_rest _ _ _ os) Er').
  + by rewrite Ep; ring.
  + rewrite Er'; case: (decide (rest x s = zero)) => [->|nr]; [left|right].
      by rewrite (right_absorb zero mul).
    have lt : deg x (rest x s) < deg x s by case: (deg_rest x s).
    case: hd => [//|hd].
    have := deg_mul x g (rest x s) ng nr.
    have := deg_mul x g s ng ns.
    rewrite -Er; lia.
Qed.

Lemma div_lvl_spec p g : over (x :: vs) p → over (x :: vs) g → g ≠ zero →
  dvd g p → p = (g * div_lvl x dv p g)%P.
Proof.
move=> op og ng [s Es]; rewrite div_lvlE.
apply: (div_loop_spec g p og ng _ p zero s) => //.
- by apply: (over_quot _ g) => //; rewrite -Es.
- by rewrite (left_absorb zero mul) (left_id zero add).
- by right; lia.
Qed.

Lemma div_lvl_zero g : div_lvl x dv zero g = zero.
Proof. by rewrite div_lvlE Nat.add_1_r /= bool_decide_eq_true_2. Qed.

(** *** Primitive parts and Gauss's lemma *)

Local Abbreviation pp p := (div_lvl x dv p (cont x gc p)).

Lemma pp_spec p : over (x :: vs) p → p = (cont x gc p * pp p)%P.
Proof.
move=> op; case: (decide (p = zero)) => [->|np].
  by rewrite div_lvl_zero (right_absorb zero mul).
apply: div_lvl_spec => //.
- by apply: over_cons; apply: cont_over.
- exact: cont_neq0.
- exact: cont_dvdp.
Qed.

Lemma pp_over p : over (x :: vs) p → over (x :: vs) (pp p).
Proof.
move=> op; case: (decide (p = zero)) => [->|np].
  by rewrite div_lvl_zero; apply: over_zero.
apply: (over_quot _ (cont x gc p)); last exact: cont_neq0.
by rewrite -pp_spec.
Qed.

Definition prim f := f ≠ zero ∧ ∀ u, deg x u = 0 → dvd u f → dvd u one.

Lemma pp_prim p : over (x :: vs) p → p ≠ zero → prim (pp p).
Proof.
move=> op np; have E := pp_spec p op; have nc := cont_neq0 p op np.
have oc := cont_over p op.
split.
  by move=> e; apply: np; rewrite E e (right_absorb zero mul).
move=> u hu up.
have : dvd (cont x gc p * u)%P (cont x gc p * one)%P.
  rewrite (right_id one mul); apply: dvd_cont_free => //.
    by apply: deg_mul0 => //; apply: deg_over.
  by rewrite {2}E; apply: dvd_mul2 => //; apply: dvd_refl.
exact: dvd_cancel_l.
Qed.

Lemma gauss_gen f g d : over (x :: vs) f → over (x :: vs) g → over vs d →
  (∀ u, dvd u d → dvd u f → dvd u one) → dvd d (f * g)%P → dvd d g.
Proof.
move Hn : (deg x f + deg x g) => n.
elim/lt_wf_ind: n f g d Hn => n IH f g d Hn hf og od cop dfg.
case: (decide (g = zero)) => [->|ng]; first exact: dvd_zero.
case: (decide (f = zero)) => [ef|nf].
  apply: (dvd_trans _ one _ _ (dvd_one_l g)).
  by apply: cop; [exact: dvd_refl | rewrite ef; exact: dvd_zero].
case: (decide (d = zero)) => [ed|nd].
  by move: dfg; rewrite ed => /dvd_zero_l /domain [].
have ob : over vs (lcx x g) by apply: over_lcx.
have nb : lcx x g ≠ zero by apply: lcx_neq0.
have egr : ∀ u, dvd u d → dvd u (lcx x g) → dvd u (gc d (lcx x g)).
  by move=> u; apply: dvd_gc.
move: (gc d (lcx x g)) (gc_over _ _ od ob) (gc_dvdl _ _ od ob)
  (gc_dvdr _ _ od ob) egr => e oe ed eb egr.
have ne : e ≠ zero by apply: (dvd_neq0 _ _ nb eb).
have eg : dvd e g.
  rewrite (rest_eq x g); apply: dvd_add; first exact: dvd_mulr.
  case: (deg_rest x g) => [->|lt]; first exact: dvd_zero.
  apply: (IH (deg x f + deg x (rest x g)) _ f (rest x g) e eq_refl hf
            (over_rest _ _ _ og) oe).
  - lia.
  - by move=> u ue uf; apply: cop => //; apply: (dvd_trans _ _ _ ue ed).
  - have -> : (f * rest x g)%P =
              (f * g - lcx x g * (f * mono (vpow x (deg x g))))%P.
      by rewrite restE; ring.
    apply: dvd_sub; first exact: (dvd_trans _ _ _ ed dfg).
    exact: dvd_mulr.
case: ed => d1 Ed; case: eg => g2 Eg.
have nd1 : d1 ≠ zero.
  by move=> e1; apply: nd; rewrite Ed e1 (right_absorb zero mul).
have ng2 : g2 ≠ zero.
  by move=> e2; apply: ng; rewrite Eg e2 (right_absorb zero mul).
have od1 : over vs d1 by apply: (over_quot _ e) => //; rewrite -Ed.
have og2 : over (x :: vs) g2 by apply: (over_quot _ e) => //; rewrite -Eg.
have dg2 : dvd d1 (f * g2)%P.
  apply: (dvd_cancel_l e) => //.
  have -> : (e * (f * g2))%P = (f * g)%P by rewrite Eg; ring.
  by rewrite -Ed.
have Eb : lcx x g = (e * lcx x g2)%P.
  by rewrite Eg lcx_mul (lcx_free x e (deg_over e oe)).
have cop1 : ∀ u, dvd u d1 → dvd u (lcx x g2) → dvd u one.
  move=> u ud ub.
  have : dvd (e * u)%P (e * one)%P.
    rewrite (right_id one mul); apply: egr.
    - by rewrite Ed; apply: dvd_mul2 => //; apply: dvd_refl.
    - by rewrite Eb; apply: dvd_mul2 => //; apply: dvd_refl.
  exact: dvd_cancel_l.
have d1a : dvd d1 (lcx x f).
  apply: (gc_euclid d1 (lcx x f) (lcx x g2)) => //.
  - exact: over_lcx.
  - exact: over_lcx.
  - rewrite -lcx_mul; apply: dvd_lcx => //; exact: deg_over.
have cop2 : ∀ u, dvd u d1 → dvd u (rest x f) → dvd u one.
  move=> u ud ur; apply: cop.
  - by rewrite Ed; apply: dvd_mull.
  - rewrite (rest_eq x f); apply: dvd_add => //.
    by apply: dvd_mulr; apply: (dvd_trans _ _ _ ud d1a).
have d1r : dvd d1 (rest x f * g2)%P.
  have -> : (rest x f * g2)%P =
            (f * g2 - lcx x f * (mono (vpow x (deg x f)) * g2))%P.
    by rewrite restE; ring.
  by apply: dvd_sub => //; apply: dvd_mulr.
have dg : dvd d1 g2.
  case: (deg_rest x f) => [er|lt].
  - apply: (dvd_trans _ one _ _ (dvd_one_l g2)).
    by apply: cop2; [exact: dvd_refl | rewrite er; exact: dvd_zero].
  - have Edg : deg x g = deg x g2.
      by rewrite Eg deg_mul // (deg_over e oe).
    apply: (IH (deg x (rest x f) + deg x g2) _ (rest x f) g2 d1 eq_refl
              (over_rest _ _ _ hf) og2 od1 cop2 d1r).
    lia.
by rewrite Ed Eg; apply: dvd_mul2 => //; apply: dvd_refl.
Qed.

Lemma prim_dvd_mul h c a : prim h → over (x :: vs) h → over vs c →
  c ≠ zero → over (x :: vs) a → dvd h (c * a)%P → dvd h a.
Proof.
move=> [nh ph] oh oc nc oa [Q EQ].
have oQ : over (x :: vs) Q.
  apply: (over_quot _ h) => //; rewrite -EQ.
  by apply: over_mul => //; apply: over_cons.
have cQ : dvd c (h * Q)%P by rewrite -EQ; apply: dvd_mul_l.
have cop : ∀ u, dvd u c → dvd u h → dvd u one.
  move=> u uc uh; apply: ph => //.
  have := dvd_deg x u c nc uc; rewrite (deg_over c oc); lia.
have [Q' EQ'] := gauss_gen h Q c oh oQ oc cop cQ.
exists Q'; apply: (mul_cancel_l c) => //.
by rewrite EQ EQ'; ring.
Qed.

(** *** Pseudo-remainders *)

Lemma prem_loop_spec a b : over (x :: vs) a → over (x :: vs) b → b ≠ zero →
  ∀ fuel r c Q, over (x :: vs) r → over vs c → c ≠ zero →
  (c * a = Q * b + r)%P → (r = zero ∨ deg x r < deg x b + fuel) →
  let r' := prem_loop x b (deg x b) (lcx x b) fuel r in
  over (x :: vs) r' ∧ (r' = zero ∨ deg x r' < deg x b) ∧
  ∃ c' Q', over vs c' ∧ c' ≠ zero ∧ (c' * a = Q' * b + r')%P.
Proof.
move=> oa ob nb; elim=> [|n IH] r c Q or oc nc Ec hd /=.
- split=> //; split; last by exists c, Q.
  by case: hd => [|?]; [left|right; lia].
- case: (decide (r = zero)) => [er|nr].
    rewrite bool_decide_eq_true_2 //=.
    by split=> //; split; [left | exists c, Q].
  rewrite bool_decide_eq_false_2 //=.
  case: Nat.ltb_spec => [lt|ge].
    by split=> //; split; [right | exists c, Q].
  have nl := lcx_neq0 x b nb.
  have ol : over vs (lcx x b) by apply: over_lcx.
  set t := (lcx x r * mono (vpow x (deg x r - deg x b)))%P.
  have ot : over (x :: vs) t.
    apply: over_mul; first by apply: over_cons; apply: over_lcx.
    by apply: over_vpow; apply: list_elem_of_here.
  apply: (IH _ (lcx x b * c)%P (lcx x b * Q + t)%P).
  + by apply: over_sub; apply: over_mul => //; apply: over_cons.
  + exact: over_mul.
  + exact: mul_neq0.
  + transitivity (lcx x b * (c * a))%P; first ring.
    by rewrite Ec; ring.
  + have hD : coeffx x (deg x r) (lcx x b * r - t * b)%P = zero.
      rewrite coeffx_sub (coeffx_mulf _ _ _ _ (deg_lcx x b)) -lcxE.
      have -> : (t * b)%P =
                (lcx x r * (b * mono (vpow x (deg x r - deg x b))))%P.
        by rewrite /t; ring.
      rewrite (coeffx_mulf _ _ _ _ (deg_lcx x r)).
      rewrite (coeffx_shift x (deg x r) (deg x r - deg x b) b).
      have h : deg x r - deg x b ≤ deg x r by lia.
      rewrite (bool_decide_eq_true_2 _ h).
      have -> : deg x r - (deg x r - deg x b) = deg x b by lia.
      by rewrite -lcxE; ring.
    (* Rewriting with [deg_lcx] here makes unification unfold [mul]. *)
    have hle : deg x (lcx x b * r - t * b)%P ≤ deg x r.
      have h1 := deg_sub_le x (lcx x b * r)%P (t * b)%P.
      have h2 := deg_mul_le x (lcx x b) r.
      have h3 := deg_mul_le x t b.
      have h4 := deg_mul_le x (lcx x r) (mono (vpow x (deg x r - deg x b))).
      have h5 := deg_lcx x r; have h6 := deg_lcx x b.
      have h7 := deg_vpow x (deg x r - deg x b).
      rewrite -/t in h4; lia.
    case: (deg_lt_top _ _ _ hle hD) => [->|lt]; [by left|right].
    case: hd => [//|hd]; lia.
Qed.

Lemma prem_spec a b : over (x :: vs) a → over (x :: vs) b → b ≠ zero →
  over (x :: vs) (prem x a b) ∧
  (prem x a b = zero ∨ deg x (prem x a b) < deg x b) ∧
  ∃ c Q, over vs c ∧ c ≠ zero ∧ (c * a = Q * b + prem x a b)%P.
Proof.
move=> oa ob nb; rewrite premE.
apply: (prem_loop_spec a b oa ob nb _ a one zero oa (over_one _) one_neq0).
- by rewrite (left_id one mul) (left_absorb zero mul) (left_id zero add).
- by right; lia.
Qed.

(** *** Primitive pseudo-remainder sequences *)

Definition pgcd h a b := over (x :: vs) h ∧ prim h ∧ dvd h a ∧ dvd h b ∧
  ∀ u, over (x :: vs) u → prim u → dvd u a → dvd u b → dvd u h.

Lemma pgcd_zero a : over (x :: vs) a → prim a → pgcd a a zero.
Proof.
move=> oa pa; split=> //; split=> //; split; first exact: dvd_refl.
by split; [exact: dvd_zero | move=> u _ _ ua _].
Qed.

Lemma pgcd_sym h a b : pgcd h a b → pgcd h b a.
Proof.
move=> [oh [ph [ha [hb hu]]]]; split=> //; split=> //; split=> //.
by split=> // u ou pu ub ua; apply: hu.
Qed.

Lemma prs_spec fuel a b : over (x :: vs) a → over (x :: vs) b → prim a →
  (b = zero ∨ prim b) → (b = zero ∨ deg x b + 2 ≤ fuel) →
  pgcd (prs x gc dv fuel a b) a b.
Proof.
elim: fuel a b => [|n IH] a b oa ob pa pb hf /=.
  by case: hf => [->|]; [exact: pgcd_zero | lia].
case_bool_decide as eb; first by rewrite eb; exact: pgcd_zero.
have pb' : prim b by case: pb.
have [opr [dpr [c [Q [oc [nc Ec]]]]]] := prem_spec a b oa ob eb.
move: (prem x a b) opr dpr Ec => r opr dpr Ec.
have Er := pp_spec r opr.
have [h1 [h2 [h3 [h4 h5]]]] : pgcd (prs x gc dv n b (pp r)) b (pp r).
  apply: IH => //; first exact: pp_over.
  - case: (decide (r = zero)) => [->|nr]; first by rewrite div_lvl_zero; left.
    by right; apply: pp_prim.
  - case: (decide (r = zero)) => [->|nr]; first by rewrite div_lvl_zero; left.
    right; case: dpr => [//|lt].
    have npp : pp r ≠ zero.
      by move=> e; apply: nr; rewrite Er e (right_absorb zero mul).
    have h0 := deg_over _ (cont_over r opr).
    have h1 := deg_mul x _ _ (cont_neq0 r opr nr) npp.
    rewrite -Er in h1.
    case: hf => [//|hf]; lia.
have ha : dvd (prs x gc dv n b (pp r)) a.
  apply: (prim_dvd_mul _ c a h2 h1 oc nc oa).
  rewrite Ec; apply: dvd_add; first exact: dvd_mull.
  by rewrite [X in dvd _ X]Er; apply: dvd_mull.
have hu : ∀ u, over (x :: vs) u → prim u → dvd u a → dvd u b →
    dvd u (prs x gc dv n b (pp r)).
  move=> u ou pu ua ub; apply: h5 => //.
  case: (decide (r = zero)) => [er|nr].
    by rewrite er div_lvl_zero; apply: dvd_zero.
  apply: (prim_dvd_mul u (cont x gc r)) => //.
  + exact: cont_over.
  + exact: cont_neq0.
  + exact: pp_over.
  + rewrite -Er.
    have -> : r = (c * a - Q * b)%P by rewrite Ec; ring.
    by apply: dvd_sub; apply: dvd_mull.
by split; [|split; [|split; [|split]]].
Qed.

Lemma gcd_lvl_spec p q : over (x :: vs) p → over (x :: vs) q →
  dvd (gcd_lvl x gc dv p q) p ∧ dvd (gcd_lvl x gc dv p q) q ∧
  ∀ u, dvd u p → dvd u q → dvd u (gcd_lvl x gc dv p q).
Proof.
move=> op oq; rewrite [gcd_lvl]unlock /=.
case: bool_decide_reflect => [->|np].
  by split; [exact: dvd_zero | split; [exact: dvd_refl | move=> u]].
case: bool_decide_reflect => [->|nq].
  by split; [exact: dvd_refl | split; [exact: dvd_zero | move=> u]].
have oa := pp_over p op; have ob := pp_over q oq.
have hg : pgcd (if (deg x (pp p) <? deg x (pp q))%nat
                then prs x gc dv (deg x (pp p) + 2) (pp q) (pp p)
                else prs x gc dv (deg x (pp q) + 2) (pp p) (pp q))
               (pp p) (pp q).
  have pa := pp_prim p op np; have pb := pp_prim q oq nq.
  case: Nat.ltb_spec => lt.
  - by apply: pgcd_sym; apply: prs_spec => //; [right | right; lia].
  - by apply: prs_spec => //; [right | right; lia].
set g := (if _ then _ else _) in hg *.
clearbody g; case: hg => og [pg [ga [gb gu]]].
have ocp := cont_over p op; have ocq := cont_over q oq.
have Ep := pp_spec p op; have Eq := pp_spec q oq.
split; [|split].
- rewrite [X in dvd _ X]Ep; apply: dvd_mul2 => //; exact: gc_dvdl.
- rewrite [X in dvd _ X]Eq; apply: dvd_mul2 => //; exact: gc_dvdr.
- move=> u up uq.
  have nu : u ≠ zero by apply: (dvd_neq0 _ _ np up).
  have ou : over (x :: vs) u by apply: (dvd_over _ _ _ op np up).
  have Eu := pp_spec u ou.
  have pu := pp_prim u ou nu; have opu := pp_over u ou.
  have dup : dvd (pp u) u.
    by move: (dvd_mul_r (cont x gc u) (pp u)); rewrite -Eu.
  have cu := cont_over u ou.
  rewrite Eu; apply: dvd_mul2.
  + apply: dvd_gc => //.
    * apply: dvd_cont_free => //; first exact: deg_over.
      exact: (dvd_trans _ _ _ (cont_dvdp u ou) up).
    * apply: dvd_cont_free => //; first exact: deg_over.
      exact: (dvd_trans _ _ _ (cont_dvdp u ou) uq).
  + apply: gu => //.
    * apply: (prim_dvd_mul _ (cont x gc p)) => //; first exact: cont_neq0.
      by rewrite -Ep; apply: (dvd_trans _ _ _ dup up).
    * apply: (prim_dvd_mul _ (cont x gc q)) => //; first exact: cont_neq0.
      by rewrite -Eq; apply: (dvd_trans _ _ _ dup uq).
Qed.

End Level.

(** ** Correctness of [gcd], [div] and [cancel] *)

Definition gcd_spec vs (gc dv : poly → poly → poly) : Prop :=
  (∀ s t, over vs s → over vs t → dvd (gc s t) s) ∧
  (∀ s t, over vs s → over vs t → dvd (gc s t) t) ∧
  (∀ u s t, over vs s → over vs t → dvd u s → dvd u t → dvd u (gc s t)) ∧
  (∀ s t, over vs s → over vs t → t ≠ zero → dvd t s → s = (t * dv s t)%P).

Lemma gcd_spec_cons x vs gc dv : x ∉ vs → gcd_spec vs gc dv →
  gcd_spec (x :: vs) (gcd_lvl x gc dv) (div_lvl x dv).
Proof.
move=> xn [h1 [h2 [h3 h4]]].
have spec := gcd_lvl_spec x vs gc dv xn h1 h2 h3 h4.
split; [|split; [|split]].
- by move=> s t os ot; case: (spec s t os ot).
- by move=> s t os ot; case: (spec s t os ot) => _ [].
- move=> u s t os ot us ut; case: (spec s t os ot) => _ [_ h].
  exact: h.
- by move=> s t os ot nt dt; apply: (div_lvl_spec x vs dv h4).
Qed.

Lemma dvd_const a b : (a | b)%Z → dvd (const a) (const b).
Proof. by move=> [k ->]; exists (const k); rewrite -const_mul Z.mul_comm. Qed.

Lemma dvd_const_inv c a : dvd (const c) (const a) → (c | a)%Z.
Proof.
case: (decide (a = 0%Z)) => [->|na]; first by move=> _; apply: Z.divide_0_r.
move=> [w Ew].
have nc : const c ≠ zero.
  move=> ec; apply: na; apply: const_inj.
  by rewrite Ew ec (left_absorb zero mul) const_zero.
have ow : over [] w.
  by apply: (over_quot _ (const c)) => //; rewrite -Ew; apply: over_const.
move: Ew; rewrite (over_nil w ow) -const_mul => /const_inj ->.
exact: Z.divide_factor_l.
Qed.

Lemma gcd_spec_nil : gcd_spec [] (ops []).1 (ops []).2.
Proof.
split; [|split; [|split]] => /=.
- move=> s t os ot; rewrite [X in dvd _ X](over_nil s os).
  apply: dvd_const; exact: Z.gcd_divide_l.
- move=> s t os ot; rewrite [X in dvd _ X](over_nil t ot).
  apply: dvd_const; exact: Z.gcd_divide_r.
- move=> u s t os ot us ut.
  case: (decide (s = zero ∧ t = zero)) => [[-> ->]|nst].
    by rewrite coeff_zero /= const_zero; apply: dvd_zero.
  have ou : over [] u.
    case: (decide (s = zero)) => [es|ns].
    + have nt : t ≠ zero by move=> et; apply: nst; split.
      exact: (dvd_over _ _ _ ot nt ut).
    + exact: (dvd_over _ _ _ os ns us).
  have cu := over_nil u ou; have cs := over_nil s os.
  have ct := over_nil t ot.
  have h1 : (coeff ∅ u | coeff ∅ s)%Z.
    by apply: dvd_const_inv; rewrite -cu -cs.
  have h2 : (coeff ∅ u | coeff ∅ t)%Z.
    by apply: dvd_const_inv; rewrite -cu -ct.
  rewrite cu; apply: dvd_const; exact: Z.gcd_greatest.
- move=> s t os ot nt dts.
  have cs := over_nil s os; have ct := over_nil t ot.
  have h : (coeff ∅ t | coeff ∅ s)%Z.
    by apply: dvd_const_inv; rewrite -cs -ct.
  have nt' : coeff ∅ t ≠ 0%Z.
    by move=> e; apply: nt; rewrite ct e const_zero.
  rewrite {1}cs {1}ct -const_mul; congr const.
  by apply/(Z.quot_exact _ _ nt')/(Z.rem_divide _ _ nt').
Qed.

Lemma ops_spec vs : NoDup vs → gcd_spec vs (ops vs).1 (ops vs).2.
Proof.
elim: vs => [|x vs IH] /=; first by move=> _; apply: gcd_spec_nil.
by move=> /list.NoDup_cons [xn nd]; apply: gcd_spec_cons => //; apply: IH.
Qed.

Lemma over_vars2 p q :
  over (remove_dups (vars p ++ vars q)) p ∧
  over (remove_dups (vars p ++ vars q)) q.
Proof.
split; apply: over_mono (over_vars _) => y yin;
  rewrite elem_of_remove_dups elem_of_app; tauto.
Qed.

Theorem gcd_dvdl p q : dvd (gcd p q) p.
Proof.
have [op oq] := over_vars2 p q.
have [h _] := ops_spec _ (NoDup_remove_dups (vars p ++ vars q)).
rewrite gcdE; exact: h.
Qed.

Theorem gcd_dvdr p q : dvd (gcd p q) q.
Proof.
have [op oq] := over_vars2 p q.
have [_ [h _]] := ops_spec _ (NoDup_remove_dups (vars p ++ vars q)).
rewrite gcdE; exact: h.
Qed.

Theorem dvd_gcd u p q : dvd u p → dvd u q → dvd u (gcd p q).
Proof.
have [op oq] := over_vars2 p q.
have [_ [_ [h _]]] := ops_spec _ (NoDup_remove_dups (vars p ++ vars q)).
rewrite gcdE; exact: h.
Qed.

Theorem div_spec p q : q ≠ zero → dvd q p → p = (q * div p q)%P.
Proof.
have [op oq] := over_vars2 p q.
have [_ [_ [_ h]]] := ops_spec _ (NoDup_remove_dups (vars p ++ vars q)).
rewrite divE; exact: h.
Qed.

Lemma unit_pm1 u : dvd u one → u = one ∨ u = (- one)%P.
Proof.
move=> [v Ev].
have ou : over [] u.
  by apply: (dvd_over _ _ one (over_one []) one_neq0); exists v.
have nu : u ≠ zero.
  by move=> eu; apply: one_neq0; rewrite Ev eu (left_absorb zero mul).
have ov : over [] v.
  by apply: (over_quot _ u) => //; rewrite -Ev; apply: over_one.
move: Ev; rewrite (over_nil u ou) (over_nil v ov) -const_mul -const_one.
move=> /const_inj e; case: (Z.eq_mul_1 _ _ (eq_sym e)) => ->.
- by left.
- by right; rewrite const_opp.
Qed.

Lemma cancel_with_coprime g p q p' q' u : g ≠ zero →
  p = (g * p')%P → q = (g * q')%P → (∀ v, dvd v p → dvd v q → dvd v g) →
  dvd u (cancel_with g p q p' q').1 → dvd u (cancel_with g p q p' q').2 →
  dvd u one.
Proof.
move=> ng Ep Eq hg.
have hc : bool_decide ((g * p')%P = p ∧ (g * q')%P = q) = true.
  by apply: bool_decide_eq_true_2; split; symmetry.
rewrite [cancel_with]unlock /= hc.
have key : dvd u p' → dvd u q' → dvd u one.
  move=> up uq.
  have : dvd (g * u)%P (g * one)%P.
    rewrite (right_id one mul); apply: hg.
    - by rewrite Ep; apply: dvd_mul2 => //; apply: dvd_refl.
    - by rewrite Eq; apply: dvd_mul2 => //; apply: dvd_refl.
  exact: dvd_cancel_l.
case: (first_neg q') => /= up uq; apply: key => //.
- by rewrite -(opp_opp p'); apply: dvd_opp.
- by rewrite -(opp_opp q'); apply: dvd_opp.
Qed.

Theorem cancel_coprime p q u : p ≠ zero ∨ q ≠ zero →
  dvd u (cancel p q).1 → dvd u (cancel p q).2 → dvd u one.
Proof.
move=> npq; have ng : gcd p q ≠ zero.
  move=> e; have := gcd_dvdl p q; have := gcd_dvdr p q.
  by rewrite e => /dvd_zero_l eq /dvd_zero_l ep; case: npq.
rewrite [cancel]unlock /=; apply: cancel_with_coprime => //.
- by apply: div_spec => //; apply: gcd_dvdl.
- by apply: div_spec => //; apply: gcd_dvdr.
- by move=> v vp vq; apply: dvd_gcd.
Qed.

(** ** Canonical forms *)

Lemma euclid a b c : (∀ u, dvd u a → dvd u b → dvd u one) →
  dvd a (b * c)%P → dvd a c.
Proof.
move=> cop abc.
case: (decide (c = zero)) => [->|nc]; first exact: dvd_zero.
have h1 : dvd a (gcd (c * a) (c * b))%P.
  by apply: dvd_gcd; [apply: dvd_mul_r | rewrite (comm mul c b)].
have [h Eh] : dvd c (gcd (c * a) (c * b))%P.
  by apply: dvd_gcd; apply: dvd_mul_l.
have ha : dvd h a.
  by apply: (dvd_cancel_l c) => //; rewrite -Eh; apply: gcd_dvdl.
have hb : dvd h b.
  by apply: (dvd_cancel_l c) => //; rewrite -Eh; apply: gcd_dvdr.
apply: (dvd_trans _ _ _ h1); rewrite Eh.
have := dvd_mul2 _ _ _ _ (dvd_refl c) (cop h ha hb).
by rewrite (right_id one mul).
Qed.

Lemma coprime_unique a b a' b' : b ≠ zero →
  (∀ u, dvd u a → dvd u b → dvd u one) →
  (∀ u, dvd u a' → dvd u b' → dvd u one) →
  (a * b' = a' * b)%P →
  (a' = a ∧ b' = b) ∨ (a' = (- a)%P ∧ b' = (- b)%P).
Proof.
move=> nb cop cop' E.
have [k Ek] : dvd b b'.
  apply: (euclid b a b') => [u ub ua|]; first exact: cop.
  by rewrite E; apply: dvd_mul_r.
have [k' Ek'] : dvd b' b.
  apply: (euclid b' a' b) => [u ub ua|]; first exact: cop'.
  by rewrite -E; apply: dvd_mul_r.
have hk : dvd k one.
  exists k'; apply: (mul_cancel_l b) => //.
  transitivity b; first ring.
  by rewrite {1}Ek' Ek; ring.
have Ea : a' = (a * k)%P.
  apply: (mul_cancel_l b) => //.
  transitivity (a' * b)%P; first ring.
  by rewrite -E Ek; ring.
case: (unit_pm1 k hk) => ek; rewrite Ea Ek ek; [left|right]; split; ring.
Qed.

Lemma cancel_norm p q : q ≠ zero →
  ∃ g a b, g ≠ zero ∧ p = (g * a)%P ∧ q = (g * b)%P ∧
    (∀ u, dvd u a → dvd u b → dvd u one) ∧
    cancel p q = if first_neg b then ((- a)%P, (- b)%P) else (a, b).
Proof.
move=> nq.
have ng : gcd p q ≠ zero.
  by move=> e; apply: nq; apply: dvd_zero_l; rewrite -e; apply: gcd_dvdr.
have Ep := div_spec p (gcd p q) ng (gcd_dvdl p q).
have Eq := div_spec q (gcd p q) ng (gcd_dvdr p q).
have cop : ∀ u, dvd u (div p (gcd p q)) → dvd u (div q (gcd p q)) →
    dvd u one.
  move=> u ua ub.
  have : dvd (gcd p q * u)%P (gcd p q * one)%P.
    rewrite (right_id one mul); apply: dvd_gcd.
    - by rewrite [X in dvd _ X]Ep; apply: dvd_mul2 => //; apply: dvd_refl.
    - by rewrite [X in dvd _ X]Eq; apply: dvd_mul2 => //; apply: dvd_refl.
  exact: dvd_cancel_l.
rewrite [cancel]unlock /=.
move: (gcd p q) ng Ep Eq cop => g ng Ep Eq cop.
move: (div p g) (div q g) Ep Eq cop => a b Ep Eq cop.
have hc : bool_decide ((g * a)%P = p ∧ (g * b)%P = q) = true.
  by apply: bool_decide_eq_true_2; split; symmetry.
by exists g, a, b; rewrite [cancel_with]unlock /= hc.
Qed.

Theorem cancel_canon p q p' q' : q ≠ zero → q' ≠ zero →
  cancel p q = cancel p' q' ↔ (p * q' = p' * q)%P.
Proof.
move=> nq nq'; split.
  have [g [Ep Eq]] := cancel_spec p q.
  have [g' [Ep' Eq']] := cancel_spec p' q'.
  move=> E; move: Ep Eq Ep' Eq'; rewrite -E.
  move: (cancel p q) => c Ep Eq Ep' Eq'.
  by rewrite Ep Eq Ep' Eq'; ring.
move=> E.
have [g [a [b [ng [Ep [Eq [cop ->]]]]]]] := cancel_norm p q nq.
have [g' [a' [b' [ng' [Ep' [Eq' [cop' ->]]]]]]] := cancel_norm p' q' nq'.
have nb : b ≠ zero.
  by move=> eb; apply: nq; rewrite Eq eb (right_absorb zero mul).
have E' : (a * b' = a' * b)%P.
  apply: (mul_cancel_l (g * g')%P); first exact: mul_neq0.
  transitivity (p * q')%P; first by rewrite Ep Eq'; ring.
  by rewrite E Ep' Eq; ring.
case: (coprime_unique a b a' b' nb cop cop' E') => [[-> ->]|[-> ->]] //.
by rewrite (first_neg_opp b nb) !opp_opp; case: (first_neg b).
Qed.

Lemma cancel_first_neg p q : q ≠ zero → first_neg (cancel p q).2 = false.
Proof.
move=> nq; have [g [a [b [ng [Ep [Eq [cop ->]]]]]]] := cancel_norm p q nq.
have nb : b ≠ zero.
  by move=> eb; apply: nq; rewrite Eq eb (right_absorb zero mul).
case E: (first_neg b) => /=; [by rewrite (first_neg_opp b nb) E | done].
Qed.

Lemma cancel_den_neq0 p q : q ≠ zero → (cancel p q).2 ≠ zero.
Proof.
move=> nq e; apply: nq; have [g [_ ->]] := cancel_spec p q.
by rewrite e (right_absorb zero mul).
Qed.

Lemma cancel_id p q : q ≠ zero → (∀ u, dvd u p → dvd u q → dvd u one) →
  first_neg q = false → cancel p q = (p, q).
Proof.
move=> nq cop fq.
have cop' : ∀ u, dvd u (cancel p q).1 → dvd u (cancel p q).2 → dvd u one.
  by move=> u; apply: cancel_coprime; right.
have fc := cancel_first_neg p q nq.
have [g [Ep Eq]] := cancel_spec p q.
move: (cancel p q) cop' fc Ep Eq => [a b] /= cop' fc Ep Eq.
have E : (p * b = a * q)%P by rewrite Ep Eq; ring.
case: (coprime_unique p q a b nq cop cop' E) => [[-> ->] //|[_ eb]].
by move: fc; rewrite eb (first_neg_opp q nq) fq.
Qed.

(** ** Divisors of monomials

    A variable is prime ([dvd_var_or_coprime]), so a divisor of a monomial is a
    monomial up to sign ([dvd_mono]). *)

Lemma coeff_const_mul c t m : coeff m (const c * t)%P = (c * coeff m t)%Z.
Proof.
induction c as [|c IH|c IH] using Z.peano_ind.
- by rewrite const_zero (left_absorb zero mul) coeff_zero.
- rewrite (_ : Z.succ c = c + 1)%Z; first lia.
  rewrite const_add const_one mul_add_l (left_id one mul) coeff_add IH; ring.
- rewrite (_ : Z.pred c = c + - (1))%Z; first lia.
  rewrite const_add const_opp const_one mul_add_l mul_opp_l (left_id one mul).
  rewrite coeff_add coeff_opp IH; ring.
Qed.

Lemma dvd_const_mono c m : dvd (const c) (mono m) → c = 1%Z ∨ c = (- (1))%Z.
Proof.
move=> [t Et]; apply: Z.divide_1_r; exists (coeff m t).
have := f_equal (coeff m) Et.
rewrite coeff_const_mul coeff_mono bool_decide_eq_true_2 //= => ->.
exact: Z.mul_comm.
Qed.

Lemma const_pm1 c :
  c = 1%Z ∨ c = (- (1))%Z → const c = one ∨ const c = (- one)%P.
Proof.
by case=> ->; [left; exact: const_one|right; rewrite const_opp const_one].
Qed.

Lemma var_neq0 x : var x ≠ zero.
Proof.
move=> /(f_equal (coeff {[+ x +]})).
by rewrite coeff_var coeff_zero bool_decide_eq_true_2.
Qed.

Lemma deg_var y x : deg y (var x) = if bool_decide (y = x) then 1 else 0.
Proof. by rewrite varE deg_mono MSet.count_singleton; case_bool_decide. Qed.

Lemma dvd_var x u :
  dvd u (var x) → (u = one ∨ u = (- one)%P) ∨ (u = var x ∨ u = (- var x)%P).
Proof.
move=> [t Et].
have nu : u ≠ zero.
  by move=> e; apply: (var_neq0 x); rewrite Et e (left_absorb zero mul).
have nt : t ≠ zero.
  by move=> e; apply: (var_neq0 x); rewrite Et e (right_absorb zero mul).
have D y : deg y u + deg y t = if bool_decide (y = x) then 1 else 0.
  by rewrite -deg_mul // -Et deg_var.
have const_of p : (∀ y, deg y p = 0) → p = const (coeff ∅ p).
  by move=> h; apply: over_nil => y _; exact: h.
case: (Nat.eq_dec (deg x u) 0) => dux.
- left; have Eu : u = const (coeff ∅ u).
    apply: const_of => y; case: (decide (y = x)) => [->|ne] //.
    by have := D y; rewrite bool_decide_eq_false_2 //; lia.
  rewrite Eu; apply: const_pm1; apply: (dvd_const_mono _ {[+ x +]}).
  by rewrite -Eu -varE; exists t.
- right; have Et' : t = const (coeff ∅ t).
    apply: const_of => y; case: (decide (y = x)) => [->|ne].
      by have := D x; rewrite bool_decide_eq_true_2 //; lia.
    by have := D y; rewrite bool_decide_eq_false_2 //; lia.
  have : dvd (const (coeff ∅ t)) (mono {[+ x +]}).
    by exists u; rewrite -varE Et {1}Et'; ring.
  move=> /dvd_const_mono hc; move: Et; rewrite Et'.
  by case: hc => ->; rewrite ?const_opp const_one => ->; [left|right]; ring.
Qed.

Lemma dvd_var_or_coprime x r :
  dvd (var x) r ∨ (∀ u, dvd u (var x) → dvd u r → dvd u one).
Proof.
case: (decide (r = (var x * div r (var x))%P)) => [e|ne].
  by left; exists (div r (var x)).
right=> u ux ur; case: (dvd_var _ _ ux) => [[->|->]|[ex|ex]].
- exact: dvd_refl.
- by exists (- one)%P; ring.
- by exfalso; apply: ne; apply: div_spec; [exact: var_neq0|rewrite -ex].
- exfalso; apply: ne; apply: div_spec; first exact: var_neq0.
  rewrite -(opp_opp (var x)) -ex; apply: (dvd_trans (- u)%P u r) => //.
  by exists (- one)%P; ring.
Qed.

Lemma dvd_mono r m :
  dvd r (mono m) → ∃ n, n ⊆ m ∧ (r = mono n ∨ r = (- mono n)%P).
Proof.
move: r; elim/(MSet.mset_ind (T := T)): m => [|x m IH] r.
  rewrite -oneE => /unit_pm1 [->|->]; exists ∅; (split; first done);
    rewrite oneE; [by left|by right].
rewrite -mul_mono -varE => hr.
case: (dvd_var_or_coprime x r) => [[r1 Er]|cop].
- subst r; have : dvd r1 (mono m) by apply: (dvd_cancel_l (var x)) => //;
    exact: var_neq0.
  move=> /IH [n [nm E]]; exists ({[+ x +]} ⊎ n); split.
    apply/MSet.subseteq_count => y; rewrite !MSet.count_disj_union.
    by have /MSet.subseteq_count := nm; move=> /(_ y); lia.
  by case: E => ->; [left|right]; rewrite varE ?mul_opp_r mul_mono.
- have cop' : ∀ u, dvd u r → dvd u (var x) → dvd u one.
    by move=> u ur ux; exact: cop u ux ur.
  have /IH [n [nm E]] := euclid r (var x) (mono m) cop' hr.
  exists n; split=> //; apply/MSet.subseteq_count => y.
  rewrite MSet.count_disj_union.
  by have /MSet.subseteq_count := nm; move=> /(_ y); lia.
Qed.

(** ** Monomial content

    [content p] is the largest monomial dividing [p] ([dvd_mono_content]) and
    [unit_part p] its cofactor, which no variable divides
    ([content_unit_part]).  Since variables are prime, contents multiply
    ([content_mul]). *)

Definition meet m n : MSet.mset T := m ∖ (m ∖ n).

lock Definition content p : MSet.mset T :=
  match elements (car p) with
  | [] => ∅
  | m :: ms => foldr meet m ms
  end.

lock Definition unmono m p : poly := mk (SMS.map (λ n, n ∖ m) (car p)).

lock Definition unit_part p : poly := unmono (content p) p.

Lemma contentE p : content p =
  match elements (car p) with
  | [] => ∅
  | m :: ms => foldr meet m ms
  end.
Proof. by rewrite [content]unlock. Qed.

Lemma car_unmono m p : car (unmono m p) = SMS.map (λ n, n ∖ m) (car p).
Proof. by rewrite [unmono]unlock. Qed.

Lemma unit_partE p : unit_part p = unmono (content p) p.
Proof. by rewrite [unit_part]unlock. Qed.

Lemma mono_neq0 m : mono m ≠ zero.
Proof.
move=> /(f_equal (coeff m)); rewrite coeff_mono coeff_zero.
by rewrite bool_decide_eq_true_2.
Qed.

Lemma count_meet x m n :
  MSet.count x (meet m n) = Nat.min (MSet.count x m) (MSet.count x n).
Proof. rewrite /meet !MSet.count_difference; lia. Qed.

Lemma foldr_meet_le x m ms n :
  n ∈ m :: ms → MSet.count x (foldr meet m ms) ≤ MSet.count x n.
Proof.
elim: ms n => [|m' ms IH] n /=; first by move=> /list_elem_of_singleton ->.
rewrite count_meet => /elem_of_cons [->|/elem_of_cons [->|h]].
- have := IH _ (list_elem_of_here _ _); lia.
- lia.
- have := IH _ (list_elem_of_further _ _ _ h); lia.
Qed.

Lemma foldr_meet_ge x m ms k :
  (∀ n, n ∈ m :: ms → k ≤ MSet.count x n) →
  k ≤ MSet.count x (foldr meet m ms).
Proof.
elim: ms => [|m' ms IH] /= h; first by apply: h; left.
rewrite count_meet; apply: Nat.min_glb; first by apply: h; right; left.
apply: IH => n /elem_of_cons [->|hn]; apply: h; first by left.
by right; right.
Qed.

Lemma content_sub p n : n ∈ car p → content p ⊆ n.
Proof.
move=> hn; apply/MSet.subseteq_count => x; move: hn.
rewrite contentE -SMS.elem_of_elements; case: (elements (car p)) => [|m ms].
  by move=> /elem_of_nil.
exact: foldr_meet_le.
Qed.

Lemma sub_content p m : p ≠ zero → (∀ n, n ∈ car p → m ⊆ n) → m ⊆ content p.
Proof.
move=> np h; apply/MSet.subseteq_count => x; rewrite contentE.
case E: (elements (car p)) => [|m0 ms].
  by case: np; apply: car_inj; rewrite car_zero; exact: SMS.elements_empty_inv.
apply: foldr_meet_ge => n hn.
have /MSet.subseteq_count := h n ltac:(by rewrite -SMS.elem_of_elements E).
by apply.
Qed.

Lemma unmonoK m p : (∀ n, n ∈ car p → m ⊆ n) → (mono m * unmono m p)%P = p.
Proof.
move=> h; apply: car_inj.
rewrite car_mul_mono car_unmono SMS.map_map.
apply: SMS.map_id_ext => n hn; apply: MSet.count_inj => x.
rewrite MSet.count_disj_union MSet.count_difference.
by have /MSet.subseteq_count := h n hn; move=> /(_ x); lia.
Qed.

Lemma dvd_mono_iff m p : dvd (mono m) p ↔ ∀ n, n ∈ car p → m ⊆ n.
Proof.
split; last by move=> h; exists (unmono m p); rewrite unmonoK.
move=> [r ->] n; rewrite car_mul_mono.
move=> /SMS.elem_of_map [n' [-> _]].
apply/MSet.subseteq_count => x; rewrite MSet.count_disj_union; lia.
Qed.

Lemma dvd_mono_content m p : p ≠ zero → dvd (mono m) p ↔ m ⊆ content p.
Proof.
move=> np; rewrite dvd_mono_iff; split; first exact: sub_content.
by move=> mc n hn; transitivity (content p) => //; exact: content_sub.
Qed.

Lemma content_unitK p : (mono (content p) * unit_part p)%P = p.
Proof. by rewrite unit_partE; apply: unmonoK => n; exact: content_sub. Qed.

Lemma unit_part_neq0 p : p ≠ zero → unit_part p ≠ zero.
Proof.
move=> np e; apply: np; rewrite -(content_unitK p) e.
exact: (right_absorb zero mul).
Qed.

Lemma content_zero : content zero = ∅.
Proof. by rewrite contentE car_zero SMS.elements_empty. Qed.

Lemma unit_part_zero : unit_part zero = zero.
Proof.
by apply: car_inj; rewrite unit_partE car_unmono car_zero SMS.map_empty.
Qed.

Lemma var_dvd_content x p : p ≠ zero → dvd (var x) p ↔ x ∈ content p.
Proof.
move=> np; rewrite varE dvd_mono_content // MSet.elem_of_count.
rewrite MSet.subseteq_count; split.
  by move=> /(_ x); rewrite MSet.count_singleton bool_decide_eq_true_2 //; lia.
move=> h y; rewrite MSet.count_singleton.
by case: bool_decide_reflect => [->|_]; lia.
Qed.

Lemma content_unit_part p : content (unit_part p) = ∅.
Proof.
case: (decide (p = zero)) => [->|np].
  by rewrite unit_part_zero content_zero.
have nu := unit_part_neq0 _ np.
apply: MSet.count_inj => x; rewrite MSet.count_empty.
case: (decide (x ∈ content (unit_part p))) => h; last first.
  by move: h; rewrite MSet.elem_of_count; lia.
exfalso; move/(var_dvd_content _ _ nu): h => h.
have : dvd (mono ({[+ x +]} ⊎ content p)) p.
  rewrite -mul_mono -{2}(content_unitK p) (comm mul (mono {[+ x +]})).
  by apply: dvd_mul2; [exact: dvd_refl|rewrite -varE; exact: h].
move=> /(dvd_mono_content _ _ np) /MSet.subseteq_count /(_ x).
rewrite MSet.count_disj_union MSet.count_singleton bool_decide_eq_true_2 //.
lia.
Qed.

Lemma content_mul p q : p ≠ zero → q ≠ zero →
  content (p * q)%P = content p ⊎ content q.
Proof.
move=> np nq; have npq := mul_neq0 _ _ np nq.
set c := content p ⊎ content q.
have E : (p * q)%P = (mono c * (unit_part p * unit_part q))%P.
  rewrite /c -mul_mono -{1}(content_unitK p) -{1}(content_unitK q); ring.
have cc : c ⊆ content (p * q)%P.
  apply/(dvd_mono_content _ _ npq); rewrite E; exact: dvd_mul_l.
apply: MSet.count_inj => x; apply: Nat.le_antisymm; last first.
  by have /MSet.subseteq_count := cc; apply.
case: (Nat.le_gt_cases (MSet.count x (content (p * q)%P)) (MSet.count x c))
  => // gt.
exfalso.
have h1 : dvd (mono ({[+ x +]} ⊎ c)) (p * q)%P.
  apply/(dvd_mono_content _ _ npq)/MSet.subseteq_count => y.
  rewrite MSet.count_disj_union MSet.count_singleton.
  case: bool_decide_reflect => [->|_]; first lia.
  by have /MSet.subseteq_count := cc; move=> /(_ y); lia.
have h2 : dvd (var x) (unit_part p * unit_part q)%P.
  apply: (dvd_cancel_l (mono c)); first exact: mono_neq0.
  by rewrite -E (comm mul (mono c)) varE mul_mono.
have nup := unit_part_neq0 _ np; have nuq := unit_part_neq0 _ nq.
case: (dvd_var_or_coprime x (unit_part p)) => [hp|cop].
  move/(var_dvd_content _ _ nup): hp; rewrite content_unit_part.
  exact: MSet.not_elem_of_empty.
move/(var_dvd_content _ _ nuq): (euclid _ _ _ cop h2).
rewrite content_unit_part; exact: MSet.not_elem_of_empty.
Qed.

Lemma unit_part_mul p q : p ≠ zero → q ≠ zero →
  unit_part (p * q)%P = (unit_part p * unit_part q)%P.
Proof.
move=> np nq.
apply: (mul_cancel_l (mono (content (p * q)%P))); first exact: mono_neq0.
rewrite content_unitK content_mul // -mul_mono.
rewrite -{1}(content_unitK p) -{1}(content_unitK q); ring.
Qed.

Lemma content_opp p : content (- p)%P = content p.
Proof.
case: (decide (p = zero)) => [->|np].
  by rewrite (_ : (- zero)%P = zero) //; ring.
have nop : (- p)%P ≠ zero.
  by move=> e; apply: np; rewrite -(opp_opp p) e; ring.
apply: MSet.count_inj => x; apply: Nat.le_antisymm.
- have : dvd (mono (content (- p)%P)) p.
    rewrite -{2}(opp_opp p); apply: dvd_opp.
    by apply/(dvd_mono_content _ _ nop).
  by move=> /(dvd_mono_content _ _ np) /MSet.subseteq_count /(_ x).
- have : dvd (mono (content p)) (- p)%P.
    by apply: dvd_opp; apply/(dvd_mono_content _ _ np).
  by move=> /(dvd_mono_content _ _ nop) /MSet.subseteq_count /(_ x).
Qed.

Lemma unit_part_opp p : unit_part (- p)%P = (- unit_part p)%P.
Proof.
apply: (mul_cancel_l (mono (content p))); first exact: mono_neq0.
rewrite -{1}(content_opp p) content_unitK -{1}(content_unitK p); ring.
Qed.

Lemma content_mono m : content (mono m) = m.
Proof. by rewrite contentE car_mono SMS.elements_singleton. Qed.

Lemma unit_part_mono m : unit_part (mono m) = one.
Proof.
apply: (mul_cancel_l (mono m)); first exact: mono_neq0.
by have := content_unitK (mono m); rewrite content_mono => ->; ring.
Qed.

Lemma content_unique m u p : p = (mono m * u)%P → u ≠ zero →
  content u = ∅ → content p = m ∧ unit_part p = u.
Proof.
move=> -> nu cu.
have cm : content (mono m * u)%P = m.
  rewrite content_mul ?content_mono ?cu ?(right_id ∅ (⊎)) //.
  exact: mono_neq0.
split=> //.
apply: (mul_cancel_l (mono m)); first exact: mono_neq0.
by rewrite -{1}cm content_unitK.
Qed.

End Gcd.

End PolyGcd.
