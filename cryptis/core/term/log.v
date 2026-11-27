(** Logarithms of group elements

    [log k t] is the exponent of the base [k] in [t], as an exponent term.
    Logarithms turn group products into sums and powers into products
    ([log_TGMul2], [log_TExp]), and they determine a term ([log_inj]).
    Coefficients of an atom that they avoid can be compared ([frac_lin]). *)

From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From Stdlib Require Import ZArith Lia Field.
From cryptis.lib Require Import fmap mset sms poly poly_gcd frac.
From cryptis.core Require Export pre_term.
From cryptis.core.term Require Import base algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Types (t u v e f : term).

Section Log.

Add Ring log_ring : (Frac.frac_ring_theory (T := PreTerm.pre_term)).
Add Field log_field : (Frac.frac_field_theory (T := PreTerm.pre_term)).
Add Field tlog_field : (Frac.frac_field_theory (T := term)).

Lemma wf_mod_of_frac_dh_map t k :
  PreTerm.wf (PreTerm.mod_of_frac (dh_map t !!! k)).
Proof.
case: (decide (dh_map t !!! k = Frac.zero)) => [->|nz].
  by apply: PreTerm.wf_mod_of_frac; exact: Frac.all_vars_zero.
have [_ [_ ar]] := PreTerm.wf_dh_map _ (wf_unfold_term t) k nz.
exact: PreTerm.wf_mod_of_frac.
Qed.

(** The exponent of the base [k] in [t]. *)
Definition log k t : term :=
  fold_term (PreTerm.mod_of_frac (dh_map t !!! unfold_term k)).

Lemma pre_frac_log k t : pre_frac (log k t) = dh_map t !!! unfold_term k.
Proof.
rewrite /log fold_termK; last exact: wf_mod_of_frac_dh_map.
case: (decide (dh_map t !!! unfold_term k = Frac.zero)) => [->|nz].
  by apply: PreTerm.frac_of_mod_of_frac; exact: Frac.all_vars_zero.
have [_ [_ ar]] := PreTerm.wf_dh_map _ (wf_unfold_term t) _ nz.
exact: PreTerm.frac_of_mod_of_frac.
Qed.

Lemma log_eq k t u : dh_map t !!! unfold_term k = pre_frac u → log k t = u.
Proof.
move=> e; apply: unfold_term_inj.
rewrite -[unfold_term u]PreTerm.mod_of_frac_frac_of; last exact: wf_unfold_term.
by rewrite -e /log fold_termK //; exact: wf_mod_of_frac_dh_map.
Qed.

Lemma log_TGMul2 k t1 t2 :
  log k (TGMul {[+ t1; t2 +]}) = TSum {[+ log k t1; log k t2 +]}.
Proof.
apply: log_eq; rewrite dh_map_TGMul -unfold_frac_of frac_of_TSum.
rewrite !Frac.ssum_disj_union !Frac.ssum_singleton.
by rewrite (Frac.map_add _ unfold_term_inj) !unfold_frac_of !pre_frac_log.
Qed.

Lemma log_TExp k t e : log k (TExp t e) = TMul {[+ log k t; e +]}.
Proof.
apply: log_eq; rewrite dh_map_TExp -unfold_frac_of frac_of_TMul2.
by rewrite (Frac.map_mul _ unfold_term_inj) !unfold_frac_of pre_frac_log.
Qed.

Lemma log_unit k : log k (TGMul ∅) = TSum ∅.
Proof.
apply: log_eq; rewrite dh_map_TGMul_empty -unfold_frac_of frac_of_TSum_empty.
by rewrite Frac.map_zero.
Qed.

Lemma log_atom k u :
  negb (is_exp u) → negb (is_gmul u) →
  log k u = if bool_decide (u = k) then TMul ∅ else TSum ∅.
Proof.
move=> uX uG; apply: log_eq.
rewrite (dh_map_Ngmul uG) (base_expN uX) (expo_frac_Nexp uX)
  FMap.lookup_singleton.
case: (bool_decide_reflect (u = k)) => [->|ne].
  rewrite bool_decide_eq_true_2 // -unfold_frac_of frac_of_TMul_empty.
  by rewrite Frac.map_one.
rewrite bool_decide_eq_false_2; last by move=> /unfold_term_inj e; apply: ne.
by rewrite -unfold_frac_of frac_of_TSum_empty Frac.map_zero.
Qed.

Lemma log_TExp_atom k u e :
  negb (is_exp u) → negb (is_gmul u) →
  log k (TExp u e) = if bool_decide (u = k) then e else TSum ∅.
Proof.
move=> uX uG; rewrite log_TExp log_atom //.
case: bool_decide; first exact: TMul_unit_l.
apply: frac_of_inj.
by rewrite frac_of_TMul2 frac_of_TSum_empty Frac.mul_zero_l.
Qed.

Lemma log_inj t1 t2 : (∀ k, log k t1 = log k t2) → t1 = t2.
Proof.
move=> e; apply: dh_map_inj; apply/FMap.fmap_eq => k.
case: (decide (PreTerm.wf k)) => [wk|nk].
  by rewrite -(fold_termK _ wk) -!pre_frac_log e.
have z t : dh_map t !!! k = Frac.zero.
  case: (decide (dh_map t !!! k = Frac.zero)) => // nz; case: nk.
  by case: (PreTerm.wf_dh_map _ (wf_unfold_term t) _ nz).
by rewrite !z.
Qed.

Lemma log_eq0 t : (∀ k, log k t = TSum ∅) → t = TGMul ∅.
Proof. by move=> e; apply: log_inj => k; rewrite e log_unit. Qed.

Lemma TExp_TSum2 t a b :
  TExp t (TSum {[+ a; b +]}) = TGMul {[+ TExp t a; TExp t b +]}.
Proof.
apply: log_inj => k; rewrite log_TGMul2 !log_TExp; apply: frac_of_inj.
rewrite !frac_of_TSum !Frac.ssum_disj_union !Frac.ssum_singleton.
by rewrite !frac_of_TMul2 frac_of_TSum Frac.ssum_disj_union
  !Frac.ssum_singleton; field.
Qed.

(** Comparing the coefficients of an atom that the coefficients avoid. *)
Lemma frac_lin h c0 c1 d0 d1 :
  negb (is_mod h) →
  h ∉ atoms c0 → h ∉ atoms c1 → h ∉ atoms d0 → h ∉ atoms d1 →
  Frac.add (frac_of c0) (Frac.mul (frac_of c1) (frac_of h)) =
  Frac.add (frac_of d0) (Frac.mul (frac_of d1) (frac_of h)) →
  c0 = d0 ∧ c1 = d1.
Proof.
move=> nh h0 h1 h2 h3.
set y := unfold_term h.
have I c : h ∉ atoms c → Frac.all_vars (λ z, z ≠ y) (pre_frac c).
  move=> hc; apply/Frac.all_vars_iff => z zc ez; apply: hc.
  apply/elem_of_atoms; exists z; split; last exact: zc.
  by rewrite ez /y unfold_termK.
have eH : pre_frac h = Frac.of_poly (Poly.var y).
  by rewrite -Frac.varE; apply: PreTerm.frac_of_Nmod; rewrite -is_mod_unfold.
have inj c d : pre_frac c = pre_frac d → c = d.
  move=> e; apply: frac_of_inj.
  apply: (Frac.map_inj unfold_term unfold_term_inj).
  by rewrite !unfold_frac_of.
move/(f_equal (Frac.map unfold_term)).
rewrite !(Frac.map_add _ unfold_term_inj) !(Frac.map_mul _ unfold_term_inj).
rewrite !unfold_frac_of eH.
set Y := Frac.of_poly (Poly.var y) => E.
case: (decide (pre_frac c1 = pre_frac d1)) => [e1|n1].
  split; last exact: inj.
  apply: inj.
  transitivity (Frac.sub (Frac.add (pre_frac c0) (Frac.mul (pre_frac c1) Y))
                         (Frac.mul (pre_frac c1) Y)); first ring.
  by rewrite E e1; ring.
exfalso.
have nz : Frac.sub (pre_frac c1) (pre_frac d1) ≠ Frac.zero.
  move=> e; apply: n1.
  transitivity (Frac.add (Frac.sub (pre_frac c1) (pre_frac d1)) (pre_frac d1));
    first ring.
  by rewrite e; ring.
have e2 : Frac.mul (Frac.sub (pre_frac c1) (pre_frac d1)) Y =
          Frac.sub (pre_frac d0) (pre_frac c0).
  transitivity (Frac.sub (Frac.add (pre_frac c0) (Frac.mul (pre_frac c1) Y))
                  (Frac.add (pre_frac c0) (Frac.mul (pre_frac d1) Y)));
                    first ring.
  by rewrite E; ring.
have eY : Y = Frac.div (Frac.sub (pre_frac d0) (pre_frac c0))
                       (Frac.sub (pre_frac c1) (pre_frac d1)).
  by rewrite -e2; field.
have : Frac.all_vars (λ z, z ≠ y) Y.
  rewrite eY; apply: Frac.all_vars_div; apply: Frac.all_vars_sub;
    exact: I.
move=> /(_ {[+ y +]} y) H; apply: H => //.
- by left; rewrite /Y Frac.car_num_var; apply/SMS.elem_of_singleton.
- exact/MSet.elem_of_singleton.
Qed.

End Log.

Lemma TExp_unit_inv t e :
  frac_of e ≠ Frac.zero → TExp t e = TGMul ∅ → t = TGMul ∅.
Proof.
move=> ne et; apply: log_eq0 => b; apply: frac_of_eq0.
move/(f_equal (λ u, frac_of (log b u))): et.
rewrite /= log_unit log_TExp frac_of_TMul2 frac_of_TSum_empty => e'.
exact: Frac.mul_eq0_l _ _ e' ne.
Qed.
