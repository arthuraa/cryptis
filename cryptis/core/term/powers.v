From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From Stdlib Require Import ZArith Lia Field.
From cryptis.lib Require Import fmap mset sms poly poly_gcd frac.
From cryptis.core Require Export pre_term.
From cryptis.core.term Require Import base algebra tsize.
From cryptis.lib Require Import poly_restrict.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Powers and their group factors.

   A power [u] (a term that is not a group product) has a logarithm
   [expo_frac u] whose numerator is a monomial.  The unit part of its
   denominator, as an exponent, is [den_unit u], and
   [laurent_part u = TExp u (den_unit u)] is its Laurent part: a power whose
   logarithm is a Laurent monomial ([laurent_part_spec],
   [laurent_expo_laurent_part]).  Stripping a signed atom other than
   [TInv (den_unit u)] keeps the unit part ([strip_den_unit]) and the signed
   atom of the Laurent part ([satoms_laurent_part]), and stripping any signed
   atom keeps the positive count of every other atom ([count_strip]).

   The group factors of [t] are the powers [k ^ (ν / D)] for the monomials
   [ν] of the numerator of the logarithm at [k], whose denominator is [D]
   ([gfactor_of], [elem_of_gfactors_log], [gfactors_of_log]).  Their unit
   parts are the unit part of [D], and their Laurent parts are
   [k ^ (ν / C)] for the monomial content [C] of [D] ([gfactor_of_spec]).
   Two Laurent powers of [k] whose monomials have the same secret part
   ([PolyRestrict.secret_part]) differ by a Laurent monomial over the public
   atoms and their denominators ([laurent_shift]). *)

Implicit Types (t u v e f : term).

Definition den_unit u : term :=
  fold_term (PreTerm.mod_of_frac
    (Frac.of_poly (PolyGcd.unit_part (Frac.den (expo_frac u))))).

Definition laurent_part u := TExp u (den_unit u).

Lemma expo_frac_atoms u :
  PreTerm.wf_frac (expo_frac u).
Proof.
exact: PreTerm.frac_of_atoms (PreTerm.wf_expo _ (wf_unfold_term u)).
Qed.

Lemma expo_frac_mono_num u : negb (is_gmul u) → Frac.mono_num (expo_frac u).
Proof.
rewrite is_gmul_unfold => Nu.
exact: PreTerm.mono_num_expo (wf_unfold_term u) Nu.
Qed.

Lemma expo_frac_TExp u e :
  negb (is_gmul u) → Frac.mono_num (Frac.mul (expo_frac u) (pre_frac e)) →
  negb (is_gmul (TExp u e)) ∧ base (TExp u e) = base u ∧
  expo_frac (TExp u e) = Frac.mul (expo_frac u) (pre_frac e).
Proof.
move=> Nu mr; have wu := wf_unfold_term u.
have Nu' : negb (PreTerm.is_gmul (unfold_term u)) by rewrite -is_gmul_unfold.
have nz : Frac.mul (expo_frac u) (pre_frac e) ≠ Frac.zero
  by exact: Frac.mono_num_neq0.
have E : unfold_term (TExp u e) =
         PreTerm.mk_exp (PreTerm.base (unfold_term u))
                        (Frac.mul (expo_frac u) (pre_frac e)).
  by rewrite unfold_TExp /PreTerm.exp (PreTerm.exp_frac_Ngmul _ _ wu Nu' nz).
have gb := PreTerm.base_Ndh _ wu Nu'.
have ar : PreTerm.wf_frac
            (Frac.mul (expo_frac u) (pre_frac e)).
  apply: Frac.all_vars_mul; first exact: expo_frac_atoms.
  exact: PreTerm.frac_of_atoms (wf_unfold_term e).
have [N [B X]] :=
  PreTerm.mk_exp_mono_num _ _ gb ar mr.
split; first by rewrite is_gmul_unfold E.
split.
  apply: unfold_term_inj; rewrite !unfold_base E B.
  by [].
by rewrite /expo_frac E X; apply: PreTerm.frac_of_mod_of_frac.
Qed.

Lemma count_expo u y M :
  Frac.num (expo_frac u) = Poly.mono M →
  count y (expo u) =
  (Z.of_nat (MSet.count (unfold_term y) M) -
   Z.of_nat (MSet.count (unfold_term y)
     (PolyGcd.content (Frac.den (expo_frac u)) ⊎
      PreTerm.unit_factors (Frac.den (expo_frac u)))))%Z.
Proof.
move=> eM; rewrite count_unfold unfold_expo (PreTerm.factors_mono_num _ _ eM).
exact: SMS.count_make.
Qed.

Lemma atoms_unit_part u :
  PreTerm.wf_frac
    (Frac.of_poly (PolyGcd.unit_part (Frac.den (expo_frac u)))).
Proof.
move=> m x; rewrite Frac.num_of_poly Frac.den_of_poly Poly.oneE Poly.car_mono.
case=> [mU|/SMS.elem_of_singleton ->] xm; last first.
  by case: (MSet.not_elem_of_empty _ xm).
have [m' [m'D xm']] := PolyGcd.elem_of_unit_part x _ m mU xm.
exact: expo_frac_atoms m' x (or_intror m'D) xm'.
Qed.

Lemma pre_frac_den_unit u :
  pre_frac (den_unit u) = Frac.of_poly
    (PolyGcd.unit_part (Frac.den (expo_frac u))).
Proof.
rewrite /den_unit fold_termK;
  last exact: PreTerm.wf_mod_of_frac (@atoms_unit_part u).
exact: PreTerm.frac_of_mod_of_frac (@atoms_unit_part u).
Qed.

Lemma den_unit_frac_neq0 u : frac_of (den_unit u) ≠ Frac.zero.
Proof.
move=> e; have := pre_frac_den_unit u; rewrite -unfold_frac_of e Frac.map_zero.
move=> /(f_equal Frac.num); rewrite Frac.num_zero Frac.num_of_poly => E.
by apply: (PolyGcd.unit_part_neq0 _ (Frac.den_neq0 (expo_frac u))); rewrite -E.
Qed.

Lemma den_unit_one u :
  PolyGcd.unit_part (Frac.den (expo_frac u)) = Poly.one → den_unit u = TMul ∅.
Proof.
move=> E; apply: frac_of_inj.
apply: (Frac.map_inj unfold_term unfold_term_inj).
by rewrite !unfold_frac_of pre_frac_den_unit E -Frac.oneE -unfold_frac_of
  frac_of_TMul_empty Frac.map_one.
Qed.

Lemma den_unit_neg u :
  negb (is_gmul u) → PolyGcd.unit_part (Frac.den (expo_frac u)) ≠ Poly.one →
  is_exp u ∧ den_unit u ∈ SMS.neg (exps u) ∧ is_mod (den_unit u).
Proof.
move=> Nu U1.
have [M eM] := expo_frac_mono_num Nu.
have uU : unfold_term (den_unit u) ∈ PreTerm.unit_factors
  (Frac.den (expo_frac u)).
  rewrite /PreTerm.unit_factors bool_decide_eq_false_2 //.
  rewrite /den_unit fold_termK;
    last exact: PreTerm.wf_mod_of_frac (@atoms_unit_part u).
  exact/MSet.elem_of_singleton.
have Mu : is_mod (den_unit u)
  by rewrite is_mod_unfold; exact: PreTerm.unit_factors_mod uU.
split.
  case Ex: (is_exp u) => //; exfalso; apply: U1.
  rewrite expo_frac_Nexp ?Ex // Frac.den_one Poly.oneE PolyGcd.unit_part_mono.
  by rewrite Poly.oneE.
split=> //; apply/count_lt0; rewrite (count_expo _ eM).
have c0 : MSet.count (unfold_term (den_unit u)) M = 0.
  apply/MSet.not_elem_of_count => uM.
  have mM : M ∈ Poly.car (Frac.num (expo_frac u)).
    by rewrite eM Poly.car_mono; exact/SMS.elem_of_singleton.
  have /andb_True [_] := @expo_frac_atoms u M _ (or_introl mM) uM.
  move: Mu; rewrite is_mod_unfold.
  by case: (PreTerm.is_mod (unfold_term (den_unit u))).
have c1 : 0 < MSet.count (unfold_term (den_unit u))
                (PolyGcd.content (Frac.den (expo_frac u)) ⊎
                 PreTerm.unit_factors (Frac.den (expo_frac u))).
  by apply/MSet.elem_of_count; apply/MSet.elem_of_disj_union; right.
lia.
Qed.

Lemma count_unit_factors_den_unit u y :
  y ≠ den_unit u →
  MSet.count (unfold_term y) (PreTerm.unit_factors (Frac.den (expo_frac u))) =
    0.
Proof.
move=> ne; apply/MSet.not_elem_of_count; rewrite /PreTerm.unit_factors.
case: bool_decide_reflect => _; first exact: MSet.not_elem_of_empty.
move=> /MSet.elem_of_singleton e; apply: ne; apply: unfold_term_inj.
rewrite e /den_unit fold_termK //.
exact: PreTerm.wf_mod_of_frac (@atoms_unit_part u).
Qed.

Lemma laurent_part_spec u :
  negb (is_gmul u) →
  negb (is_gmul (laurent_part u)) ∧ base (laurent_part u) = base u ∧
  Frac.num (expo_frac (laurent_part u)) = Frac.num (expo_frac u) ∧
  Frac.den (expo_frac (laurent_part u)) =
    Poly.mono (PolyGcd.content (Frac.den (expo_frac u))).
Proof.
move=> Nu; have [M eM] := expo_frac_mono_num Nu.
have [en ed] := Frac.mul_unit_part_canon (expo_frac u) M eM.
have mr : Frac.mono_num (Frac.mul (expo_frac u) (pre_frac (den_unit u))).
  by exists M; rewrite pre_frac_den_unit en.
have [N [B L]] := expo_frac_TExp Nu mr.
rewrite /laurent_part L pre_frac_den_unit en ed eM.
by do !split.
Qed.

Lemma laurent_expo_laurent_part u :
  negb (is_gmul u) → laurent (expo (laurent_part u)).
Proof.
move=> Nu; have [_ [_ [en ed]]] := laurent_part_spec Nu.
have [M eM] := expo_frac_mono_num Nu.
apply/laurent_unfold; rewrite unfold_expo.
apply/(PreTerm.laurent_frac_of _ (PreTerm.wf_expo _ (wf_unfold_term _))).
rewrite -/(expo_frac (laurent_part u)).
by exists M, (PolyGcd.content (Frac.den (expo_frac u))); rewrite en ed eM.
Qed.

Lemma count_expo_laurent_part u y :
  negb (is_gmul u) →
  count y (expo (laurent_part u)) =
  (count y (expo u) +
   Z.of_nat (MSet.count (unfold_term y)
               (PreTerm.unit_factors (Frac.den (expo_frac u)))))%Z.
Proof.
move=> Nu; have [M eM] := expo_frac_mono_num Nu.
have [_ [_ [en ed]]] := laurent_part_spec Nu.
rewrite (count_expo _ eM) (@count_expo (laurent_part u) y M);
  last by rewrite en.
rewrite ed PolyGcd.content_mono PreTerm.unit_factors_mono (right_id ∅ (⊎)).
rewrite MSet.count_disj_union; lia.
Qed.

Lemma elem_of_satoms_count f e :
  f ∈ satoms (factors e) ↔
  (0 < count f e)%Z ∨ ∃ x, f = TInv x ∧ (count x e < 0)%Z.
Proof.
rewrite /satoms elem_of_app list_elem_of_fmap MSet.elem_of_elements -count_gt0.
split; case=> [h|[x [-> h]]]; [left|right|left|right] => //.
- by exists x; split=> //; apply/count_lt0; apply/MSet.elem_of_elements.
- by exists x; split=> //; apply/MSet.elem_of_elements; apply/count_lt0.
Qed.

Lemma satoms_laurent_part u f :
  negb (is_gmul u) → f ∈ satoms (exps u) → f ≠ TInv (den_unit u) →
  f ∈ satoms (exps (laurent_part u)).
Proof.
move=> Nu; rewrite /exps !elem_of_satoms_count.
case=> [h|[x [-> h]]] nf.
  by left; rewrite count_expo_laurent_part //; lia.
right; exists x; split=> //.
have ne : x ≠ den_unit u by move=> e; apply: nf; rewrite e.
rewrite count_expo_laurent_part // (count_unit_factors_den_unit ne); lia.
Qed.

Lemma laurent_partK u : TExp (laurent_part u) (TInv (den_unit u)) = u.
Proof. rewrite /laurent_part; apply: TExpK; exact: den_unit_frac_neq0. Qed.

Lemma strip_den_unit u f :
  negb (is_gmul u) → f ∈ satoms (exps u) → f ≠ TInv (den_unit u) →
  negb (is_gmul (TExp u (TInv f))) ∧
  PolyGcd.unit_part (Frac.den (expo_frac (TExp u (TInv f)))) =
  PolyGcd.unit_part (Frac.den (expo_frac u)).
Proof.
move=> Nu; have [M eM] := expo_frac_mono_num Nu.
have A := @expo_frac_atoms u.
rewrite /exps elem_of_satoms_count.
case=> [h|[x [-> h]]] nf.
- move: h; rewrite (count_expo _ eM) => h.
  have fM : unfold_term f ∈ M by apply/MSet.elem_of_count; lia.
  have [wf nf'] : PreTerm.wf (unfold_term f) ∧
                  negb (PreTerm.is_mod (unfold_term f)).
    apply/andb_True; apply: (A M) fM; left.
    by rewrite eM Poly.car_mono; apply/SMS.elem_of_singleton.
  have ef : pre_frac (TInv f) = Frac.inv (Frac.var (unfold_term f)).
    by rewrite pre_frac_TInv PreTerm.frac_of_Nmod.
  have [en ed] := Frac.mul_inv_var_canon (expo_frac u) M (unfold_term f) eM fM.
  have mr : Frac.mono_num (Frac.mul (expo_frac u) (pre_frac (TInv f))).
    by exists (M ∖ {[+ unfold_term f +]}); rewrite ef en.
  have [N [_ L]] := expo_frac_TExp Nu mr.
  by split=> //; rewrite L ef ed.
- have ne : x ≠ den_unit u by move=> e; apply: nf; rewrite e.
  move: h; rewrite (count_expo _ eM) MSet.count_disj_union.
  rewrite (count_unit_factors_den_unit ne) => h.
  have xc : unfold_term x ∈ PolyGcd.content (Frac.den (expo_frac u)).
    by apply/MSet.elem_of_count; lia.
  have [n [nD xn]] := PolyGcd.elem_of_content _ _ xc.
  have [wx nx] : PreTerm.wf (unfold_term x) ∧
                 negb (PreTerm.is_mod (unfold_term x)).
    by apply/andb_True; apply: (A n) xn; right.
  have ef : pre_frac (TInv (TInv x)) = Frac.var (unfold_term x).
    by rewrite TInvK PreTerm.frac_of_Nmod.
  have [en [ed eD]] :=
    Frac.mul_var_content_canon (expo_frac u) M (unfold_term x) eM xc.
  have mr : Frac.mono_num (Frac.mul (expo_frac u) (pre_frac (TInv (TInv x)))).
    by exists M; rewrite ef en.
  have [N [_ L]] := expo_frac_TExp Nu mr.
  split=> //; rewrite L ef ed.
  set Dc := PolyGcd.div_mono {[+ unfold_term x +]} (Frac.den (expo_frac u)) in
    eD *.
  have nDc : Dc ≠ Poly.zero.
    move=> e; apply: (Frac.den_neq0 (expo_frac u)); rewrite -eD e.
    exact: (right_absorb Poly.zero Poly.mul).
  rewrite -[in RHS]eD.
  rewrite (PolyGcd.unit_part_mul _ _ (PolyGcd.mono_neq0 _) nDc).
  by rewrite PolyGcd.unit_part_mono (left_id Poly.one Poly.mul).
Qed.

Lemma TInv_den_unit_Nnonce u (a : nonce) : TInv (den_unit u) ≠ TNonce a.
Proof.
have nU := PolyGcd.unit_part_neq0 _ (Frac.den_neq0 (expo_frac u)).
have E1 : Frac.num (pre_frac (TInv (den_unit u))) = Poly.one.
  rewrite pre_frac_TInv pre_frac_den_unit.
  by case:
    (Frac.inv_of_poly_canon _ nU (Frac.first_neg_unit_part (expo_frac u))).
have E2 : Frac.num (pre_frac (TNonce a)) = Poly.var (unfold_term (TNonce a)).
  rewrite (PreTerm.frac_of_Nmod (unfold_term (TNonce a))) //.
  by rewrite Frac.varE Frac.num_of_poly.
move=> e; rewrite e E2 Poly.varE Poly.oneE in E1.
have ne : (∅ : MSet.mset PreTerm.pre_term) ≠ {[+ unfold_term (TNonce a) +]}.
  move=> /(f_equal (MSet.count (unfold_term (TNonce a)))).
  by rewrite MSet.count_empty MSet.count_singleton bool_decide_eq_true_2.
move: E1 => /(f_equal (Poly.coeff ∅)); rewrite !Poly.coeff_mono.
by rewrite (bool_decide_eq_true_2 (∅ = ∅)) // bool_decide_eq_false_2.
Qed.

Add Ring poly_ring_P : (Poly.poly_ring_theory (T := PreTerm.pre_term)).

(** The power [k ^ (ν / D)] of a group factor, for a monomial [ν] of the
    numerator of the logarithm at [k] and its denominator [D]. *)
Definition gfactor_of t u k ν :=
  ν ∈ Poly.car (Frac.num (dh_map t !!! k)) ∧
  unfold_term u =
  PreTerm.mk_exp k (Frac.make (Poly.mono ν) (Frac.den (dh_map t !!! k))).

Lemma elem_of_gfactors_log t u :
  u ∈ gfactors t → ∃ k ν, gfactor_of t u k ν.
Proof.
move=> /elem_of_gfactors_unfold.
rewrite (PreTerm.gfactors_dh _ (wf_unfold_term t)) -/(dh_map t).
move=> /PreTerm.elem_of_dh_factors [k [r [ν [kr [νr ue]]]]].
have /FMap.elem_of_to_list [mk nr] := kr.
exists k, ν; rewrite /gfactor_of mk; split=> //.
have nD := Frac.den_neq0 r.
have [r' [n' [-> [Er' Hr']]]] := PreTerm.elem_of_exp_factor k _ ν _ nD ue.
have [h [_ [en _]]] := Frac.make_mono_canon ν _ nD (Frac.den_first_neg r).
case: Hr' => Er; first by rewrite Er.
exfalso.
move: Er'; rewrite Er Frac.num_opp en => e.
have e' := Poly.mono_pm_inj n' (ν ∖ h) (or_intror (eq_sym e)).
by apply: (Poly.mono_neq_opp n'); rewrite -{1}e e'.
Qed.

Lemma exp_factor_canon k (D : Poly.poly PreTerm.pre_term) ν :
  D ≠ Poly.zero → Poly.first_neg D = false →
  PreTerm.exp_factor k D ν =
  {[+ PreTerm.mk_exp k (Frac.make (Poly.mono ν) D) +]}.
Proof.
move=> nD fD; have [h [_ [en _]]] := Frac.make_mono_canon ν _ nD fD.
by rewrite /PreTerm.exp_factor; cbv zeta; rewrite en Poly.first_neg_mono.
Qed.

Lemma gfactor_of_spec t u k ν :
  gfactor_of t u k ν →
  negb (is_gmul u) ∧
  dh_map u = {[k := Frac.make (Poly.mono ν) (Frac.den (dh_map t !!! k))]} ∧
  pre_frac (den_unit u) =
  Frac.of_poly (PolyGcd.unit_part (Frac.den (dh_map t !!! k))) ∧
  dh_map (laurent_part u) =
  {[k := Frac.make (Poly.mono ν)
           (Poly.mono (PolyGcd.content (Frac.den (dh_map t !!! k))))]}.
Proof.
case=> νr eu; have nr := Frac.num_car_neq0 _ _ νr.
set r := dh_map t !!! k in nr νr eu *.
set D := Frac.den r in eu *.
have [wk [gk ar]] := PreTerm.wf_dh_map _ (wf_unfold_term t) k nr.
have nD : D ≠ Poly.zero := Frac.den_neq0 r.
have [h [hν [en eD]]] := Frac.make_mono_canon ν _ nD (Frac.den_first_neg r).
set r' := Frac.make (Poly.mono ν) D in en eD eu *.
have mr : Frac.mono_num r' by exists (ν ∖ h).
have nr' : r' ≠ Frac.zero := Frac.mono_num_neq0 _ mr.
have ar' := Frac.all_vars_make_mono _ _ _ νr ar.
have [Nk [Bk Xk]] :=
  PreTerm.mk_exp_mono_num _ _ gk ar' mr.
have Nu : negb (is_gmul u) by rewrite is_gmul_unfold eu.
have lu : expo_frac u = r'.
  by rewrite /expo_frac eu Xk; exact: PreTerm.frac_of_mod_of_frac.
have UD : PolyGcd.unit_part (Frac.den r') = PolyGcd.unit_part D.
  rewrite -[in RHS]eD.
  rewrite (PolyGcd.unit_part_mul _ _ (PolyGcd.mono_neq0 _) (Frac.den_neq0 r')).
  by rewrite PolyGcd.unit_part_mono (left_id Poly.one Poly.mul).
split=> //; split.
  by rewrite /dh_map eu
    (PreTerm.dh_map_mk_exp _ _ gk ar' nr').
split; first by rewrite pre_frac_den_unit lu UD.
have [Nl [Bl [nl dl]]] := laurent_part_spec Nu.
rewrite (dh_map_Ngmul Nl) Bl unfold_base eu Bk; congr {[_ := _]}.
rewrite -(Frac.make_num_den (expo_frac (laurent_part u))) nl dl lu en.
apply: Frac.make_eq; try exact: PolyGcd.mono_neq0.
have CD : PolyGcd.content D = h ⊎ PolyGcd.content (Frac.den r').
  rewrite -[in LHS]eD.
  rewrite (PolyGcd.content_mul _ _ (PolyGcd.mono_neq0 _) (Frac.den_neq0 r')).
  by rewrite PolyGcd.content_mono.
rewrite CD !Poly.mul_mono; congr Poly.mono.
apply: MSet.count_inj => x.
rewrite !MSet.count_disj_union MSet.count_difference.
have := proj1 (MSet.subseteq_count _ _) hν x; lia.
Qed.

Lemma gfactors_of_log t k ν :
  ν ∈ Poly.car (Frac.num (dh_map t !!! k)) →
  ∃ u, u ∈ gfactors t ∧ gfactor_of t u k ν.
Proof.
move=> νr; have nr := Frac.num_car_neq0 _ _ νr.
have wd := PreTerm.wf_dh_map _ (wf_unfold_term t).
have [wk [gk ar]] := wd k nr.
set r := dh_map t !!! k in nr νr ar *.
set D := Frac.den r.
have nD : D ≠ Poly.zero := Frac.den_neq0 r.
have fD : Poly.first_neg D = false := Frac.den_first_neg r.
set r' := Frac.make (Poly.mono ν) D.
have [h [hν [en eD]]] := Frac.make_mono_canon ν _ nD fD.
have mr : Frac.mono_num r' by exists (ν ∖ h).
have nr' : r' ≠ Frac.zero := Frac.mono_num_neq0 _ mr.
have ar' := Frac.all_vars_make_mono _ _ _ νr ar.
have wz : PreTerm.wf (PreTerm.mk_exp k r').
  exact: PreTerm.wf_mk_exp wk gk nr' ar'.
have ez := fold_termK _ wz.
exists (fold_term (PreTerm.mk_exp k r')).
split; last by rewrite /gfactor_of ez; do !split.
apply/elem_of_gfactors_unfold.
rewrite ez (PreTerm.gfactors_dh _ (wf_unfold_term t)) -/(dh_map t).
apply/SMS.elem_of_count.
have [Nk [Bk Xk]] :=
  PreTerm.mk_exp_mono_num _ _ gk ar' mr.
rewrite (PreTerm.count_dh_factors _ _ wd) Bk -/r /PreTerm.entry_factors.
have Z0 : ∀ ν', ν' ∈ Poly.car (Frac.num r) → ν' ≠ ν →
    SMS.count (PreTerm.mk_exp k r') (PreTerm.exp_factor k D ν') = 0%Z.
  move=> ν' ν'r ne; rewrite (exp_factor_canon _ _ nD fD) SMS.count_singleton.
  rewrite bool_decide_eq_false_2 // => e.
  have [h' [_ [en' _]]] := Frac.make_mono_canon ν' _ nD fD.
  have mr'' : Frac.mono_num (Frac.make (Poly.mono ν') D) by exists (ν' ∖ h').
  have ar'' := Frac.all_vars_make_mono _ _ _ ν'r ar.
  have [_ [_ X'']] :=
    PreTerm.mk_exp_mono_num _ _ gk ar'' mr''.
  have e' : r' = Frac.make (Poly.mono ν') D.
    have := f_equal (λ pt, PreTerm.frac_of (PreTerm.expo pt)) e; cbv beta.
    rewrite Xk X'' (PreTerm.frac_of_mod_of_frac _ ar').
    by rewrite (PreTerm.frac_of_mod_of_frac _ ar'').
  have := Frac.make_cross _ _ _ _ nD nD e'.
  rewrite ![(_ * D)%P](comm Poly.mul) => /(PolyGcd.mul_cancel_l _ _ _ nD) em.
  by apply: ne; apply: (Poly.mono_pm_inj ν' ν); left; rewrite em.
rewrite (SMS.count_bind_single _ _ _ ν Z0) (exp_factor_canon _ _ nD fD).
rewrite SMS.count_singleton bool_decide_eq_true_2 //.
have : SMS.count ν (Poly.car (Frac.num r)) ≠ 0%Z by apply/SMS.elem_of_count.
change (Z.b2z true) with 1%Z; lia.
Qed.

Lemma expo_frac_gfactor t u k ν :
  gfactor_of t u k ν →
  expo_frac u = Frac.make (Poly.mono ν) (Frac.den (dh_map t !!! k)).
Proof.
case=> νr eu; have nr := Frac.num_car_neq0 _ _ νr.
have [wk [gk ar]] := PreTerm.wf_dh_map _ (wf_unfold_term t) k nr.
set r := dh_map t !!! k in nr νr eu ar *.
have nD := Frac.den_neq0 r.
have [h [_ [en _]]] := Frac.make_mono_canon ν _ nD (Frac.den_first_neg r).
have mr : Frac.mono_num (Frac.make (Poly.mono ν) (Frac.den r)).
  by exists (ν ∖ h).
have ar' := Frac.all_vars_make_mono _ _ _ νr ar.
have [_ [_ Xk]] :=
  PreTerm.mk_exp_mono_num _ _ gk ar' mr.
by rewrite /expo_frac eu Xk; apply: PreTerm.frac_of_mod_of_frac.
Qed.

Lemma gfactor_content_neg t u k ν a :
  gfactor_of t u k ν → a ∈ PolyGcd.content (Frac.den (dh_map t !!! k)) →
  a ∉ ν →
  fold_term a ∈ SMS.neg (exps u) ∧ negb (is_mod (fold_term a)) ∧
  unfold_term (fold_term a) = a.
Proof.
move=> G aD aν; have lu := expo_frac_gfactor G.
case: G => νr eu; have nr := Frac.num_car_neq0 _ _ νr.
have [wk [gk ar]] := PreTerm.wf_dh_map _ (wf_unfold_term t) k nr.
set r := dh_map t !!! k in nr νr eu ar aD lu.
have nD := Frac.den_neq0 r.
have [h [hν [en eD]]] := Frac.make_mono_canon ν _ nD (Frac.den_first_neg r).
have [m [mD am]] := PolyGcd.elem_of_content _ _ aD.
have /andb_True [wa na] := ar m a (or_intror mD) am.
have ea : unfold_term (fold_term a) = a := fold_termK _ wa.
split; last by split=> //; rewrite is_mod_unfold ea.
have nden := Frac.den_neq0 (Frac.make (Poly.mono ν) (Frac.den r)).
have CD : PolyGcd.content (Frac.den r) =
          h ⊎ PolyGcd.content (Frac.den (Frac.make (Poly.mono ν) (Frac.den r))).
  rewrite -[in LHS]eD (PolyGcd.content_mul _ _ (PolyGcd.mono_neq0 _) nden).
  by rewrite PolyGcd.content_mono.
have ah : MSet.count a h = 0.
  apply/MSet.not_elem_of_count => ah; apply: aν.
  exact: MSet.elem_of_subseteq hν ah.
apply/count_lt0; rewrite (@count_expo u _ (ν ∖ h)); last by rewrite lu en.
rewrite lu ea MSet.count_difference MSet.count_disj_union.
have : 0 < MSet.count a (PolyGcd.content (Frac.den r)).
  exact/MSet.elem_of_count.
rewrite CD MSet.count_disj_union ah.
have : MSet.count a ν = 0 by apply/MSet.not_elem_of_count.
lia.
Qed.

Lemma is_mod_den_unit u : is_mod (den_unit u).
Proof.
rewrite is_mod_unfold /den_unit fold_termK; last first.
  exact: PreTerm.wf_mod_of_frac (@atoms_unit_part u).
set Z := PolyGcd.unit_part (Frac.den (expo_frac u)).
case E: (PreTerm.is_mod (PreTerm.mod_of_frac (Frac.of_poly Z))) => //.
exfalso; have [x [EZ _]] := PreTerm.mod_of_frac_Nmod _ E.
have := PolyGcd.content_unit_part (Frac.den (expo_frac u)).
rewrite -/Z (Frac.of_poly_inj _ _ EZ) Poly.varE PolyGcd.content_mono.
by move=> e; apply: (MSet.empty_neq_singleton x); rewrite e.
Qed.


Lemma count_strip t f y :
  negb (is_gmul t) → f ∈ satoms (exps t) → y ≠ f →
  negb (is_gmul (TExp t (TInv f))) ∧ base (TExp t (TInv f)) = base t ∧
  (count y (expo t) ≤ count y (expo (TExp t (TInv f))))%Z.
Proof.
move=> Nt; have [M eM] := expo_frac_mono_num Nt.
have A := @expo_frac_atoms t.
set D := Frac.den (expo_frac t).
have nD : D ≠ Poly.zero := Frac.den_neq0 (expo_frac t).
rewrite /exps elem_of_satoms_count.
case=> [h|[x [-> h]]] yf.
- move: h; rewrite (count_expo _ eM) => h.
  have fM : unfold_term f ∈ M by apply/MSet.elem_of_count; lia.
  have [wf nf'] : PreTerm.wf (unfold_term f) ∧
                  negb (PreTerm.is_mod (unfold_term f)).
    apply/andb_True; apply: (A M) fM; left.
    by rewrite eM Poly.car_mono; apply/SMS.elem_of_singleton.
  have ef : pre_frac (TInv f) = Frac.inv (Frac.var (unfold_term f)).
    by rewrite pre_frac_TInv PreTerm.frac_of_Nmod.
  have [en ed] := Frac.mul_inv_var_canon (expo_frac t) M (unfold_term f) eM fM.
  have mr : Frac.mono_num (Frac.mul (expo_frac t) (pre_frac (TInv f))).
    by exists (M ∖ {[+ unfold_term f +]}); rewrite ef en.
  have [N [B L]] := expo_frac_TExp Nt mr.
  split=> //; split=> //.
  have ne : unfold_term y ≠ unfold_term f by move=> /unfold_term_inj.
  rewrite (@count_expo (TExp t (TInv f)) y (M ∖ {[+ unfold_term f +]}));
    last by rewrite L ef en.
  rewrite L ef ed MSet.count_difference MSet.count_singleton.
  rewrite bool_decide_eq_false_2 // (count_expo _ eM); lia.
- have ef : TExp t (TInv (TInv x)) = TExp t x by rewrite TInvK.
  rewrite ef.
  move: h; rewrite (count_expo _ eM) -/D => h.
  case: (decide (x = den_unit t)) => [ex|nx].
  + subst x.
    have [en ed] := Frac.mul_unit_part_canon (expo_frac t) M eM.
    have mr : Frac.mono_num (Frac.mul (expo_frac t) (pre_frac (den_unit t))).
      by exists M; rewrite pre_frac_den_unit en.
    have [N [B L]] := expo_frac_TExp Nt mr.
    split=> //; split=> //.
    rewrite (@count_expo (TExp t (den_unit t)) y M);
      last by rewrite L pre_frac_den_unit en.
    rewrite L pre_frac_den_unit ed -/D PolyGcd.content_mono
      PreTerm.unit_factors_mono.
    rewrite (right_id ∅ (⊎)) (count_expo _ eM) -/D.
    rewrite MSet.count_disj_union; lia.
  + move: h; rewrite MSet.count_disj_union (count_unit_factors_den_unit nx)
      => h.
    have xc : unfold_term x ∈ PolyGcd.content D.
      by apply/MSet.elem_of_count; lia.
    have [n [nD' xn]] := PolyGcd.elem_of_content _ _ xc.
    have [wx nx'] : PreTerm.wf (unfold_term x) ∧
                    negb (PreTerm.is_mod (unfold_term x)).
      by apply/andb_True; apply: (A n) xn; right.
    have ex' : pre_frac x = Frac.var (unfold_term x).
      by rewrite PreTerm.frac_of_Nmod.
    have [en [ed eD]] :=
      Frac.mul_var_content_canon (expo_frac t) M (unfold_term x) eM xc.
    have mr : Frac.mono_num (Frac.mul (expo_frac t) (pre_frac x)).
      by exists M; rewrite ex' en.
    have [N [B L]] := expo_frac_TExp Nt mr.
    split=> //; split=> //.
    set Dc := PolyGcd.div_mono {[+ unfold_term x +]} D in ed eD.
    rewrite -/D in eD.
    have nDc : Dc ≠ Poly.zero.
      move=> e; apply: nD; rewrite -eD e.
      exact: (right_absorb Poly.zero Poly.mul).
    have CD : PolyGcd.content D = {[+ unfold_term x +]} ⊎ PolyGcd.content Dc.
      rewrite -[in LHS]eD (PolyGcd.content_mul _ _ (PolyGcd.mono_neq0 _) nDc).
      by rewrite PolyGcd.content_mono.
    have UD : PolyGcd.unit_part D = PolyGcd.unit_part Dc.
      rewrite -[in LHS]eD (PolyGcd.unit_part_mul _ _ (PolyGcd.mono_neq0 _) nDc).
      by rewrite PolyGcd.unit_part_mono (left_id Poly.one Poly.mul).
    rewrite (@count_expo (TExp t x) y M); last by rewrite L ex' en.
    rewrite L ex' ed (count_expo _ eM) -/D.
    have UU : PreTerm.unit_factors D =
      PreTerm.unit_factors Dc by rewrite /PreTerm.unit_factors UD.
    rewrite CD UU !MSet.count_disj_union; lia.
Qed.

Lemma atoms_make_monos (P : PreTerm.pre_term → Prop)
    (X Y : MSet.mset PreTerm.pre_term) :
  (∀ y, y ∈ X ∨ y ∈ Y → P y) →
  Frac.all_vars P (Frac.make (Poly.mono X) (Poly.mono Y)).
Proof.
move=> h; apply: (Frac.all_vars_over _ (elements (X ⊎ Y))).
  apply: Frac.over_make; apply: PolyGcd.over_intro => m x;
    rewrite Poly.car_mono => /SMS.elem_of_singleton -> xm;
    apply/MSet.elem_of_elements/MSet.elem_of_disj_union; by [left|right].
by move=> x /MSet.elem_of_elements /MSet.elem_of_disj_union; exact: h.
Qed.

Lemma laurent_shift v w k (μ ν C C' : MSet.mset PreTerm.pre_term)
    (pub : PreTerm.pre_term → bool) :
  dh_map v = {[k := Frac.make (Poly.mono μ) (Poly.mono C)]} →
  dh_map w = {[k := Frac.make (Poly.mono ν) (Poly.mono C')]} →
  PolyRestrict.secret_part pub μ = PolyRestrict.secret_part pub ν →
  (∀ y, y ∈ μ ∨ y ∈ ν ∨ y ∈ C ∨ y ∈ C' →
        PreTerm.wf y && negb (PreTerm.is_mod y)) →
  ∃ π, laurent π ∧
       (∀ y, y ∈ atoms π → ∃ a, y = fold_term a ∧
             (a ∈ C ∨ a ∈ C' ∨ pub a)) ∧
       w = TExp v π.
Proof.
move=> ev ew es hw.
set X := PolyRestrict.public_part pub ν ⊎ C.
set Y := PolyRestrict.public_part pub μ ⊎ C'.
have pp z m : z ∈ PolyRestrict.public_part pub m → z ∈ m.
  move=> /MSet.elem_of_count; rewrite PolyRestrict.count_public_part.
  by case: (pub z) => h; [apply/MSet.elem_of_count|lia].
have AW : PreTerm.wf_frac
            (Frac.make (Poly.mono X) (Poly.mono Y)).
  apply: atoms_make_monos => y.
  case=> /MSet.elem_of_disj_union [/pp yp|yc]; apply: hw; tauto.
have wπ := PreTerm.wf_mod_of_frac _ AW.
set π := fold_term
  (PreTerm.mod_of_frac (Frac.make (Poly.mono X) (Poly.mono Y))).
have eπ : pre_frac π = Frac.make (Poly.mono X) (Poly.mono Y).
  by rewrite /π fold_termK // PreTerm.frac_of_mod_of_frac.
exists π; split.
  apply/laurent_unfold.
  apply/(PreTerm.laurent_frac_of _ (wf_unfold_term _)); rewrite eπ.
  exact: Frac.laurent_make_mono.
split.
  move=> y /elem_of_atoms [a [-> ap]]; exists a; split=> //.
  move: ap; rewrite /PreTerm.atoms eπ => ap.
  have oXY : Frac.over (elements (X ⊎ Y))
               (Frac.make (Poly.mono X) (Poly.mono Y)).
    apply: Frac.over_make; apply: PolyGcd.over_intro => m x;
      rewrite Poly.car_mono => /SMS.elem_of_singleton -> xm;
      apply/MSet.elem_of_elements/MSet.elem_of_disj_union; by [left|right].
  move: ap; rewrite /Frac.vars elem_of_app !Poly.elem_of_vars.
  case=> -[m [mr am]];
    have := Frac.over_elem _ _ m a oXY ltac:(tauto) am;
    move=> /MSet.elem_of_elements /MSet.elem_of_disj_union [];
    move=> /MSet.elem_of_disj_union [ap|ac]; try tauto;
    right; right; move/MSet.elem_of_count: ap;
      rewrite PolyRestrict.count_public_part;
    by case: (pub a) => //; lia.
apply: dh_map_inj; apply/FMap.fmap_eq => k'.
rewrite dh_map_TExp unfold_frac_of eπ ev ew !FMap.lookup_singleton.
case: bool_decide; last by rewrite Frac.mul_zero_l.
rewrite Frac.mul_make; try exact: PolyGcd.mono_neq0.
apply: Frac.make_eq; try exact: PolyGcd.mul_neq0 (PolyGcd.mono_neq0 _)
  (PolyGcd.mono_neq0 _).
  exact: PolyGcd.mono_neq0.
rewrite !Poly.mul_mono; congr Poly.mono.
apply: MSet.count_inj => z; rewrite /X /Y !MSet.count_disj_union.
have Eμ := f_equal (MSet.count z) (PolyRestrict.secret_part_public_part pub μ).
have Eν := f_equal (MSet.count z) (PolyRestrict.secret_part_public_part pub ν).
have Es := f_equal (MSet.count z) es.
rewrite !MSet.count_disj_union in Eμ Eν; lia.
Qed.

Lemma count_expo_gfactor t u k ν y :
  gfactor_of t u k ν → negb (is_mod y) →
  count y (expo u) =
  (Z.of_nat (MSet.count (unfold_term y) ν) -
   Z.of_nat (MSet.count (unfold_term y)
               (PolyGcd.content (Frac.den (dh_map t !!! k)))))%Z.
Proof.
move=> G ny; have lu := expo_frac_gfactor G.
case: G => νr eu; have nr := Frac.num_car_neq0 _ _ νr.
set r := dh_map t !!! k in nr νr eu lu *.
have nD := Frac.den_neq0 r.
have [h [hν [en eD]]] := Frac.make_mono_canon ν _ nD (Frac.den_first_neg r).
have nden := Frac.den_neq0 (Frac.make (Poly.mono ν) (Frac.den r)).
have CD : PolyGcd.content (Frac.den r) =
          h ⊎ PolyGcd.content (Frac.den (Frac.make (Poly.mono ν) (Frac.den r))).
  rewrite -[in LHS]eD (PolyGcd.content_mul _ _ (PolyGcd.mono_neq0 _) nden).
  by rewrite PolyGcd.content_mono.
rewrite (@count_expo u y (ν ∖ h)); last by rewrite lu en.
rewrite lu MSet.count_difference MSet.count_disj_union CD MSet.count_disj_union.
have -> : MSet.count (unfold_term y)
            (PreTerm.unit_factors
              (Frac.den (Frac.make (Poly.mono ν) (Frac.den r))))
          = 0.
  apply/MSet.not_elem_of_count => /PreTerm.unit_factors_mod.
  by rewrite -is_mod_unfold; move: ny; case: (is_mod y).
have := proj1 (MSet.subseteq_count _ _) hν (unfold_term y); lia.
Qed.

(** ** Logarithms *)

Lemma count_expo_gfactors_big {h T u} :
  negb (is_mod h) → u ∈ gfactors T → tsize T ≤ tsize h →
  count h (expo u) = 0%Z.
Proof.
move=> Nh uT le; case: (decide (count h (expo u) = 0%Z)) => // ne.
have h_in : h ∈ exps u by apply/count_neq0.
have := tsize_exps_lt _ _ h_in Nh; have := tsize_gfactors_le _ _ uT; lia.
Qed.
