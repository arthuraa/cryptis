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

   A power [u] (a term that is not a group product) has a logarithm [lg u]
   whose numerator is a monomial.  The unit part of its denominator, as an
   exponent, is [uprt u], and [lpart u = TExp u (uprt u)] is its Laurent part:
   a power whose logarithm is a Laurent monomial ([lpart_spec],
   [laurent_lpart]).  Stripping a signed atom other than [TInv (uprt u)] keeps
   the unit part ([strip_uprt]) and the signed atom of the Laurent part
   ([satoms_lpart]), and stripping any signed atom keeps the positive count
   of every other atom ([count_strip]).

   The group factors of [t] are the powers [k ^ (ν / D)] for the monomials
   [ν] of the numerator of the logarithm at [k], whose denominator is [D]
   ([gfactor_of], [elem_of_gfactors_log], [gfactors_of_log]).  Their unit
   parts are the unit part of [D], and their Laurent parts are
   [k ^ (ν / C)] for the monomial content [C] of [D] ([gfactor_of_spec]).
   Two Laurent powers of [k] whose monomials have the same secret part
   ([PolyRestrict.sec]) differ by a Laurent monomial over the public atoms
   and their denominators ([laurent_shift]).

   [log k t] is the exponent of the base [k] in [t], as an exponent term:
   logarithms turn group products into sums and powers into products
   ([log_TGMul2], [log_TExp]), and they determine a term ([log_inj]).
   Coefficients of an atom that they avoid can be compared ([frac_lin]). *)

Implicit Types (t u v e f : term).

Abbreviation pfrac t := (PreTerm.frac_of (unfold_term t)).

Definition lg u := PreTerm.frac_of (PreTerm.expo (unfold_term u)).

Definition uprt u : term :=
  fold_term (PreTerm.mod_aux
    (Frac.of_poly (PolyGcd.unit_part (Frac.den (lg u))))).

Definition lpart u := TExp u (uprt u).

Lemma lg_atoms u :
  PreTerm.atoms_all (λ x, PreTerm.wf x && negb (PreTerm.is_mod x)) (lg u).
Proof.
exact: PreTerm.frac_of_atoms (PreTerm.wf_expo _ (wf_unfold_term u)).
Qed.

Lemma lg_mnum u : negb (is_gmul u) → PreTerm.mnum (lg u).
Proof.
rewrite is_gmul_unfold => Nu.
exact: PreTerm.mnum_expo (wf_unfold_term u) Nu.
Qed.

Lemma lg_TExp u e :
  negb (is_gmul u) → PreTerm.mnum (Frac.mul (lg u) (pfrac e)) →
  negb (is_gmul (TExp u e)) ∧ base (TExp u e) = base u ∧
  lg (TExp u e) = Frac.mul (lg u) (pfrac e).
Proof.
move=> Nu mr; have wu := wf_unfold_term u.
have Nu' : negb (PreTerm.is_gmul (unfold_term u)) by rewrite -is_gmul_unfold.
have nz : Frac.mul (lg u) (pfrac e) ≠ Frac.zero by exact: PreTerm.mnum_neq0.
have E : unfold_term (TExp u e) =
         PreTerm.mk_exp (PreTerm.base (unfold_term u))
                        (Frac.mul (lg u) (pfrac e)).
  by rewrite unfold_TExp /PreTerm.exp (PreTerm.exp_frac_Ngmul _ _ wu Nu' nz).
have gb := PreTerm.base_Ngnf _ wu Nu'.
have [N [B X]] := PreTerm.mk_exp_mnum _ _ gb mr.
split; first by rewrite is_gmul_unfold E.
split.
  apply: unfold_term_inj; rewrite !unfold_base E B.
  by [].
rewrite /lg E X; apply: PreTerm.frac_of_mod_aux_wf.
apply: PreTerm.atoms_all_mul; first exact: lg_atoms.
exact: PreTerm.frac_of_atoms (wf_unfold_term e).
Qed.

Lemma count_expo u y M :
  Frac.num (lg u) = Poly.mono M →
  count y (expo u) =
  (Z.of_nat (MSet.count (unfold_term y) M) -
   Z.of_nat (MSet.count (unfold_term y)
     (PolyGcd.content (Frac.den (lg u)) ⊎
      PreTerm.units (Frac.den (lg u)))))%Z.
Proof.
move=> eM; rewrite count_unfold unfold_expo (PreTerm.factors_mono_num _ _ eM).
exact: SMS.count_make.
Qed.

Lemma atoms_unit_part u :
  PreTerm.atoms_all (λ x, PreTerm.wf x && negb (PreTerm.is_mod x))
    (Frac.of_poly (PolyGcd.unit_part (Frac.den (lg u)))).
Proof.
move=> m x; rewrite Frac.num_of_poly Frac.den_of_poly Poly.oneE Poly.car_mono.
case=> [mU|/SMS.elem_of_singleton ->] xm; last first.
  by case: (MSet.not_elem_of_empty _ xm).
have [m' [m'D xm']] := PreTerm.elem_of_unit_part x _ m mU xm.
exact: lg_atoms m' x (or_intror m'D) xm'.
Qed.

Lemma pfrac_uprt u :
  pfrac (uprt u) = Frac.of_poly (PolyGcd.unit_part (Frac.den (lg u))).
Proof.
rewrite /uprt fold_termK; last exact: PreTerm.wf_mod_aux (@atoms_unit_part u).
exact: PreTerm.frac_of_mod_aux_wf (@atoms_unit_part u).
Qed.

Lemma uprt_frac_neq0 u : frac_of (uprt u) ≠ Frac.zero.
Proof.
move=> e; have := pfrac_uprt u; rewrite -unfold_frac_of e Frac.map_zero.
move=> /(f_equal Frac.num); rewrite Frac.num_zero Frac.num_of_poly => E.
by apply: (PolyGcd.unit_part_neq0 _ (Frac.den_neq0 (lg u))); rewrite -E.
Qed.

Lemma uprt_one u :
  PolyGcd.unit_part (Frac.den (lg u)) = Poly.one → uprt u = TMul ∅.
Proof.
move=> E; apply: frac_of_inj.
apply: (Frac.map_inj unfold_term unfold_term_inj).
by rewrite !unfold_frac_of pfrac_uprt E -Frac.oneE -unfold_frac_of
  frac_of_TMul_empty Frac.map_one.
Qed.

Lemma lg_Nexp u : negb (is_exp u) → lg u = Frac.one.
Proof.
rewrite is_exp_unfold => nE.
by rewrite /lg (PreTerm.expo_expN _ nE) PreTerm.frac_of_one.
Qed.

Lemma uprt_neg u :
  negb (is_gmul u) → PolyGcd.unit_part (Frac.den (lg u)) ≠ Poly.one →
  is_exp u ∧ uprt u ∈ SMS.neg (exps u) ∧ is_mod (uprt u).
Proof.
move=> Nu U1.
have [M eM] := lg_mnum Nu.
have uU : unfold_term (uprt u) ∈ PreTerm.units (Frac.den (lg u)).
  rewrite /PreTerm.units bool_decide_eq_false_2 //.
  rewrite /uprt fold_termK; last exact: PreTerm.wf_mod_aux (@atoms_unit_part u).
  exact/MSet.elem_of_singleton.
have Mu : is_mod (uprt u) by rewrite is_mod_unfold; exact: PreTerm.units_mod uU.
split.
  case Ex: (is_exp u) => //; exfalso; apply: U1.
  rewrite lg_Nexp ?Ex // Frac.den_one Poly.oneE PolyGcd.unit_part_mono.
  by rewrite Poly.oneE.
split=> //; apply/count_lt0; rewrite (count_expo _ eM).
have c0 : MSet.count (unfold_term (uprt u)) M = 0.
  apply/MSet.not_elem_of_count => uM.
  have mM : M ∈ Poly.car (Frac.num (lg u)).
    by rewrite eM Poly.car_mono; exact/SMS.elem_of_singleton.
  have /andb_True [_] := @lg_atoms u M _ (or_introl mM) uM.
  move: Mu; rewrite is_mod_unfold.
  by case: (PreTerm.is_mod (unfold_term (uprt u))).
have c1 : 0 < MSet.count (unfold_term (uprt u))
                (PolyGcd.content (Frac.den (lg u)) ⊎
                 PreTerm.units (Frac.den (lg u))).
  by apply/MSet.elem_of_count; apply/MSet.elem_of_disj_union; right.
lia.
Qed.

Lemma count_units_uprt u y :
  y ≠ uprt u →
  MSet.count (unfold_term y) (PreTerm.units (Frac.den (lg u))) = 0.
Proof.
move=> ne; apply/MSet.not_elem_of_count; rewrite /PreTerm.units.
case: bool_decide_reflect => _; first exact: MSet.not_elem_of_empty.
move=> /MSet.elem_of_singleton e; apply: ne; apply: unfold_term_inj.
rewrite e /uprt fold_termK //.
exact: PreTerm.wf_mod_aux (@atoms_unit_part u).
Qed.

Lemma lpart_spec u :
  negb (is_gmul u) →
  negb (is_gmul (lpart u)) ∧ base (lpart u) = base u ∧
  Frac.num (lg (lpart u)) = Frac.num (lg u) ∧
  Frac.den (lg (lpart u)) = Poly.mono (PolyGcd.content (Frac.den (lg u))).
Proof.
move=> Nu; have [M eM] := lg_mnum Nu.
have [en ed] := Frac.mul_unit_part_canon (lg u) M eM.
have mr : PreTerm.mnum (Frac.mul (lg u) (pfrac (uprt u))).
  by exists M; rewrite pfrac_uprt en.
have [N [B L]] := lg_TExp Nu mr.
rewrite /lpart L pfrac_uprt en ed eM.
by do !split.
Qed.

Lemma laurent_lpart u : negb (is_gmul u) → laurent (expo (lpart u)).
Proof.
move=> Nu; have [_ [_ [en ed]]] := lpart_spec Nu.
have [M eM] := lg_mnum Nu.
apply/laurent_unfold; rewrite unfold_expo.
apply/(PreTerm.laurent_mfrac _ (PreTerm.wf_expo _ (wf_unfold_term _))).
rewrite -/(lg (lpart u)).
by exists M, (PolyGcd.content (Frac.den (lg u))); rewrite en ed eM.
Qed.

Lemma count_expo_lpart u y :
  negb (is_gmul u) →
  count y (expo (lpart u)) =
  (count y (expo u) +
   Z.of_nat (MSet.count (unfold_term y)
               (PreTerm.units (Frac.den (lg u)))))%Z.
Proof.
move=> Nu; have [M eM] := lg_mnum Nu.
have [_ [_ [en ed]]] := lpart_spec Nu.
rewrite (count_expo _ eM) (@count_expo (lpart u) y M); last by rewrite en.
rewrite ed PolyGcd.content_mono PreTerm.units_mono (right_id ∅ (⊎)).
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

Lemma satoms_lpart u f :
  negb (is_gmul u) → f ∈ satoms (exps u) → f ≠ TInv (uprt u) →
  f ∈ satoms (exps (lpart u)).
Proof.
move=> Nu; rewrite /exps !elem_of_satoms_count.
case=> [h|[x [-> h]]] nf.
  by left; rewrite count_expo_lpart //; lia.
right; exists x; split=> //.
have ne : x ≠ uprt u by move=> e; apply: nf; rewrite e.
rewrite count_expo_lpart // (count_units_uprt ne); lia.
Qed.

Lemma lpartK u : TExp (lpart u) (TInv (uprt u)) = u.
Proof. rewrite /lpart; apply: TExpK; exact: uprt_frac_neq0. Qed.

Lemma strip_uprt u f :
  negb (is_gmul u) → f ∈ satoms (exps u) → f ≠ TInv (uprt u) →
  negb (is_gmul (TExp u (TInv f))) ∧
  PolyGcd.unit_part (Frac.den (lg (TExp u (TInv f)))) =
  PolyGcd.unit_part (Frac.den (lg u)).
Proof.
move=> Nu; have [M eM] := lg_mnum Nu.
have A := @lg_atoms u.
rewrite /exps elem_of_satoms_count.
case=> [h|[x [-> h]]] nf.
- move: h; rewrite (count_expo _ eM) => h.
  have fM : unfold_term f ∈ M by apply/MSet.elem_of_count; lia.
  have [wf nf'] : PreTerm.wf (unfold_term f) ∧
                  negb (PreTerm.is_mod (unfold_term f)).
    apply/andb_True; apply: (A M) fM; left.
    by rewrite eM Poly.car_mono; apply/SMS.elem_of_singleton.
  have ef : pfrac (TInv f) = Frac.inv (Frac.var (unfold_term f)).
    by rewrite efrac_TInv PreTerm.frac_of_var.
  have [en ed] := Frac.mul_inv_var_canon (lg u) M (unfold_term f) eM fM.
  have mr : PreTerm.mnum (Frac.mul (lg u) (pfrac (TInv f))).
    by exists (M ∖ {[+ unfold_term f +]}); rewrite ef en.
  have [N [_ L]] := lg_TExp Nu mr.
  by split=> //; rewrite L ef ed.
- have ne : x ≠ uprt u by move=> e; apply: nf; rewrite e.
  move: h; rewrite (count_expo _ eM) MSet.count_disj_union.
  rewrite (count_units_uprt ne) => h.
  have xc : unfold_term x ∈ PolyGcd.content (Frac.den (lg u)).
    by apply/MSet.elem_of_count; lia.
  have [n [nD xn]] := PreTerm.elem_of_content _ _ xc.
  have [wx nx] : PreTerm.wf (unfold_term x) ∧
                 negb (PreTerm.is_mod (unfold_term x)).
    by apply/andb_True; apply: (A n) xn; right.
  have ef : pfrac (TInv (TInv x)) = Frac.var (unfold_term x).
    by rewrite TInvK PreTerm.frac_of_var.
  have [en [ed eD]] :=
    Frac.mul_var_content_canon (lg u) M (unfold_term x) eM xc.
  have mr : PreTerm.mnum (Frac.mul (lg u) (pfrac (TInv (TInv x)))).
    by exists M; rewrite ef en.
  have [N [_ L]] := lg_TExp Nu mr.
  split=> //; rewrite L ef ed.
  set Dc := PolyGcd.unmono {[+ unfold_term x +]} (Frac.den (lg u)) in eD *.
  have nDc : Dc ≠ Poly.zero.
    move=> e; apply: (Frac.den_neq0 (lg u)); rewrite -eD e.
    exact: (right_absorb Poly.zero Poly.mul).
  rewrite -[in RHS]eD.
  rewrite (PolyGcd.unit_part_mul _ _ (PolyGcd.mono_neq0 _) nDc).
  by rewrite PolyGcd.unit_part_mono (left_id Poly.one Poly.mul).
Qed.

Lemma TInv_uprt_Nnonce u (a : nonce) : TInv (uprt u) ≠ TNonce a.
Proof.
have nU := PolyGcd.unit_part_neq0 _ (Frac.den_neq0 (lg u)).
have E1 : Frac.num (pfrac (TInv (uprt u))) = Poly.one.
  rewrite efrac_TInv pfrac_uprt.
  by case: (Frac.inv_of_poly_canon _ nU (Frac.first_neg_unit_part (lg u))).
have E2 : Frac.num (pfrac (TNonce a)) = Poly.var (unfold_term (TNonce a)).
  rewrite (PreTerm.frac_of_Nmod (unfold_term (TNonce a))) //.
  by rewrite Frac.num_of_poly.
move=> e; rewrite e E2 Poly.varE Poly.oneE in E1.
have ne : (∅ : MSet.mset PreTerm.pre_term) ≠ {[+ unfold_term (TNonce a) +]}.
  move=> /(f_equal (MSet.count (unfold_term (TNonce a)))).
  by rewrite MSet.count_empty MSet.count_singleton bool_decide_eq_true_2.
move: E1 => /(f_equal (Poly.coeff ∅)); rewrite !Poly.coeff_mono.
by rewrite (bool_decide_eq_true_2 (∅ = ∅)) // bool_decide_eq_false_2.
Qed.

Add Ring poly_ring_P : (Poly.poly_ring_theory (T := PreTerm.pre_term)).

Lemma make_mono_canon (ν : MSet.mset PreTerm.pre_term)
    (D : Poly.poly PreTerm.pre_term) :
  D ≠ Poly.zero → Poly.first_neg D = false →
  ∃ h, h ⊆ ν ∧ Frac.num (Frac.make (Poly.mono ν) D) = Poly.mono (ν ∖ h) ∧
       (Poly.mono h * Frac.den (Frac.make (Poly.mono ν) D))%P = D.
Proof.
move=> nD fD.
have [e1 e2] := Frac.make_cancel (Poly.mono ν) D nD.
have [g [EP EQ]] := Poly.cancel_spec (Poly.mono ν) D.
rewrite -e1 in EP; rewrite -e2 in EQ.
set r := Frac.make (Poly.mono ν) D in EP EQ *.
have [h [hν hg]] := PolyGcd.dvd_mono g ν ltac:(by exists (Frac.num r)).
have nden := Frac.den_neq0 r.
have nh : Poly.mono h ≠ Poly.zero := PolyGcd.mono_neq0 h.
case: hg => eg; last first.
  exfalso; move: fD; rewrite EQ eg.
  have nh' : (- Poly.mono h)%P ≠ Poly.zero.
    move=> e; apply: nh.
    by rewrite -(Poly.opp_opp (Poly.mono h)) e Poly.opp_zero.
  rewrite (Poly.first_neg_mul _ _ nh' nden) (Frac.den_first_neg r).
  by rewrite Poly.first_neg_opp_mono.
exists h; split=> //; split; last by rewrite -eg.
apply: (PolyGcd.mul_cancel_l (Poly.mono h)) => //.
rewrite -eg -EP eg Poly.mul_mono; congr Poly.mono.
apply: MSet.count_inj => x; rewrite MSet.count_disj_union MSet.count_difference.
have := proj1 (MSet.subseteq_count _ _) hν x; lia.
Qed.

(** The power [k ^ (ν / D)] of a group factor, for a monomial [ν] of the
    numerator of the logarithm at [k] and its denominator [D]. *)
Definition gfactor_of t u k ν :=
  tdh t !!! k ≠ Frac.zero ∧ ν ∈ Poly.car (Frac.num (tdh t !!! k)) ∧
  unfold_term u =
  PreTerm.mk_exp k (Frac.make (Poly.mono ν) (Frac.den (tdh t !!! k))).

Lemma elem_of_gfactors_log t u :
  u ∈ gfactors t → ∃ k ν, gfactor_of t u k ν.
Proof.
move=> /elem_of_gfactors_unfold.
rewrite (PreTerm.gfactors_dh _ (wf_unfold_term t)) -/(tdh t).
move=> /PreTerm.elem_of_dh_factors [k [r [ν [kr [νr ue]]]]].
have /FMap.elem_of_to_list [mk nr] := kr.
exists k, ν; rewrite /gfactor_of mk; split=> //; split=> //.
have nD := Frac.den_neq0 r.
have [r' [n' [-> [Er' Hr']]]] := PreTerm.elem_of_exp_factor k _ ν _ nD ue.
have [h [_ [en _]]] := make_mono_canon ν nD (Frac.den_first_neg r).
case: Hr' => Er; first by rewrite Er.
exfalso.
move: Er'; rewrite Er Frac.num_opp en => e.
have e' := Poly.mono_pm_inj n' (ν ∖ h) (or_intror (eq_sym e)).
by apply: (PreTerm.mono_neq_opp n'); rewrite -{1}e e'.
Qed.

Lemma tdh_Ngmul v :
  negb (is_gmul v) → tdh v = {[unfold_term (base v) := lg v]}.
Proof.
rewrite is_gmul_unfold => Nv.
by rewrite /tdh (PreTerm.dh_map_Ngmul _ (wf_unfold_term v) Nv) unfold_base.
Qed.

Lemma exp_factor_canon k (D : Poly.poly PreTerm.pre_term) ν :
  D ≠ Poly.zero → Poly.first_neg D = false →
  PreTerm.exp_factor k D ν =
  {[+ PreTerm.mk_exp k (Frac.make (Poly.mono ν) D) +]}.
Proof.
move=> nD fD; have [h [_ [en _]]] := make_mono_canon ν nD fD.
by rewrite /PreTerm.exp_factor; cbv zeta; rewrite en Poly.first_neg_mono.
Qed.

Lemma gfactor_of_spec t u k ν :
  gfactor_of t u k ν →
  negb (is_gmul u) ∧
  tdh u = {[k := Frac.make (Poly.mono ν) (Frac.den (tdh t !!! k))]} ∧
  pfrac (uprt u) =
  Frac.of_poly (PolyGcd.unit_part (Frac.den (tdh t !!! k))) ∧
  tdh (lpart u) =
  {[k := Frac.make (Poly.mono ν)
           (Poly.mono (PolyGcd.content (Frac.den (tdh t !!! k))))]}.
Proof.
case=> nr [νr eu].
set r := tdh t !!! k in nr νr eu *.
set D := Frac.den r in eu *.
have [wk [gk ar]] := PreTerm.wf_dh_map _ (wf_unfold_term t) k nr.
have nD : D ≠ Poly.zero := Frac.den_neq0 r.
have [h [hν [en eD]]] := make_mono_canon ν nD (Frac.den_first_neg r).
set r' := Frac.make (Poly.mono ν) D in en eD eu *.
have mr : PreTerm.mnum r' by exists (ν ∖ h).
have nr' : r' ≠ Frac.zero := PreTerm.mnum_neq0 _ mr.
have [Nk [Bk Xk]] := PreTerm.mk_exp_mnum _ _ gk mr.
have ar' := PreTerm.atoms_all_make_mono _ _ _ νr ar.
have Nu : negb (is_gmul u) by rewrite is_gmul_unfold eu.
have lu : lg u = r'.
  by rewrite /lg eu Xk; exact: PreTerm.frac_of_mod_aux_wf.
have UD : PolyGcd.unit_part (Frac.den r') = PolyGcd.unit_part D.
  rewrite -[in RHS]eD.
  rewrite (PolyGcd.unit_part_mul _ _ (PolyGcd.mono_neq0 _) (Frac.den_neq0 r')).
  by rewrite PolyGcd.unit_part_mono (left_id Poly.one Poly.mul).
split=> //; split.
  by rewrite /tdh eu (PreTerm.dh_map_mk_exp _ _ gk nr').
split; first by rewrite pfrac_uprt lu UD.
have [Nl [Bl [nl dl]]] := lpart_spec Nu.
rewrite (tdh_Ngmul Nl) Bl unfold_base eu Bk; congr {[_ := _]}.
rewrite -(Frac.make_num_den (lg (lpart u))) nl dl lu en.
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
  tdh t !!! k ≠ Frac.zero → ν ∈ Poly.car (Frac.num (tdh t !!! k)) →
  ∃ u, u ∈ gfactors t ∧ gfactor_of t u k ν.
Proof.
move=> nr νr.
have wd := PreTerm.wf_dh_map _ (wf_unfold_term t).
have [wk [gk ar]] := wd k nr.
set r := tdh t !!! k in nr νr ar *.
set D := Frac.den r.
have nD : D ≠ Poly.zero := Frac.den_neq0 r.
have fD : Poly.first_neg D = false := Frac.den_first_neg r.
set r' := Frac.make (Poly.mono ν) D.
have [h [hν [en eD]]] := make_mono_canon ν nD fD.
have mr : PreTerm.mnum r' by exists (ν ∖ h).
have nr' : r' ≠ Frac.zero := PreTerm.mnum_neq0 _ mr.
have ar' := PreTerm.atoms_all_make_mono _ _ _ νr ar.
have wz : PreTerm.wf (PreTerm.mk_exp k r').
  exact: PreTerm.wf_mk_exp wk gk nr' ar'.
have ez := fold_termK _ wz.
exists (fold_term (PreTerm.mk_exp k r')).
split; last by rewrite /gfactor_of ez; do !split.
apply/elem_of_gfactors_unfold.
rewrite ez (PreTerm.gfactors_dh _ (wf_unfold_term t)) -/(tdh t).
apply/SMS.elem_of_count.
have [Nk [Bk Xk]] := PreTerm.mk_exp_mnum _ _ gk mr.
rewrite (PreTerm.count_dh_factors _ _ wd) Bk -/r /PreTerm.lfactors.
have Z0 : ∀ ν', ν' ∈ Poly.car (Frac.num r) → ν' ≠ ν →
    SMS.count (PreTerm.mk_exp k r') (PreTerm.exp_factor k D ν') = 0%Z.
  move=> ν' ν'r ne; rewrite (exp_factor_canon _ _ nD fD) SMS.count_singleton.
  rewrite bool_decide_eq_false_2 // => e.
  have [h' [_ [en' _]]] := make_mono_canon ν' nD fD.
  have mr'' : PreTerm.mnum (Frac.make (Poly.mono ν') D) by exists (ν' ∖ h').
  have [_ [_ X'']] := PreTerm.mk_exp_mnum _ _ gk mr''.
  have ar'' := PreTerm.atoms_all_make_mono _ _ _ ν'r ar.
  have e' : r' = Frac.make (Poly.mono ν') D.
    have := f_equal (λ pt, PreTerm.frac_of (PreTerm.expo pt)) e; cbv beta.
    rewrite Xk X'' (PreTerm.frac_of_mod_aux_wf _ ar').
    by rewrite (PreTerm.frac_of_mod_aux_wf _ ar'').
  have := Frac.make_cross _ _ _ _ nD nD e'.
  rewrite ![(_ * D)%P](comm Poly.mul) => /(PolyGcd.mul_cancel_l _ _ _ nD) em.
  by apply: ne; apply: (Poly.mono_pm_inj ν' ν); left; rewrite em.
rewrite (SMS.count_bind_single _ _ _ ν Z0) (exp_factor_canon _ _ nD fD).
rewrite SMS.count_singleton bool_decide_eq_true_2 //.
have : SMS.count ν (Poly.car (Frac.num r)) ≠ 0%Z by apply/SMS.elem_of_count.
change (Z.b2z true) with 1%Z; lia.
Qed.

Lemma lg_gfactor t u k ν :
  gfactor_of t u k ν →
  lg u = Frac.make (Poly.mono ν) (Frac.den (tdh t !!! k)).
Proof.
case=> nr [νr eu].
have [wk [gk ar]] := PreTerm.wf_dh_map _ (wf_unfold_term t) k nr.
set r := tdh t !!! k in nr νr eu ar *.
have nD := Frac.den_neq0 r.
have [h [_ [en _]]] := make_mono_canon ν nD (Frac.den_first_neg r).
have mr : PreTerm.mnum (Frac.make (Poly.mono ν) (Frac.den r)).
  by exists (ν ∖ h).
have [_ [_ Xk]] := PreTerm.mk_exp_mnum _ _ gk mr.
rewrite /lg eu Xk; apply: PreTerm.frac_of_mod_aux_wf.
exact: PreTerm.atoms_all_make_mono νr ar.
Qed.

Lemma vars_den_split (D : Poly.poly PreTerm.pre_term) y :
  y ∈ Poly.vars D →
  y ∈ PolyGcd.content D ∨ y ∈ Poly.vars (PolyGcd.unit_part D).
Proof.
move=> /Poly.elem_of_vars [m [mD ym]].
move: mD; rewrite -{1}(PolyGcd.content_unitK D) Poly.car_mul_mono.
move=> /SMS.elem_of_map [n [em nZ]]; rewrite em in ym.
case/MSet.elem_of_disj_union: ym => [yC|yn]; first by left.
by right; apply/Poly.elem_of_vars; exists n.
Qed.

Lemma mset_empty_neq_singleton (a : PreTerm.pre_term) :
  (∅ : MSet.mset PreTerm.pre_term) ≠ {[+ a +]}.
Proof.
move=> /(f_equal (MSet.count a)).
by rewrite MSet.count_empty MSet.count_singleton bool_decide_eq_true_2.
Qed.

Lemma content_den_missing (r : Frac.frac PreTerm.pre_term) a :
  r ≠ Frac.zero → a ∈ PolyGcd.content (Frac.den r) →
  ∃ ν, ν ∈ Poly.car (Frac.num r) ∧ a ∉ ν.
Proof.
move=> nr aD.
case: (decide (Exists (λ ν, MSet.count a ν = 0)
                      (elements (Poly.car (Frac.num r))))).
  case/Exists_exists=> ν [νN aν]; exists ν; split.
    apply/SMS.elem_of_elements; by [|apply/list_elem_of_In].
  exact/MSet.not_elem_of_count.
move=> no; exfalso.
have nN : Frac.num r ≠ Poly.zero := Frac.num_neq0 _ nr.
have aN : a ∈ PolyGcd.content (Frac.num r).
  apply/MSet.singleton_subseteq; apply: PolyGcd.sub_content nN _ => ν νN.
  apply/MSet.singleton_subseteq; apply/MSet.elem_of_count.
  case: (decide (MSet.count a ν = 0)) => [aν|]; last lia.
  case: no; apply/Exists_exists; exists ν; split=> //.
  have νe : ν ∈ elements (Poly.car (Frac.num r)) by apply/SMS.elem_of_elements.
  by [|apply/list_elem_of_In].
have dN : PolyGcd.dvd (Poly.var a) (Frac.num r).
  exact/PolyGcd.var_dvd_content.
have dD : PolyGcd.dvd (Poly.var a) (Frac.den r).
  by apply/PolyGcd.var_dvd_content => //; exact: Frac.den_neq0.
have ne := @mset_empty_neq_singleton a.
case: (PolyGcd.unit_pm1 _ (Frac.num_den_coprime _ _ dN dD)).
- move=> /(f_equal (Poly.coeff ∅)); rewrite Poly.coeff_var Poly.coeff_one.
  by rewrite bool_decide_eq_false_2 // bool_decide_eq_true_2.
- move=> /(f_equal (Poly.coeff ∅)).
  rewrite Poly.coeff_var Poly.coeff_opp Poly.coeff_one.
  by rewrite bool_decide_eq_false_2 // bool_decide_eq_true_2.
Qed.

Lemma gfactor_content_neg t u k ν a :
  gfactor_of t u k ν → a ∈ PolyGcd.content (Frac.den (tdh t !!! k)) →
  a ∉ ν →
  fold_term a ∈ SMS.neg (exps u) ∧ negb (is_mod (fold_term a)) ∧
  unfold_term (fold_term a) = a.
Proof.
move=> G aD aν; have lu := lg_gfactor G.
case: G => nr [νr eu].
have [wk [gk ar]] := PreTerm.wf_dh_map _ (wf_unfold_term t) k nr.
set r := tdh t !!! k in nr νr eu ar aD lu.
have nD := Frac.den_neq0 r.
have [h [hν [en eD]]] := make_mono_canon ν nD (Frac.den_first_neg r).
have [m [mD am]] := PreTerm.elem_of_content _ _ aD.
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

Lemma is_mod_uprt u : is_mod (uprt u).
Proof.
rewrite is_mod_unfold /uprt fold_termK; last first.
  exact: PreTerm.wf_mod_aux (@atoms_unit_part u).
rewrite /PreTerm.mod_aux /PreTerm.mod_of_lists.
case E: (PreTerm.lone_atom _) => [x|] //.
move/PreTerm.lone_atom_Some: E => E; exfalso.
set Z := PolyGcd.unit_part (Frac.den (lg u)) in E.
have EZ : Frac.of_poly Z = Frac.of_poly (Poly.var x).
  by apply: PreTerm.lists_inj; rewrite PreTerm.lists_var.
have := PolyGcd.content_unit_part (Frac.den (lg u)).
rewrite -/Z (Frac.of_poly_inj _ _ EZ) Poly.varE PolyGcd.content_mono.
by move=> e; apply: (@mset_empty_neq_singleton x); rewrite e.
Qed.


Lemma exps_pos_atom t u : u ∈ SMS.pos (exps t) → negb (is_mod u).
Proof.
move=> ut; have xt := is_exp_of_exps (SMS.elem_of_pos _ _ ut).
have Nt : negb (is_gmul t) by apply: is_exp_Ngmul.
have [M eM] := lg_mnum Nt.
move/count_gt0: ut; rewrite /exps (count_expo _ eM) => h.
have uM : unfold_term u ∈ M by apply/MSet.elem_of_count; lia.
have mM : M ∈ Poly.car (Frac.num (lg t)).
  by rewrite eM Poly.car_mono; exact/SMS.elem_of_singleton.
have /andb_True [_] := @lg_atoms t M _ (or_introl mM) uM.
by rewrite -is_mod_unfold.
Qed.

Lemma count_strip t f y :
  negb (is_gmul t) → f ∈ satoms (exps t) → y ≠ f →
  negb (is_gmul (TExp t (TInv f))) ∧ base (TExp t (TInv f)) = base t ∧
  (count y (expo t) ≤ count y (expo (TExp t (TInv f))))%Z.
Proof.
move=> Nt; have [M eM] := lg_mnum Nt.
have A := @lg_atoms t.
set D := Frac.den (lg t).
have nD : D ≠ Poly.zero := Frac.den_neq0 (lg t).
rewrite /exps elem_of_satoms_count.
case=> [h|[x [-> h]]] yf.
- move: h; rewrite (count_expo _ eM) => h.
  have fM : unfold_term f ∈ M by apply/MSet.elem_of_count; lia.
  have [wf nf'] : PreTerm.wf (unfold_term f) ∧
                  negb (PreTerm.is_mod (unfold_term f)).
    apply/andb_True; apply: (A M) fM; left.
    by rewrite eM Poly.car_mono; apply/SMS.elem_of_singleton.
  have ef : pfrac (TInv f) = Frac.inv (Frac.var (unfold_term f)).
    by rewrite efrac_TInv PreTerm.frac_of_var.
  have [en ed] := Frac.mul_inv_var_canon (lg t) M (unfold_term f) eM fM.
  have mr : PreTerm.mnum (Frac.mul (lg t) (pfrac (TInv f))).
    by exists (M ∖ {[+ unfold_term f +]}); rewrite ef en.
  have [N [B L]] := lg_TExp Nt mr.
  split=> //; split=> //.
  have ne : unfold_term y ≠ unfold_term f by move=> /unfold_term_inj.
  rewrite (@count_expo (TExp t (TInv f)) y (M ∖ {[+ unfold_term f +]}));
    last by rewrite L ef en.
  rewrite L ef ed MSet.count_difference MSet.count_singleton.
  rewrite bool_decide_eq_false_2 // (count_expo _ eM); lia.
- have ef : TExp t (TInv (TInv x)) = TExp t x by rewrite TInvK.
  rewrite ef.
  move: h; rewrite (count_expo _ eM) -/D => h.
  case: (decide (x = uprt t)) => [ex|nx].
  + subst x.
    have [en ed] := Frac.mul_unit_part_canon (lg t) M eM.
    have mr : PreTerm.mnum (Frac.mul (lg t) (pfrac (uprt t))).
      by exists M; rewrite pfrac_uprt en.
    have [N [B L]] := lg_TExp Nt mr.
    split=> //; split=> //.
    rewrite (@count_expo (TExp t (uprt t)) y M);
      last by rewrite L pfrac_uprt en.
    rewrite L pfrac_uprt ed -/D PolyGcd.content_mono PreTerm.units_mono.
    rewrite (right_id ∅ (⊎)) (count_expo _ eM) -/D.
    rewrite MSet.count_disj_union; lia.
  + move: h; rewrite MSet.count_disj_union (count_units_uprt nx) => h.
    have xc : unfold_term x ∈ PolyGcd.content D.
      by apply/MSet.elem_of_count; lia.
    have [n [nD' xn]] := PreTerm.elem_of_content _ _ xc.
    have [wx nx'] : PreTerm.wf (unfold_term x) ∧
                    negb (PreTerm.is_mod (unfold_term x)).
      by apply/andb_True; apply: (A n) xn; right.
    have ex' : pfrac x = Frac.var (unfold_term x).
      by rewrite PreTerm.frac_of_var.
    have [en [ed eD]] :=
      Frac.mul_var_content_canon (lg t) M (unfold_term x) eM xc.
    have mr : PreTerm.mnum (Frac.mul (lg t) (pfrac x)).
      by exists M; rewrite ex' en.
    have [N [B L]] := lg_TExp Nt mr.
    split=> //; split=> //.
    set Dc := PolyGcd.unmono {[+ unfold_term x +]} D in ed eD.
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
    have UU : PreTerm.units D = PreTerm.units Dc by rewrite /PreTerm.units UD.
    rewrite CD UU !MSet.count_disj_union; lia.
Qed.

Lemma atoms_uprt u y :
  y ∈ atoms (uprt u) ↔
  ∃ a, y = fold_term a ∧
       a ∈ Poly.vars (PolyGcd.unit_part (Frac.den (lg u))).
Proof.
rewrite elem_of_atoms /PreTerm.atoms pfrac_uprt /PreTerm.frac_vars.
rewrite Frac.num_of_poly Frac.den_of_poly; split.
- case=> a [-> /elem_of_app [aZ|a1]]; first by exists a.
  move/Poly.elem_of_vars: a1 => [m []].
  rewrite Poly.oneE Poly.car_mono => /SMS.elem_of_singleton -> am.
  by case: (MSet.not_elem_of_empty _ am).
- by case=> a [-> aZ]; exists a; split=> //; apply/elem_of_app; left.
Qed.

Lemma atoms_make_monos (P : PreTerm.pre_term → Prop)
    (X Y : MSet.mset PreTerm.pre_term) :
  (∀ y, y ∈ X ∨ y ∈ Y → P y) →
  PreTerm.atoms_all P (Frac.make (Poly.mono X) (Poly.mono Y)).
Proof.
move=> h; apply: (PreTerm.atoms_all_over _ (elements (X ⊎ Y))).
  apply: Frac.over_make; apply: PreTerm.over_of_atoms => m x;
    rewrite Poly.car_mono => /SMS.elem_of_singleton -> xm;
    apply/MSet.elem_of_elements/MSet.elem_of_disj_union; by [left|right].
by move=> x /MSet.elem_of_elements /MSet.elem_of_disj_union; exact: h.
Qed.

Lemma laurent_shift v w k (μ ν C C' : MSet.mset PreTerm.pre_term)
    (pub : PreTerm.pre_term → bool) :
  tdh v = {[k := Frac.make (Poly.mono μ) (Poly.mono C)]} →
  tdh w = {[k := Frac.make (Poly.mono ν) (Poly.mono C')]} →
  PolyRestrict.sec pub μ = PolyRestrict.sec pub ν →
  (∀ y, y ∈ μ ∨ y ∈ ν ∨ y ∈ C ∨ y ∈ C' →
        PreTerm.wf y && negb (PreTerm.is_mod y)) →
  ∃ π, laurent π ∧
       (∀ y, y ∈ atoms π → ∃ a, y = fold_term a ∧
             (a ∈ C ∨ a ∈ C' ∨ pub a)) ∧
       w = TExp v π.
Proof.
move=> ev ew es hw.
set X := PolyRestrict.pubp pub ν ⊎ C.
set Y := PolyRestrict.pubp pub μ ⊎ C'.
have pp z m : z ∈ PolyRestrict.pubp pub m → z ∈ m.
  move=> /MSet.elem_of_count; rewrite PolyRestrict.count_pubp.
  by case: (pub z) => h; [apply/MSet.elem_of_count|lia].
have AW : PreTerm.atoms_all (λ x, PreTerm.wf x && negb (PreTerm.is_mod x))
            (Frac.make (Poly.mono X) (Poly.mono Y)).
  apply: atoms_make_monos => y.
  case=> /MSet.elem_of_disj_union [/pp yp|yc]; apply: hw; tauto.
have wπ := PreTerm.wf_mod_aux _ AW.
set π := fold_term (PreTerm.mod_aux (Frac.make (Poly.mono X) (Poly.mono Y))).
have eπ : pfrac π = Frac.make (Poly.mono X) (Poly.mono Y).
  by rewrite /π fold_termK // PreTerm.frac_of_mod_aux_wf.
exists π; split.
  apply/laurent_unfold.
  apply/(PreTerm.laurent_mfrac _ (wf_unfold_term _)); rewrite eπ.
  exact: PreTerm.mfrac_make_mono.
split.
  move=> y /elem_of_atoms [a [-> ap]]; exists a; split=> //.
  move: ap; rewrite /PreTerm.atoms eπ => ap.
  have oXY : Frac.over (elements (X ⊎ Y))
               (Frac.make (Poly.mono X) (Poly.mono Y)).
    apply: Frac.over_make; apply: PreTerm.over_of_atoms => m x;
      rewrite Poly.car_mono => /SMS.elem_of_singleton -> xm;
      apply/MSet.elem_of_elements/MSet.elem_of_disj_union; by [left|right].
  move: ap; rewrite /PreTerm.frac_vars elem_of_app !Poly.elem_of_vars.
  case=> -[m [mr am]];
    have := Frac.over_elem _ _ m a oXY ltac:(tauto) am;
    move=> /MSet.elem_of_elements /MSet.elem_of_disj_union [];
    move=> /MSet.elem_of_disj_union [ap|ac]; try tauto;
    right; right; move/MSet.elem_of_count: ap; rewrite PolyRestrict.count_pubp;
    by case: (pub a) => //; lia.
apply: tdh_inj; apply/FMap.fmap_eq => k'.
rewrite tdh_TExp unfold_frac_of eπ ev ew !FMap.lookup_singleton.
case: bool_decide; last by rewrite Frac.mul_zero_l.
rewrite Frac.mul_make; try exact: PolyGcd.mono_neq0.
apply: Frac.make_eq; try exact: PolyGcd.mul_neq0 (PolyGcd.mono_neq0 _)
  (PolyGcd.mono_neq0 _).
  exact: PolyGcd.mono_neq0.
rewrite !Poly.mul_mono; congr Poly.mono.
apply: MSet.count_inj => z; rewrite /X /Y !MSet.count_disj_union.
have Eμ := f_equal (MSet.count z) (PolyRestrict.sec_pubp pub μ).
have Eν := f_equal (MSet.count z) (PolyRestrict.sec_pubp pub ν).
have Es := f_equal (MSet.count z) es.
rewrite !MSet.count_disj_union in Eμ Eν; lia.
Qed.

Lemma count_expo_gfactor t u k ν y :
  gfactor_of t u k ν → negb (is_mod y) →
  count y (expo u) =
  (Z.of_nat (MSet.count (unfold_term y) ν) -
   Z.of_nat (MSet.count (unfold_term y)
               (PolyGcd.content (Frac.den (tdh t !!! k)))))%Z.
Proof.
move=> G ny; have lu := lg_gfactor G.
case: G => nr [νr eu].
set r := tdh t !!! k in nr νr eu lu *.
have nD := Frac.den_neq0 r.
have [h [hν [en eD]]] := make_mono_canon ν nD (Frac.den_first_neg r).
have nden := Frac.den_neq0 (Frac.make (Poly.mono ν) (Frac.den r)).
have CD : PolyGcd.content (Frac.den r) =
          h ⊎ PolyGcd.content (Frac.den (Frac.make (Poly.mono ν) (Frac.den r))).
  rewrite -[in LHS]eD (PolyGcd.content_mul _ _ (PolyGcd.mono_neq0 _) nden).
  by rewrite PolyGcd.content_mono.
rewrite (@count_expo u y (ν ∖ h)); last by rewrite lu en.
rewrite lu MSet.count_difference MSet.count_disj_union CD MSet.count_disj_union.
have -> : MSet.count (unfold_term y)
            (PreTerm.units (Frac.den (Frac.make (Poly.mono ν) (Frac.den r))))
          = 0.
  apply/MSet.not_elem_of_count => /PreTerm.units_mod.
  by rewrite -is_mod_unfold; move: ny; case: (is_mod y).
have := proj1 (MSet.subseteq_count _ _) hν (unfold_term y); lia.
Qed.

(** ** Logarithms *)

Section Log.

Add Ring log_ring : (Frac.frac_ring_theory (T := PreTerm.pre_term)).
Add Field log_field : (Frac.frac_field_theory (T := PreTerm.pre_term)).
Add Field tlog_field : (Frac.frac_field_theory (T := term)).

Lemma wf_mod_aux_tdh t k : PreTerm.wf (PreTerm.mod_aux (tdh t !!! k)).
Proof.
case: (decide (tdh t !!! k = Frac.zero)) => [->|nz].
  by apply: PreTerm.wf_mod_aux; exact: PreTerm.atoms_all_zero.
have [_ [_ ar]] := PreTerm.wf_dh_map _ (wf_unfold_term t) k nz.
exact: PreTerm.wf_mod_aux.
Qed.

(** The exponent of the base [k] in [t]. *)
Definition log k t : term :=
  fold_term (PreTerm.mod_aux (tdh t !!! unfold_term k)).

Lemma pfrac_log k t : pfrac (log k t) = tdh t !!! unfold_term k.
Proof.
rewrite /log fold_termK; last exact: wf_mod_aux_tdh.
case: (decide (tdh t !!! unfold_term k = Frac.zero)) => [->|nz].
  by apply: PreTerm.frac_of_mod_aux_wf; exact: PreTerm.atoms_all_zero.
have [_ [_ ar]] := PreTerm.wf_dh_map _ (wf_unfold_term t) _ nz.
exact: PreTerm.frac_of_mod_aux_wf.
Qed.

Lemma log_eq k t u : tdh t !!! unfold_term k = pfrac u → log k t = u.
Proof.
move=> e; apply: unfold_term_inj.
rewrite -[unfold_term u]PreTerm.mod_aux_frac_of; last exact: wf_unfold_term.
by rewrite -e /log fold_termK //; exact: wf_mod_aux_tdh.
Qed.

Lemma log_TGMul2 k t1 t2 :
  log k (TGMul {[+ t1; t2 +]}) = TSum {[+ log k t1; log k t2 +]}.
Proof.
apply: log_eq; rewrite tdh_TGMul -unfold_frac_of frac_of_TSum.
rewrite !Frac.ssum_disj_union !Frac.ssum_singleton.
by rewrite (Frac.map_add _ unfold_term_inj) !unfold_frac_of !pfrac_log.
Qed.

Lemma log_TExp k t e : log k (TExp t e) = TMul {[+ log k t; e +]}.
Proof.
apply: log_eq; rewrite tdh_TExp -unfold_frac_of frac_of_TMul2.
by rewrite (Frac.map_mul _ unfold_term_inj) !unfold_frac_of pfrac_log.
Qed.

Lemma log_unit k : log k (TGMul ∅) = TSum ∅.
Proof.
apply: log_eq; rewrite tdh_TGMul_empty -unfold_frac_of frac_of_TSum_empty.
by rewrite Frac.map_zero.
Qed.

Lemma log_atom k u :
  negb (is_exp u) → negb (is_gmul u) →
  log k u = if bool_decide (u = k) then TMul ∅ else TSum ∅.
Proof.
move=> uX uG; apply: log_eq.
rewrite (tdh_Ngmul uG) (base_expN uX) (lg_Nexp uX) FMap.lookup_singleton.
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
move=> e; apply: tdh_inj; apply/FMap.fmap_eq => k.
case: (decide (PreTerm.wf k)) => [wk|nk].
  by rewrite -(fold_termK _ wk) -!pfrac_log e.
have z t : tdh t !!! k = Frac.zero.
  case: (decide (tdh t !!! k = Frac.zero)) => // nz; case: nk.
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
have I c : h ∉ atoms c → PreTerm.atoms_all (λ z, z ≠ y) (pfrac c).
  move=> hc; apply/PreTerm.atoms_all_vars => z zc ez; apply: hc.
  apply/elem_of_atoms; exists z; split; last exact: zc.
  by rewrite ez /y unfold_termK.
have eH : pfrac h = Frac.of_poly (Poly.var y).
  by apply: PreTerm.frac_of_Nmod; rewrite -is_mod_unfold.
have inj c d : pfrac c = pfrac d → c = d.
  move=> e; apply: frac_of_inj.
  apply: (Frac.map_inj unfold_term unfold_term_inj).
  by rewrite !unfold_frac_of.
move/(f_equal (Frac.map unfold_term)).
rewrite !(Frac.map_add _ unfold_term_inj) !(Frac.map_mul _ unfold_term_inj).
rewrite !unfold_frac_of eH.
set Y := Frac.of_poly (Poly.var y) => E.
case: (decide (pfrac c1 = pfrac d1)) => [e1|n1].
  split; last exact: inj.
  apply: inj.
  transitivity (Frac.sub (Frac.add (pfrac c0) (Frac.mul (pfrac c1) Y))
                         (Frac.mul (pfrac c1) Y)); first ring.
  by rewrite E e1; ring.
exfalso.
have nz : Frac.sub (pfrac c1) (pfrac d1) ≠ Frac.zero.
  move=> e; apply: n1.
  transitivity (Frac.add (Frac.sub (pfrac c1) (pfrac d1)) (pfrac d1));
    first ring.
  by rewrite e; ring.
have e2 : Frac.mul (Frac.sub (pfrac c1) (pfrac d1)) Y =
          Frac.sub (pfrac d0) (pfrac c0).
  transitivity (Frac.sub (Frac.add (pfrac c0) (Frac.mul (pfrac c1) Y))
                  (Frac.add (pfrac c0) (Frac.mul (pfrac d1) Y))); first ring.
  by rewrite E; ring.
have eY : Y = Frac.div (Frac.sub (pfrac d0) (pfrac c0))
                       (Frac.sub (pfrac c1) (pfrac d1)).
  by rewrite -e2; field.
have : PreTerm.atoms_all (λ z, z ≠ y) Y.
  rewrite eY; apply: PreTerm.atoms_all_div; apply: PreTerm.atoms_all_sub;
    exact: I.
move=> /(_ {[+ y +]} y) H; apply: H => //.
- by left; rewrite /Y PreTerm.car_num_var; apply/SMS.elem_of_singleton.
- exact/MSet.elem_of_singleton.
Qed.

End Log.
