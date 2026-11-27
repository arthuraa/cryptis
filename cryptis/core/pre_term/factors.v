(** Factors of exponents *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list_numbers.
From cryptis.lib Require Import list_sort fmap mset sms poly poly_gcd frac.
From cryptis.core.pre_term Require Import base with_stdpp normalize.

Module PreTerm.
Import base.PreTerm normalize.PreTerm.

Local Abbreviation poly := (Poly.poly pre_term).

(** ** Scalars

    [mul s] and [sum s] multiply and add up the scalars of a signed multiset
    through their fractions ([frac_of_mul], [frac_of_sum]).  [factors pt]
    lists the atoms of the monomial content of the numerator of [frac_of pt]
    (positively) and of its denominator (negatively), with their unit parts
    when these are not [1], so that [mul (factors pt) = pt] ([factorsK]).
    On an atom [x], [count x pt] is the [x]-adic valuation of [pt]
    ([count_valuation]). *)

Definition mul (s : SMS.sms pre_term) : pre_term :=
  mod_of_frac (Frac.sprod frac_of s).

Definition sum (s : SMS.sms pre_term) : pre_term :=
  mod_of_frac (Frac.ssum frac_of s).

Definition unit_factors (p : poly) : MSet.mset pre_term :=
  if bool_decide (PolyGcd.unit_part p = Poly.one) then ∅
  else {[+ mod_of_frac (Frac.of_poly (PolyGcd.unit_part p)) +]}.

Definition factors pt : SMS.sms pre_term :=
  SMS.make
    (PolyGcd.content (Frac.num (frac_of pt)) ⊎ unit_factors
      (Frac.num (frac_of pt)))
    (PolyGcd.content (Frac.den (frac_of pt)) ⊎ unit_factors
      (Frac.den (frac_of pt))).

Definition count x pt : Z := SMS.count x (factors pt).

Lemma sum_empty : sum ∅ = PT0 O0Zero.
Proof. by rewrite /sum Frac.ssum_empty mod_of_frac_zero. Qed.

Lemma all_vars_fprod_frac_of P (l : list pre_term) :
  (∀ x, x ∈ l → Frac.all_vars P (frac_of x)) →
  Frac.all_vars P (Frac.fprod (frac_of <$> l)).
Proof.
move=> h; apply: Frac.all_vars_fprod; apply/Forall_fmap/list.Forall_forall.
by move=> x /h.
Qed.

Lemma all_vars_fsum_frac_of P (l : list pre_term) :
  (∀ x, x ∈ l → Frac.all_vars P (frac_of x)) →
  Frac.all_vars P (Frac.fsum (frac_of <$> l)).
Proof.
move=> h; apply: Frac.all_vars_fsum; apply/Forall_fmap/list.Forall_forall.
by move=> x /h.
Qed.

Lemma all_vars_sprod_frac_of P s :
  (∀ x, x ∈ s → Frac.all_vars P (frac_of x)) →
  Frac.all_vars P (Frac.sprod frac_of s).
Proof.
move=> h; rewrite Frac.sprodE; apply: Frac.all_vars_div;
  apply: all_vars_fprod_frac_of => x /MSet.elem_of_elements hx; apply: h.
- exact: SMS.elem_of_pos hx.
- exact: SMS.elem_of_neg hx.
Qed.

Lemma all_vars_ssum_frac_of P s :
  (∀ x, x ∈ s → Frac.all_vars P (frac_of x)) →
  Frac.all_vars P (Frac.ssum frac_of s).
Proof.
move=> h; rewrite Frac.ssumE; apply: Frac.all_vars_sub;
  apply: all_vars_fsum_frac_of => x /MSet.elem_of_elements hx; apply: h.
- exact: SMS.elem_of_pos hx.
- exact: SMS.elem_of_neg hx.
Qed.

Lemma wf_mul s : (∀ x, x ∈ s → wf x) → wf (mul s).
Proof.
move=> h; apply: wf_mod_of_frac.
by apply: all_vars_sprod_frac_of => x /h; exact: frac_of_atoms.
Qed.

Lemma wf_sum s : (∀ x, x ∈ s → wf x) → wf (sum s).
Proof.
move=> h; apply: wf_mod_of_frac.
by apply: all_vars_ssum_frac_of => x /h; exact: frac_of_atoms.
Qed.

Lemma frac_of_mul s :
  (∀ x, x ∈ s → wf x) → frac_of (mul s) = Frac.sprod frac_of s.
Proof.
move=> h; apply: frac_of_mod_of_frac_wf.
by apply: all_vars_sprod_frac_of => x /h; exact: frac_of_atoms.
Qed.

Lemma frac_of_sum s :
  (∀ x, x ∈ s → wf x) → frac_of (sum s) = Frac.ssum frac_of s.
Proof.
move=> h; apply: frac_of_mod_of_frac_wf.
by apply: all_vars_ssum_frac_of => x /h; exact: frac_of_atoms.
Qed.

Lemma unit_factors_mod (p : poly) y : y ∈ unit_factors p → is_mod y.
Proof.
rewrite /unit_factors; case: bool_decide_reflect => [_|nu].
  by move=> h; case: (MSet.not_elem_of_empty _ h).
move=> /MSet.elem_of_singleton ->.
case E: (is_mod (mod_of_frac (Frac.of_poly (PolyGcd.unit_part p)))) => //.
exfalso; have [z [Er _]] := mod_of_frac_Nmod _ E.
have := PolyGcd.content_unit_part p.
rewrite (Frac.of_poly_inj _ _ Er) Poly.varE PolyGcd.content_mono.
move=> /(f_equal (MSet.count z)); rewrite MSet.count_singleton MSet.count_empty.
by rewrite bool_decide_eq_true_2.
Qed.

Lemma frac_of_unit_factors (p : poly) y :
  (∀ m x, m ∈ Poly.car p → x ∈ m → negb (is_mod x)) →
  y ∈ unit_factors p → frac_of y = Frac.of_poly (PolyGcd.unit_part p).
Proof.
move=> h; rewrite /unit_factors; case: bool_decide_reflect => [_|_].
  by move=> e; case: (MSet.not_elem_of_empty _ e).
move=> /MSet.elem_of_singleton ->; apply: frac_of_mod_of_frac.
apply: Frac.all_vars_of_poly => m x mu xm.
have [m' [m'p xm']] := PolyGcd.elem_of_unit_part x p m mu xm.
exact: h m'p xm'.
Qed.

Lemma wf_unit_factors (p : poly) y :
  (∀ m x, m ∈ Poly.car p → x ∈ m → wf x && negb (is_mod x)) →
  y ∈ unit_factors p → wf y.
Proof.
move=> h; rewrite /unit_factors; case: bool_decide_reflect => [_|_].
  by move=> e; case: (MSet.not_elem_of_empty _ e).
move=> /MSet.elem_of_singleton ->; apply: wf_mod_of_frac.
apply: Frac.all_vars_of_poly => m x mu xm.
have [m' [m'p xm']] := PolyGcd.elem_of_unit_part x p m mu xm.
exact: h m'p xm'.
Qed.

Lemma wf_factors pt y : wf pt → y ∈ factors pt → wf y.
Proof.
move=> wpt; have A := frac_of_atoms pt wpt.
have hn : ∀ m x, m ∈ Poly.car (Frac.num (frac_of pt)) → x ∈ m →
    wf x && negb (is_mod x).
  by move=> m x mr xm; apply: (A m x) => //; left.
have hd : ∀ m x, m ∈ Poly.car (Frac.den (frac_of pt)) → x ∈ m →
    wf x && negb (is_mod x).
  by move=> m x mr xm; apply: (A m x) => //; right.
rewrite /factors => /SMS.elem_of_make [] /MSet.elem_of_disj_union [].
- move=> /(PolyGcd.elem_of_content y) [m [mr xm]].
  by have /andb_True [] := hn m y mr xm.
- exact: wf_unit_factors hn.
- move=> /(PolyGcd.elem_of_content y) [m [mr xm]].
  by have /andb_True [] := hd m y mr xm.
- exact: wf_unit_factors hd.
Qed.

Lemma factors_atom pt : negb (is_mod pt) → factors pt = {[+ pt +]}.
Proof.
move=> npt.
rewrite /factors (frac_of_Nmod _ npt) Frac.num_of_poly Frac.den_of_poly.
rewrite Poly.varE Poly.oneE !PolyGcd.content_mono /unit_factors.
rewrite !PolyGcd.unit_part_mono bool_decide_eq_true_2 //.
by rewrite !(right_id ∅ (⊎)) -SMS.singleton_make.
Qed.

Lemma count_valuation x pt :
  negb (is_mod x) → count x pt = Frac.valuation x (frac_of pt).
Proof.
move=> nx.
have U p : MSet.count x (unit_factors p) = 0.
  apply/MSet.not_elem_of_count => /unit_factors_mod.
  by case: (is_mod x) nx.
rewrite /count /factors SMS.count_make !MSet.count_disj_union !U
  Frac.valuationE.
lia.
Qed.

Lemma frac_of_var pt : negb (is_mod pt) → frac_of pt = Frac.var pt.
Proof. by rewrite Frac.varE; exact: frac_of_Nmod. Qed.

Lemma fprod_frac_of_var (l : list pre_term) :
  (∀ x, x ∈ l → negb (is_mod x)) →
  Frac.fprod (frac_of <$> l) = Frac.fprod (Frac.var <$> l).
Proof.
elim: l => [|x l IH] h; first by [].
have hl : ∀ y, y ∈ l → negb (is_mod y) by move=> y yl; apply: h; right.
rewrite !fmap_cons !Frac.fprod_cons (IH hl) frac_of_var //.
by apply: h; left.
Qed.

Lemma frac_of_unit_part (p : poly) :
  (∀ m x, m ∈ Poly.car p → x ∈ m → negb (is_mod x)) →
  frac_of (mod_of_frac (Frac.of_poly (PolyGcd.unit_part p))) =
  Frac.of_poly (PolyGcd.unit_part p).
Proof.
move=> h; apply: frac_of_mod_of_frac; apply: Frac.all_vars_of_poly => m x mu xm.
have [m' [m'p xm']] := PolyGcd.elem_of_unit_part x p m mu xm.
exact: h m'p xm'.
Qed.

Lemma fprod_unit_factors (p : poly) :
  (∀ m x, m ∈ Poly.car p → x ∈ m → negb (is_mod x)) →
  Frac.fprod (frac_of <$> elements (unit_factors p)) =
  Frac.of_poly (PolyGcd.unit_part p).
Proof.
move=> h; rewrite /unit_factors; case: bool_decide_reflect => [->|nu].
  by rewrite MSet.elements_empty fmap_nil Frac.fprod_nil Frac.oneE.
rewrite MSet.elements_singleton fmap_cons fmap_nil.
rewrite Frac.fprod_cons Frac.fprod_nil frac_of_unit_part //.
by rewrite (comm Frac.mul) (left_id Frac.one Frac.mul).
Qed.

Lemma fprod_content_unit_factors (p : poly) :
  (∀ m x, m ∈ Poly.car p → x ∈ m → negb (is_mod x)) →
  Frac.fprod (frac_of <$> elements (PolyGcd.content p ⊎ unit_factors p)) =
  Frac.of_poly p.
Proof.
move=> h.
have C : ∀ x, x ∈ elements (PolyGcd.content p) → negb (is_mod x).
  move=> x /MSet.elem_of_elements /(PolyGcd.elem_of_content x) [m [mp xm]].
  exact: h mp xm.
rewrite Frac.fprod_disj_union fprod_unit_factors // (fprod_frac_of_var _ C).
by rewrite Frac.fprod_var -Frac.of_poly_mul PolyGcd.content_unitK.
Qed.

Lemma frac_of_unit_factors_neq0 (p : poly) y :
  (∀ m x, m ∈ Poly.car p → x ∈ m → negb (is_mod x)) → p ≠ Poly.zero →
  y ∈ PolyGcd.content p ⊎ unit_factors p → frac_of y ≠ Frac.zero.
Proof.
move=> h np /MSet.elem_of_disj_union [].
- move=> /(PolyGcd.elem_of_content y) [m [mp xm]].
  rewrite frac_of_var; last exact: h mp xm.
  exact: Frac.var_neq0.
- move=> yu; rewrite (frac_of_unit_factors p y h yu) Frac.zeroE
    => /Frac.of_poly_inj.
  exact: PolyGcd.unit_part_neq0.
Qed.

Lemma factorsK pt : wf pt → mul (factors pt) = pt.
Proof.
move=> wpt; have A := frac_of_atoms pt wpt.
have hn : ∀ m x, m ∈ Poly.car (Frac.num (frac_of pt)) → x ∈ m →
    negb (is_mod x).
  by move=> m x mr xm; have /andb_True [] := A m x (or_introl mr) xm.
have hd : ∀ m x, m ∈ Poly.car (Frac.den (frac_of pt)) → x ∈ m →
    negb (is_mod x).
  by move=> m x mr xm; have /andb_True [] := A m x (or_intror mr) xm.
have S : ∀ x, x ∈ PolyGcd.content (Frac.num (frac_of pt)) ⊎
                  unit_factors (Frac.num (frac_of pt)) →
              x ∈ PolyGcd.content (Frac.den (frac_of pt)) ⊎
                  unit_factors (Frac.den (frac_of pt)) →
              frac_of x ≠ Frac.zero.
  move=> x _; apply: frac_of_unit_factors_neq0 hd _; exact: Frac.den_neq0.
rewrite /mul /factors (Frac.sprod_make _ _ _ S) !fprod_content_unit_factors //.
by rewrite -Frac.make_div Frac.make_num_den mod_of_frac_frac_of.
Qed.

Lemma unit_factors_mono X : unit_factors (Poly.mono X) = ∅.
Proof. by rewrite /unit_factors PolyGcd.unit_part_mono bool_decide_eq_true_2.
  Qed.

Lemma factors_mul_atoms s :
  (∀ x, x ∈ s → wf x ∧ negb (is_mod x)) → factors (mul s) = s.
Proof.
move=> h.
have W : ∀ x, x ∈ s → wf x by move=> x /h [].
have E : Frac.sprod frac_of s = Frac.sprod Frac.var s.
  by apply: Frac.sprod_ext => x /h [_ nx]; exact: frac_of_var.
have [en ed] := Frac.sprod_var_canon s.
rewrite /factors (frac_of_mul _ W) E en ed !PolyGcd.content_mono
  !unit_factors_mono.
by rewrite !(right_id ∅ (⊎)) SMS.make_pos_neg.
Qed.

Lemma elem_of_atoms x pt :
  x ∈ atoms pt ↔
  ∃ m, (m ∈ Poly.car (Frac.num (frac_of pt)) ∨
        m ∈ Poly.car (Frac.den (frac_of pt))) ∧ x ∈ m.
Proof.
rewrite /atoms /Frac.vars elem_of_app !Poly.elem_of_vars.
split.
- by case=> -[m [mp xm]]; exists m; split=> //; [left|right].
- by case=> m [[mp|mp] xm]; [left|right]; exists m.
Qed.

Lemma atoms_wf pt x : wf pt → x ∈ atoms pt → wf x ∧ negb (is_mod x).
Proof.
move=> wpt /elem_of_atoms [m [mp xm]].
by have /andb_True := frac_of_atoms pt wpt m x mp xm.
Qed.

Lemma atoms_atom pt x : negb (is_mod pt) → x ∈ atoms pt ↔ x = pt.
Proof.
move=> npt; rewrite elem_of_atoms (frac_of_Nmod _ npt).
rewrite Frac.car_num_var Frac.car_den_of_poly; split.
- case=> m [[/SMS.elem_of_singleton ->|/SMS.elem_of_singleton ->]].
    by move/MSet.elem_of_singleton.
  by move=> e; case: (MSet.not_elem_of_empty _ e).
- move=> ->; exists {[+ pt +]}; split.
    by left; apply/SMS.elem_of_singleton.
  exact/MSet.elem_of_singleton.
Qed.

(** ** Laurent monomials

    A fraction is a Laurent monomial ([Frac.laurent]) when its numerator and its
    denominator are monomials; a pre-term is [laurent] when its factors are
    atoms, which happens exactly when its fraction is a Laurent monomial
    ([laurent_frac_of]). *)

Section Laurent.

Add Ring poly_ring_M : (Poly.poly_ring_theory (T := pre_term)).

Definition laurent pt : Prop := ∀ x, x ∈ factors pt → negb (is_mod x).

Lemma laurent_frac_of pt : wf pt → laurent pt ↔ Frac.laurent (frac_of pt).
Proof.
move=> wpt; split.
- move=> L; rewrite -(factorsK _ wpt).
  rewrite (frac_of_mul _ (λ x hx, wf_factors _ _ wpt hx)).
  have E : Frac.sprod frac_of (factors pt) = Frac.sprod Frac.var (factors pt).
    by apply: Frac.sprod_ext => x /L; exact: frac_of_var.
  rewrite E; exact: Frac.laurent_sprod_var.
- move=> [n [Q [en eQ]]] x; rewrite /factors en eQ !PolyGcd.content_mono.
  rewrite !unit_factors_mono !(right_id ∅ (⊎)) => /SMS.elem_of_make hx.
  have A := frac_of_atoms pt wpt.
  have nn : n ∈ Poly.car (Frac.num (frac_of pt)).
    by rewrite en Poly.car_mono; apply/SMS.elem_of_singleton.
  have nQ : Q ∈ Poly.car (Frac.den (frac_of pt)).
    by rewrite eQ Poly.car_mono; apply/SMS.elem_of_singleton.
  case: hx => hx.
  + by have /andb_True [] := A n x (or_introl nn) hx.
  + by have /andb_True [] := A Q x (or_intror nQ) hx.
Qed.

End Laurent.

Lemma factors_mono_num pt M :
  Frac.num (frac_of pt) = Poly.mono M →
  factors pt =
  SMS.make M (PolyGcd.content (Frac.den (frac_of pt)) ⊎
              unit_factors (Frac.den (frac_of pt))).
Proof.
move=> e; rewrite /factors e PolyGcd.content_mono unit_factors_mono.
by rewrite (right_id ∅ (⊎)).
Qed.

Lemma factors_atoms pt x : x ∈ factors pt → negb (is_mod x) → x ∈ atoms pt.
Proof.
rewrite /factors => /SMS.elem_of_make [] /MSet.elem_of_disj_union [] h nx.
- have [m [mp xm]] := PolyGcd.elem_of_content _ _ h.
  by apply/elem_of_atoms; exists m; split=> //; left.
- by move: (unit_factors_mod _ _ h); case: (is_mod x) nx.
- have [m [mp xm]] := PolyGcd.elem_of_content _ _ h.
  by apply/elem_of_atoms; exists m; split=> //; right.
- by move: (unit_factors_mod _ _ h); case: (is_mod x) nx.
Qed.

Lemma factors_atoms_sub pt u y :
  wf pt → u ∈ factors pt → y ∈ atoms u →
  y ∈ atoms pt.
Proof.
move=> wpt; set r := frac_of pt.
have A := frac_of_atoms pt wpt.
have S (p : Poly.poly pre_term) :
    (∀ m, m ∈ Poly.car p →
          m ∈ Poly.car (Frac.num r) ∨ m ∈ Poly.car (Frac.den r)) →
    u ∈ PolyGcd.content p ⊎ unit_factors p → y ∈ atoms u →
    y ∈ atoms pt.
  move=> hp.
  have N m x : m ∈ Poly.car p → x ∈ m → negb (is_mod x).
    by move=> /hp mp xm; have /andb_True [] := A m x mp xm.
  move=> /MSet.elem_of_disj_union [uc|uu] yu.
  - have [m [mp um]] := PolyGcd.elem_of_content _ _ uc.
    move: yu; rewrite (atoms_atom _ _ (N m u mp um)) => ->.
    by apply/elem_of_atoms; exists m; split=> //; apply: hp.
  - move: yu; rewrite /atoms (frac_of_unit_factors p u N uu).
    rewrite /Frac.vars elem_of_app !Poly.elem_of_vars.
    rewrite Frac.num_of_poly Frac.den_of_poly Poly.oneE Poly.car_mono.
    case=> -[m [mu ym]]; last first.
      move/SMS.elem_of_singleton: mu ym => -> e.
      by case: (MSet.not_elem_of_empty _ e).
    have [m' [m'p ym']] := PolyGcd.elem_of_unit_part y p m mu ym.
    by apply/elem_of_atoms; exists m'; split=> //; apply: hp.
rewrite /factors => /SMS.elem_of_make [] h.
- by apply: S h => m; left.
- by apply: S h => m; right.
Qed.

End PreTerm.
