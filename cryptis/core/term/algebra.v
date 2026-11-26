From cryptis Require Import lib.
From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia Ring Field.
From stdpp Require Import sorting gmap.
From cryptis.lib Require Import list_sort mathcomp_compat fmap mset sms.
From cryptis.lib Require Import poly poly_gcd frac.
From iris.heap_lang Require locations.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core Require Export pre_term.
From cryptis.core.term Require Import base.

Implicit Types (t k : term) (ts : list term) (s : tsms).

(** * Exponents

    Exponents form a field: [frac_of] is injective and turns [TMul], [TSum]
    and [TInv] into field operations, so identities between exponents follow
    from field identities.  On Laurent monomials, [factors] is moreover a
    homomorphism into the free abelian group on atoms ([factors_TMul]), so
    their laws also follow by comparing counts ([count_inj]).  The group
    laws of [TGMul] and [TExp] follow, and the last sections relate the atoms
    of terms ([atoms]), their fractions over pre-terms ([pre_frac]) and the
    signed atoms of exponents ([satoms]). *)

Section Exponents.

Add Field tfrac_field : (Frac.frac_field_theory (T := term)).

Lemma gcount_unfold x t :
  gcount x t = SMS.count (unfold_term x) (PreTerm.gfactors (unfold_term t)).
Proof.
rewrite /gcount -unfold_gfactors SMS.count_map_inj //; exact: unfold_term_inj.
Qed.

Lemma frac_of_TMul_empty : frac_of (TMul ∅) = Frac.one.
Proof. by rewrite frac_of_TMul Frac.sprod_empty. Qed.

Lemma frac_of_TSum_empty : frac_of (TSum ∅) = Frac.zero.
Proof. by rewrite frac_of_TSum Frac.ssum_empty. Qed.

Lemma frac_of_TMul2 t1 t2 :
  frac_of (TMul {[+ t1; t2 +]}) = Frac.mul (frac_of t1) (frac_of t2).
Proof. by rewrite frac_of_TMul Frac.sprod_pair. Qed.

Lemma TMul_singleton t : TMul {[+ t +]} = t.
Proof. by apply: frac_of_inj; rewrite frac_of_TMul Frac.sprod_singleton. Qed.

Lemma TSum_singleton t : TSum {[+ t +]} = t.
Proof. by apply: frac_of_inj; rewrite frac_of_TSum Frac.ssum_singleton. Qed.

Lemma TMul_unit_l t : TMul {[+ TMul ∅; t +]} = t.
Proof.
by apply: frac_of_inj; rewrite frac_of_TMul2 frac_of_TMul_empty; ring.
Qed.

Lemma TMul_unit_r t : TMul {[+ t; TMul ∅ +]} = t.
Proof. by rewrite (comm (⊎)) TMul_unit_l. Qed.

Lemma TMul_inv_r t :
  frac_of t ≠ Frac.zero → TMul {[+ TInv t; t +]} = TMul ∅.
Proof.
move=> nt; apply: frac_of_inj.
by rewrite frac_of_TMul2 frac_of_TInv frac_of_TMul_empty; field.
Qed.

Lemma TMul_disj_union s1 s2 :
  (∀ x, x ∈ s1 → x ∈ s2 → frac_of x ≠ Frac.zero) →
  TMul (s1 ⊎ s2) = TMul {[+ TMul s1; TMul s2 +]}.
Proof.
move=> nz; apply: frac_of_inj.
by rewrite frac_of_TMul2 !frac_of_TMul (Frac.sprod_disj_union _ _ _ nz).
Qed.

#[global] Instance TInv_inj : Inj (=) (=) TInv.
Proof. by move=> x y e; rewrite -(TInvK x) e TInvK. Qed.

Lemma TInv_TMul s : TInv (TMul s) = TMul (SMS.inv s).
Proof.
by apply: frac_of_inj; rewrite frac_of_TInv !frac_of_TMul Frac.sprod_inv.
Qed.

Lemma frac_of_TInv_neq0 t :
  frac_of t ≠ Frac.zero → frac_of (TInv t) ≠ Frac.zero.
Proof.
move=> nt; rewrite frac_of_TInv => e; apply: nt.
by rewrite -(Frac.inv_inv (frac_of t)) e Frac.inv_zero.
Qed.

End Exponents.

(** ** Laurent monomials *)

Lemma factors_TMul_empty : factors (TMul ∅) = ∅.
Proof.
apply: factors_TMul_atoms => x.
by rewrite SMS.elem_of_count SMS.count_empty => /(_ eq_refl).
Qed.

Lemma laurent_TMul s : (∀ x, x ∈ s → laurent x) → laurent (TMul s).
Proof.
move=> L x; rewrite factors_TMul // => /SMS.elem_of_bind [y [ys xy]].
exact: L ys x xy.
Qed.

Lemma laurent_TMul_empty : laurent (TMul ∅).
Proof.
move=> x; rewrite factors_TMul_empty SMS.elem_of_count SMS.count_empty.
by move=> /(_ eq_refl).
Qed.

Lemma laurent_TInv t : laurent t → laurent (TInv t).
Proof.
move=> L x; rewrite factors_TInv // SMS.elem_of_count SMS.count_inv => h.
by apply: L; apply/SMS.elem_of_count; lia.
Qed.

Lemma laurent_pair t1 t2 :
  laurent t1 → laurent t2 → ∀ x, x ∈ ({[+ t1; t2 +]} : tsms) → laurent x.
Proof.
by move=> L1 L2 x /SMS.elem_of_disj_union [] /SMS.elem_of_singleton ->.
Qed.

Lemma laurent_TMul2 t1 t2 :
  laurent t1 → laurent t2 → laurent (TMul {[+ t1; t2 +]}).
Proof. by move=> L1 L2; apply: laurent_TMul; exact: laurent_pair. Qed.

Lemma laurent_frac_neq0 t : laurent t → frac_of t ≠ Frac.zero.
Proof.
move=> L e; have := f_equal frac_of (factorsK t).
rewrite e frac_of_TMul.
have E : Frac.sprod frac_of (factors t) = Frac.sprod Frac.var (factors t).
  by apply: Frac.sprod_ext => x /L; exact: frac_of_Nmod.
rewrite E => /(f_equal Frac.num); rewrite Frac.num_zero.
have [en _] := Frac.sprod_var_canon (factors t).
rewrite en; exact: PolyGcd.mono_neq0.
Qed.

Lemma laurent_unfold t : laurent t ↔ PreTerm.laurent (unfold_term t).
Proof.
split=> L x.
- move=> xt; have wx := PreTerm.wf_factors _ _ (wf_unfold_term t) xt.
  rewrite -(fold_termK _ wx) -is_mod_unfold; apply: L.
  by rewrite elem_of_factors_unfold fold_termK.
- by rewrite elem_of_factors_unfold is_mod_unfold => /L.
Qed.

Lemma laurent_frac_of t :
  laurent t → Frac.laurent (PreTerm.frac_of (unfold_term t)).
Proof.
by move=> /laurent_unfold /(PreTerm.laurent_frac_of _ (wf_unfold_term t)).
Qed.

(** An exponent is monic when the numerator of its fraction is a monomial
    with coefficient [1].  A non-product raised to a monic exponent is a power
    ([TExp_Ngmul]). *)
Definition mono_num e := Frac.mono_num (PreTerm.frac_of (unfold_term e)).

Lemma laurent_mono_num e : laurent e → mono_num e.
Proof. by move=> /laurent_frac_of; exact: Frac.laurent_mono_num. Qed.

Lemma mono_num_atom e : negb (is_mod e) → mono_num e.
Proof. by move=> /laurent_atom; exact: laurent_mono_num. Qed.

Lemma count_TMul t s :
  (∀ x, x ∈ s → laurent x) →
  count t (TMul s) = SMS.count t (SMS.bind factors s).
Proof. by move=> L; rewrite /count factors_TMul. Qed.

Lemma count_TMul_empty t : count t (TMul ∅) = 0%Z.
Proof. by rewrite /count factors_TMul_empty SMS.count_empty. Qed.

Lemma count_TMul_disj_union t s1 s2 :
  (∀ x, x ∈ s1 → laurent x) → (∀ x, x ∈ s2 → laurent x) →
  count t (TMul (s1 ⊎ s2)) = (count t (TMul s1) + count t (TMul s2))%Z.
Proof.
move=> L1 L2.
have L : ∀ x, x ∈ s1 ⊎ s2 → laurent x.
  by move=> x /SMS.elem_of_disj_union [/L1|/L2].
rewrite (count_TMul _ _ L) (count_TMul _ _ L1) (count_TMul _ _ L2).
by rewrite SMS.bind_disj_union SMS.count_disj_union.
Qed.

Lemma count_TMul2 t t1 t2 :
  laurent t1 → laurent t2 →
  count t (TMul {[+ t1; t2 +]}) = (count t t1 + count t t2)%Z.
Proof.
move=> L1 L2; rewrite (count_TMul _ _ (laurent_pair _ _ L1 L2)).
by rewrite SMS.bind_disj_union !SMS.bind_singleton SMS.count_disj_union.
Qed.

Lemma count_TMul_inv t s :
  (∀ x, x ∈ s → laurent x) →
  count t (TMul (SMS.inv s)) = (- count t (TMul s))%Z.
Proof.
move=> L.
have L' : ∀ x, x ∈ SMS.inv s → laurent x.
  move=> x /SMS.elem_of_count; rewrite SMS.count_inv => h.
  by apply: L; apply/SMS.elem_of_count; lia.
rewrite (count_TMul _ _ L') (count_TMul _ _ L).
by rewrite SMS.bind_inv SMS.count_inv.
Qed.

Lemma tunitP t : t = TMul ∅ ↔ factors t = ∅.
Proof.
split; first by move=> ->; exact: factors_TMul_empty.
by move=> e; apply: factors_inj; rewrite e factors_TMul_empty.
Qed.

Lemma is_mod_TInv_atom t : negb (is_mod t) → is_mod (TInv t).
Proof.
move=> Nm; case E: (is_mod (TInv t)) => //.
have Nmi : negb (is_mod (TInv t)) by rewrite E.
have := factors_TInv t (laurent_atom _ Nm).
rewrite (factors_Nmod _ Nmi) (factors_Nmod _ Nm).
move=> /(f_equal (λ s, elements (SMS.pos s))).
by rewrite SMS.pos_inv SMS.pos_singleton SMS.neg_singleton
  MSet.elements_singleton MSet.elements_empty.
Qed.

Lemma count_neq0 t t' : count t t' ≠ 0%Z ↔ t ∈ factors t'.
Proof. by rewrite SMS.elem_of_count. Qed.

Lemma count_gt0 t t' : (0 < count t t')%Z ↔ t ∈ SMS.pos (factors t').
Proof. exact: SMS.count_pos. Qed.

Lemma count_lt0 t t' : (count t t' < 0)%Z ↔ t ∈ SMS.neg (factors t').
Proof. exact: SMS.count_neg. Qed.

Lemma not_elem_of_count t t' : t ∉ factors t' → count t t' = 0%Z.
Proof. exact: SMS.not_elem_of_count. Qed.

Lemma elem_of_factors_TInv x t :
  negb (is_mod x) → x ∈ factors (TInv t) ↔ x ∈ factors t.
Proof. by move=> nx; rewrite -!count_neq0 count_TInv //; split; lia. Qed.

Lemma elem_of_factors_TMul2 t1 t2 t' :
  laurent t1 → laurent t2 →
  t' ∈ factors (TMul {[+ t1; t2 +]}) → t' ∈ factors t1 ∨ t' ∈ factors t2.
Proof.
move=> L1 L2; rewrite -!count_neq0 count_TMul2 //.
case: (decide (count t' t1 = 0%Z)) => ?; [right|left]; lia.
Qed.

Lemma is_mod_TMul2 t1 t2 :
  negb (is_mod t1) -> negb (is_mod t2) -> is_mod (TMul {[+ t1; t2 +]}).
Proof.
move=> Nm1 Nm2; case E: (is_mod (TMul {[+ t1; t2 +]})) => //.
have Nm : negb (is_mod (TMul {[+ t1; t2 +]})) by rewrite E.
have H : factors (TMul {[+ t1; t2 +]}) = {[+ t1; t2 +]}.
  apply: factors_TMul_atoms => x.
  by case/SMS.elem_of_disj_union => /SMS.elem_of_singleton ->.
have D1 : SMS.pos ({[+ t1 +]} : tsms) ## SMS.neg ({[+ t2 +]} : tsms).
  by rewrite SMS.neg_singleton => y _ e; case: (MSet.not_elem_of_empty _ e).
have D2 : SMS.neg ({[+ t1 +]} : tsms) ## SMS.pos ({[+ t2 +]} : tsms).
  by rewrite SMS.neg_singleton => y e _; case: (MSet.not_elem_of_empty _ e).
move: H; rewrite (factors_Nmod _ Nm) => /(f_equal (λ s, length (elements s))).
rewrite (Permutation_length (SMS.elements_disj_union _ _ D1 D2)).
by rewrite length_app !SMS.elements_singleton.
Qed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Atoms *)

Lemma count_atom_ne t1 t2 :
  negb (is_mod t2) -> t1 ≠ t2 -> count t1 t2 = 0%Z.
Proof.
move=> Nm2 ne; rewrite /count factors_Nmod // SMS.count_singleton.
by rewrite bool_decide_eq_false_2.
Qed.

Lemma count_atom_ge0 t1 t2 : negb (is_mod t2) -> (0 <= count t1 t2)%Z.
Proof.
move=> Nm2; rewrite /count factors_Nmod // SMS.count_singleton.
by case: bool_decide.
Qed.

Lemma count_atom_diag t : negb (is_mod t) -> count t t = 1%Z.
Proof.
move=> Nm; rewrite /count factors_Nmod // SMS.count_singleton.
by rewrite bool_decide_eq_true_2.
Qed.

Lemma count_TMul_atoms x s :
  (∀ u, u ∈ s → negb (is_mod u)) → count x (TMul s) = SMS.count x s.
Proof. by move=> Hs; rewrite /count factors_TMul_atoms. Qed.

Lemma count_TMul_atoms_ne t s :
  (∀ u, u ∈ s → negb (is_mod u) ∧ t ≠ u) → count t (TMul s) = 0%Z.
Proof.
move=> H; rewrite count_TMul_atoms; last by move=> u /H [].
by apply: SMS.not_elem_of_count => /H [_ []].
Qed.

Lemma not_elem_of_factors_TMul t s :
  (∀ u, u ∈ s → negb (is_mod u) ∧ t ≠ u) → t ∉ factors (TMul s).
Proof. by move=> H /count_neq0; rewrite (count_TMul_atoms_ne H). Qed.

Lemma not_elem_of_factors_atom t1 t2 :
  negb (is_mod t2) -> t1 ≠ t2 -> t1 ∉ factors t2.
Proof. by move=> f2 ne /count_neq0; rewrite (count_atom_ne f2 ne). Qed.

Lemma elem_of_factors_Nmod x t : negb (is_mod t) -> x ∈ factors t ↔ x = t.
Proof.
by move=> Nm; rewrite factors_Nmod // SMS.elem_of_singleton.
Qed.

Lemma atom_frac_neq0 t : negb (is_mod t) → frac_of t ≠ Frac.zero.
Proof. by move=> Nm; apply: laurent_frac_neq0; exact: laurent_atom. Qed.

(** * The group

    [TGMul] is a group operation: its laws follow from the logarithms of the
    Diffie-Hellman map ([dh_map]).  On elements with Laurent logarithms,
    [gfactors] is moreover a homomorphism ([gfactors_TGMul]). *)

Definition dh_map t : PreTerm.dhmap := PreTerm.dh_map (unfold_term t).

Section Group.

Add Ring dh_ring : (Frac.frac_ring_theory (T := PreTerm.pre_term)).
Add Field dh_field : (Frac.frac_field_theory (T := PreTerm.pre_term)).

Lemma dh_map_inj t1 t2 : dh_map t1 = dh_map t2 → t1 = t2.
Proof.
move=> e; apply: unfold_term_inj.
exact: (PreTerm.dh_map_inj _ _ (wf_unfold_term _) (wf_unfold_term _) e).
Qed.

Lemma dh_map_TGMul s (k : PreTerm.pre_term) :
  dh_map (TGMul s) !!! k = Frac.ssum (λ t, dh_map t !!! k) s.
Proof.
have W : ∀ pt, pt ∈ SMS.map unfold_term s → PreTerm.wf pt.
  by move=> pt /SMS.elem_of_map [t [-> _]].
rewrite /dh_map unfold_TGMul (PreTerm.dh_map_gmul _ W).
by rewrite PreTerm.lookup_dh_sum_ssum Frac.ssum_map.
Qed.

Lemma dh_map_TExp b e (k : PreTerm.pre_term) :
  dh_map (TExp b e) !!! k =
  Frac.mul (dh_map b !!! k) (Frac.map unfold_term (frac_of e)).
Proof.
by rewrite /dh_map unfold_TExp PreTerm.dh_map_exp // PreTerm.lookup_dh_scale
  unfold_frac_of.
Qed.

Lemma dh_map_TGMul_empty (k : PreTerm.pre_term) :
  dh_map (TGMul ∅) !!! k = Frac.zero.
Proof. by rewrite dh_map_TGMul Frac.ssum_empty. Qed.

Lemma map_unfold_TMul_empty :
  Frac.map unfold_term (frac_of (TMul ∅)) = Frac.one.
Proof. by rewrite frac_of_TMul_empty Frac.map_one. Qed.

Lemma TGMul_singleton t : TGMul {[+ t +]} = t.
Proof.
apply: dh_map_inj; apply/FMap.fmap_eq => k.
by rewrite dh_map_TGMul Frac.ssum_singleton.
Qed.

Lemma TGMul_disj_union s1 s2 :
  TGMul (s1 ⊎ s2) = TGMul {[+ TGMul s1; TGMul s2 +]}.
Proof.
apply: dh_map_inj; apply/FMap.fmap_eq => k.
rewrite !dh_map_TGMul !Frac.ssum_disj_union !Frac.ssum_singleton.
by rewrite !dh_map_TGMul.
Qed.

Lemma TGMul_unit_l t : TGMul {[+ TGMul ∅; t +]} = t.
Proof.
apply: dh_map_inj; apply/FMap.fmap_eq => k.
rewrite dh_map_TGMul Frac.ssum_disj_union !Frac.ssum_singleton.
by rewrite dh_map_TGMul_empty; move: (dh_map t !!! k) => a; ring.
Qed.

Lemma TGMul_unit_r t : TGMul {[+ t; TGMul ∅ +]} = t.
Proof. by rewrite (comm (⊎)) TGMul_unit_l. Qed.

Lemma TGMul_inv_r t : TGMul {[+ TGInv t; t +]} = TGMul ∅.
Proof.
apply: dh_map_inj; apply/FMap.fmap_eq => k.
rewrite dh_map_TGMul Frac.ssum_disj_union !Frac.ssum_singleton
  dh_map_TGMul_empty.
rewrite /TGInv dh_map_TGMul Frac.ssum_inv Frac.ssum_singleton.
by move: (dh_map t !!! k) => a; ring.
Qed.

Lemma gfactors_TGMul_empty : gfactors (TGMul ∅) = ∅.
Proof.
rewrite gfactors_TGMul ?SMS.bind_empty // => x.
by rewrite SMS.elem_of_count SMS.count_empty => /(_ eq_refl).
Qed.

Lemma gtunitP t : t = TGMul ∅ ↔ gfactors t = ∅.
Proof.
split; first by move=> ->; exact: gfactors_TGMul_empty.
by move=> e; apply: gfactors_inj; rewrite e gfactors_TGMul_empty.
Qed.

#[global] Instance TGInv_inj : Inj (=) (=) TGInv.
Proof. by move=> x y e; rewrite -(TGInvK x) e TGInvK. Qed.

Lemma TGInv_TGMul s : TGInv (TGMul s) = TGMul (SMS.inv s).
Proof.
apply: dh_map_inj; apply/FMap.fmap_eq => k.
rewrite /TGInv !dh_map_TGMul Frac.ssum_inv Frac.ssum_singleton dh_map_TGMul.
by rewrite Frac.ssum_inv.
Qed.

Lemma gcount_TGMul t s :
  (∀ x, x ∈ s → mono_den_logs x) →
  gcount t (TGMul s) = SMS.count t (SMS.bind gfactors s).
Proof. by move=> L; rewrite /gcount gfactors_TGMul. Qed.

Lemma gcount_TGMul_empty t : gcount t (TGMul ∅) = 0%Z.
Proof. by rewrite /gcount gfactors_TGMul_empty SMS.count_empty. Qed.

Lemma mono_den_logs_pair t1 t2 :
  mono_den_logs t1 → mono_den_logs t2 → ∀ x, x ∈ ({[+ t1; t2 +]} : tsms) →
    mono_den_logs x.
Proof.
by move=> L1 L2 x /SMS.elem_of_disj_union [] /SMS.elem_of_singleton ->.
Qed.

Lemma gcount_TGMul2 t t1 t2 :
  mono_den_logs t1 → mono_den_logs t2 →
  gcount t (TGMul {[+ t1; t2 +]}) = (gcount t t1 + gcount t t2)%Z.
Proof.
move=> L1 L2; rewrite (gcount_TGMul _ (mono_den_logs_pair L1 L2)).
by rewrite SMS.bind_disj_union !SMS.bind_singleton SMS.count_disj_union.
Qed.

Lemma gcount_diag t : gcount t t = if is_gmul t then 0%Z else 1%Z.
Proof.
case Em: (is_gmul t); first by rewrite is_gmul_gcount ?Em.
rewrite /gcount gfactors_Ngmul ?Em // SMS.count_singleton.
by rewrite bool_decide_eq_true_2.
Qed.

Lemma gcount_neq0 t t' : gcount t t' ≠ 0%Z ↔ t ∈ gfactors t'.
Proof. by rewrite SMS.elem_of_count. Qed.

Lemma gcount_gt0 t t' : (0 < gcount t t')%Z ↔ t ∈ SMS.pos (gfactors t').
Proof. exact: SMS.count_pos. Qed.

Lemma gcount_lt0 t t' : (gcount t t' < 0)%Z ↔ t ∈ SMS.neg (gfactors t').
Proof. exact: SMS.count_neg. Qed.

Lemma not_elem_of_gcount t t' : t ∉ gfactors t' → gcount t t' = 0%Z.
Proof. exact: SMS.not_elem_of_count. Qed.

Lemma elem_of_gfactors_TGMul2 t1 t2 t' :
  mono_den_logs t1 → mono_den_logs t2 →
  t' ∈ gfactors (TGMul {[+ t1; t2 +]}) → t' ∈ gfactors t1 ∨ t' ∈ gfactors t2.
Proof.
move=> L1 L2; rewrite -!gcount_neq0 gcount_TGMul2 //.
case: (decide (gcount t' t1 = 0%Z)) => ?; [right|left]; lia.
Qed.

Lemma elem_of_gfactors_Ngmul x t :
  negb (is_gmul t) -> x ∈ gfactors t ↔ x = t.
Proof.
by move=> Nm; rewrite gfactors_Ngmul // SMS.elem_of_singleton.
Qed.

Lemma gcount_atom_ge0 t1 t2 : negb (is_gmul t2) -> (0 <= gcount t1 t2)%Z.
Proof.
move=> Nm2; rewrite /gcount gfactors_Ngmul // SMS.count_singleton.
by case: bool_decide.
Qed.

Lemma Ngmul_neq_unit t : negb (is_gmul t) → t ≠ TGMul ∅.
Proof.
move=> tNm /gtunitP; rewrite (gfactors_Ngmul _ tNm).
move=> /(f_equal (SMS.count t)).
by rewrite SMS.count_singleton SMS.count_empty bool_decide_eq_true_2.
Qed.

(** * Exponentiation *)

Lemma TExpA b e1 e2 : TExp (TExp b e1) e2 = TExp b (TMul {[+ e1; e2 +]}).
Proof.
apply: dh_map_inj; apply/FMap.fmap_eq => k; rewrite !dh_map_TExp frac_of_TMul2.
rewrite (Frac.map_mul unfold_term unfold_term_inj).
by move: (dh_map b !!! k) (Frac.map _ (frac_of e1)) (Frac.map _ (frac_of e2))
  => x y z; ring.
Qed.

Lemma TExpC g a b : TExp (TExp g a) b = TExp (TExp g b) a.
Proof. by rewrite !TExpA (comm (⊎)). Qed.

Lemma TExp_unit b : TExp b (TMul ∅) = b.
Proof.
apply: dh_map_inj; apply/FMap.fmap_eq => k.
by rewrite dh_map_TExp map_unfold_TMul_empty; move: (dh_map b !!! k) => a; ring.
Qed.

Lemma TExpK u v : frac_of v ≠ Frac.zero → TExp (TExp u v) (TInv v) = u.
Proof.
move=> nv; rewrite TExpA (comm (⊎)) TMul_inv_r //; exact: TExp_unit.
Qed.

Lemma TExpKV u v : frac_of v ≠ Frac.zero → TExp (TExp u (TInv v)) v = u.
Proof.
move=> nv; have := TExpK u (frac_of_TInv_neq0 _ nv).
by rewrite TInvK.
Qed.

Lemma TExp_injl e t1 t2 :
  frac_of e ≠ Frac.zero → TExp t1 e = TExp t2 e -> t1 = t2.
Proof. by move=> ne E; rewrite -(TExpK t1 ne) E TExpK. Qed.

Lemma TExp_TGMul s e : TExp (TGMul s) e = TGMul (SMS.map (λ u, TExp u e) s).
Proof.
apply: dh_map_inj; apply/FMap.fmap_eq => k.
rewrite dh_map_TExp !dh_map_TGMul Frac.ssum_map -Frac.ssum_mul_r.
by apply: Frac.ssum_ext => u _; rewrite dh_map_TExp.
Qed.

Lemma TExp_gfactors b e :
  TExp b e = TGMul (SMS.map (λ u, TExp u e) (gfactors b)).
Proof. by rewrite -TExp_TGMul gfactorsK. Qed.

Lemma TExp_TGInv t e : TExp (TGInv t) e = TGInv (TExp t e).
Proof. by rewrite /TGInv TExp_TGMul SMS.map_inv SMS.map_singleton. Qed.

Lemma TExp_gunit e : TExp (TGMul ∅) e = TGMul ∅.
Proof. by rewrite TExp_TGMul SMS.map_empty. Qed.

Lemma TExp_injr t t1 t2 : t ≠ TGMul ∅ → TExp t t1 = TExp t t2 → t1 = t2.
Proof.
move=> nt e.
have [k nk] : ∃ k : PreTerm.pre_term, dh_map t !!! k ≠ Frac.zero.
  destruct (FMap.to_list (dh_map t)) as [|[k v] l] eqn:El.
  - exfalso; apply: nt; apply: dh_map_inj; apply/FMap.fmap_eq => k.
    by rewrite dh_map_TGMul_empty PreTerm.lookup_to_list El.
  - have /FMap.elem_of_to_list [ek nv] : (k, v) ∈ FMap.to_list (dh_map t).
      by rewrite El; left.
    by exists k; rewrite ek.
have E : dh_map (TExp t t1) !!! k = dh_map (TExp t t2) !!! k by rewrite e.
rewrite !dh_map_TExp in E.
apply: frac_of_inj; apply: (Frac.map_inj unfold_term unfold_term_inj).
move: (dh_map t !!! k) nk E => l nl.
move: (Frac.map _ (frac_of t1)) (Frac.map _ (frac_of t2)) => a b E.
have Ea : a = Frac.mul (Frac.inv l) (Frac.mul l a) by field.
have Eb : b = Frac.mul (Frac.inv l) (Frac.mul l b) by field.
by rewrite Ea Eb E.
Qed.

End Group.

(** ** Laurent logarithms *)

Lemma mono_den_logs_TGMul s :
  (∀ x, x ∈ s → mono_den_logs x) → mono_den_logs (TGMul s).
Proof.
move=> L k; rewrite -/(dh_map (TGMul s)) dh_map_TGMul Frac.ssumE Frac.subE.
have F : ∀ X : MSet.mset term, (∀ x, x ∈ X → x ∈ s) →
    Frac.mono_den (Frac.fsum ((λ t, dh_map t !!! k) <$> elements X)).
  move=> X hX; apply: Frac.mono_den_fsum; apply/Forall_fmap/list.Forall_forall.
  by move=> x /MSet.elem_of_elements /hX /L /(_ k).
exact: proj1 (PreTerm.entry_factors_add PreTerm.one _ _
         (F _ (λ x hx, SMS.elem_of_pos _ _ hx))
         (Frac.mono_den_opp _ (F _ (λ x hx, SMS.elem_of_neg _ _ hx)))).
Qed.

Lemma mono_den_logs_TExp b e :
  mono_den_logs b → laurent e → mono_den_logs (TExp b e).
Proof.
move=> Lb Le k; rewrite -/(dh_map (TExp b e)) dh_map_TExp unfold_frac_of.
apply: Frac.mono_den_mul; first exact: Lb.
exact: Frac.laurent_mono_den (laurent_frac_of _ Le).
Qed.

Lemma mono_den_logs_Ngnf t :
  negb (is_exp t) → negb (is_gmul t) → mono_den_logs t.
Proof.
rewrite is_exp_unfold is_gmul_unfold => Ne Ng k.
have G : negb (PreTerm.is_gnon_free (unfold_term t)).
  rewrite /PreTerm.is_gnon_free; move: Ne Ng.
  by case: (PreTerm.is_exp (unfold_term t));
    case: (PreTerm.is_gmul (unfold_term t)).
rewrite (PreTerm.dh_map_Ngnf _ G) FMap.lookup_singleton.
by case: bool_decide; [exact: Frac.mono_den_one|exact: Frac.mono_den_zero].
Qed.

Lemma mono_den_logs_TGInv t : mono_den_logs t → mono_den_logs (TGInv t).
Proof.
move=> L; apply: mono_den_logs_TGMul => x.
move=> /SMS.elem_of_count; rewrite SMS.count_inv => h.
have : x ∈ ({[+ t +]} : tsms) by apply/SMS.elem_of_count; lia.
by move/SMS.elem_of_singleton => ->.
Qed.

Lemma mono_den_logs_gfactors b u :
  mono_den_logs b → u ∈ gfactors b → mono_den_logs u ∧ laurent (expo u).
Proof.
move=> L /elem_of_gfactors_unfold ub.
have [_ [Lu mu]] := PreTerm.gfactors_mono_den_logs _ _ (wf_unfold_term b) L ub.
split; first exact: Lu.
apply/laurent_unfold; rewrite unfold_expo.
exact/(PreTerm.laurent_frac_of _ (PreTerm.wf_expo _ (wf_unfold_term u))).
Qed.

(** ** Powers of non-products *)

Lemma unfold_TMul_empty : unfold_term (TMul ∅) = PreTerm.one.
Proof.
rewrite unfold_TMul SMS.map_empty /PreTerm.mul Frac.sprod_empty.
by rewrite /PreTerm.mod_of_frac PreTerm.frac_lists_of_one.
Qed.

Lemma is_exp_Nmod t : is_exp t -> negb (is_mod t).
Proof. rewrite is_exp_unfold is_mod_unfold; exact: PreTerm.is_exp_Nmod. Qed.

Lemma is_exp_Ngmul t : is_exp t -> negb (is_gmul t).
Proof. rewrite is_exp_unfold is_gmul_unfold; exact: PreTerm.is_exp_Ngmul. Qed.

Lemma is_mod_Ngmul t : is_mod t -> negb (is_gmul t).
Proof. rewrite is_mod_unfold is_gmul_unfold; exact: PreTerm.is_mod_Ngmul. Qed.

Lemma is_mod_Nexp t : is_mod t -> negb (is_exp t).
Proof. rewrite is_mod_unfold is_exp_unfold; by case: (unfold_term t). Qed.

Lemma is_gmul_Nexp t : is_gmul t → negb (is_exp t).
Proof. rewrite is_gmul_unfold is_exp_unfold; exact: PreTerm.is_gmul_Nexp. Qed.

Lemma base_expN t : negb (is_exp t) → base t = t.
Proof.
rewrite is_exp_unfold => tNx; apply: unfold_term_inj.
rewrite unfold_base; exact: PreTerm.base_expN.
Qed.

Lemma expo_expN t : negb (is_exp t) → expo t = TMul ∅.
Proof.
rewrite is_exp_unfold => tNx; apply: unfold_term_inj.
rewrite unfold_expo unfold_TMul_empty; exact: PreTerm.expo_expN.
Qed.

Lemma base_Nexp t : negb (is_exp (base t)).
Proof.
rewrite is_exp_unfold unfold_base.
case E: (PreTerm.is_exp (unfold_term t)).
  case: (PreTerm.is_expP (unfold_term t)) E (wf_unfold_term t)
    => [b m d -> _ /PreTerm.wf_exp_entry [_ [gb _]]|//].
  exact: PreTerm.Ngnf_Nexp gb.
have nE : negb (PreTerm.is_exp (unfold_term t)) by rewrite E.
by rewrite (PreTerm.base_expN _ nE).
Qed.

Lemma base_idem t : base (base t) = base t.
Proof. exact: base_expN (base_Nexp t). Qed.

Lemma is_gmul_base t : is_gmul (base t) = is_gmul t.
Proof.
rewrite !is_gmul_unfold unfold_base.
case E: (PreTerm.is_exp (unfold_term t)).
  case: (PreTerm.is_expP (unfold_term t)) E (wf_unfold_term t)
    => [b m d -> _ /PreTerm.wf_exp_entry [_ [gb _]]|//].
  move: (PreTerm.Ngnf_Ngmul _ gb)
        (PreTerm.is_exp_Ngmul (PreTerm.PTDH [(b, (([m], []), d))]) I).
  rewrite [PreTerm.base _]/=.
  by case: (PreTerm.is_gmul b); case: (PreTerm.is_gmul (PreTerm.PTDH _)).
have nE : negb (PreTerm.is_exp (unfold_term t)) by rewrite E.
by rewrite (PreTerm.base_expN _ nE).
Qed.

Lemma unfold_TExp_Ngmul b e :
  negb (is_gmul b) → mono_num e →
  unfold_term (TExp b e) =
  PreTerm.mk_exp (PreTerm.base (unfold_term b))
    (Frac.mul (PreTerm.frac_of (PreTerm.expo (unfold_term b)))
              (PreTerm.frac_of (unfold_term e))).
Proof.
rewrite is_gmul_unfold => Nb me.
have mb := PreTerm.mono_num_expo _ (wf_unfold_term b) Nb.
rewrite unfold_TExp /PreTerm.exp.
rewrite (PreTerm.exp_frac_Ngmul _ _ (wf_unfold_term b) Nb) //.
exact: Frac.mono_num_neq0 (Frac.mono_num_mul _ _ mb me).
Qed.

(** Raising a power of a base to a monic exponent multiplies its exponent;
    with other exponents, such as sums, the result is a group product. *)
Lemma TExp_Ngmul b e :
  negb (is_gmul b) → mono_num e →
  negb (is_gmul (TExp b e)) ∧ base (TExp b e) = base b ∧
  expo (TExp b e) = TMul {[+ expo b; e +]}.
Proof.
move=> Nb me.
have Nb' : negb (PreTerm.is_gmul (unfold_term b)) by rewrite -is_gmul_unfold.
have mb := PreTerm.mono_num_expo _ (wf_unfold_term b) Nb'.
have [N [B X]] := PreTerm.mk_exp_mono_num _ _
  (PreTerm.base_Ngnf _ (wf_unfold_term b) Nb') (Frac.mono_num_mul _ _ mb me).
have U := unfold_TExp_Ngmul Nb me.
split; first by rewrite is_gmul_unfold U.
split; first by apply: unfold_term_inj; rewrite !unfold_base U B.
apply: unfold_term_inj; rewrite unfold_expo U X unfold_TMul.
rewrite SMS.map_disj_union !SMS.map_singleton /PreTerm.mul Frac.sprod_pair.
by rewrite unfold_expo.
Qed.

Lemma Ngmul_TExp b e :
  negb (is_gmul b) → mono_num e → negb (is_gmul (TExp b e)).
Proof. by move=> Nb me; case: (TExp_Ngmul Nb me). Qed.

Lemma base_TExp b e :
  negb (is_gmul b) → mono_num e → base (TExp b e) = base b.
Proof. by move=> Nb me; case: (TExp_Ngmul Nb me) => _ []. Qed.

Lemma expo_TExp b e :
  negb (is_gmul b) → mono_num e → expo (TExp b e) = TMul {[+ expo b; e +]}.
Proof. by move=> Nb me; case: (TExp_Ngmul Nb me) => _ []. Qed.

Lemma laurent_expo_expN t : negb (is_exp t) → laurent (expo t).
Proof. by move=> nE; rewrite expo_expN //; exact: laurent_TMul_empty. Qed.

Lemma expo_TExp_expN b e :
  negb (is_exp b) → negb (is_gmul b) → mono_num e → expo (TExp b e) = e.
Proof.
by move=> nE nG me; rewrite (expo_TExp nG me) (expo_expN nE) TMul_unit_l.
Qed.

Lemma TExp_base_expo t : TExp (base t) (expo t) = t.
Proof.
case G: (is_gmul t).
  have nE : negb (is_exp t) by apply: is_gmul_Nexp; rewrite G.
  by rewrite (base_expN nE) (expo_expN nE) TExp_unit.
have Nt : negb (PreTerm.is_gmul (unfold_term t)) by rewrite -is_gmul_unfold G.
apply: dh_map_inj; apply/FMap.fmap_eq => k.
rewrite dh_map_TExp unfold_frac_of /dh_map unfold_base unfold_expo.
rewrite (PreTerm.dh_map_Ngmul _ (wf_unfold_term t) Nt).
rewrite (PreTerm.dh_map_Ngnf _ (PreTerm.base_Ngnf _ (wf_unfold_term t) Nt)).
rewrite !FMap.lookup_singleton.
case: bool_decide; first exact: (left_id Frac.one Frac.mul).
exact: Frac.mul_zero_l.
Qed.

Definition exps t := factors (expo t).

Lemma count_exps_pos x t :
  Z.of_nat (MSet.count x (SMS.pos (exps t))) = Z.max 0 (count x (expo t)).
Proof. exact: SMS.count_pos_max. Qed.

Lemma base_expsK t : TExp (base t) (TMul (exps t)) = t.
Proof. by rewrite /exps factorsK TExp_base_expo. Qed.

Lemma exps_TExp_expN b e :
  negb (is_exp b) → negb (is_gmul b) → mono_num e → exps (TExp b e) = factors e.
Proof. by move=> gNX gNm me; rewrite /exps expo_TExp_expN. Qed.

Lemma exps_TExp_TMul t s :
  negb (is_exp t) -> negb (is_gmul t) ->
  (∀ u, u ∈ s → negb (is_mod u)) → exps (TExp t (TMul s)) = s.
Proof.
move=> tNexp tNm Hs.
have Ls := laurent_mono_num _ (laurent_TMul_atoms _ Hs).
by rewrite /exps (expo_TExp_expN tNexp tNm Ls) factors_TMul_atoms.
Qed.

Lemma is_exp_of_exps t t' : t' ∈ exps t -> is_exp t.
Proof.
case E: (is_exp t) => //.
have nE : negb (is_exp t) by rewrite E.
rewrite /exps (expo_expN nE) factors_TMul_empty SMS.elem_of_count.
by rewrite SMS.count_empty => /(_ eq_refl).
Qed.

Lemma count_expo_TExp t1 t2 t3 :
  negb (is_gmul t2) → laurent (expo t2) → laurent t3 →
  count t1 (expo (TExp t2 t3)) = (count t1 (expo t2) + count t1 t3)%Z.
Proof.
by move=> Nm L2 L3; rewrite (expo_TExp Nm (laurent_mono_num _ L3)) count_TMul2.
Qed.

Lemma count_expo_TExp_eq t1 t2 :
  negb (is_mod t1) → negb (is_gmul t2) → laurent (expo t2) →
  count t1 (expo (TExp t2 t1)) = (count t1 (expo t2) + 1)%Z.
Proof.
move=> Nm1 Nm2 L2.
by rewrite (count_expo_TExp _ Nm2 L2 (laurent_atom _ Nm1)) count_atom_diag.
Qed.

Section ExpSingletons.

Add Field tfrac_field' : (Frac.frac_field_theory (T := term)).

Lemma TExp_TMul_singleton_l t x X Y :
  (∀ y, y ∈ Y → frac_of y ≠ Frac.zero) →
  TExp t (TMul (SMS.make ({[+ x +]} ⊎ X) Y)) =
  TExp (TExp t (TMul (SMS.make X Y))) x.
Proof.
move=> nY; rewrite TExpA; congr TExp; apply: frac_of_inj.
rewrite frac_of_TMul2 !frac_of_TMul.
rewrite (Frac.sprod_make _ _ _ (λ y _ hy, nY y hy)).
rewrite (Frac.sprod_make _ _ _ (λ y _ hy, nY y hy)).
rewrite Frac.fprod_disj_union MSet.elements_singleton fmap_cons fmap_nil.
rewrite Frac.fprod_cons Frac.fprod_nil !Frac.divE.
by move: (Frac.fprod _) (Frac.fprod _) => a c; ring.
Qed.

Lemma TExp_TMul_singleton_r t y X Y :
  (∀ z, z ∈ X → frac_of z ≠ Frac.zero) →
  TExp t (TMul (SMS.make X ({[+ y +]} ⊎ Y))) =
  TExp (TExp t (TMul (SMS.make X Y))) (TInv y).
Proof.
move=> nX; rewrite TExpA; congr TExp; apply: frac_of_inj.
rewrite frac_of_TMul2 frac_of_TInv !frac_of_TMul.
rewrite (Frac.sprod_make _ _ _ (λ z hz _, nX z hz)).
rewrite (Frac.sprod_make _ _ _ (λ z hz _, nX z hz)).
rewrite Frac.fprod_disj_union MSet.elements_singleton fmap_cons fmap_nil.
rewrite Frac.fprod_cons Frac.fprod_nil !Frac.divE !Frac.inv_mul Frac.inv_one.
by move: (Frac.fprod _) (Frac.fprod _) => a c; ring.
Qed.

End ExpSingletons.

(** ** Signed atoms *)

(* The elements of [s] as signed atoms: [x] for a positive element [x],
   [TInv x] for a negative one. *)
Definition satoms (s : tsms) :=
  elements (SMS.pos s) ++ (TInv <$> elements (SMS.neg s)).

Definition scount f t := (count f t - count (TInv f) t)%Z.

Lemma is_mod_count_laurent x t : is_mod x → laurent t → count x t = 0%Z.
Proof.
move=> Mx L; apply: not_elem_of_count => /L.
by case: (is_mod x) Mx.
Qed.

Lemma scount_TInv_l f t : scount (TInv f) t = (- scount f t)%Z.
Proof. rewrite /scount TInvK; lia. Qed.

Lemma scount_TInv_r f t : laurent t → scount f (TInv t) = (- scount f t)%Z.
Proof.
by move=> L; rewrite /scount /count !factors_TInv // !SMS.count_inv; lia.
Qed.

Lemma scount_Nmod f t : negb (is_mod f) → laurent t → scount f t = count f t.
Proof.
move=> Nm L.
by rewrite /scount (is_mod_count_laurent (is_mod_TInv_atom _ Nm) L); lia.
Qed.

Lemma scount_expo_TExp f t1 t2 :
  negb (is_gmul t1) → laurent (expo t1) → laurent t2 →
  scount f (expo (TExp t1 t2)) = (scount f (expo t1) + scount f t2)%Z.
Proof.
by move=> Nm L1 L2; rewrite /scount !(count_expo_TExp _ Nm L1 L2); lia.
Qed.

Lemma elem_of_satoms f t :
  laurent t → f ∈ satoms (factors t) ↔ (0 < scount f t)%Z.
Proof.
move=> L.
rewrite /satoms elem_of_app list_elem_of_fmap MSet.elem_of_elements -count_gt0.
rewrite /scount.
case Em: (is_mod f).
- have Mf : is_mod f by rewrite Em.
  rewrite (is_mod_count_laurent Mf L); split.
  + case=> [|[x [-> /count_lt0 x_t]]]; first lia.
    by rewrite TInvK; lia.
  + move=> H; right; exists (TInv f); rewrite TInvK; split => //.
    by apply/count_lt0; lia.
- have Nm : negb (is_mod f) by rewrite Em.
  rewrite (is_mod_count_laurent (is_mod_TInv_atom _ Nm) L) Z.sub_0_r.
  split; last by left.
  case=> // [[x [Ex x_t]]].
  have := is_mod_TInv_atom _ (L _ (SMS.elem_of_neg _ _ x_t)).
  by rewrite -Ex Em.
Qed.

Lemma elem_of_satoms_TInv x t :
  negb (is_mod x) → laurent t →
  TInv x ∈ satoms (factors t) ↔ x ∈ SMS.neg (factors t).
Proof.
move=> Nm L; rewrite elem_of_satoms // scount_TInv_l scount_Nmod //.
rewrite -count_lt0; lia.
Qed.

Lemma is_exp_of_satoms f t : f ∈ satoms (exps t) → is_exp t.
Proof.
rewrite /satoms elem_of_app list_elem_of_fmap.
case=> [f_t|[x [_ x_t]]].
- exact: is_exp_of_exps (SMS.elem_of_pos _ _ f_t).
- exact: is_exp_of_exps (SMS.elem_of_neg _ _ x_t).
Qed.

Lemma satoms_satom f t :
  laurent t →
  f ∈ satoms (factors t) → negb (is_mod f) ∨ negb (is_mod (TInv f)).
Proof.
move=> L; rewrite /satoms elem_of_app list_elem_of_fmap.
case=> [f_t|[x [-> x_t]]].
  by left; exact: L _ (SMS.elem_of_pos _ _ f_t).
by right; rewrite TInvK; exact: L _ (SMS.elem_of_neg _ _ x_t).
Qed.

Lemma count_TInv_atom_self f : negb (is_mod f) → count (TInv f) f = 0%Z.
Proof.
move=> Nm.
have ne : TInv f ≠ f.
  by move=> e; move: (is_mod_TInv_atom _ Nm); rewrite e; case: (is_mod f) Nm.
exact: count_atom_ne Nm ne.
Qed.

Lemma scount_satom_diag f :
  negb (is_mod f) ∨ negb (is_mod (TInv f)) → scount f f = 1%Z.
Proof.
case=> Nm.
  by rewrite /scount count_atom_diag // count_TInv_atom_self.
have La := laurent_atom _ Nm.
rewrite -[f]TInvK scount_TInv_l (scount_TInv_r _ La) (scount_Nmod Nm La).
by rewrite count_atom_diag //; lia.
Qed.

Lemma scount_satom_ne g f :
  negb (is_mod f) ∨ negb (is_mod (TInv f)) → g ≠ f → g ≠ TInv f →
  scount g f = 0%Z.
Proof.
move=> Af gf gTf.
have Tgf : TInv g ≠ f by move=> e; apply: gTf; rewrite -e TInvK.
have TgTf : TInv g ≠ TInv f by move=> /(inj TInv).
case: Af => Nm.
  by rewrite /scount (count_atom_ne Nm gf) (count_atom_ne Nm Tgf).
have La := laurent_atom _ Nm.
rewrite -[f]TInvK (scount_TInv_r _ La) /scount.
rewrite (count_atom_ne Nm gTf) (count_atom_ne Nm TgTf); lia.
Qed.

(** ** Group factors of powers *)

Lemma gfactors_TExp b e :
  mono_den_logs b → laurent e →
  gfactors (TExp b e) = SMS.map (λ u, TExp u e) (gfactors b).
Proof.
move=> Lb Le.
have G : ∀ x, x ∈ SMS.map (λ u, TExp u e) (gfactors b) → mono_den_logs x.
  move=> x /SMS.elem_of_map [u [-> ub]].
  by apply: mono_den_logs_TExp Le; case: (mono_den_logs_gfactors Lb ub).
rewrite {1}(TExp_gfactors b e) (gfactors_TGMul _ G) SMS.bind_map.
rewrite [SMS.map]unlock.
apply: SMS.bind_ext => u ub; apply: gfactors_Ngmul.
exact: Ngmul_TExp (Ngmul_gfactors _ _ ub) (laurent_mono_num _ Le).
Qed.

Lemma gfactors_nonempty t : t ≠ TGMul ∅ → ∃ u, u ∈ gfactors t.
Proof.
move=> nt; destruct (elements (gfactors t)) as [|w l] eqn:E.
  by case: nt; apply/gtunitP; exact: SMS.elements_empty_inv.
have w_in : w ∈ w :: l by left.
by rewrite -E in w_in; exists w; apply/SMS.elem_of_elements.
Qed.

(** ** Atoms *)

Lemma factors_atoms t x : x ∈ factors t → negb (is_mod x) → x ∈ atoms t.
Proof.
move=> /elem_of_factors_unfold h; rewrite is_mod_unfold => nx.
apply/elem_of_atoms; exists (unfold_term x); split.
  by rewrite unfold_termK.
exact: PreTerm.factors_atoms.
Qed.

Lemma atoms_TInv t y : y ∈ atoms (TInv t) ↔ y ∈ atoms t.
Proof.
have sub (r : Frac.frac PreTerm.pre_term) z :
    z ∈ Frac.vars (Frac.inv r) → z ∈ Frac.vars r.
  by apply: Frac.vars_over; apply: Frac.over_inv;
    apply: Frac.over_vars_sub.
rewrite !elem_of_atoms /PreTerm.atoms pre_frac_TInv; split.
- by case=> z [-> zt]; exists z; split=> //; exact: sub.
- case=> z [-> zt]; exists z; split=> //; apply: sub.
  by rewrite Frac.inv_inv.
Qed.

Lemma atoms_TMul_sub s y : y ∈ atoms (TMul s) → ∃ u, u ∈ s ∧ y ∈ atoms u.
Proof.
move=> /elem_of_atoms [a [-> ap]].
move: ap; rewrite /PreTerm.atoms pre_frac_TMul => /(Frac.vars_sprod _ s a)
  [u [us au]].
by exists u; split=> //; apply/elem_of_atoms; exists a.
Qed.

Lemma atoms_TSum_sub s y : y ∈ atoms (TSum s) → ∃ u, u ∈ s ∧ y ∈ atoms u.
Proof.
move=> /elem_of_atoms [a [-> ap]].
have E : PreTerm.frac_of (unfold_term (TSum s)) =
         Frac.ssum (λ u, PreTerm.frac_of (unfold_term u)) s.
  rewrite -unfold_frac_of frac_of_TSum.
  rewrite (Frac.map_ssum unfold_term unfold_term_inj).
  by apply: Frac.ssum_ext => u _; rewrite unfold_frac_of.
move: ap; rewrite /PreTerm.atoms E => /(Frac.vars_ssum _ s a) [u [us au]].
by exists u; split=> //; apply/elem_of_atoms; exists a.
Qed.

Lemma not_elem_of_atoms_TSum2 h a b :
  h ∉ atoms a → h ∉ atoms b → h ∉ atoms (TSum {[+ a; b +]}).
Proof.
move=> ha hb /atoms_TSum_sub [u [/SMS.elem_of_disj_union []
  /SMS.elem_of_singleton -> hu]] //.
Qed.

Lemma not_elem_of_atoms_TMul2 h a b :
  h ∉ atoms a → h ∉ atoms b → h ∉ atoms (TMul {[+ a; b +]}).
Proof.
move=> ha hb /atoms_TMul_sub [u [/SMS.elem_of_disj_union []
  /SMS.elem_of_singleton -> hu]] //.
Qed.

Lemma not_elem_of_atoms_atom h a : negb (is_mod a) → h ≠ a → h ∉ atoms a.
Proof. by move=> na ne; rewrite atoms_atom. Qed.

Lemma not_elem_of_atoms_TSum_empty h : h ∉ atoms (TSum ∅).
Proof.
by move=> /atoms_TSum_sub [u [/SMS.elem_of_count]]; rewrite SMS.count_empty.
Qed.

Lemma not_elem_of_atoms_pre_frac h t :
  h ∉ atoms t → Frac.all_vars (λ z, z ≠ unfold_term h) (pre_frac t).
Proof.
move=> ht; apply/Frac.all_vars_iff => z zt ez; apply: ht.
apply/elem_of_atoms; exists z; split; last exact: zt.
by rewrite ez unfold_termK.
Qed.

(** ** Fractions *)

Lemma pre_frac_TMul2 a b :
  pre_frac (TMul {[+ a; b +]}) = Frac.mul (pre_frac a) (pre_frac b).
Proof.
by rewrite -!unfold_frac_of frac_of_TMul2 (Frac.map_mul _ unfold_term_inj).
Qed.

Lemma pre_frac_TSum2 a b :
  pre_frac (TSum {[+ a; b +]}) = Frac.add (pre_frac a) (pre_frac b).
Proof.
rewrite -!unfold_frac_of frac_of_TSum Frac.ssum_disj_union.
by rewrite !Frac.ssum_singleton (Frac.map_add _ unfold_term_inj).
Qed.

Lemma pre_frac_atom a :
  negb (is_mod a) → pre_frac a = Frac.of_poly (Poly.var (unfold_term a)).
Proof. by move=> na; apply: PreTerm.frac_of_Nmod; rewrite -is_mod_unfold. Qed.

Lemma frac_of_eq0 (u : term) : frac_of u = Frac.zero → u = TSum ∅.
Proof. by move=> e; apply: frac_of_inj; rewrite e frac_of_TSum_empty. Qed.

Lemma expo_frac_Nexp u : negb (is_exp u) → expo_frac u = Frac.one.
Proof.
rewrite is_exp_unfold => nE.
by rewrite /expo_frac (PreTerm.expo_expN _ nE) PreTerm.frac_of_one.
Qed.

Lemma dh_map_Ngmul v :
  negb (is_gmul v) → dh_map v = {[unfold_term (base v) := expo_frac v]}.
Proof.
rewrite is_gmul_unfold => Nv.
by rewrite /dh_map (PreTerm.dh_map_Ngmul _ (wf_unfold_term v) Nv) unfold_base.
Qed.

(** ** Signed atoms of exponents *)

Lemma satoms_nonempty t : is_exp t → ∃ f, f ∈ satoms (exps t).
Proof.
move=> xt; case E: (satoms (exps t)) => [|f l]; last by exists f; left.
exfalso; move: E; rewrite /satoms => /app_eq_nil [ep en].
have /fmap_nil_inv en' := en.
have E0 : exps t = ∅.
  rewrite -(SMS.make_pos_neg (exps t)).
  rewrite (MSet.elements_empty_inv _ ep) (MSet.elements_empty_inv _ en').
  apply: SMS.count_inj => z.
  by rewrite SMS.count_make.
have : expo t = TMul ∅ by rewrite -(factorsK (expo t)) -/(exps t) E0.
move=> eE; have := TExp_base_expo t; rewrite eE TExp_unit => eb.
by move: (base_Nexp t); rewrite eb; case: (is_exp t) xt.
Qed.

Lemma laurent_satom g : negb (is_mod g) ∨ negb (is_mod (TInv g)) → laurent g.
Proof.
case=> Ng; first exact: laurent_atom.
by rewrite -[g]TInvK; apply: laurent_TInv; apply: laurent_atom.
Qed.

Lemma laurent_TExp_satom t g :
  negb (is_gmul t) → laurent (expo t) →
  negb (is_mod g) ∨ negb (is_mod (TInv g)) →
  negb (is_gmul (TExp t g)) ∧ laurent (expo (TExp t g)) ∧
  base (TExp t g) = base t.
Proof.
move=> Nm L Ag; have mg := laurent_mono_num _ (laurent_satom Ag).
split; first exact: Ngmul_TExp.
split; last exact: base_TExp.
by rewrite (expo_TExp Nm mg); apply: laurent_TMul2 => //; exact: laurent_satom.
Qed.

Lemma pos_exps_two u (a b : term) :
  (1 + (if bool_decide (a = b) then 1 else 0) ≤ count a (expo u))%Z →
  (1 ≤ count b (expo u))%Z →
  {[+ a; b +]} ⊆ SMS.pos (exps u).
Proof.
move=> ca cb; apply/MSet.subseteq_count => z.
have E := count_exps_pos z u.
rewrite MSet.count_disj_union !MSet.count_singleton.
case: (decide (z = a)) => [ez|za].
  subst z; rewrite bool_decide_eq_true_2 //.
  case: (bool_decide_reflect (a = b)) => [e|ne].
  - by rewrite (bool_decide_eq_true_2 _ e) in ca; lia.
  - by rewrite (bool_decide_eq_false_2 _ ne) in ca; lia.
rewrite bool_decide_eq_false_2 //.
case: (decide (z = b)) => [ez|zb]; first by subst z; rewrite
  bool_decide_eq_true_2 //; lia.
by rewrite bool_decide_eq_false_2 //; lia.
Qed.
