From cryptis Require Import lib.
From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import sorting gmap.
From cryptis.lib Require Import list_sort mathcomp_compat sms.
From iris.heap_lang Require locations.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core Require Export pre_term.
From cryptis.core.term Require Import base.

Implicit Types (t k : term) (ts : list term) (s : tsms).

(** * Products

    [factors] is an injective homomorphism into the free abelian group
    [SMS.sms] ([factors_inj], [factors_TMul]), so the laws of products follow
    by comparing signed counts ([count_inj]). *)

Lemma count_unfold x t :
  count x t = SMS.count (unfold_term x) (PreTerm.factors (unfold_term t)).
Proof.
rewrite /count -unfold_factors SMS.count_map_inj //; exact: unfold_term_inj.
Qed.

Lemma gcount_unfold x t :
  gcount x t = SMS.count (unfold_term x) (PreTerm.gfactors (unfold_term t)).
Proof.
rewrite /gcount -unfold_gfactors SMS.count_map_inj //; exact: unfold_term_inj.
Qed.

Lemma factors_TMul_empty : factors (TMul ∅) = ∅.
Proof. by rewrite factors_TMul SMS.bind_empty. Qed.

Lemma TMul_singleton t : TMul {[+ t +]} = t.
Proof. by apply: factors_inj; rewrite factors_TMul SMS.bind_singleton. Qed.

Lemma count_TMul t s : count t (TMul s) = SMS.count t (SMS.bind factors s).
Proof. by rewrite /count factors_TMul. Qed.

Lemma count_TMul_empty t : count t (TMul ∅) = 0%Z.
Proof. by rewrite /count factors_TMul_empty SMS.count_empty. Qed.

Lemma count_TMul_disj_union t s1 s2 :
  count t (TMul (s1 ⊎ s2)) = (count t (TMul s1) + count t (TMul s2))%Z.
Proof. by rewrite !count_TMul SMS.bind_disj_union SMS.count_disj_union. Qed.

Lemma count_TMul_inv t s : count t (TMul (SMS.inv s)) = (- count t (TMul s))%Z.
Proof. by rewrite !count_TMul SMS.bind_inv SMS.count_inv. Qed.

Lemma TMul_disj_union s1 s2 : TMul (s1 ⊎ s2) = TMul {[+ TMul s1; TMul s2 +]}.
Proof.
apply: factors_inj; rewrite !factors_TMul !SMS.bind_disj_union.
by rewrite !SMS.bind_singleton !factors_TMul.
Qed.

Lemma TMul_unit_l t : TMul {[+ TMul ∅; t +]} = t.
Proof.
apply: count_inj => x _.
by rewrite count_TMul_disj_union !TMul_singleton count_TMul_empty.
Qed.

Lemma TMul_unit_r t : TMul {[+ t; TMul ∅ +]} = t.
Proof. by rewrite (comm (⊎)) TMul_unit_l. Qed.

Lemma TMul_inv_r t : TMul {[+ TInv t; t +]} = TMul ∅.
Proof.
apply: count_inj => x _.
rewrite count_TMul_disj_union !TMul_singleton count_TInv count_TMul_empty; lia.
Qed.

Lemma tunitP t : t = TMul ∅ ↔ factors t = ∅.
Proof.
split; first by move=> ->; exact: factors_TMul_empty.
by move=> e; apply: factors_inj; rewrite e factors_TMul_empty.
Qed.

#[global] Instance TInv_inj : Inj (=) (=) TInv.
Proof. by move=> x y e; rewrite -(TInvK x) e TInvK. Qed.

Lemma TInv_TMul s : TInv (TMul s) = TMul (SMS.inv s).
Proof.
by apply: factors_inj; rewrite factors_TInv !factors_TMul SMS.bind_inv.
Qed.

Lemma TInv_fixed t : TInv t = t ↔ t = TMul ∅.
Proof.
split=> [e|->]; last first.
  by apply: count_inj => x _; rewrite count_TInv count_TMul_empty.
apply: count_inj => x _; rewrite count_TMul_empty.
have := f_equal (count x) e; rewrite count_TInv; lia.
Qed.

Lemma count_diag t : count t t = if is_mul t then 0%Z else 1%Z.
Proof.
case Em: (is_mul t); first by rewrite is_mul_count ?Em.
rewrite /count factors_Nmul ?Em // SMS.count_singleton.
by rewrite bool_decide_eq_true_2.
Qed.

Lemma count_neq0 t t' : count t t' ≠ 0%Z ↔ t ∈ factors t'.
Proof. by rewrite SMS.elem_of_count. Qed.

Lemma count_gt0 t t' : (0 < count t t')%Z ↔ t ∈ SMS.pos (factors t').
Proof. exact: SMS.count_pos. Qed.

Lemma count_lt0 t t' : (count t t' < 0)%Z ↔ t ∈ SMS.neg (factors t').
Proof. exact: SMS.count_neg. Qed.

Lemma not_elem_of_count t t' : t ∉ factors t' → count t t' = 0%Z.
Proof. exact: SMS.not_elem_of_count. Qed.

Lemma elem_of_factors_TInv x t : x ∈ factors (TInv t) ↔ x ∈ factors t.
Proof. by rewrite -!count_neq0 count_TInv; split; lia. Qed.

Lemma elem_of_factors_TMul2 t1 t2 t' :
  t' ∈ factors (TMul {[+ t1; t2 +]}) → t' ∈ factors t1 ∨ t' ∈ factors t2.
Proof.
rewrite -!count_neq0 count_TMul_disj_union !TMul_singleton.
case: (decide (count t' t1 = 0%Z)) => ?; [right|left]; lia.
Qed.

(** ** The group *)

Lemma gfactors_TGMul_empty : gfactors (TGMul ∅) = ∅.
Proof. by rewrite gfactors_TGMul SMS.bind_empty. Qed.

Lemma TGMul_singleton t : TGMul {[+ t +]} = t.
Proof. by apply: gfactors_inj; rewrite gfactors_TGMul SMS.bind_singleton. Qed.

Lemma gcount_TGMul t s : gcount t (TGMul s) = SMS.count t (SMS.bind gfactors s).
Proof. by rewrite /gcount gfactors_TGMul. Qed.

Lemma gcount_TGMul_empty t : gcount t (TGMul ∅) = 0%Z.
Proof. by rewrite /gcount gfactors_TGMul_empty SMS.count_empty. Qed.

Lemma gcount_TGMul_disj_union t s1 s2 :
  gcount t (TGMul (s1 ⊎ s2)) = (gcount t (TGMul s1) + gcount t (TGMul s2))%Z.
Proof. by rewrite !gcount_TGMul SMS.bind_disj_union SMS.count_disj_union. Qed.

Lemma gcount_TGMul_inv t s :
  gcount t (TGMul (SMS.inv s)) = (- gcount t (TGMul s))%Z.
Proof. by rewrite !gcount_TGMul SMS.bind_inv SMS.count_inv. Qed.

Lemma TGMul_disj_union s1 s2 :
  TGMul (s1 ⊎ s2) = TGMul {[+ TGMul s1; TGMul s2 +]}.
Proof.
apply: gfactors_inj; rewrite !gfactors_TGMul !SMS.bind_disj_union.
by rewrite !SMS.bind_singleton !gfactors_TGMul.
Qed.

Lemma TGMul_unit_l t : TGMul {[+ TGMul ∅; t +]} = t.
Proof.
apply: gcount_inj => x _.
by rewrite gcount_TGMul_disj_union !TGMul_singleton gcount_TGMul_empty.
Qed.

Lemma TGMul_unit_r t : TGMul {[+ t; TGMul ∅ +]} = t.
Proof. by rewrite (comm (⊎)) TGMul_unit_l. Qed.

Lemma TGMul_inv_r t : TGMul {[+ TGInv t; t +]} = TGMul ∅.
Proof.
apply: gcount_inj => x _.
rewrite gcount_TGMul_disj_union !TGMul_singleton gcount_TGInv.
rewrite gcount_TGMul_empty; lia.
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
by apply: gfactors_inj; rewrite gfactors_TGInv !gfactors_TGMul SMS.bind_inv.
Qed.

Lemma TGInv_fixed t : TGInv t = t ↔ t = TGMul ∅.
Proof.
split=> [e|->]; last first.
  by apply: gcount_inj => x _; rewrite gcount_TGInv gcount_TGMul_empty.
apply: gcount_inj => x _; rewrite gcount_TGMul_empty.
have := f_equal (gcount x) e; rewrite gcount_TGInv; lia.
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
  t' ∈ gfactors (TGMul {[+ t1; t2 +]}) → t' ∈ gfactors t1 ∨ t' ∈ gfactors t2.
Proof.
rewrite -!gcount_neq0 gcount_TGMul_disj_union !TGMul_singleton.
case: (decide (gcount t' t1 = 0%Z)) => ?; [right|left]; lia.
Qed.

(** * Exponentiation *)

Lemma Ngmul_TExp b e : negb (is_gmul b) -> negb (is_gmul (TExp b e)).
Proof.
rewrite !is_gmul_unfold unfold_TExp => Nm.
exact: PreTerm.Ngmul_exp.
Qed.

Lemma base_idem pt : base (base pt) = base pt.
Proof.
apply: unfold_term_inj; rewrite !unfold_base.
rewrite PreTerm.base_expN //; exact: PreTerm.base_Nexp.
Qed.

Lemma base_Nexp t : negb (is_exp (base t)).
Proof. rewrite is_exp_unfold unfold_base; exact: PreTerm.base_Nexp. Qed.

Lemma expo_expN t : negb (is_exp t) → expo t = TMul ∅.
Proof.
rewrite is_exp_unfold => tNx; apply: unfold_term_inj.
rewrite unfold_expo unfold_TMul_make.
exact: PreTerm.expo_expN.
Qed.

(* The three non-free heads are mutually exclusive. *)
Lemma is_exp_Nmul t : is_exp t -> negb (is_mul t).
Proof.
rewrite is_exp_unfold is_mul_unfold; by case: (unfold_term t) => [|||[|] ??].
Qed.

Lemma is_exp_Ngmul t : is_exp t -> negb (is_gmul t).
Proof.
rewrite is_exp_unfold is_gmul_unfold; by case: (unfold_term t) => [|||[|] ??].
Qed.

Lemma is_mul_Ngmul t : is_mul t -> negb (is_gmul t).
Proof.
rewrite is_mul_unfold is_gmul_unfold; by case: (unfold_term t) => [|||[|] ??].
Qed.

Lemma is_mul_Nexp t : is_mul t -> negb (is_exp t).
Proof.
rewrite is_mul_unfold is_exp_unfold; by case: (unfold_term t) => [|||[|] ??].
Qed.

Lemma is_gmul_base t : is_gmul (base t) = is_gmul t.
Proof. rewrite !is_gmul_unfold unfold_base; exact: PreTerm.is_gmul_base. Qed.

Lemma base_expN t : negb (is_exp t) → base t = t.
Proof.
rewrite is_exp_unfold => tNx; apply: unfold_term_inj.
rewrite unfold_base; exact: PreTerm.base_expN.
Qed.

Lemma base_TExp b e : negb (is_gmul b) -> base (TExp b e) = base b.
Proof.
rewrite is_gmul_unfold => Nm.
apply: unfold_term_inj; rewrite !unfold_base unfold_TExp.
exact: PreTerm.base_exp.
Qed.

Lemma expo_TExp b e :
  negb (is_gmul b) -> expo (TExp b e) = TMul {[+ expo b; e +]}.
Proof.
rewrite is_gmul_unfold => Nm.
apply: unfold_term_inj; rewrite !unfold_expo unfold_TExp.
rewrite !SMS.singleton_make SMS.disj_union_make unfold_TMul_make /= unfold_expo.
exact: PreTerm.expo_exp.
Qed.

Lemma expo_TExp_expN b e :
  negb (is_exp b) → negb (is_gmul b) → expo (TExp b e) = e.
Proof. by move=> gNX gNm; rewrite expo_TExp // expo_expN // TMul_unit_l. Qed.

Lemma TExp_gfactors b e :
  TExp b e =
  TGMul (SMS.map (λ u, TExp u e) (gfactors b)).
Proof.
apply: unfold_term_inj.
rewrite unfold_TExp unfold_TGMul /PreTerm.exp -unfold_gfactors.
rewrite (SMS.map_map unfold_term _ (gfactors b)).
rewrite (SMS.map_map _ unfold_term (gfactors b)).
congr PreTerm.gmul; apply: SMS.map_ext => u u_b /=.
rewrite unfold_TExp PreTerm.exp_Ngmul //; try exact: wf_unfold_term.
by rewrite -is_gmul_unfold; exact: (Ngmul_gfactors _ _ u_b).
Qed.

Lemma gfactors_TExp b e :
  gfactors (TExp b e) =
  SMS.map (λ u, TExp u e) (gfactors b).
Proof.
rewrite {1}(TExp_gfactors b e) gfactors_TGMul_atoms // => x.
move=> /SMS.elem_of_map [u [-> u_b]].
by apply: Ngmul_TExp; apply: Ngmul_gfactors u_b.
Qed.

Lemma TExp_TGMul s e : TExp (TGMul s) e = TGMul (SMS.map (λ u, TExp u e) s).
Proof.
apply: gfactors_inj; rewrite gfactors_TExp !gfactors_TGMul.
rewrite SMS.map_bind SMS.bind_map.
by apply: SMS.bind_ext => u _; rewrite gfactors_TExp.
Qed.

Lemma TExp_TGInv t e : TExp (TGInv t) e = TGInv (TExp t e).
Proof.
apply: gfactors_inj.
rewrite gfactors_TExp !gfactors_TGInv gfactors_TExp.
exact: SMS.map_inv.
Qed.

Lemma TExp_gunit e : TExp (TGMul ∅) e = TGMul ∅.
Proof. by rewrite TExp_TGMul SMS.map_empty. Qed.

Definition exps t := factors (expo t).

Lemma count_mem_exps_pos x t :
  Z.of_nat (count_mem x (SMS.pos (exps t))) = Z.max 0 (count x (expo t)).
Proof. exact: SMS.count_mem_pos. Qed.

Lemma exps_TExp_expN b e :
  negb (is_exp b) → negb (is_gmul b) → exps (TExp b e) = factors e.
Proof. by move=> gNX gNm; rewrite /exps expo_TExp_expN. Qed.

Lemma TExp_base_expo t : TExp (base t) (expo t) = t.
Proof.
apply: unfold_term_inj; rewrite unfold_TExp unfold_base unfold_expo.
exact: PreTerm.exp_base_expo.
Qed.

Lemma TExpA b e1 e2 : TExp (TExp b e1) e2 = TExp b (TMul {[+ e1; e2 +]}).
Proof.
wlog: b / negb (is_gmul b).
  move=> Hb.
  rewrite [in LHS](TExp_gfactors b e1) TExp_TGMul.
  rewrite [in RHS](TExp_gfactors b (TMul {[+ e1; e2 +]})) SMS.map_map.
  congr TGMul; apply: SMS.map_ext => u u_b.
  by apply: Hb; apply: Ngmul_gfactors u_b.
move=> Nm.
have Nm1 := Ngmul_TExp b e1 Nm.
rewrite -[LHS]TExp_base_expo -[RHS]TExp_base_expo.
rewrite !(base_TExp _ _ Nm1) !(expo_TExp _ _ Nm1).
rewrite !(base_TExp _ _ Nm) !(expo_TExp _ _ Nm).
congr TExp; apply: count_inj => x _.
rewrite !count_TMul_disj_union !TMul_singleton !count_TMul_disj_union.
rewrite !TMul_singleton; lia.
Qed.

Lemma TExpE b e : TExp b e = TExp (base b) (TMul {[+ expo b; e +]}).
Proof. by rewrite -{1}(TExp_base_expo b) TExpA. Qed.

Lemma TExp_unit b : TExp b (TMul ∅) = b.
Proof.
by rewrite -{1}(TExp_base_expo b) TExpA TMul_unit_r TExp_base_expo.
Qed.

Lemma base_expsK t : TExp (base t) (TMul (exps t)) = t.
Proof. by rewrite /exps factorsK TExp_base_expo. Qed.

Lemma TExpK u v : TExp (TExp u v) (TInv v) = u.
Proof.
rewrite TExpA (_ : TMul {[+ v; TInv v +]} = TMul ∅) ?TExp_unit //.
by rewrite (comm (⊎)) TMul_inv_r.
Qed.

Lemma TExpKV u v : TExp (TExp u (TInv v)) v = u.
Proof. by have := TExpK u (TInv v); rewrite TInvK. Qed.

Lemma is_gmul_TExp b e : is_gmul (TExp b e) = is_gmul b.
Proof.
have := Ngmul_TExp b e; have := Ngmul_TExp (TExp b e) (TInv e).
rewrite TExpK.
by case: (is_gmul b); case: (is_gmul (TExp b e)) => //= /(_ I).
Qed.

(* Distributivity makes [TGMul ∅ ^ e = TGMul ∅] for every [e], so
   exponentiation is genuinely not injective in the exponent at the group
   unit; hence the group-atom premise. *)
Lemma TExp_injr t t1 t2 :
  negb (is_gmul t) -> TExp t t1 = TExp t t2 -> t1 = t2.
Proof.
move=> Nm e; have /(f_equal expo) := e; rewrite !(expo_TExp _ _ Nm) => e'.
apply: count_inj => x _; have := f_equal (count x) e'.
rewrite !count_TMul_disj_union !TMul_singleton; lia.
Qed.

(* Exponentiation is injective in the base, once group products are excluded.
   The group unit is the only base it collapses, and it is a group product. *)
Lemma TExp_injl t1 t2 e :
  negb (is_gmul t1) -> negb (is_gmul t2) ->
  TExp t1 e = TExp t2 e -> t1 = t2.
Proof.
move=> Nm1 Nm2 E.
have Eb : base t1 = base t2.
  by rewrite -(base_TExp t1 e Nm1) -(base_TExp t2 e Nm2) E.
have Ee : expo t1 = expo t2.
  apply: count_inj => x _.
  have := f_equal (count x) (f_equal expo E).
  rewrite !expo_TExp // !count_TMul_disj_union !TMul_singleton; lia.
by rewrite -(TExp_base_expo t1) -(TExp_base_expo t2) Eb Ee.
Qed.

Lemma is_mul_TMul2 t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) -> is_mul (TMul {[+ t1; t2 +]}).
Proof.
move=> Nm1 Nm2; case E: (is_mul (TMul {[+ t1; t2 +]})) => //.
have Nm : negb (is_mul (TMul {[+ t1; t2 +]})) by rewrite E.
have H : factors (TMul {[+ t1; t2 +]}) = {[+ t1; t2 +]}.
  apply: factors_TMul_atoms => x.
  by case/SMS.elem_of_disj_union => /SMS.elem_of_singleton ->.
move: H; rewrite (factors_Nmul _ Nm) => /(f_equal (λ s, length (elements s))).
rewrite SMS.elements_singleton !SMS.singleton_make SMS.disj_union_make /=.
by rewrite (Permutation_length (SMS.elements_make_nil_r _)).
Qed.

Lemma count_expo_TExp t1 t2 t3 :
  negb (is_gmul t2) ->
  count t1 (expo (TExp t2 t3)) = (count t1 (expo t2) + count t1 t3)%Z.
Proof.
by move=> Nm; rewrite (expo_TExp _ _ Nm) count_TMul_disj_union !TMul_singleton.
Qed.

Lemma count_expo_TExp_eq t1 t2 :
  negb (is_mul t1) -> negb (is_gmul t2) ->
  count t1 (expo (TExp t2 t1)) = (count t1 (expo t2) + 1)%Z.
Proof.
move=> Nm1 Nm2; rewrite (count_expo_TExp _ _ _ Nm2) count_diag.
by case: is_mul Nm1.
Qed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma is_expE t : is_exp t ↔ expo t ≠ TMul ∅.
Proof.
rewrite is_exp_unfold.
have ->: expo t ≠ TMul ∅ ↔ unfold_term (expo t) ≠ unfold_term (TMul ∅).
  split; last congruence.
  by move=> n1 contra; apply: n1; apply: inj contra.
rewrite unfold_expo unfold_TMul_make.
rewrite -[PreTerm.mul _]/(PreTerm.PTMul [] []).
case: unfold_term (wf_unfold_term t) => /=; try by intuition congruence.
case; try by intuition congruence.
by move=> t1 t2; rewrite !andb_True bool_decide_spec; case; intuition.
Qed.

Lemma is_expNE t : negb (is_exp t) ↔ expo t = TMul ∅.
Proof.
rewrite negb_True is_expE; split; eauto.
exact: dec_stable.
Qed.

Lemma is_exp_of_exps t t' : t' ∈ exps t -> is_exp t.
Proof.
move=> t'_t; apply/is_expE => e.
move: t'_t; rewrite /exps e factors_TMul_empty.
by rewrite SMS.elem_of_count SMS.count_empty.
Qed.

Lemma count_expo_TExp_gt0 t1 t2 :
  (0 < count t1 (expo (TExp t2 t1)))%Z ↔
  negb (is_mul t1) ∧ negb (is_gmul t2) ∧ (0 ≤ count t1 (expo t2))%Z.
Proof.
split; last by case=> Nm1 [Nm2 ?]; rewrite count_expo_TExp_eq //; lia.
move=> pos; have t1_in : t1 ∈ exps (TExp t2 t1).
  by rewrite /exps; apply/count_neq0; lia.
have Nm1 := Nmul_factors _ _ t1_in.
have Nm2 : negb (is_gmul t2).
  rewrite -(is_gmul_TExp t2 t1); exact: is_exp_Ngmul _ (is_exp_of_exps t1_in).
split=> //; split=> //; move: pos; rewrite count_expo_TExp_eq //; lia.
Qed.

Lemma TExp_TMul_cons_l t x X Y :
  TExp t (TMul (SMS.make (x :: X) Y)) = TExp (TExp t (TMul (SMS.make X Y))) x.
Proof.
rewrite TExpA; congr TExp; apply: count_inj => z _.
rewrite count_TMul_disj_union !TMul_singleton !count_TMul SMS.bind_make_cons_l.
rewrite SMS.count_disj_union /count; lia.
Qed.

Lemma TExp_TMul_cons_r t y X Y :
  TExp t (TMul (SMS.make X (y :: Y))) =
  TExp (TExp t (TMul (SMS.make X Y))) (TInv y).
Proof.
rewrite TExpA; congr TExp; apply: count_inj => z _.
rewrite count_TMul_disj_union !TMul_singleton count_TInv !count_TMul.
rewrite SMS.bind_make_cons_r SMS.count_disj_union SMS.count_inv /count; lia.
Qed.

Lemma exps_TExp_TMul t s :
  negb (is_exp t) -> negb (is_gmul t) ->
  (∀ u, u ∈ s → negb (is_mul u)) →
  exps (TExp t (TMul s)) = s.
Proof.
by move=> tNexp tNm Hs; rewrite /exps expo_TExp_expN // factors_TMul_atoms.
Qed.

Lemma TExpC g a b : TExp (TExp g a) b = TExp (TExp g b) a.
Proof. by rewrite !TExpA (comm (⊎)). Qed.

(** ** Atoms *)

Lemma count_atom_ne t1 t2 :
  negb (is_mul t2) -> t1 ≠ t2 -> count t1 t2 = 0%Z.
Proof.
move=> Nm2 ne; rewrite /count factors_Nmul // SMS.count_singleton.
by rewrite bool_decide_eq_false_2.
Qed.

Lemma count_atom_ge0 t1 t2 : negb (is_mul t2) -> (0 <= count t1 t2)%Z.
Proof.
move=> Nm2; rewrite /count factors_Nmul // SMS.count_singleton.
by case: bool_decide.
Qed.

Lemma count_TMul_atoms x s :
  (∀ u, u ∈ s → negb (is_mul u)) → count x (TMul s) = SMS.count x s.
Proof. by move=> Hs; rewrite /count factors_TMul_atoms. Qed.

Lemma count_TMul_atoms_ne t s :
  (∀ u, u ∈ s → negb (is_mul u) ∧ t ≠ u) → count t (TMul s) = 0%Z.
Proof.
move=> H; rewrite count_TMul_atoms; last by move=> u /H [].
by apply: SMS.not_elem_of_count => /H [_ []].
Qed.

Lemma not_elem_of_factors_TMul t s :
  (∀ u, u ∈ s → negb (is_mul u) ∧ t ≠ u) → t ∉ factors (TMul s).
Proof. by move=> H /count_neq0; rewrite (count_TMul_atoms_ne H). Qed.

Lemma not_elem_of_factors_atom t1 t2 :
  negb (is_mul t2) -> t1 ≠ t2 -> t1 ∉ factors t2.
Proof. by move=> f2 ne /count_neq0; rewrite (count_atom_ne f2 ne). Qed.

Lemma count_atom_diag t : negb (is_mul t) -> count t t = 1%Z.
Proof. by rewrite count_diag; case: is_mul. Qed.

Lemma elem_of_factors_Nmul x t : negb (is_mul t) -> x ∈ factors t ↔ x = t.
Proof.
by move=> Nm; rewrite factors_Nmul // SMS.elem_of_singleton.
Qed.

Lemma elem_of_gfactors_Ngmul x t : negb (is_gmul t) -> x ∈ gfactors t ↔ x = t.
Proof.
by move=> Nm; rewrite gfactors_Ngmul // SMS.elem_of_singleton.
Qed.

Lemma gcount_atom_ge0 t1 t2 : negb (is_gmul t2) -> (0 <= gcount t1 t2)%Z.
Proof.
move=> Nm2; rewrite /gcount gfactors_Ngmul // SMS.count_singleton.
by case: bool_decide.
Qed.
