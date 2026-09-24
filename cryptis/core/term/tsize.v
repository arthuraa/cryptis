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
From cryptis.core.term Require Import base algebra.

Implicit Types (t k : term) (ts : list term).

(* The [tsize] measure and the well-founded induction principles it supports.
   [tsize] is [PreTerm.tsize] pulled back along [unfold_term]; the [tsize_*_lt]
   lemmas are the termination side conditions feeding [term_lt_rect] /
   [term_lt_ind].  It depends on core/term/algebra.v, which does not depend on
   it — no term-algebra lemma mentions [tsize]. *)

Definition tsize t := PreTerm.tsize (unfold_term t).

Lemma tsize_gt0 t : 0 < tsize t.
Proof. rewrite /tsize; case: unfold_term => [o|o t'|o t1 t2|[] ts] /=; lia. Qed.

Lemma tsize_eq t :
  tsize t =
  match t with
  | TInt _ => 1
  | TPair t1 t2 => S (tsize t1 + tsize t2)
  | TNonce _ => 1
  | TKey _ t => S (tsize t)
  | TSeal k t => S (tsize k + tsize t)
  | THash t => S (tsize t)
  | TNonFree pt _ _ => PreTerm.tsize pt
  end.
Proof. by case: t. Qed.

Lemma tsize_TInv t :
  negb (is_mul t) → negb (is_inv t) → tsize (TInv t) = S (tsize t).
Proof.
rewrite /tsize is_mul_unfold is_inv_unfold unfold_TInv => Nm Ni.
rewrite PreTerm.inv_Nmul //.
by case: unfold_term Nm Ni => //=; case.
Qed.

Lemma tsize_TGInv t :
  negb (is_gmul t) → negb (is_ginv t) → tsize (TGInv t) = S (tsize t).
Proof.
rewrite /tsize is_gmul_unfold is_ginv_unfold unfold_TGInv => Nm Ni.
rewrite PreTerm.ginv_Ngmul //.
by case: unfold_term Nm Ni => //=; case.
Qed.

(* The base must not be a group product or a group inverse: [TExp] distributes
   over those, and the result is not an exponential at all.  A *scalar* product
   or inverse in the base is fine — it is an atom. *)
Lemma tsize_TExp t1 t2 :
  negb (is_exp t1) → negb (is_gmul t1) → negb (is_ginv t1) →
  t2 ≠ TMulN [] →
  tsize (TExp t1 t2) = S (tsize t1 + tsize t2).
Proof.
rewrite /tsize is_exp_unfold is_gmul_unfold is_ginv_unfold unfold_TExp.
move=> Nx1 Nm1 Ni1 N12.
rewrite (PreTerm.exp_Ngmul _ _ (wf_unfold_term _) (wf_unfold_term _) Nm1).
rewrite (PreTerm.exp_aux_Nginv _ _ Ni1).
rewrite (PreTerm.base_expN _ Nx1) (PreTerm.expo_expN _ Nx1).
rewrite PreTerm.mul_unit_l PreTerm.mul1; last exact: wf_unfold_term.
rewrite /PreTerm.mk_exp bool_decide_eq_false_2 //.
move=> e; apply: N12; apply: (inj unfold_term).
by rewrite unfold_TMulN.
Qed.

(* The negative check the group/exponent split exists to make true: a *scalar*
   product in a base is an atom.  [TExp] does not distribute over it, so
   [TExp (t1 * t2) e] is a genuine exponential node whose size is the sum.  The
   same statement with [TGMulN] in place of [TMulN] is false --- there [TExp]
   distributes, and at the group unit it even collapses ([TExp_gunit]). *)
Lemma tsize_TExp_TMulN t1 t2 e :
  negb (is_mul t1) -> negb (is_mul t2) -> t1 ≠ TInv t2 ->
  e ≠ TMulN [] ->
  tsize (TExp (TMulN [t1; t2]) e)
  = S (tsize (TMulN [t1; t2]) + tsize e).
Proof.
move=> Nm1 Nm2 ne eN0.
have Xm : is_mul (TMulN [t1; t2]) := is_mul_TMulN2 _ _ Nm1 Nm2 ne.
by apply: tsize_TExp => //;
  [exact: is_mul_Nexp | exact: is_mul_Ngmul | exact: is_mul_Nginv].
Qed.

Lemma tsize_TMulN ts :
  invs_canceled ts →
  tsize (TMulN ts) =
  Nat.b2n (bool_decide (length ts ≠ 1)) +
  sum_list_with tsize ts.
Proof.
move=> ic; case: (decide (length ts = 1)) => len_ts.
  rewrite bool_decide_eq_false_2 //=; last congruence.
  case: ts len_ts {ic} => // t [] //.
  rewrite TMulN1 /=; lia.
rewrite /tsize.
case: (unfold_TMulN_strong _ ic len_ts)=> ts' [] -> /= e.
by rewrite bool_decide_eq_true_2 //= e sum_list_with_fmap.
Qed.

Lemma tsize_TGMulN ts :
  ginvs_canceled ts →
  tsize (TGMulN ts) =
  Nat.b2n (bool_decide (length ts ≠ 1)) +
  sum_list_with tsize ts.
Proof.
move=> ic; case: (decide (length ts = 1)) => len_ts.
  rewrite bool_decide_eq_false_2 //=; last congruence.
  case: ts len_ts {ic} => // t [] //.
  rewrite TGMulN1 /=; lia.
rewrite /tsize.
case: (unfold_TGMulN_strong _ ic len_ts)=> ts' [] -> /= e.
by rewrite bool_decide_eq_true_2 //= e sum_list_with_fmap.
Qed.

Definition tsizeE :=
  (tsize_TInv, tsize_TGInv, tsize_TExp, tsize_TMulN, tsize_TGMulN, tsize_eq).

(* Peeling an inverse strictly shrinks the term. *)
Lemma tsize_TInv_lt t : is_inv t -> tsize (TInv t) < tsize t.
Proof.
move=> Xi.
have Nm : negb (is_mul (TInv t)) by rewrite is_mul_TInv; exact: is_inv_Nmul.
have Ni : negb (is_inv (TInv t)).
  by rewrite (is_inv_TInv _ (is_inv_Nmul _ Xi)); case: is_inv Xi.
have := tsize_TInv _ Nm Ni; rewrite TInvK; lia.
Qed.

Lemma tsize_TGInv_lt t : is_ginv t -> tsize (TGInv t) < tsize t.
Proof.
move=> Xi.
have Nm : negb (is_gmul (TGInv t)) by rewrite is_gmul_TGInv; exact: is_ginv_Ngmul.
have Ni : negb (is_ginv (TGInv t)).
  by rewrite (is_ginv_TGInv _ (is_ginv_Ngmul _ Xi)); case: is_ginv Xi.
have := tsize_TGInv _ Nm Ni; rewrite TGInvK; lia.
Qed.

Lemma tsize_lt_TInv {t} : negb (is_mul t) → tsize (TInv t) ≤ S (tsize t).
Proof.
move=> Nm.
case: (decide (is_inv t)) => [tV|/negb_True tNV].
- rewrite -{2}[t]TInvK (tsize_TInv (TInv t)) ?is_mul_TInv //; first lia.
  by rewrite is_inv_TInv // negb_involutive.
- by rewrite tsize_TInv.
Qed.

Lemma tsize_TExpN t ts :
  negb (is_exp t) → negb (is_gmul t) → negb (is_ginv t) →
  invs_canceled ts →
  tsize (TExpN t ts) =
  (if bool_decide (ts ≠ []) then 1 else 0) +
  (if bool_decide (1 < length ts) then 1 else 0)
  + tsize t + sum_list_with tsize ts.
Proof.
move=> tNx tNm tNi ic; rewrite /TExpN.
case: (decide (ts = [])) => [->|tsN0] /=; first by rewrite TExp_unit; lia.
rewrite bool_decide_eq_true_2 //= tsize_TExp //; first last.
  move=> /(f_equal factors) e; have /Permutation_nil ? : [] ≡ₚ ts.
    rewrite -[ts]factors_TMulN // -[[]]factors_TMulN ?e //.
    exact: invs_canceled0.
  congruence.
rewrite tsize_TMulN //.
have ->: bool_decide (length ts ≠ 1) = bool_decide (1 < length ts).
  apply: bool_decide_ext; split; last lia.
  case: (ts) tsN0=> //= ? [] //=; lia.
case: bool_decide => /=; lia.
Qed.

(* [t1] must not be a group product or a group inverse:
   [TExp (TGMulN []) t2 = TGMulN []], so the strict inequality genuinely fails
   at the group unit. *)
Lemma tsize_lt_TExp_strong t1 t2 :
  negb (is_gmul t1) → negb (is_ginv t1) →
  negb (is_mul t2) → TInv t2 ∉ exps t1 →
  tsize t1 < tsize (TExp t1 t2) ∧
  S (tsize t2) < tsize (TExp t1 t2).
Proof.
move=> t1Nm t1Ni t2Nm t2_t1; rewrite TExpE -/(TMul _ _).
have xE: TMul (expo t1) t2 = TMulN (t2 :: factors (expo t1)).
  by rewrite /TMul -{1}[expo t1]factorsK TMulN_cat TMulN_catC.
have xN1: TMul (expo t1) t2 ≠ TMulN [].
  rewrite -/(TMul _ _) => /(f_equal (TMul (TInv t2))).
  rewrite [TMul _ t2]TMulC -TMulA TMulK_l TMul1_l TMul1 => eexpo.
  move: t2_t1; rewrite /exps eexpo factors_Nmul ?is_mul_TInv //.
  rewrite list_elem_of_singleton; congruence.
have ic: invs_canceled (t2 :: factors (expo t1)).
  rewrite invs_canceled_cons; do 2!split => //.
  exact: invs_canceled_factors.
rewrite (tsize_TExp _ _ (base_Nexp _)) ?is_gmul_base ?is_ginv_base //.
rewrite xE tsize_TMulN //=.
have ? := tsize_gt0 (base t1); split; last lia.
rewrite -{1}[t1]TExp_base_expo.
case: (decide (expo t1 = TMulN [])) => [->|n1].
  rewrite factors_TMulN0 /= TExp_unit; lia.
rewrite (tsize_TExp _ _ (base_Nexp _)) ?is_gmul_base ?is_ginv_base //.
rewrite -{1}[expo t1]factorsK tsize_TMulN; last exact: invs_canceled_factors.
have ? := tsize_gt0 t2.
move: n1; rewrite tunitP; case: factors=> [|? [| ??]] //=; lia.
Qed.

Lemma tsize_lt_TExp t1 t2 :
  negb (is_gmul t1) → negb (is_ginv t1) →
  negb (is_mul t2) → TInv t2 ∉ exps t1 →
  tsize t1 < tsize (TExp t1 t2) ∧
  tsize (TInv t2) < tsize (TExp t1 t2) ∧
  tsize t2 < tsize (TExp t1 t2).
Proof.
move => Nm1 Ni1 Nm2 t2_t1.
case: (tsize_lt_TExp_strong _ _ Nm1 Ni1 Nm2 t2_t1) => H1 H2.
have H3 := tsize_lt_TInv Nm2.
do !split; lia.
Qed.

Lemma tsize_TExp_TInv t1 t2 :
  negb (is_mul (TInv t2)) → t2 ∈ exps t1 →
  tsize t2 < tsize t1 ∧
  tsize (TInv t2) < tsize t1 ∧
  tsize (TExp t1 (TInv t2)) < tsize t1.
Proof.
move => NmI2 H.
have Nm2 : negb (is_mul t2) by rewrite is_mul_TInv in NmI2.
(* [t2 ∈ exps t1] forces [t1] to be an exponential, hence an atom-headed one *)
have en : exps t1 ≠ [] by move=> e; rewrite e elem_of_nil in H.
have xt : is_exp t1 by move: en; rewrite /exps -tunitP is_expE.
have Nm1 := is_exp_Ngmul _ xt.
have Ni1 := is_exp_Nginv _ xt.
set t1' := TExp t1 (TInv t2).
have t1E: t1 = TExp t1' t2.
  by rewrite /t1' TExpA -/(TMul _ _) TMulK_l TExp_unit.
have {}H: TInv t2 ∉ exps t1'.
  rewrite /exps -count_gt0 in H.
  rewrite /exps -count_gt0 /t1' (expo_TExp _ _ Nm1 Ni1) count_TMulN /=.
  rewrite !count_TInv_l count_TInv count_diag.
  case: is_mul Nm2 => //=; lia.
rewrite t1E.
case: (tsize_lt_TExp _ _ (Ngmul_TExp _ _ Nm1) (Nginv_TExp _ _ Nm1 Ni1) Nm2 H).
by move=> ? [] ??; eauto.
Qed.

Lemma term_lt_rect (T : term -> Type) :
  (forall t, (forall t', (tsize t' < tsize t) -> T t') -> T t) ->
  forall t, T t.
Proof.
move=> H t.
move: {-1}(tsize t) (Nat.le_refl (tsize t)) => n.
elim: n / (lt_wf n) t => n _ IH t t_n.
apply: H => t' t'_t.
apply: (IH (tsize t')); lia.
Qed.

Lemma tsize_base_lt t : is_exp t → tsize (base t) < tsize t.
Proof.
rewrite is_exp_unfold => xt.
rewrite /tsize unfold_base; move: xt.
by case: (unfold_term t) => [o|o t'|[||] t1 t2|[] ts] //= _; lia.
Qed.

Lemma tsize_expo_lt t : is_exp t → tsize (expo t) < tsize t.
Proof.
rewrite /tsize is_exp_unfold unfold_expo.
case: unfold_term (wf_unfold_term t) => //=; try lia.
case=> //=; try lia.
Qed.

Lemma tsize_factors_le t t' : t ∈ factors t' → tsize t ≤ tsize t'.
Proof.
move=> ?; rewrite -[t']factorsK tsize_TMulN; last exact: invs_canceled_factors.
suff: tsize t ≤ sum_list_with tsize (factors t') by lia.
exact: sum_list_with_in.
Qed.

Lemma tsize_exps_lt t' t : t' ∈ exps t → tsize t' < tsize t.
Proof.
move => t'_t.
have en: exps t ≠ [] by move=> e; rewrite e elem_of_nil in t'_t.
have xt: is_exp t by move: en; rewrite /exps -tunitP is_expE.
have ?: tsize (expo t) < tsize t by exact: tsize_expo_lt.
have := tsize_factors_le _ _ t'_t; lia.
Qed.

Lemma tsize_factors_lt t' t : is_mul t → t' ∈ factors t → tsize t' < tsize t.
Proof.
move => xt t'_t.
have tsN0 : factors t ≠ [] by move=> e; rewrite e elem_of_nil in t'_t.
rewrite -{1}(factorsK t) tsize_TMulN; last exact: invs_canceled_factors.
have le: tsize t' ≤ sum_list_with tsize (factors t) by exact: sum_list_with_in.
rewrite -is_mulE; case: is_mul xt => //=; lia.
Qed.

Lemma tsize_gfactors_le t t' : t ∈ gfactors t' → tsize t ≤ tsize t'.
Proof.
move=> ?; rewrite -[t']gfactorsK tsize_TGMulN;
  last exact: ginvs_canceled_gfactors.
suff: tsize t ≤ sum_list_with tsize (gfactors t') by lia.
exact: sum_list_with_in.
Qed.

Lemma tsize_gfactors_lt t' t : is_gmul t → t' ∈ gfactors t → tsize t' < tsize t.
Proof.
move => xt t'_t.
have tsN0 : gfactors t ≠ [] by move=> e; rewrite e elem_of_nil in t'_t.
rewrite -{1}(gfactorsK t) tsize_TGMulN; last exact: ginvs_canceled_gfactors.
have le: tsize t' ≤ sum_list_with tsize (gfactors t) by exact: sum_list_with_in.
rewrite -is_gmulE; case: is_gmul xt => //=; lia.
Qed.

Lemma term_lt_ind (T : term -> Prop) :
  (forall t, (forall t', (tsize t' < tsize t) -> T t') -> T t) ->
  forall t, T t.
Proof. exact: term_lt_rect. Qed.

Arguments tsize_lt_TExp {t1 t2} _ _.
Arguments tsize_TExp_TInv {t1 t2} _ _.
