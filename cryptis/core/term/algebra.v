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

Implicit Types (t k : term) (ts : list term).

Lemma TMulN_catC ts1 ts2 : TMulN (ts1 ++ ts2) = TMulN (ts2 ++ ts1).
Proof. by rewrite Permutation_app_comm. Qed.

Lemma TExpN_catC t ts1 ts2 : TExpN t (ts1 ++ ts2) = TExpN t (ts2 ++ ts1).
Proof. by rewrite /TExpN TMulN_catC. Qed.

Lemma TMulN_app A B : TMulN [TMulN A; TMulN B] = TMulN (A ++ B).
Proof. by rewrite TMulN_cat TMulN_catC /= TMulN_cat TMulN_catC. Qed.

Definition TMul a b := TMulN [a; b].
Arguments TMul : simpl never.

Lemma TMulC a b : TMul a b = TMul b a.
Proof. by rewrite /TMul Permutation_swap. Qed.

Lemma TMul1 a : TMul a (TMulN []) = a.
Proof.
by rewrite /TMul Permutation_swap TMulN_cat /= TMulN1.
Qed.

Lemma TMulA a b c : TMul (TMul a b) c = TMul a (TMul b c).
Proof.
apply: count_inj => t; rewrite !count_TMulN /= !count_TMulN /=.
by lia.
Qed.

Lemma TMul1_l a : TMul (TMulN []) a = a.
Proof. by rewrite TMulC TMul1. Qed.

Lemma TMulK a : TMul a (TInv a) = TMulN [].
Proof.
by apply: count_inj => x _; rewrite /TMul !count_TMulN /= count_TInv; lia.
Qed.

Lemma TMulK_l a : TMul (TInv a) a = TMulN [].
Proof. by rewrite TMulC TMulK. Qed.

Lemma TMul_cancel a b c : TMul a b = TMul a c -> b = c.
Proof.
move=> E.
have H : TMul (TInv a) (TMul a b) = TMul (TInv a) (TMul a c) by rewrite E.
by rewrite -!TMulA !TMulK_l !TMul1_l in H.
Qed.

Lemma TInvK t : TInv (TInv t) = t.
Proof. apply: (@TMul_cancel (TInv t)); by rewrite TMulK TMulK_l. Qed.

Global Instance TInv_inj : Inj (=) (=) TInv.
Proof. by move=> t1 t2 /(f_equal TInv); rewrite !TInvK. Qed.

Lemma base_expsK t : TExpN (base t) (exps t) = t.
Proof.
by rewrite /TExpN /exps factorsK TExp_base_expo.
Qed.

Lemma TExpNA t ts1 ts2 : TExpN (TExpN t ts1) ts2 = TExpN t (ts1 ++ ts2).
Proof. by rewrite /TExpN TExpA TMulN_app. Qed.

Lemma no_inv_singleton {t} : negb (is_mul t) -> forall x, x ∈ [t] -> TInv x ∉ [t].
Proof.
move=> Nm x /list_elem_of_singleton ->.
rewrite list_elem_of_singleton; exact: (TInv_Nid _ Nm).
Qed.

Lemma invs_canceled1 {t} : negb (is_mul t) → invs_canceled [t].
Proof.
move=> tNm x x_t; split; first exact: no_inv_singleton tNm x x_t.
by move: x_t => /list_elem_of_singleton ->.
Qed.

Lemma invs_canceled2 {t1 t2} :
  negb (is_mul t1) → negb (is_mul t2) →
  invs_canceled [t1; t2] ↔ t1 ≠ TInv t2.
Proof.
move=> t1Nm t2Nm.
rewrite !invs_canceled_cons !elem_of_nil !list_elem_of_singleton.
split.
- by case=> neq _ contra; apply: neq; rewrite contra TInvK.
- move=> t1_t2; do 4?split => //; eauto.
  + by move=> contra; apply: t1_t2; rewrite -contra TInvK.
  + exact: invs_canceled0.
Qed.

Global Instance invs_canceled_Permutation :
  Proper ((≡ₚ) ==> (↔)) invs_canceled.
Proof.
move=> ts1 ts2 peq; split => H x Hx.
- rewrite -peq; apply: H; by rewrite peq.
- rewrite peq; apply: H; by rewrite -peq.
Qed.

Lemma TExpN0 t : TExpN t [] = t.
Proof. by rewrite /TExpN TExp_unit. Qed.

Lemma TInv_TMulN ts : TInv (TMulN ts) = TMulN (TInv <$> ts).
Proof.
apply: count_inj => t _; rewrite count_TInv !count_TMulN.
elim: ts => //= t0 ts <-; rewrite count_TInv /fmap; lia.
Qed.

Lemma TExpNK ts t : TExpN (TExpN t ts) (TInv <$> ts) = t.
Proof.
by rewrite /TExpN TExpA -TInv_TMulN -/(TMul _ _) TMulC TMulK_l TExp_unit.
Qed.

Lemma TExpK u v : TExp (TExp u v) (TInv v) = u.
Proof. by have := TExpNK [v] u; rewrite /TExpN /= !TMulN1. Qed.

Lemma TExpKV u v : TExp (TExp u (TInv v)) v = u.
Proof. by have := TExpK u (TInv v); rewrite TInvK. Qed.

Lemma TExp_injr t t1 t2 : TExp t t1 = TExp t t2 -> t1 = t2.
Proof.
move=> e.
have: TMul (expo t) t1 = TMul (expo t) t2.
  by have /(f_equal expo) := e; rewrite !expo_TExp.
move=> /(f_equal (TMul (TInv (expo t)))).
by rewrite -TMulA TMulK_l -TMulA TMulK_l !TMul1_l.
Qed.

Lemma not_elem_of_count t t' : t ∉ factors t' → (count t t' ≤ 0)%Z.
Proof.
move=> t_nin; rewrite /count; apply: SMS.not_elem_of_count.
by rewrite -unfold_factors (list_elem_of_fmap_inj unfold_term).
Qed.

Lemma is_mul_TInv t : is_mul (TInv t) = is_mul t.
Proof.
have H: ∀ t, is_mul (TInv t) → is_mul t.
  move=> {}t; case e: (is_mul t) => //.
  suff -> : is_mul (TInv t) = false by [].
  rewrite !is_mul_unfold unfold_TInv in e *.
  rewrite PreTerm.inv_Nmul ?e //.
  case: unfold_term (wf_unfold_term t) e => //=.
  case => //= {}t /andb_True [] /andb_True [].
  by case: PreTerm.is_mul.
apply: eq_bool_prop_intro; split; eauto.
rewrite -{1}[t]TInvK; exact: H.
Qed.

Lemma not_elem_of_count_strong t t' :
  t ∉ factors t' →
  TInv t ∉ factors t' →
  count t t' = 0%Z.
Proof.
move=> t_nin tV_nin; apply: SMS.not_elem_of_count_strong.
  by rewrite -unfold_factors list_elem_of_fmap_inj.
set tV := PreTerm.inv_aux _ => tV_in; apply: tV_nin.
have wf_tV: PreTerm.wf tV.
  apply: PreTerm.wf_factors_wf tV_in.
  exact: PreTerm.wf_wf_factors.
have tNm : negb (PreTerm.is_mul (unfold_term t)).
  by rewrite /tV in wf_tV; case: unfold_term wf_tV.
rewrite -(list_elem_of_fmap_inj unfold_term) unfold_TInv PreTerm.inv_Nmul //.
by rewrite unfold_factors.
Qed.

Lemma invs_canceled_factors t : invs_canceled (factors t).
Proof.
apply: wf_factors_invs_canceled.
exact: PreTerm.wf_wf_factors.
Qed.

Lemma is_mul_count t t' : is_mul t → count t t' = 0%Z.
Proof.
move=> tm; apply: not_elem_of_count_strong.
- move=> t_in; case: (invs_canceled_factors _ _ t_in).
  by case: is_mul in tm *.
- move=> t_in; case: (invs_canceled_factors _ _ t_in).
  by rewrite -is_mul_TInv in tm; case: is_mul in tm *.
Qed.

Lemma count_TInv_l t t' : count (TInv t) t' = (- count t t')%Z.
Proof.
case: (decide (is_mul t)) => tm.
  by rewrite ?is_mul_count // is_mul_TInv.
rewrite /count unfold_TInv PreTerm.inv_Nmul; last first.
  by rewrite negb_True -is_mul_unfold.
by rewrite SMS.count_i // PreTerm.inv_auxK.
Qed.

Lemma not_elem_of_count0 t t' :
  t ∉ factors t' ∧ TInv t ∉ factors t' ↔ count t t' = 0%Z.
Proof.
split; first by case; exact: not_elem_of_count_strong.
have H: ∀ t, count t t' = 0%Z → t ∉ factors t'.
  move=> {}t cE0 t_in.
  have t_inP : unfold_term t ∈ PreTerm.factors (unfold_term t') ↔
               PreTerm.inv_aux (unfold_term t) ∈ PreTerm.factors (unfold_term t').
    exact: SMS.count_eq0_elem_of.
  case: (invs_canceled_factors _ _ t_in) => tV_in tNm.
  rewrite is_mul_unfold in tNm.
  rewrite -PreTerm.inv_Nmul // -unfold_TInv -unfold_factors in t_inP.
  rewrite !(list_elem_of_fmap_inj unfold_term) in t_inP.
  tauto.
move=> cE0; split; first exact: H.
by apply: H; rewrite count_TInv_l cE0.
Qed.

Lemma count_gt0 t t' : (count t t' > 0)%Z ↔ t ∈ factors t'.
Proof.
split.
- move=> gt0; case: (decide (t ∈ factors t')) => // t_nin.
  have := not_elem_of_count _ _ t_nin; lia.
- move=> t_in.
  have tV_in: TInv t ∉ factors t' by case: (invs_canceled_factors _ _ t_in).
  have := not_elem_of_count _ _ tV_in; rewrite count_TInv_l => c_ge0.
  have ?: count t t' ≠ 0%Z by move=> /not_elem_of_count0; tauto.
  lia.
Qed.

Lemma count_expo_TExp t1 t2 t3 :
  count t1 (expo (TExp t2 t3)) =
  (count t1 (expo t2) + count t1 t3)%Z.
Proof. rewrite expo_TExp count_TMulN /=; lia. Qed.

Lemma count_diag t : count t t = if is_mul t then 0 else 1.
Proof.
case e: is_mul; first by apply: is_mul_count; rewrite e.
rewrite /count -unfold_factors factors_Nmul ?e //=.
rewrite SMS.count_cons bool_decide_eq_true_2 //= bool_decide_eq_false_2 /=.
- rewrite /SMS.count /=; lia.
- exact: PreTerm.inv_aux_Nid.
Qed.

Lemma count_expo_TExp_eq t1 t2 :
  negb (is_mul t1) ->
  count t1 (expo (TExp t2 t1)) = (count t1 (expo t2) + 1)%Z.
Proof. by rewrite count_expo_TExp count_diag; case: is_mul. Qed.

Lemma exps_count_TExpW t1 t2 t3 :
  negb (is_mul t3) →
  t1 ≠ TInv t3 →
  (count t1 (expo t2) ≤ count t1 (expo (TExp t2 t3)))%Z.
Proof.
move=> Nm3 t1_t3; rewrite count_expo_TExp.
suff: (0 ≤ count t1 t3)%Z by lia.
have: t1 ∉ factors (TInv t3).
  by rewrite factors_Nmul ?list_elem_of_singleton // is_mul_TInv.
rewrite -count_gt0 count_TInv; lia.
Qed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Global Instance TExpN_proper : Proper ((=) ==> (≡ₚ) ==> (=)) TExpN.
Proof.
by rewrite /TExpN => t _ <- ts1 ts2 <-.
Qed.

Lemma TExpNC2 g t1 t2 : TExpN g [t1; t2] = TExpN g [t2; t1].
Proof. by rewrite Permutation_swap. Qed.

Lemma not_elem_of_TInv_exps t1 t2 :
  negb (is_mul t1) →
  TInv t1 ∉ exps t2 ↔ t1 ∈ exps (TExp t2 t1).
Proof.
rewrite  /exps expo_TExp -!count_gt0 count_TInv_l count_TMulN /=.
rewrite count_diag; case: is_mul => //; lia.
Qed.

Lemma countE t1 t2 : count t1 t2 = SMS.count TInv t1 (factors t2).
Proof.
have E: ∀ t1, t1 ∈ factors t2 → count t1 t2 = SMS.count TInv t1 (factors t2).
  move=> {}t1 t1_t2.
  case: (invs_canceled_factors _ _ t1_t2) => t1V_t2 t1Nm.
  rewrite /count -unfold_factors !SMS.count_count_mem //.
    rewrite count_mem_fmap //; exact: inj.
  rewrite -PreTerm.inv_Nmul // -?unfold_TInv ?list_elem_of_fmap_inj //.
  by rewrite -is_mul_unfold.
case: (decide (t1 ∈ factors t2)) => t1_t2; first by rewrite E.
case: (decide (TInv t1 ∈ factors t2)) => t1V_t2.
  rewrite -[t1 in LHS]TInvK count_TInv_l E // SMS.count_i ?TInvK //; lia.
rewrite not_elem_of_count_strong //.
by rewrite SMS.not_elem_of_count_strong //.
Qed.

Lemma count_count_mem t1 t2 :
  t1 ∈ factors t2 → count t1 t2 = count_mem t1 (factors t2).
Proof.
move=> t1_t2; rewrite countE SMS.count_count_mem //.
by case: (invs_canceled_factors _ _ t1_t2).
Qed.

Lemma factors_TInv t : factors (TInv t) ≡ₚ TInv <$> factors t.
Proof.
have e: ∀ t0, t0 ∈ factors (TInv t) ↔ t0 ∈ (TInv <$> factors t).
  move=> t0; rewrite -{2}[t0]TInvK (list_elem_of_fmap_inj TInv).
  by rewrite -!count_gt0 count_TInv count_TInv_l.
apply: Permutation_count_mem => t0.
case: (decide (t0 ∈ factors (TInv t))) => t0_in1; last first.
  have t0_in2: t0 ∉ TInv <$> factors t by rewrite -e.
  rewrite !not_elem_of_count_mem in t0_in1 t0_in2.
  by rewrite t0_in1 t0_in2.
have t0V_nin1: TInv t0 ∉ factors (TInv t).
  by case: (invs_canceled_factors _ _ t0_in1).
move/e: (t0_in1) => t0_in2.
move/e: (t0V_nin1) => t0V_nin2.
have := count_count_mem t0_in1; rewrite count_TInv => e1.
rewrite -(list_elem_of_fmap_inj TInv) in t0_in2.
rewrite -[RHS](count_mem_fmap TInv); last exact: inj.
have ef: TInv <$> (TInv <$> factors t) = factors t.
  rewrite -list_fmap_compose -[RHS]list_fmap_id.
  apply/Forall_fmap_ext/Forall_forall=> ? _; exact: TInvK.
rewrite ef in t0_in2 *.
have := count_count_mem t0_in2; rewrite count_TInv_l => e2.
lia.
Qed.

Lemma TInv_fixed t : TInv t = t ↔ t = TMulN [].
Proof.
split.
- move=> et; apply: count_inj => t0 _.
  rewrite count_TMulN /=; suff ?: count t0 t = (- count t0 t)%Z by lia.
  by rewrite -{1}et count_TInv.
- by move=> ->; rewrite TInvE factors_TMulN0.
Qed.

Lemma factors_TMulN ts :
  invs_canceled ts →
  factors (TMulN ts) ≡ₚ ts.
Proof.
move=> ic.
have wfU : Forall PreTerm.wf (unfold_term <$> ts) := wf_unfold_terms ts.
have Nm : forall x, x ∈ (unfold_term <$> ts) -> negb (PreTerm.is_mul x).
  move=> _ /list_elem_of_fmap [t' [-> t'in]].
  by rewrite -is_mul_unfold; case: (ic t' t'in).
have nopairs : forall x, x ∈ (unfold_term <$> ts) ->
                 PreTerm.inv_aux x ∉ (unfold_term <$> ts).
  move=> _ /list_elem_of_fmap [t' [-> t'in]].
  have [Vnin t'Nm] := ic t' t'in.
  rewrite -PreTerm.inv_Nmul; last by rewrite -is_mul_unfold.
  rewrite -unfold_TInv => /list_elem_of_fmap [t'' [/unfold_term_inj e t''in]].
  by apply: Vnin; rewrite e.
have flat : forall l, (forall x, x ∈ l -> negb (PreTerm.is_mul x)) ->
              mbind PreTerm.factors l = l.
  elim=> [//|x l IH] H /=.
  rewrite PreTerm.factors_Nmul; last by apply: H; apply/elem_of_cons; left.
  by rewrite -/(mbind PreTerm.factors l) IH // => y yin; apply: H;
     apply/elem_of_cons; right.
rewrite /factors unfold_TMulN /PreTerm.mul PreTerm.mul_auxK;
  last exact: PreTerm.wf_normalize_factors wfU.
rewrite /PreTerm.normalize_factors flat // (SMS.to_id_perm _ _ _ nopairs).
by rewrite fmap_unfold_termK.
Qed.

Lemma unfold_TMulN_strong ts :
  invs_canceled ts →
  length ts ≠ 1 →
  ∃ ts' : list _,
    unfold_term (TMulN ts) = PreTerm.PTMul ts' ∧
    ts' ≡ₚ unfold_term <$> ts.
Proof.
move=> ic tsN1; rewrite unfold_TMulN.
pose (ts' := PreTerm.normalize_factors (unfold_term <$> ts)).
have e: ts' ≡ₚ unfold_term <$> ts.
  have -> : ts' = PreTerm.factors (unfold_term (TMulN ts)).
    rewrite /ts' unfold_TMulN /PreTerm.mul PreTerm.mul_auxK //.
    exact: PreTerm.wf_normalize_factors (wf_unfold_terms ts).
  by rewrite -unfold_factors; apply: Permutation_map; apply: factors_TMulN.
exists ts'; split => //.
rewrite -(length_fmap unfold_term) -e /ts' in tsN1.
rewrite /PreTerm.mul /ts'.
by case: PreTerm.normalize_factors tsN1 => //= ? [].
Qed.

Lemma tunitP t : t = TMulN [] ↔ factors t = [].
Proof.
by split=> [->|<-]; rewrite ?factorsK // factors_TMulN0.
Qed.

Lemma is_expE t : is_exp t ↔ expo t ≠ TMulN [].
Proof.
rewrite is_exp_unfold.
have ->: expo t ≠ TMulN [] ↔ unfold_term (expo t) ≠ unfold_term (TMulN []).
  split; last congruence.
  by move=> n1 contra; apply: n1; apply: inj contra.
rewrite unfold_expo unfold_TMulN /= -[PreTerm.mul _]/(PreTerm.PTMul []).
case: unfold_term (wf_unfold_term t) => /=; try by intuition congruence.
case; try by intuition congruence.
by move=> t1 t2; rewrite !andb_True bool_decide_spec; case; intuition.
Qed.

Lemma is_expNE t : negb (is_exp t) ↔ expo t = TMulN [].
Proof.
rewrite negb_True is_expE; split; eauto.
exact: dec_stable.
Qed.

Lemma TExp_TExpN t1 ts1 t2 : TExp (TExpN t1 ts1) t2 = TExpN t1 (t2 :: ts1).
Proof.
have -> : TExp (TExpN t1 ts1) t2 = TExpN (TExpN t1 ts1) [t2].
  by rewrite /TExpN TMulN1.
by rewrite TExpNA Permutation_app_comm.
Qed.

(* The [t1 ≠ TInv t'] premise is not optional: without it, taking [ts = [x]]
   and [t1 = TInv x] over a non-exponential [t2] gives [0 <= -1].  It is the
   [n]-ary form of the side condition [exps_count_TExpW] carries. *)
Lemma exps_count_TExpNW t1 t2 ts :
  invs_canceled ts →
  (∀ t', t' ∈ ts → t1 ≠ TInv t') →
  (count t1 (expo t2) ≤ count t1 (expo (TExpN t2 ts)))%Z.
Proof.
elim: ts => [|t ts IH]; first by move => _ _; rewrite TExpN0; lia.
case/invs_canceled_cons=> tV_ts [] tNm ic ts_t.
have t1_t : t1 ≠ TInv t by apply: ts_t; apply/elem_of_cons; left.
have ts_t' : ∀ t', t' ∈ ts → t1 ≠ TInv t'.
  by move=> t' t'_ts; apply: ts_t; apply/elem_of_cons; right.
rewrite -TExp_TExpN.
have ? := IH ic ts_t'.
have := exps_count_TExpW t1 (TExpN t2 ts) t tNm t1_t.
lia.
Qed.

Lemma elem_of_TExpN2l g t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) ->
  t1 ≠ TInv t2 →
  TInv t1 ∉ exps g →
  t1 ∈ exps (TExpN g [t1; t2]).
Proof.
move=> Nm1 Nm2 t1_t2 t1_g.
rewrite (not_elem_of_TInv_exps _ Nm1) /exps -count_gt0 in t1_g.
have e : TExpN g [t1; t2] = TExp (TExp g t1) t2.
  rewrite (_ : TExp g t1 = TExpN g [t1]); last by rewrite /TExpN TMulN1.
  rewrite TExp_TExpN; exact: TExpNC2.
rewrite e /exps -count_gt0.
have := exps_count_TExpW t1 (TExp g t1) t2 Nm2 t1_t2.
lia.
Qed.

Lemma elem_of_TExpN2r g t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) ->
  t1 ≠ TInv t2 →
  TInv t2 ∉ exps g →
  t2 ∈ exps (TExpN g [t1; t2]).
Proof.
move=> Nm1 Nm2 t1_t2 t2_g.
rewrite TExpNC2.
apply: (elem_of_TExpN2l Nm2 Nm1); last exact: t2_g.
by move=> contra; apply: t1_t2; rewrite contra TInvK.
Qed.

Lemma exps_TExpN t ts :
  negb (is_exp t) -> invs_canceled ts ->
  exps (TExpN t ts) ≡ₚ ts.
Proof.
move => tNexp ic.
rewrite /exps /TExpN expo_TExp (expo_expN _ tNexp) TMulN_cat /= TMulN1.
by apply: factors_TMulN.
Qed.

Lemma TExp2_TExpN g a b : TExp (TExp g a) b = TExpN g [b; a].
Proof.
rewrite (_ : TExp g a = TExpN g [a]); last by rewrite /TExpN TMulN1.
by rewrite TExp_TExpN.
Qed.

Lemma TExpC g a b : TExp (TExp g a) b = TExp (TExp g b) a.
Proof.
rewrite (_ : TExp g a = TExpN g [a]); last by rewrite /TExpN TMulN1.
rewrite (_ : TExp g b = TExpN g [b]); last by rewrite /TExpN TMulN1.
by rewrite !TExp_TExpN TExpNC2.
Qed.
