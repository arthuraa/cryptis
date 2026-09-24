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

(** [invs_canceled] *)

Lemma invs_canceled1 {t} : negb (is_mul t) → invs_canceled [t].
Proof.
move=> tNm x /list_elem_of_singleton ->; rewrite list_elem_of_singleton.
by split=> //; apply: TInv_Nid.
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

(** Multiplication, factors, counting and inverses *)

Lemma factors_TMulN0 : factors (TMulN []) = [].
Proof. by rewrite !unlock /=. Qed.

Lemma count_TMulN_app t ts1 ts2 :
  count t (TMulN (ts1 ++ ts2)) =
  (count t (TMulN ts1) + count t (TMulN ts2))%Z.
Proof.
rewrite !count_TMulN.
elim: ts1 => //= t' ts1 ->; rewrite /fmap; lia.
Qed.

Lemma TMulN1 t : TMulN [t] = t.
Proof.
by apply: unfold_term_inj; rewrite unfold_TMulN /= PreTerm.mul1.
Qed.

Lemma TMulN_unit_r t : TMulN [t; TMulN []] = t.
Proof.
apply: count_inj=> t0 ?; rewrite count_TMulN /= count_TMulN /=; lia.
Qed.

Instance perm_TMulN : Proper ((≡ₚ) ==> (=)) TMulN.
Proof.
move=> ts1 ts2 peq; apply: count_inj => t tNm.
rewrite !count_TMulN; apply: foldr_permutation_proper.
- lia.
- by rewrite peq.
Qed.

Lemma TMulN_cat ts1 ts2 : TMulN (TMulN ts1 :: ts2) = TMulN (ts1 ++ ts2).
Proof.
apply: count_inj => t tNm.
by rewrite (count_TMulN_app _ [TMulN ts1]) count_TMulN_app TMulN1.
Qed.

Lemma TMulN_inv_r t : TMulN [TInv t; t] = TMulN [].
Proof.
apply: count_inj=> t0 t0Nm; rewrite !count_TMulN /=.
rewrite count_TInv; lia.
Qed.

Lemma TMulN_eq_unit ts : TMulN ts = TMulN [] ↔ factors (TMulN ts) = [].
Proof.
split.
- move=> /(f_equal factors) => ->.
  apply: (inj (fmap unfold_term : list _ → _)).
  by rewrite unfold_factors /= unfold_TMulN.
- by move=> <-; rewrite factorsK.
Qed.

Lemma TMulN_catC ts1 ts2 : TMulN (ts1 ++ ts2) = TMulN (ts2 ++ ts1).
Proof. by rewrite Permutation_app_comm. Qed.

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
  by rewrite /tV in wf_tV; case: unfold_term wf_tV => [o|o u|o c d|[] us] //=.
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
have := count_count_mem _ _ t0_in1; rewrite count_TInv => e1.
rewrite -(list_elem_of_fmap_inj TInv) in t0_in2.
rewrite -[RHS](count_mem_fmap TInv); last exact: inj.
have ef: TInv <$> (TInv <$> factors t) = factors t.
  rewrite -list_fmap_compose -[RHS]list_fmap_id.
  apply/Forall_fmap_ext/Forall_forall=> ? _; exact: TInvK.
rewrite ef in t0_in2 *.
have := count_count_mem _ _ t0_in2; rewrite count_TInv_l => e2.
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

(* Every factor of a product of non-products is one of them: [TMulN] only
   permutes and cancels its argument, it never introduces new factors.  This is
   [SMS.elem_of_to] at the term layer. *)
Lemma elem_of_factors_TMulN t ts :
  Forall (fun u => negb (is_mul u)) ts -> t ∈ factors (TMulN ts) -> t ∈ ts.
Proof.
move=> Nm t_in.
have Nm' : Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts).
  apply/Forall_fmap/list.Forall_forall => u u_ts.
  rewrite /compose -is_mul_unfold; by move/list.Forall_forall: Nm; apply.
have : unfold_term t ∈ PreTerm.factors (unfold_term (TMulN ts)).
  by rewrite -unfold_factors; apply/list_elem_of_fmap; exists t.
rewrite unfold_TMulN /PreTerm.mul PreTerm.mul_auxK; last first.
  exact: (PreTerm.wf_normalize_factors _ (wf_unfold_terms ts)).
rewrite /PreTerm.normalize_factors (PreTerm.mbind_factors_Nmul _ Nm').
move=> /(SMS.elem_of_to _ _ _ _).
by rewrite (list_elem_of_fmap_inj unfold_term).
Qed.

(* Every factor of a two-element product comes from one of the two.  Unlike
   [elem_of_factors_TMulN] this needs no side condition: it is read straight
   off the signed counts. *)
Lemma elem_of_factors_TMulN2 t1 t2 t' :
  t' ∈ factors (TMulN [t1; t2]) → t' ∈ factors t1 ++ factors t2.
Proof.
by rewrite elem_of_app -!count_gt0 count_TMulN /fmap /=; lia.
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

Lemma TInv_TMulN ts : TInv (TMulN ts) = TMulN (TInv <$> ts).
Proof.
apply: count_inj => t _; rewrite count_TInv !count_TMulN.
elim: ts => //= t0 ts <-; rewrite count_TInv /fmap; lia.
Qed.

Lemma count_diag t : count t t = if is_mul t then 0 else 1.
Proof.
case e: is_mul; first by apply: is_mul_count; rewrite e.
rewrite /count -unfold_factors factors_Nmul ?e //=.
rewrite SMS.count_cons bool_decide_eq_true_2 //= bool_decide_eq_false_2 /=.
- rewrite /SMS.count /=; lia.
- exact: PreTerm.inv_aux_Nid.
Qed.


(** * The Diffie-Hellman group

    [TGMulN] / [TGInv] repeat the theory above at the group operations.  The two
    structures never interact: [gcount] counts group factors, [count] counts
    exponent factors, and each set of laws is proved from its own injectivity
    principle. *)

Lemma ginvs_canceled1 {t} : negb (is_gmul t) → ginvs_canceled [t].
Proof.
move=> tNm x /list_elem_of_singleton ->; rewrite list_elem_of_singleton.
by split=> //; apply: TGInv_Nid.
Qed.

Lemma ginvs_canceled2 {t1 t2} :
  negb (is_gmul t1) → negb (is_gmul t2) →
  ginvs_canceled [t1; t2] ↔ t1 ≠ TGInv t2.
Proof.
move=> t1Nm t2Nm.
rewrite !ginvs_canceled_cons !elem_of_nil !list_elem_of_singleton.
split.
- by case=> neq _ contra; apply: neq; rewrite contra TGInvK.
- move=> t1_t2; do 4?split => //; eauto.
  + by move=> contra; apply: t1_t2; rewrite -contra TGInvK.
  + exact: ginvs_canceled0.
Qed.

Global Instance ginvs_canceled_Permutation :
  Proper ((≡ₚ) ==> (↔)) ginvs_canceled.
Proof.
move=> ts1 ts2 peq; split => H x Hx.
- rewrite -peq; apply: H; by rewrite peq.
- rewrite peq; apply: H; by rewrite -peq.
Qed.

Lemma gfactors_TGMulN0 : gfactors (TGMulN []) = [].
Proof. by rewrite !unlock /=. Qed.

Lemma gcount_TGMulN_app t ts1 ts2 :
  gcount t (TGMulN (ts1 ++ ts2)) =
  (gcount t (TGMulN ts1) + gcount t (TGMulN ts2))%Z.
Proof.
rewrite !gcount_TGMulN.
elim: ts1 => //= t' ts1 ->; rewrite /fmap; lia.
Qed.

Lemma TGMulN1 t : TGMulN [t] = t.
Proof.
by apply: unfold_term_inj; rewrite unfold_TGMulN /= PreTerm.gmul1.
Qed.

Lemma TGMulN_unit_r t : TGMulN [t; TGMulN []] = t.
Proof.
apply: gcount_inj=> t0 ?; rewrite gcount_TGMulN /= gcount_TGMulN /=; lia.
Qed.

Instance perm_TGMulN : Proper ((≡ₚ) ==> (=)) TGMulN.
Proof.
move=> ts1 ts2 peq; apply: gcount_inj => t tNm.
rewrite !gcount_TGMulN; apply: foldr_permutation_proper.
- lia.
- by rewrite peq.
Qed.

Lemma TGMulN_cat ts1 ts2 : TGMulN (TGMulN ts1 :: ts2) = TGMulN (ts1 ++ ts2).
Proof.
apply: gcount_inj => t tNm.
by rewrite (gcount_TGMulN_app _ [TGMulN ts1]) gcount_TGMulN_app TGMulN1.
Qed.

Lemma TGMulN_inv_r t : TGMulN [TGInv t; t] = TGMulN [].
Proof.
apply: gcount_inj=> t0 t0Nm; rewrite !gcount_TGMulN /=.
rewrite gcount_TGInv; lia.
Qed.

Lemma TGMulN_eq_unit ts : TGMulN ts = TGMulN [] ↔ gfactors (TGMulN ts) = [].
Proof.
split.
- move=> /(f_equal gfactors) => ->.
  apply: (inj (fmap unfold_term : list _ → _)).
  by rewrite unfold_gfactors /= unfold_TGMulN.
- by move=> <-; rewrite gfactorsK.
Qed.

Lemma TGMulN_catC ts1 ts2 : TGMulN (ts1 ++ ts2) = TGMulN (ts2 ++ ts1).
Proof. by rewrite Permutation_app_comm. Qed.

Lemma TGMulN_app A B : TGMulN [TGMulN A; TGMulN B] = TGMulN (A ++ B).
Proof. by rewrite TGMulN_cat TGMulN_catC /= TGMulN_cat TGMulN_catC. Qed.

Definition TGMul a b := TGMulN [a; b].
Arguments TGMul : simpl never.

Lemma TGMulC a b : TGMul a b = TGMul b a.
Proof. by rewrite /TGMul Permutation_swap. Qed.

Lemma TGMul1 a : TGMul a (TGMulN []) = a.
Proof.
by rewrite /TGMul Permutation_swap TGMulN_cat /= TGMulN1.
Qed.

Lemma TGMulA a b c : TGMul (TGMul a b) c = TGMul a (TGMul b c).
Proof.
apply: gcount_inj => t; rewrite !gcount_TGMulN /= !gcount_TGMulN /=.
by lia.
Qed.

Lemma TGMul1_l a : TGMul (TGMulN []) a = a.
Proof. by rewrite TGMulC TGMul1. Qed.

Lemma TGMulK a : TGMul a (TGInv a) = TGMulN [].
Proof.
by apply: gcount_inj => x _; rewrite /TGMul !gcount_TGMulN /= gcount_TGInv; lia.
Qed.

Lemma TGMulK_l a : TGMul (TGInv a) a = TGMulN [].
Proof. by rewrite TGMulC TGMulK. Qed.

Lemma TGMul_cancel a b c : TGMul a b = TGMul a c -> b = c.
Proof.
move=> E.
have H : TGMul (TGInv a) (TGMul a b) = TGMul (TGInv a) (TGMul a c) by rewrite E.
by rewrite -!TGMulA !TGMulK_l !TGMul1_l in H.
Qed.

Global Instance TGInv_inj : Inj (=) (=) TGInv.
Proof. by move=> t1 t2 /(f_equal TGInv); rewrite !TGInvK. Qed.

Lemma not_elem_of_gcount t t' : t ∉ gfactors t' → (gcount t t' ≤ 0)%Z.
Proof.
move=> t_nin; rewrite /gcount; apply: SMS.not_elem_of_count.
by rewrite -unfold_gfactors (list_elem_of_fmap_inj unfold_term).
Qed.

Lemma is_gmul_TGInv t : is_gmul (TGInv t) = is_gmul t.
Proof.
have H: ∀ t, is_gmul (TGInv t) → is_gmul t.
  move=> {}t; case e: (is_gmul t) => //.
  suff -> : is_gmul (TGInv t) = false by [].
  rewrite !is_gmul_unfold unfold_TGInv in e *.
  rewrite PreTerm.ginv_Ngmul ?e //.
  case: unfold_term (wf_unfold_term t) e => //=.
  case => //= {}t /andb_True [] /andb_True [].
  by case: PreTerm.is_gmul.
apply: eq_bool_prop_intro; split; eauto.
rewrite -{1}[t]TGInvK; exact: H.
Qed.

Lemma not_elem_of_gcount_strong t t' :
  t ∉ gfactors t' →
  TGInv t ∉ gfactors t' →
  gcount t t' = 0%Z.
Proof.
move=> t_nin tV_nin; apply: SMS.not_elem_of_count_strong.
  by rewrite -unfold_gfactors list_elem_of_fmap_inj.
set tV := PreTerm.ginv_aux _ => tV_in; apply: tV_nin.
have wf_tV: PreTerm.wf tV.
  apply: PreTerm.wf_gfactors_wf tV_in.
  exact: PreTerm.wf_wf_gfactors.
have tNm : negb (PreTerm.is_gmul (unfold_term t)).
  by rewrite /tV in wf_tV; case: unfold_term wf_tV => [o|o u|o c d|[|] us] //=.
rewrite -(list_elem_of_fmap_inj unfold_term) unfold_TGInv PreTerm.ginv_Ngmul //.
by rewrite unfold_gfactors.
Qed.

Lemma ginvs_canceled_gfactors t : ginvs_canceled (gfactors t).
Proof.
apply: wf_gfactors_ginvs_canceled.
exact: PreTerm.wf_wf_gfactors.
Qed.

Lemma is_gmul_gcount t t' : is_gmul t → gcount t t' = 0%Z.
Proof.
move=> tm; apply: not_elem_of_gcount_strong.
- move=> t_in; case: (ginvs_canceled_gfactors _ _ t_in).
  by case: is_gmul in tm *.
- move=> t_in; case: (ginvs_canceled_gfactors _ _ t_in).
  by rewrite -is_gmul_TGInv in tm; case: is_gmul in tm *.
Qed.

Lemma gcount_TGInv_l t t' : gcount (TGInv t) t' = (- gcount t t')%Z.
Proof.
case: (decide (is_gmul t)) => tm.
  by rewrite ?is_gmul_gcount // is_gmul_TGInv.
rewrite /gcount unfold_TGInv PreTerm.ginv_Ngmul; last first.
  by rewrite negb_True -is_gmul_unfold.
by rewrite SMS.count_i // PreTerm.ginv_auxK.
Qed.

Lemma not_elem_of_gcount0 t t' :
  t ∉ gfactors t' ∧ TGInv t ∉ gfactors t' ↔ gcount t t' = 0%Z.
Proof.
split; first by case; exact: not_elem_of_gcount_strong.
have H: ∀ t, gcount t t' = 0%Z → t ∉ gfactors t'.
  move=> {}t cE0 t_in.
  have t_inP : unfold_term t ∈ PreTerm.gfactors (unfold_term t') ↔
               PreTerm.ginv_aux (unfold_term t)
                 ∈ PreTerm.gfactors (unfold_term t').
    exact: SMS.count_eq0_elem_of.
  case: (ginvs_canceled_gfactors _ _ t_in) => tV_in tNm.
  rewrite is_gmul_unfold in tNm.
  rewrite -PreTerm.ginv_Ngmul // -unfold_TGInv -unfold_gfactors in t_inP.
  rewrite !(list_elem_of_fmap_inj unfold_term) in t_inP.
  tauto.
move=> cE0; split; first exact: H.
by apply: H; rewrite gcount_TGInv_l cE0.
Qed.

Lemma gcount_gt0 t t' : (gcount t t' > 0)%Z ↔ t ∈ gfactors t'.
Proof.
split.
- move=> gt0; case: (decide (t ∈ gfactors t')) => // t_nin.
  have := not_elem_of_gcount _ _ t_nin; lia.
- move=> t_in.
  have tV_in: TGInv t ∉ gfactors t'.
    by case: (ginvs_canceled_gfactors _ _ t_in).
  have := not_elem_of_gcount _ _ tV_in; rewrite gcount_TGInv_l => c_ge0.
  have ?: gcount t t' ≠ 0%Z by move=> /not_elem_of_gcount0; tauto.
  lia.
Qed.

Lemma gcountE t1 t2 : gcount t1 t2 = SMS.count TGInv t1 (gfactors t2).
Proof.
have E: ∀ t1, t1 ∈ gfactors t2 →
        gcount t1 t2 = SMS.count TGInv t1 (gfactors t2).
  move=> {}t1 t1_t2.
  case: (ginvs_canceled_gfactors _ _ t1_t2) => t1V_t2 t1Nm.
  rewrite /gcount -unfold_gfactors !SMS.count_count_mem //.
    rewrite count_mem_fmap //; exact: inj.
  rewrite -PreTerm.ginv_Ngmul // -?unfold_TGInv ?list_elem_of_fmap_inj //.
  by rewrite -is_gmul_unfold.
case: (decide (t1 ∈ gfactors t2)) => t1_t2; first by rewrite E.
case: (decide (TGInv t1 ∈ gfactors t2)) => t1V_t2.
  rewrite -[t1 in LHS]TGInvK gcount_TGInv_l E // SMS.count_i ?TGInvK //; lia.
rewrite not_elem_of_gcount_strong //.
by rewrite SMS.not_elem_of_count_strong //.
Qed.

Lemma gcount_count_mem t1 t2 :
  t1 ∈ gfactors t2 → gcount t1 t2 = count_mem t1 (gfactors t2).
Proof.
move=> t1_t2; rewrite gcountE SMS.count_count_mem //.
by case: (ginvs_canceled_gfactors _ _ t1_t2).
Qed.

Lemma gfactors_TGInv t : gfactors (TGInv t) ≡ₚ TGInv <$> gfactors t.
Proof.
have e: ∀ t0, t0 ∈ gfactors (TGInv t) ↔ t0 ∈ (TGInv <$> gfactors t).
  move=> t0; rewrite -{2}[t0]TGInvK (list_elem_of_fmap_inj TGInv).
  by rewrite -!gcount_gt0 gcount_TGInv gcount_TGInv_l.
apply: Permutation_count_mem => t0.
case: (decide (t0 ∈ gfactors (TGInv t))) => t0_in1; last first.
  have t0_in2: t0 ∉ TGInv <$> gfactors t by rewrite -e.
  rewrite !not_elem_of_count_mem in t0_in1 t0_in2.
  by rewrite t0_in1 t0_in2.
have t0V_nin1: TGInv t0 ∉ gfactors (TGInv t).
  by case: (ginvs_canceled_gfactors _ _ t0_in1).
move/e: (t0_in1) => t0_in2.
move/e: (t0V_nin1) => t0V_nin2.
have := gcount_count_mem _ _ t0_in1; rewrite gcount_TGInv => e1.
rewrite -(list_elem_of_fmap_inj TGInv) in t0_in2.
rewrite -[RHS](count_mem_fmap TGInv); last exact: inj.
have ef: TGInv <$> (TGInv <$> gfactors t) = gfactors t.
  rewrite -list_fmap_compose -[RHS]list_fmap_id.
  apply/Forall_fmap_ext/Forall_forall=> ? _; exact: TGInvK.
rewrite ef in t0_in2 *.
have := gcount_count_mem _ _ t0_in2; rewrite gcount_TGInv_l => e2.
lia.
Qed.

Lemma TGInv_fixed t : TGInv t = t ↔ t = TGMulN [].
Proof.
split.
- move=> et; apply: gcount_inj => t0 _.
  rewrite gcount_TGMulN /=; suff ?: gcount t0 t = (- gcount t0 t)%Z by lia.
  by rewrite -{1}et gcount_TGInv.
- by move=> ->; rewrite TGInvE gfactors_TGMulN0.
Qed.

Lemma gfactors_TGMulN ts :
  ginvs_canceled ts →
  gfactors (TGMulN ts) ≡ₚ ts.
Proof.
move=> ic.
have wfU : Forall PreTerm.wf (unfold_term <$> ts) := wf_unfold_terms ts.
have Nm : forall x, x ∈ (unfold_term <$> ts) -> negb (PreTerm.is_gmul x).
  move=> _ /list_elem_of_fmap [t' [-> t'in]].
  by rewrite -is_gmul_unfold; case: (ic t' t'in).
have nopairs : forall x, x ∈ (unfold_term <$> ts) ->
                 PreTerm.ginv_aux x ∉ (unfold_term <$> ts).
  move=> _ /list_elem_of_fmap [t' [-> t'in]].
  have [Vnin t'Nm] := ic t' t'in.
  rewrite -PreTerm.ginv_Ngmul; last by rewrite -is_gmul_unfold.
  rewrite -unfold_TGInv => /list_elem_of_fmap [t'' [/unfold_term_inj e t''in]].
  by apply: Vnin; rewrite e.
have flat : forall l, (forall x, x ∈ l -> negb (PreTerm.is_gmul x)) ->
              mbind PreTerm.gfactors l = l.
  elim=> [//|x l IH] H /=.
  rewrite PreTerm.gfactors_Ngmul; last by apply: H; apply/elem_of_cons; left.
  by rewrite -/(mbind PreTerm.gfactors l) IH // => y yin; apply: H;
     apply/elem_of_cons; right.
rewrite /gfactors unfold_TGMulN /PreTerm.gmul PreTerm.gmul_auxK;
  last exact: PreTerm.wf_normalize_gfactors wfU.
rewrite /PreTerm.normalize_gfactors flat // (SMS.to_id_perm _ _ _ nopairs).
by rewrite fmap_unfold_termK.
Qed.

Lemma elem_of_gfactors_TGMulN t ts :
  Forall (fun u => negb (is_gmul u)) ts -> t ∈ gfactors (TGMulN ts) -> t ∈ ts.
Proof.
move=> Nm t_in.
have Nm' : Forall (fun pt => negb (PreTerm.is_gmul pt)) (unfold_term <$> ts).
  apply/Forall_fmap/list.Forall_forall => u u_ts.
  rewrite /compose -is_gmul_unfold; by move/list.Forall_forall: Nm; apply.
have : unfold_term t ∈ PreTerm.gfactors (unfold_term (TGMulN ts)).
  by rewrite -unfold_gfactors; apply/list_elem_of_fmap; exists t.
rewrite unfold_TGMulN /PreTerm.gmul PreTerm.gmul_auxK; last first.
  exact: (PreTerm.wf_normalize_gfactors _ (wf_unfold_terms ts)).
rewrite /PreTerm.normalize_gfactors (PreTerm.mbind_gfactors_Ngmul _ Nm').
move=> /(SMS.elem_of_to _ _ _ _).
by rewrite (list_elem_of_fmap_inj unfold_term).
Qed.

(* The group counterpart of [elem_of_factors_TMulN2]: every group factor of a
   two-element group product comes from one of the two, with no side condition
   -- it is read straight off the signed counts. *)
Lemma elem_of_gfactors_TGMulN2 t1 t2 t' :
  t' ∈ gfactors (TGMulN [t1; t2]) → t' ∈ gfactors t1 ++ gfactors t2.
Proof.
by rewrite elem_of_app -!gcount_gt0 gcount_TGMulN /fmap /=; lia.
Qed.

Lemma unfold_TGMulN_strong ts :
  ginvs_canceled ts →
  length ts ≠ 1 →
  ∃ ts' : list _,
    unfold_term (TGMulN ts) = PreTerm.PTGMul ts' ∧
    ts' ≡ₚ unfold_term <$> ts.
Proof.
move=> ic tsN1; rewrite unfold_TGMulN.
pose (ts' := PreTerm.normalize_gfactors (unfold_term <$> ts)).
have e: ts' ≡ₚ unfold_term <$> ts.
  have -> : ts' = PreTerm.gfactors (unfold_term (TGMulN ts)).
    rewrite /ts' unfold_TGMulN /PreTerm.gmul PreTerm.gmul_auxK //.
    exact: PreTerm.wf_normalize_gfactors (wf_unfold_terms ts).
  by rewrite -unfold_gfactors; apply: Permutation_map; apply: gfactors_TGMulN.
exists ts'; split => //.
rewrite -(length_fmap unfold_term) -e /ts' in tsN1.
rewrite /PreTerm.gmul /ts'.
by case: PreTerm.normalize_gfactors tsN1 => //= ? [].
Qed.

Lemma gtunitP t : t = TGMulN [] ↔ gfactors t = [].
Proof.
by split=> [->|<-]; rewrite ?gfactorsK // gfactors_TGMulN0.
Qed.

Lemma TGInv_TGMulN ts : TGInv (TGMulN ts) = TGMulN (TGInv <$> ts).
Proof.
apply: gcount_inj => t _; rewrite gcount_TGInv !gcount_TGMulN.
elim: ts => //= t0 ts <-; rewrite gcount_TGInv /fmap; lia.
Qed.

Lemma gcount_diag t : gcount t t = if is_gmul t then 0 else 1.
Proof.
case e: is_gmul; first by apply: is_gmul_gcount; rewrite e.
rewrite /gcount -unfold_gfactors gfactors_Ngmul ?e //=.
rewrite SMS.count_cons bool_decide_eq_true_2 //= bool_decide_eq_false_2 /=.
- rewrite /SMS.count /=; lia.
- exact: PreTerm.ginv_aux_Nid.
Qed.

Lemma TGMulN_bind (f : term -> list term) ts :
  TGMulN ((λ t, TGMulN (f t)) <$> ts) = TGMulN (ts ≫= f).
Proof.
elim: ts => [//|t ts IH].
by rewrite fmap_cons bind_cons TGMulN_cat -TGMulN_app IH TGMulN_app.
Qed.

(** Exponentiation, base, exponents

    Everything below is about the *base* of an exponential, so every side
    condition is group-side ([is_gmul] / [is_ginv]).  The exponent side stays
    scalar. *)

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

Lemma expo_expN t : negb (is_exp t) → expo t = TMulN [].
Proof.
rewrite is_exp_unfold => tNx; apply: unfold_term_inj.
rewrite unfold_expo unfold_TMulN /=.
exact: PreTerm.expo_expN.
Qed.

(* The five non-free heads are mutually exclusive. *)
Lemma is_exp_Nmul t : is_exp t -> negb (is_mul t).
Proof. rewrite is_exp_unfold is_mul_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

Lemma is_exp_Ngmul t : is_exp t -> negb (is_gmul t).
Proof. rewrite is_exp_unfold is_gmul_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

Lemma is_inv_Nmul t : is_inv t -> negb (is_mul t).
Proof. rewrite is_inv_unfold is_mul_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

Lemma is_ginv_Ngmul t : is_ginv t -> negb (is_gmul t).
Proof. rewrite is_ginv_unfold is_gmul_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

Lemma is_exp_Ninv t : is_exp t -> negb (is_inv t).
Proof. rewrite is_exp_unfold is_inv_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

Lemma is_exp_Nginv t : is_exp t -> negb (is_ginv t).
Proof. rewrite is_exp_unfold is_ginv_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

Lemma is_inv_Ngmul t : is_inv t -> negb (is_gmul t).
Proof. rewrite is_inv_unfold is_gmul_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

Lemma is_inv_Nexp t : is_inv t -> negb (is_exp t).
Proof. rewrite is_inv_unfold is_exp_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

Lemma is_inv_Nginv t : is_inv t -> negb (is_ginv t).
Proof.
rewrite is_inv_unfold is_ginv_unfold.
by case: (unfold_term t) => [?|[?| | |]?|???|[|] ?].
Qed.

Lemma is_ginv_Nmul t : is_ginv t -> negb (is_mul t).
Proof. rewrite is_ginv_unfold is_mul_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

Lemma is_ginv_Nexp t : is_ginv t -> negb (is_exp t).
Proof. rewrite is_ginv_unfold is_exp_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

Lemma is_ginv_Ninv t : is_ginv t -> negb (is_inv t).
Proof.
rewrite is_ginv_unfold is_inv_unfold.
by case: (unfold_term t) => [?|[?| | |]?|???|[|] ?].
Qed.

(* [base] does not change the [is_gmul] / [is_ginv] head; see the [PreTerm]
   versions for why [is_exp] is different, and why there is no scalar
   counterpart. *)
Lemma is_gmul_base t : is_gmul (base t) = is_gmul t.
Proof. rewrite !is_gmul_unfold unfold_base; exact: PreTerm.is_gmul_base. Qed.

Lemma is_ginv_base t : is_ginv (base t) = is_ginv t.
Proof. rewrite !is_ginv_unfold unfold_base; exact: PreTerm.is_ginv_base. Qed.

Lemma base_expN t : negb (is_exp t) → base t = t.
Proof.
rewrite is_exp_unfold => tNx; apply: unfold_term_inj.
rewrite unfold_base; exact: PreTerm.base_expN.
Qed.

Lemma base_TExp b e :
  negb (is_gmul b) -> negb (is_ginv b) -> base (TExp b e) = base b.
Proof.
rewrite is_gmul_unfold is_ginv_unfold => Nm Ni.
apply: unfold_term_inj; rewrite !unfold_base unfold_TExp.
exact: PreTerm.base_exp.
Qed.

Lemma expo_TExp b e :
  negb (is_gmul b) -> negb (is_ginv b) -> expo (TExp b e) = TMulN [expo b; e].
Proof.
rewrite is_gmul_unfold is_ginv_unfold => Nm Ni.
apply: unfold_term_inj; rewrite !unfold_expo unfold_TExp unfold_TMulN /=.
by rewrite unfold_expo; apply: PreTerm.expo_exp.
Qed.

Lemma TExp_gfactors b e : TExp b e = TGMulN ((λ t, TExp t e) <$> gfactors b).
Proof.
apply: unfold_term_inj; rewrite unfold_TExp unfold_TGMulN.
rewrite -list_fmap_compose /compose.
have -> : (λ t, unfold_term (TExp t e)) <$> gfactors b
        = (λ pt, PreTerm.exp_aux pt (unfold_term e)) <$> (unfold_term <$> gfactors b).
  rewrite -list_fmap_compose /compose.
  apply/Forall_fmap_ext_1/list.Forall_forall => t t_b.
  rewrite unfold_TExp PreTerm.exp_Ngmul //.
  have H : unfold_term t ∈ PreTerm.gfactors (unfold_term b).
    by rewrite -unfold_gfactors; apply/list_elem_of_fmap; exists t.
  apply: (PreTerm.wf_gfactors_Ngmul _ _ _ H); exact: PreTerm.wf_wf_gfactors.
by rewrite unfold_gfactors.
Qed.

Lemma TMulN_bind (f : term -> list term) ts :
  TMulN ((λ t, TMulN (f t)) <$> ts) = TMulN (ts ≫= f).
Proof.
elim: ts => [//|t ts IH].
by rewrite fmap_cons bind_cons TMulN_cat -TMulN_app IH TMulN_app.
Qed.

(* No side condition: a general list is first flattened into its group atoms,
   where [PreTerm.exp_gmul] applies, and [TExp_gfactors] puts it back
   together. *)
Lemma TExp_TGMulN ts e : TExp (TGMulN ts) e = TGMulN ((λ t, TExp t e) <$> ts).
Proof.
wlog: ts / Forall (λ t, negb (is_gmul t)) ts.
  move=> H.
  have -> : TGMulN ts = TGMulN (ts ≫= gfactors).
    rewrite -TGMulN_bind; congr TGMulN; rewrite -[LHS]list_fmap_id.
    by apply/Forall_fmap_ext/list.Forall_forall => t _; rewrite gfactorsK.
  rewrite H; first last.
    apply/Forall_bind/list.Forall_forall => t _.
    by apply/list.Forall_forall => x x_t; exact: Ngmul_gfactors x_t.
  rewrite list_bind_fmap -TGMulN_bind.
  congr TGMulN; apply/Forall_fmap_ext_1/list.Forall_forall => t _.
  by rewrite -TExp_gfactors.
move=> Nm_ts; apply: unfold_term_inj.
rewrite unfold_TExp !unfold_TGMulN -list_fmap_compose /compose.
have -> : (λ t, unfold_term (TExp t e)) <$> ts
        = (λ pt, PreTerm.exp_aux pt (unfold_term e)) <$> (unfold_term <$> ts).
  rewrite -list_fmap_compose /compose.
  apply/Forall_fmap_ext_1/list.Forall_forall => t t_ts.
  rewrite unfold_TExp PreTerm.exp_Ngmul // -is_gmul_unfold.
  by move/list.Forall_forall: Nm_ts; apply.
apply: PreTerm.exp_gmul => //.
- by apply/Forall_fmap/list.Forall_forall => t _; exact: wf_unfold_term.
- apply/Forall_fmap/list.Forall_forall => t t_ts.
  rewrite /compose -is_gmul_unfold; by move/list.Forall_forall: Nm_ts; apply.
Qed.

Lemma TExp_TGInv t e : TExp (TGInv t) e = TGInv (TExp t e).
Proof.
wlog: t / negb (is_gmul t).
  move=> H.
  have -> : TExp (TGInv t) e = TGMulN ((λ x, TExp (TGInv x) e) <$> gfactors t).
    by rewrite -{1}(gfactorsK t) TGInv_TGMulN TExp_TGMulN -list_fmap_compose.
  have -> : TGInv (TExp t e) = TGMulN ((λ x, TGInv (TExp x e)) <$> gfactors t).
    by rewrite -{1}(gfactorsK t) TExp_TGMulN TGInv_TGMulN -list_fmap_compose.
  congr TGMulN; apply/Forall_fmap_ext_1/list.Forall_forall => x x_t.
  by apply: H; exact: Ngmul_gfactors x_t.
rewrite is_gmul_unfold => Nm; apply: unfold_term_inj.
rewrite unfold_TExp !unfold_TGInv unfold_TExp.
exact: PreTerm.exp_ginv.
Qed.

Definition exps pt := factors (expo pt).

Lemma Nginv_TExp b e :
  negb (is_gmul b) -> negb (is_ginv b) -> negb (is_ginv (TExp b e)).
Proof.
rewrite is_gmul_unfold !is_ginv_unfold unfold_TExp => Nm Ni.
exact: PreTerm.Nginv_exp.
Qed.

Lemma TExp_base_expo t : TExp (base t) (expo t) = t.
Proof.
apply: unfold_term_inj; rewrite unfold_TExp unfold_base unfold_expo.
exact: PreTerm.exp_base_expo.
Qed.

Lemma TExpA b e1 e2 : TExp (TExp b e1) e2 = TExp b (TMulN [e1; e2]).
Proof.
wlog: b / negb (is_gmul b).
  rewrite [in LHS](TExp_gfactors b e1) => Hb.
  rewrite TExp_TGMulN -list_fmap_compose /compose.
  rewrite [in RHS](TExp_gfactors b (TMulN [e1; e2])).
  congr TGMulN; apply/Forall_fmap_ext_1/list.Forall_forall => t t_b.
  by apply: Hb; exact: Ngmul_gfactors t_b.
wlog: b / negb (is_ginv b).
  move=> Hb Nm; case Ei: (is_ginv b); last by apply: Hb => //; rewrite Ei.
  have Nmu : negb (is_gmul (TGInv b)) by rewrite is_gmul_TGInv.
  have Niu : negb (is_ginv (TGInv b)) by rewrite (is_ginv_TGInv _ Nm) Ei.
  have bE : b = TGInv (TGInv b) by rewrite TGInvK.
  rewrite [in LHS]bE [in RHS]bE.
  rewrite (TExp_TGInv (TGInv b) e1) (TExp_TGInv (TExp (TGInv b) e1) e2).
  rewrite (TExp_TGInv (TGInv b) (TMulN [e1; e2])).
  by rewrite (Hb _ Niu Nmu).
move=> Ni Nm.
have Nm1 := Ngmul_TExp b e1 Nm.
have Ni1 := Nginv_TExp b e1 Nm Ni.
rewrite -[LHS]TExp_base_expo -[RHS]TExp_base_expo.
rewrite !(base_TExp _ _ Nm1 Ni1) !(expo_TExp _ _ Nm1 Ni1).
rewrite !(base_TExp _ _ Nm Ni) !(expo_TExp _ _ Nm Ni) TMulN_cat /=.
rewrite [in RHS]Permutation_swap TMulN_cat /=.
by rewrite -[[e1; e2; expo b]]/([e1; e2] ++ [expo b]) Permutation_app_comm.
Qed.

Lemma TExpE b e : TExp b e = TExp (base b) (TMulN [expo b; e]).
Proof. by rewrite -{1}(TExp_base_expo b) TExpA. Qed.

Lemma TExp_unit b : TExp b (TMulN []) = b.
Proof.
by rewrite -{1}(TExp_base_expo b) TExpA TMulN_unit_r TExp_base_expo.
Qed.

Lemma TExpN_catC t ts1 ts2 : TExpN t (ts1 ++ ts2) = TExpN t (ts2 ++ ts1).
Proof. by rewrite /TExpN TMulN_catC. Qed.

Lemma base_expsK t : TExpN (base t) (exps t) = t.
Proof.
by rewrite /TExpN /exps factorsK TExp_base_expo.
Qed.

Lemma TExpNA t ts1 ts2 : TExpN (TExpN t ts1) ts2 = TExpN t (ts1 ++ ts2).
Proof. by rewrite /TExpN TExpA TMulN_app. Qed.

Lemma TExpN0 t : TExpN t [] = t.
Proof. by rewrite /TExpN TExp_unit. Qed.

Lemma TExpNK ts t : TExpN (TExpN t ts) (TInv <$> ts) = t.
Proof.
by rewrite /TExpN TExpA -TInv_TMulN -/(TMul _ _) TMulC TMulK_l TExp_unit.
Qed.

Lemma TExpK u v : TExp (TExp u v) (TInv v) = u.
Proof. by have := TExpNK [v] u; rewrite /TExpN /= !TMulN1. Qed.

Lemma TExpKV u v : TExp (TExp u (TInv v)) v = u.
Proof. by have := TExpK u (TInv v); rewrite TInvK. Qed.

(* The base must be neither a group product nor a group inverse.
   Distributivity makes [TGMulN [] ^ e = TGMulN []] for every [e], so
   exponentiation is genuinely not injective in the exponent at the group
   unit. *)
Lemma TExp_injr t t1 t2 :
  negb (is_gmul t) -> negb (is_ginv t) -> TExp t t1 = TExp t t2 -> t1 = t2.
Proof.
move=> Nm Ni e.
have: TMul (expo t) t1 = TMul (expo t) t2.
  by have /(f_equal expo) := e; rewrite !(expo_TExp _ _ Nm Ni).
move=> /(f_equal (TMul (TInv (expo t)))).
by rewrite -TMulA TMulK_l -TMulA TMulK_l !TMul1_l.
Qed.

(* Exponentiation preserves the head shape of a non-group-product base: a group
   inverse base stays a group inverse, because [(a⁻¹) ^ e = (a ^ e)⁻¹]. *)
Lemma is_ginv_TExp t e : negb (is_gmul t) -> is_ginv (TExp t e) = is_ginv t.
Proof.
move=> Nm; case Ei: (is_ginv t); last first.
  have Ni : negb (is_ginv t) by rewrite Ei.
  by move: (Nginv_TExp t e Nm Ni); case: (is_ginv (TExp t e)) => // _.
have Nmv : negb (is_gmul (TGInv t)) by rewrite is_gmul_TGInv.
have Niv : negb (is_ginv (TGInv t)) by rewrite (is_ginv_TGInv t Nm) Ei.
have E : TExp t e = TGInv (TExp (TGInv t) e) by rewrite -TExp_TGInv TGInvK.
rewrite E (is_ginv_TGInv _ (Ngmul_TExp (TGInv t) e Nmv)).
by move: (Nginv_TExp (TGInv t) e Nmv Niv);
   case: (is_ginv (TExp (TGInv t) e)) => // _.
Qed.

(* Exponentiation is injective in the base, once group products are excluded.
   The group unit is the only base it collapses, and it is a group product. *)
Lemma TExp_injl t1 t2 e :
  negb (is_gmul t1) -> negb (is_gmul t2) ->
  TExp t1 e = TExp t2 e -> t1 = t2.
Proof.
have main : forall u1 u2, negb (is_gmul u1) -> negb (is_ginv u1) ->
                          negb (is_gmul u2) -> negb (is_ginv u2) ->
                          TExp u1 e = TExp u2 e -> u1 = u2.
  move=> u1 u2 Nm1 Ni1 Nm2 Ni2 E.
  have Eb : base u1 = base u2.
    by rewrite -(base_TExp u1 e Nm1 Ni1) -(base_TExp u2 e Nm2 Ni2) E.
  have Ee : expo u1 = expo u2.
    apply: (TMul_cancel e).
    rewrite (TMulC e (expo u1)) (TMulC e (expo u2)) /TMul.
    by rewrite -(expo_TExp u1 e Nm1 Ni1) -(expo_TExp u2 e Nm2 Ni2) E.
  by rewrite -(TExp_base_expo u1) -(TExp_base_expo u2) Eb Ee.
move=> Nm1 Nm2 E.
have Einv : is_ginv t1 = is_ginv t2.
  by rewrite -(is_ginv_TExp t1 e Nm1) -(is_ginv_TExp t2 e Nm2) E.
case Ei: (is_ginv t1) Einv => Einv; last first.
  have Ni1 : negb (is_ginv t1) by rewrite Ei.
  have Ni2 : negb (is_ginv t2) by rewrite -Einv.
  exact: main.
have Nmv1 : negb (is_gmul (TGInv t1)) by rewrite is_gmul_TGInv.
have Nmv2 : negb (is_gmul (TGInv t2)) by rewrite is_gmul_TGInv.
have Niv1 : negb (is_ginv (TGInv t1)) by rewrite (is_ginv_TGInv t1 Nm1) Ei.
have Niv2 : negb (is_ginv (TGInv t2)) by rewrite (is_ginv_TGInv t2 Nm2) -Einv.
have E' : TExp (TGInv t1) e = TExp (TGInv t2) e.
  have H1 : TGInv (TExp (TGInv t1) e) = TExp t1 e by rewrite -TExp_TGInv TGInvK.
  have H2 : TGInv (TExp (TGInv t2) e) = TExp t2 e by rewrite -TExp_TGInv TGInvK.
  have H3 : TGInv (TExp (TGInv t1) e) = TGInv (TExp (TGInv t2) e)
    by rewrite H1 H2.
  by rewrite -(TGInvK (TExp (TGInv t1) e)) H3 TGInvK.
by rewrite -(TGInvK t1) -(TGInvK t2) (main _ _ Nmv1 Niv1 Nmv2 Niv2 E').
Qed.

Lemma ginvs_canceled_TExp b e :
  ginvs_canceled ((fun u => TExp u e) <$> gfactors b).
Proof.
move=> t /list_elem_of_fmap [u [-> u_b]].
have Nmu : negb (is_gmul u) := Ngmul_gfactors b u u_b.
split; last exact: Ngmul_TExp.
move=> /list_elem_of_fmap [u' [E u'_b]].
have Nmu' : negb (is_gmul u') := Ngmul_gfactors b u' u'_b.
have Nmiu : negb (is_gmul (TGInv u)) by rewrite is_gmul_TGInv.
have E' : TExp (TGInv u) e = TExp u' e by rewrite TExp_TGInv.
have [VI _] := ginvs_canceled_gfactors b u u_b.
by apply: VI; rewrite (TExp_injl (TGInv u) u' e Nmiu Nmu' E').
Qed.

(* Distributivity, read off the group factor multiset. *)
Lemma gfactors_TExp b e :
  gfactors (TExp b e) ≡ₚ (fun u => TExp u e) <$> gfactors b.
Proof.
by rewrite {1}(TExp_gfactors b e) gfactors_TGMulN //; exact: ginvs_canceled_TExp.
Qed.


(** * The split, as behavioural checks

    [TExp] distributes over the *group* product and the *group* inverse, and
    fixes the group unit.  It does **not** distribute over the scalar product:
    see [tsize_TExp_TMulN] in [tsize.v] for that half of the story.  Identifying
    the two structures would make [_ ^ x] an endomorphism of the exponent ring
    too, which forces exponentiation to degenerate (see [CLAUDE.md]). *)

(* The five non-free heads are mutually exclusive; these are the three
   exclusions the checks need. *)
Lemma is_mul_Ngmul t : is_mul t -> negb (is_gmul t).
Proof. rewrite is_mul_unfold is_gmul_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

Lemma is_mul_Nginv t : is_mul t -> negb (is_ginv t).
Proof. rewrite is_mul_unfold is_ginv_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

Lemma is_mul_Nexp t : is_mul t -> negb (is_exp t).
Proof. rewrite is_mul_unfold is_exp_unfold; by case: (unfold_term t) => [|||[|] ?]. Qed.

(* Check 1, [(a ⋅ b) ^ x = a^x ⋅ b^x], is [TExp_TGMulN] above.
   Check 2, [(a⁻¹) ^ x = (a^x)⁻¹], is [TExp_TGInv] above. *)

(* Check 3: the group unit is fixed, [1 ^ x = 1]. *)
Lemma TExp_gunit e : TExp (TGMulN []) e = TGMulN [].
Proof. by rewrite TExp_TGMulN. Qed.

(* A two-factor scalar product really is a product: nothing collapses it.
   Used to state check 4. *)
Lemma is_mul_TMulN2 t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) -> t1 ≠ TInv t2 ->
  is_mul (TMulN [t1; t2]).
Proof.
move=> Nm1 Nm2 ne.
have ic : invs_canceled [t1; t2] by apply/invs_canceled2.
have len := Permutation_length (factors_TMulN _ ic).
rewrite is_mulE; apply/Is_true_true/bool_decide_eq_true_2.
by rewrite len.
Qed.

(* Reading the exponent back needs a base that [TExp] does not distribute
   over; see [expo_TExp]. *)
Lemma count_expo_TExp t1 t2 t3 :
  negb (is_gmul t2) -> negb (is_ginv t2) ->
  count t1 (expo (TExp t2 t3)) =
  (count t1 (expo t2) + count t1 t3)%Z.
Proof. by move=> Nm Ni; rewrite (expo_TExp _ _ Nm Ni) count_TMulN /=; lia. Qed.

Lemma count_expo_TExp_eq t1 t2 :
  negb (is_mul t1) -> negb (is_gmul t2) -> negb (is_ginv t2) ->
  count t1 (expo (TExp t2 t1)) = (count t1 (expo t2) + 1)%Z.
Proof.
move=> Nm1 Nm2 Ni2; rewrite (count_expo_TExp _ _ _ Nm2 Ni2) count_diag.
by case: is_mul Nm1.
Qed.

Lemma exps_count_TExpW t1 t2 t3 :
  negb (is_mul t3) →
  negb (is_gmul t2) -> negb (is_ginv t2) ->
  t1 ≠ TInv t3 →
  (count t1 (expo t2) ≤ count t1 (expo (TExp t2 t3)))%Z.
Proof.
move=> Nm3 Nm2 Ni2 t1_t3; rewrite (count_expo_TExp _ _ _ Nm2 Ni2).
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
  negb (is_gmul t2) -> negb (is_ginv t2) ->
  TInv t1 ∉ exps t2 ↔ t1 ∈ exps (TExp t2 t1).
Proof.
move=> Nm1 Nm2 Ni2.
rewrite /exps (expo_TExp _ _ Nm2 Ni2) -!count_gt0 count_TInv_l count_TMulN /=.
by rewrite count_diag; case: is_mul Nm1 => //= _; lia.
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

(* Having an exponent makes a term an exponential, hence an atom-headed one.
   This is how the side conditions of the [exps]-counting lemmas are usually
   discharged: their hypotheses already mention [exps]. *)
Lemma is_exp_of_exps t t' : t' ∈ exps t -> is_exp t.
Proof.
move=> t'_t; apply/is_expE => e.
by move: t'_t; rewrite /exps e factors_TMulN0 elem_of_nil.
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
  negb (is_gmul t2) -> negb (is_ginv t2) ->
  invs_canceled ts →
  (∀ t', t' ∈ ts → t1 ≠ TInv t') →
  (count t1 (expo t2) ≤ count t1 (expo (TExpN t2 ts)))%Z.
Proof.
move=> Nm2 Ni2.
elim: ts => [|t ts IH]; first by move => _ _; rewrite TExpN0; lia.
case/invs_canceled_cons=> tV_ts [] tNm ic ts_t.
have t1_t : t1 ≠ TInv t by apply: ts_t; apply/elem_of_cons; left.
have ts_t' : ∀ t', t' ∈ ts → t1 ≠ TInv t'.
  by move=> t' t'_ts; apply: ts_t; apply/elem_of_cons; right.
rewrite -TExp_TExpN.
have ? := IH ic ts_t'.
have := exps_count_TExpW t1 (TExpN t2 ts) t tNm
          (Ngmul_TExp _ _ Nm2) (Nginv_TExp _ _ Nm2 Ni2) t1_t.
lia.
Qed.

Lemma elem_of_TExpN2l g t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) ->
  negb (is_gmul g) -> negb (is_ginv g) ->
  t1 ≠ TInv t2 →
  TInv t1 ∉ exps g →
  t1 ∈ exps (TExpN g [t1; t2]).
Proof.
move=> Nm1 Nm2 Nmg Nig t1_t2 t1_g.
rewrite (not_elem_of_TInv_exps Nm1 Nmg Nig) /exps -count_gt0 in t1_g.
have e : TExpN g [t1; t2] = TExp (TExp g t1) t2.
  rewrite (_ : TExp g t1 = TExpN g [t1]); last by rewrite /TExpN TMulN1.
  rewrite TExp_TExpN; exact: TExpNC2.
rewrite e /exps -count_gt0.
have := exps_count_TExpW t1 (TExp g t1) t2 Nm2
          (Ngmul_TExp _ _ Nmg) (Nginv_TExp _ _ Nmg Nig) t1_t2.
lia.
Qed.

Lemma elem_of_TExpN2r g t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) ->
  negb (is_gmul g) -> negb (is_ginv g) ->
  t1 ≠ TInv t2 →
  TInv t2 ∉ exps g →
  t2 ∈ exps (TExpN g [t1; t2]).
Proof.
move=> Nm1 Nm2 Nmg Nig t1_t2 t2_g.
rewrite TExpNC2.
apply: (elem_of_TExpN2l Nm2 Nm1 Nmg Nig); last exact: t2_g.
by move=> contra; apply: t1_t2; rewrite contra TInvK.
Qed.

Lemma exps_TExpN t ts :
  negb (is_exp t) -> negb (is_gmul t) -> negb (is_ginv t) ->
  invs_canceled ts ->
  exps (TExpN t ts) ≡ₚ ts.
Proof.
move => tNexp tNm tNi ic.
rewrite /exps /TExpN (expo_TExp _ _ tNm tNi) (expo_expN _ tNexp).
rewrite TMulN_cat /= TMulN1.
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

(** ** Exponent-free terms

    A term that is neither a scalar product nor a scalar inverse -- a nonce or a
    hash, say -- is the single factor of itself, so its signed count against
    another such term is decided by plain disequality.  That is what turns a
    handful of pairwise disequalities into the [factors] memberships a protocol
    needs when it must locate one exponent inside a product of others. *)

Lemma TInv_Nenf_ne t1 t2 :
  negb (is_enon_free t1) -> negb (is_enon_free t2) -> TInv t1 ≠ t2.
Proof.
move=> f1 f2 e.
have e1 : t1 = TInv t2 by rewrite -e TInvK.
move: (Nenf_Ninv _ f1); rewrite e1 (is_inv_TInv _ (Nenf_Nmul _ f2)).
by case: is_inv (Nenf_Ninv _ f2).
Qed.

Lemma count_Nenf_ne t1 t2 :
  negb (is_enon_free t1) -> negb (is_enon_free t2) -> t1 ≠ t2 ->
  count t1 t2 = 0%Z.
Proof.
move=> f1 f2 ne; apply: not_elem_of_count_strong;
  rewrite (factors_Nmul _ (Nenf_Nmul _ f2)) list_elem_of_singleton //.
exact: TInv_Nenf_ne.
Qed.

Lemma count_TMulN_Nenf t ts :
  negb (is_enon_free t) ->
  Forall (fun u => negb (is_enon_free u) /\ t ≠ u) ts ->
  count t (TMulN ts) = 0%Z.
Proof.
move=> ft; elim: ts => [|u ts IH] /=; first by rewrite count_TMulN.
case/Forall_cons => [[fu ne] /IH IHts].
rewrite count_TMulN /= -count_TMulN IHts (count_Nenf_ne ft fu ne); lia.
Qed.

Lemma elem_of_factors_cons t ts :
  negb (is_enon_free t) ->
  Forall (fun u => negb (is_enon_free u) /\ t ≠ u) ts ->
  t ∈ factors (TMulN (t :: ts)).
Proof.
move=> ft H; apply/count_gt0.
rewrite count_TMulN /= -count_TMulN (count_TMulN_Nenf ft H) count_diag.
by case: is_mul (Nenf_Nmul _ ft) => //=; lia.
Qed.

Lemma not_elem_of_factors_TMulN_Nenf t ts :
  negb (is_enon_free t) ->
  Forall (fun u => negb (is_enon_free u) /\ t ≠ u) ts ->
  t ∉ factors (TMulN ts).
Proof.
move=> ft H /count_gt0; rewrite (count_TMulN_Nenf ft H); lia.
Qed.

Lemma not_elem_of_factors_Nenf t1 t2 :
  negb (is_enon_free t1) -> negb (is_enon_free t2) -> t1 ≠ t2 ->
  t1 ∉ factors t2.
Proof.
move=> f1 f2 ne.
by rewrite (factors_Nmul _ (Nenf_Nmul _ f2)) list_elem_of_singleton.
Qed.

(* Weaker than [elem_of_factors_cons]: the tail may repeat [t], which still only
   pushes the count up.  Needed where two of the exponents are not known to
   differ. *)
Lemma count_Nenf_ge0 t1 t2 :
  negb (is_enon_free t1) -> negb (is_enon_free t2) -> TInv t1 ≠ t2 ->
  (0 <= count t1 t2)%Z.
Proof.
move=> f1 f2 neV.
case: (decide (t1 = t2)) => [->|ne].
- by rewrite count_diag; case: is_mul (Nenf_Nmul _ f2).
- by rewrite (count_Nenf_ne f1 f2 ne).
Qed.

Lemma count_TMulN_Nenf_ge0 t ts :
  negb (is_enon_free t) ->
  Forall (fun u => negb (is_enon_free u) /\ TInv t ≠ u) ts ->
  (0 <= count t (TMulN ts))%Z.
Proof.
move=> ft; elim: ts => [|u ts IH] /=; first by rewrite count_TMulN.
case/Forall_cons => [[fu neV] /IH IHts].
rewrite count_TMulN /= -count_TMulN.
have := count_Nenf_ge0 ft fu neV; lia.
Qed.

Lemma elem_of_factors_cons_weak t ts :
  negb (is_enon_free t) ->
  Forall (fun u => negb (is_enon_free u) /\ TInv t ≠ u) ts ->
  t ∈ factors (TMulN (t :: ts)).
Proof.
move=> ft H; apply/count_gt0.
rewrite count_TMulN /= -count_TMulN count_diag.
have := count_TMulN_Nenf_ge0 ft H.
by case: is_mul (Nenf_Nmul _ ft) => //=; lia.
Qed.
