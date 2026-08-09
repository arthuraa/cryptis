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

(* Term algebra: multiplicative group laws and DH exponentiation. *)

Lemma TInv_Nid {t} : negb (is_mul t) -> TInv t ≠ t.
Proof.
rewrite is_mul_unfold => Nm E.
move: (f_equal unfold_term E); rewrite unfold_TInv (PreTerm.inv_Nmul _ Nm).
exact: PreTerm.inv_aux_Nid.
Qed.

Lemma TMulN_perm ts1 ts2 : ts1 ≡ₚ ts2 -> TMulN ts1 = TMulN ts2.
Proof.
move=> peq; apply: count_factors_inj => x Nx.
rewrite !(count_factors_TMulN_concat _ _ Nx).
have peq' : concat (factors <$> ts1) ≡ₚ concat (factors <$> ts2) by rewrite peq.
by rewrite peq'.
Qed.

Lemma TMulN1 t : TMulN [t] = t.
Proof.
by apply: unfold_term_inj;
   rewrite unfold_TMulN /= (PreTerm.mul_wf1 _ (wf_unfold_term t)).
Qed.

Lemma TMulN_cat ts ts' : TMulN (TMulN ts :: ts') = TMulN (ts ++ ts').
Proof.
apply: count_factors_inj => x Nx.
by rewrite (count_factors_TMulN_concat x (TMulN ts :: ts') Nx)
           (count_factors_TMulN_concat x (ts ++ ts') Nx)
           fmap_cons concat_cons fmap_app concat_app
           (SMS.count_app TInv x (factors (TMulN ts)))
           (count_factors_TMulN_concat x ts Nx)
           (SMS.count_app TInv x (concat (factors <$> ts))).
Qed.

Lemma TExpN_perm t ts1 ts2 : ts1 ≡ₚ ts2 -> TExpN t ts1 = TExpN t ts2.
Proof. by move => peq; rewrite /TExpN (TMulN_perm _ _ peq). Qed.

Lemma TExpN_catC t ts1 ts2 : TExpN t (ts1 ++ ts2) = TExpN t (ts2 ++ ts1).
Proof. by apply: TExpN_perm; rewrite Permutation_app_comm. Qed.

Lemma base_TExp b e : base (TExp b e) = base b.
Proof.
apply: unfold_term_inj; rewrite !unfold_base unfold_TExp.
by rewrite (PreTerm.base_exp _ _ (wf_unfold_term b)).
Qed.

Lemma base_TExpN t ts : base (TExpN t ts) = base t.
Proof. by rewrite /TExpN base_TExp. Qed.

Lemma factorsK t : TMulN (factors t) = t.
Proof.
apply: count_factors_inj => x Nx.
rewrite (count_factors_TMulN_concat x (factors t) Nx).
have E : concat (factors <$> factors t) = factors t.
  have Hall := atom_factors t.
  elim: (factors t) Hall => [|u us IH] Hall //=.
  have [Nu Nus] := Forall_cons_1 _ _ _ Hall.
  by rewrite (factors_atomic u Nu) (IH Nus).
by rewrite E.
Qed.

(** ** Fundamental algebra of the term operations

    [term] is (up to exponentiation) the free abelian group on atoms.  We lift
    the fundamental equations from the [wf]-assuming pre-term identities, then
    derive the group laws ([TMul_cancel]/[TInvK]/…) here at [T = term] from the
    fundamentals alone — never from a pre-term "derived" lemma.  Notation of the
    header: [1 := TMulN []], [a * b := TMul a b := TMulN [a; b]], [a^-1 := TInv a]. *)

Lemma TInv_factors t : TInv t = TMulN (TInv <$> factors t).
Proof.
apply: unfold_term_inj.
rewrite unfold_TInv (PreTerm.inv_factors _ (wf_unfold_term t)) unfold_TMulN.
congr (PreTerm.mul _).
rewrite -unfold_factors.
have -> : unfold_term <$> (TInv <$> factors t)
        = PreTerm.inv_aux <$> (unfold_term <$> factors t).
  rewrite -!(list_fmap_compose _ _ (factors t)); apply: Forall_fmap_ext_1.
  apply/Forall_forall => x x_ts /=.
  have /list.Forall_forall Hat := atom_factors t; exact: (unfold_TInv_Nmul (Hat x x_ts)).
done.
Qed.

(* [a * a^-1 = 1] on atomic lists ([mul_invs] lifted). *)
Lemma TMulN_TInv_cancel ts : atomic ts -> TMulN (ts ++ (TInv <$> ts)) = TMulN [].
Proof.
move=> _; apply: count_factors_inj => x Nx.
rewrite factors_one (count_factors_TMulN_concat x (ts ++ (TInv <$> ts)) Nx).
rewrite fmap_app concat_app (SMS.count_app TInv x (concat (factors <$> ts))).
have Hinv : forall us,
    SMS.count TInv x (concat (factors <$> (TInv <$> us)))
  = (- SMS.count TInv x (concat (factors <$> us)))%Z.
  elim=> [|u us IH].
  - by rewrite /SMS.count /=; lia.
  - rewrite !fmap_cons !concat_cons
            (SMS.count_app TInv x (factors (TInv u)))
            (SMS.count_app TInv x (factors u))
            (count_factors_TInv x u Nx) IH; lia.
rewrite (Hinv ts).
have C0 : SMS.count TInv x (@nil term) = 0%Z by rewrite /SMS.count /=; lia.
rewrite C0; lia.
Qed.

(* [n]-ary associativity glue: [(prod A) * (prod B) = prod (A ++ B)]. *)
Lemma TMulN_app A B : TMulN [TMulN A; TMulN B] = TMulN (A ++ B).
Proof.
rewrite (TMulN_cat A [TMulN B]).
rewrite (TMulN_perm (A ++ [TMulN B]) (TMulN B :: A) (Permutation_app_comm A [TMulN B])).
rewrite (TMulN_cat B A).
exact: (TMulN_perm (B ++ A) (A ++ B) (Permutation_app_comm B A)).
Qed.

(** The binary product and the fundamental group laws.  These six equations
    ([TMulC]/[TMulA]/[TMul1]/[TMulK], with [TExpNA]/[TExpN0] above) generate the
    algebra; everything below is derived from them at [T = term]. *)

Definition TMul a b := TMulN [a; b].
Arguments TMul : simpl never.

Lemma TMulC a b : TMul a b = TMul b a.
Proof. by rewrite /TMul (TMulN_perm [a; b] [b; a]); last exact: Permutation_swap. Qed.

Lemma TMul1 a : TMul a (TMulN []) = a.
Proof.
rewrite /TMul (TMulN_perm [a; TMulN []] (TMulN [] :: [a])); last exact: Permutation_swap.
by rewrite (TMulN_cat [] [a]) TMulN1.
Qed.

Lemma TMulA a b c : TMul (TMul a b) c = TMul a (TMul b c).
Proof.
rewrite /TMul (TMulN_cat [a; b] [c]).
rewrite (TMulN_perm [a; TMulN [b; c]] (TMulN [b; c] :: [a])); last exact: Permutation_swap.
rewrite (TMulN_cat [b; c] [a]).
by apply: TMulN_perm; exact: (Permutation_app_comm [a] [b; c]).
Qed.

Lemma TMul1_l a : TMul (TMulN []) a = a.
Proof. by rewrite TMulC TMul1. Qed.

(* [a * a^-1 = 1] for arbitrary [a], via the factor decomposition. *)
Lemma TMulK a : TMul a (TInv a) = TMulN [].
Proof.
have E : TMul a (TInv a) = TMulN (factors a ++ (TInv <$> factors a)).
  by rewrite -TMulN_app -(TInv_factors a) (factorsK a) /TMul.
by rewrite E (TMulN_TInv_cancel (factors a) (atom_factors a)).
Qed.

Lemma TMulK_l a : TMul (TInv a) a = TMulN [].
Proof. by rewrite TMulC TMulK. Qed.

(* Left cancellation — the workhorse for the derived inverse laws. *)
Lemma TMul_cancel a b c : TMul a b = TMul a c -> b = c.
Proof.
move=> E.
have H : TMul (TInv a) (TMul a b) = TMul (TInv a) (TMul a c) by rewrite E.
by rewrite -!TMulA !TMulK_l !TMul1_l in H.
Qed.

(* [(a^-1)^-1 = a], derived at [T = term] from cancellation (no [PreTerm.invK]). *)
Lemma TInvK t : TInv (TInv t) = t.
Proof. apply: (@TMul_cancel (TInv t)); by rewrite TMulK TMulK_l. Qed.

Global Instance TInv_inj : Inj (=) (=) TInv.
Proof. by move=> t1 t2 /(f_equal TInv); rewrite !TInvK. Qed.

(* The term layer's canonical factor form is [SMS.to term_order TInv ts], the
   signed-multiset normal form at [T = term].  On an atomic list it conjugates
   the pre-term computation [SMS.to pt_order PreTerm.inv_aux] through
   [unfold_term], since there [unfold_term (TInv t) = PreTerm.inv_aux (unfold_term t)]. *)

(* [unfold_term] maps the term-level canonical form to the pre-term one: it is
   injective, order-preserving ([term_order] is [pt_order] pulled back), and
   conjugates [TInv] to [PreTerm.inv_aux] on atomic factors — exactly [SMS.to_fmap]. *)
Lemma unfold_to ts :
  Forall (fun t => negb (is_mul t)) ts ->
  unfold_term <$> SMS.to term_order TInv ts
  = SMS.to pt_order PreTerm.inv_aux (unfold_term <$> ts).
Proof.
move=> /list.Forall_forall atom; apply: SMS.to_fmap.
- exact: (@unfold_term_inj).
- move=> x xin; exact: (unfold_TInv_Nmul (atom x xin)).
- by move=> x y; rewrite /term_order.
Qed.

Lemma mem_cancel_invs ts : forall t, t ∈ SMS.to term_order TInv ts -> t ∈ ts.
Proof. move=> t; exact: (SMS.mem_to term_order TInv t ts). Qed.

(* [exps (TExpN t ts)] is exactly the canonical sorted-cancelled form of the
   combined exponent list — [SMS.to] already sorts, so no outer [merge_sort]. *)
Lemma exps_TExpN t ts :
  Forall (fun t => negb (is_mul t)) ts ->
  exps (TExpN t ts) = SMS.to term_order TInv (exps t ++ ts).
Proof.
move => atom.
have atomU : Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts).
  exact/map_unfold_Nmul.
have atomE : Forall (fun t => negb (is_mul t)) (exps t).
  apply/Forall_forall => t' t't; rewrite is_mul_unfold.
  have /list.Forall_forall H := PreTerm.Nmul_factors _ (PreTerm.wf_expo _ (wf_unfold_term t)).
  apply: H; rewrite -/(PreTerm.exps (unfold_term t)) -unfold_exps.
  apply: list_elem_of_fmap_2; exact: t't.
have atomEts : Forall (fun t => negb (is_mul t)) (exps t ++ ts)
  by apply/Forall_app; split.
apply: (inj (fmap unfold_term)).
rewrite unfold_exps unfold_TExpN.
rewrite (PreTerm.exps_exp _ _ (wf_unfold_term t)
          (PreTerm.wf_mul _ (wf_unfold_terms ts))).
rewrite (PreTerm.factors_mul _ (wf_unfold_terms ts))
        (PreTerm.flatten_factors_Nmul_id _ atomU).
rewrite (unfold_to _ atomEts) fmap_app unfold_exps.
exact: (PreTerm.to_cat_to _ _
             (PreTerm.wf_exps _ (wf_unfold_term t))
             (wf_unfold_terms ts)).
Qed.

Lemma is_exp_base_bool t : negb (is_exp (base t)).
Proof.
rewrite is_exp_unfold unfold_base.
exact: (PreTerm.base_Nexp _ (wf_unfold_term t)).
Qed.

Lemma is_exp_TInv t : negb (is_mul t) -> negb (is_inv t) -> negb (is_exp (TInv t)).
Proof.
move => Nm; rewrite is_inv_unfold => Ni.
by rewrite is_exp_unfold (unfold_TInv_Nmul Nm) (PreTerm.inv_invN _ Ni).
Qed.

Lemma base_expsK t : TExpN (base t) (exps t) = t.
Proof.
apply/unfold_term_inj; rewrite unfold_TExpN unfold_base unfold_exps /PreTerm.exps.
rewrite (PreTerm.mul_factors _ (PreTerm.wf_expo _ (wf_unfold_term t))).
exact: (PreTerm.exp_base_expo _ (wf_unfold_term t)).
Qed.

Lemma base_expN_bool t : negb (is_exp t) -> base t = t.
Proof.
rewrite is_exp_unfold=> tNX; apply: unfold_term_inj.
by rewrite unfold_base (PreTerm.base_expN _ tNX).
Qed.

Lemma exps_expN_bool t : negb (is_exp t) -> exps t = [].
Proof.
rewrite is_exp_unfold=> tNX; apply: (inj (fmap unfold_term)).
by rewrite unfold_exps (PreTerm.exps_expN _ tNX).
Qed.

Lemma is_nonce_TExp t1 t2 : negb (is_exp t1) -> negb (is_mul t2) -> negb (is_nonce (TExp t1 t2)).
Proof.
move => Nx1 Nm2.
rewrite is_exp_unfold in Nx1; rewrite is_mul_unfold in Nm2.
rewrite is_nonce_unfold unfold_TExp /PreTerm.exp
  (PreTerm.expo_expN _ Nx1).
have -> : PreTerm.mul [PreTerm.PTMul []; unfold_term t2] = unfold_term t2.
  rewrite PreTerm.mul_unit_l; exact: (PreTerm.mul_wf1 _ (wf_unfold_term t2)).
have Hne : unfold_term t2 ≠ PreTerm.PTMul [].
  by move=> e; move: Nm2; rewrite e.
rewrite (bool_decide_eq_false_2 _ Hne).
by case: (unfold_term t2) Hne.
Qed.

Lemma TExpNA t ts1 ts2 : TExpN (TExpN t ts1) ts2 = TExpN t (ts1 ++ ts2).
Proof.
rewrite /TExpN; apply: unfold_term_inj.
rewrite !unfold_TExp !unfold_TMulN.
rewrite (PreTerm.expA _ _ _ (wf_unfold_term t)
          (PreTerm.wf_mul _ (wf_unfold_terms ts1)) (PreTerm.wf_mul _ (wf_unfold_terms ts2))).
by rewrite (PreTerm.mul_mul2 _ _ (wf_unfold_terms ts1) (wf_unfold_terms ts2)) fmap_app.
Qed.

(* The well-formedness of a factor list at the term layer is [SMS.wf term_order
   TInv]: sorted, no factor occurring with its inverse, and (automatically, on
   atomic lists) involution-lawful.  A product also requires atomicity and
   [length <> 1]. *)
Definition wf_mul_list (ts : list term) : Prop :=
  atomic ts /\ SMS.wf term_order TInv ts /\ length ts ≠ 1.

(* Bridges relating [SMS.wf term_order TInv] and the plain permutation-stable "no
   inverse pairs" property to its image under [unfold_term] at the pre-term layer. *)

Lemma no_inv_of_wf ts : SMS.wf term_order TInv ts -> forall t, t ∈ ts -> TInv t ∉ ts.
Proof.
move=> H; apply/(SMS.invs_canceledP TInv ts).
exact: (SMS.wf_invs_canceled term_order TInv ts H).
Qed.

(* Transport "no inverse pairs" (spelled out) along [unfold_term]: [TInv] unfolds
   to [PreTerm.inv] and [unfold_term] is injective. *)
Lemma no_inv_unfold ts :
  (forall t, t ∈ ts -> TInv t ∉ ts) ->
  forall pt, pt ∈ (unfold_term <$> ts) -> PreTerm.inv pt ∉ (unfold_term <$> ts).
Proof.
move=> nc pt /list_elem_of_fmap [t [-> tin]]; rewrite -unfold_TInv => Hin.
apply: (nc t tin); move: Hin; exact: list_elem_of_fmap_inj_2.
Qed.

Lemma no_inv_aux_unfold ts :
  (forall t, t ∈ ts -> negb (is_mul t)) ->
  (forall t, t ∈ ts -> TInv t ∉ ts) ->
  forall pt, pt ∈ (unfold_term <$> ts) -> PreTerm.inv_aux pt ∉ (unfold_term <$> ts).
Proof.
move=> Nm nc pt /list_elem_of_fmap [t [-> tin]]; rewrite -unfold_TInv_Nmul.
- by rewrite list_elem_of_fmap_inj; eauto.
- by eauto.
Qed.

Lemma wf_TInvI ts :
  atomic ts -> StronglySorted term_order ts -> (forall t, t ∈ ts -> TInv t ∉ ts) ->
  SMS.wf term_order TInv ts.
Proof.
move=> /list.Forall_forall atom sorted nc; apply: (SMS.wf_intro term_order TInv ts) => //.
- move=> t _; exact: TInvK.
- move=> t tin; exact: (TInv_Nid (atom t tin)).
Qed.

Lemma wf_mul_list_unfold ts :
  wf_mul_list ts -> PreTerm.wf (PreTerm.PTMul (unfold_term <$> ts)).
Proof.
move=> [atom [wf szN1]].
apply: PreTerm.wf_MulI.
- exact: wf_unfold_terms.
- exact: (atomic_unfold _ atom).
- apply: (StronglySorted_fmap unfold_term term_order pt_order); last first.
    exact: (SMS.wf_sorted term_order TInv ts wf).
  by move=> x y; rewrite /term_order.
- exact: (no_inv_unfold ts (no_inv_of_wf ts wf)).
- by rewrite length_fmap.
Qed.

Lemma no_inv_singleton {t} : negb (is_mul t) -> forall x, x ∈ [t] -> TInv x ∉ [t].
Proof.
move=> Nm x /list_elem_of_singleton ->.
rewrite list_elem_of_singleton; exact: (TInv_Nid Nm).
Qed.

(* Spelled-out "no inverse pairs" combinators (permutation-stable, no sorting). *)
Lemma no_inv_cons {t ts} :
  negb (is_mul t) ->
  (forall x, x ∈ t :: ts -> TInv x ∉ t :: ts)
    <-> (TInv t ∉ ts /\ (forall x, x ∈ ts -> TInv x ∉ ts)).
Proof.
move=> Nm; split.
- move=> H; split.
  + by move: (H t (list_elem_of_here _ _)) => /not_elem_of_cons [_ ?].
  + move=> t' Ht'; move: (H t' (list_elem_of_further _ _ _ Ht')).
    by move=> /not_elem_of_cons [_ ?].
- move=> [Ht H] t'; rewrite elem_of_cons => -[->|Ht'].
  + rewrite not_elem_of_cons; split; [exact: (TInv_Nid Nm) | exact: Ht].
  + rewrite not_elem_of_cons; split; last exact: (H t' Ht').
    move=> E; apply: Ht.
    have Heq : t' = TInv t by rewrite -(TInvK t') E.
    by rewrite -Heq.
Qed.

Lemma no_inv2 {t1 t2} :
  negb (is_mul t1) -> negb (is_mul t2) ->
  (forall x, x ∈ [t1; t2] -> TInv x ∉ [t1; t2]) <-> t1 ≠ TInv t2.
Proof.
move=> Nm1 Nm2; rewrite (no_inv_cons Nm1); split.
- move=> [H _] E; apply: H; rewrite list_elem_of_singleton E TInvK //.
- move=> H; split.
  + rewrite list_elem_of_singleton => E; apply: H; rewrite -E TInvK //.
  + exact: (no_inv_singleton Nm2).
Qed.

Lemma no_inv_Permutation ts1 ts2 :
  ts1 ≡ₚ ts2 ->
  (forall x, x ∈ ts1 -> TInv x ∉ ts1) <-> (forall x, x ∈ ts2 -> TInv x ∉ ts2).
Proof.
move=> peq; split => H x Hx.
- rewrite -peq; apply: H; by rewrite peq.
- rewrite peq; apply: H; by rewrite -peq.
Qed.

Lemma no_inv_exps t : forall t', t' ∈ exps t -> TInv t' ∉ exps t.
Proof.
move=> t' t't Hin.
have H := PreTerm.no_inv_exps_pt _ (wf_unfold_term t).
move: H; rewrite -unfold_exps.
move=> /(_ (unfold_term t') (list_elem_of_fmap_2 unfold_term _ _ t't)) Hni.
apply: Hni; rewrite -unfold_TInv; exact: (list_elem_of_fmap_2 unfold_term _ _ Hin).
Qed.

Lemma exps_Nmul t' t : t' ∈ exps t -> negb (is_mul t').
Proof.
move => t'_t; rewrite is_mul_unfold.
have /list.Forall_forall H := PreTerm.Nmul_factors _ (PreTerm.wf_expo _ (wf_unfold_term t)).
apply: H; rewrite -/(PreTerm.exps (unfold_term t)) -unfold_exps.
apply: list_elem_of_fmap_2; exact: t'_t.
Qed.

Lemma atom_exps t : atomic (exps t).
Proof. apply/Forall_forall => t' t't; exact: exps_Nmul t't. Qed.

(* A list with no inverse pairs is only reordered by [SMS.to] (no cancellation). *)
Lemma to_perm_id ts :
  (forall x, x ∈ ts -> TInv x ∉ ts) -> SMS.to term_order TInv ts ≡ₚ ts.
Proof. exact: (SMS.to_id_perm term_order TInv ts). Qed.

(* On a list with no inverse pairs, [SMS.to] only permutes, so it is transparent
   under the permutation-invariant [union] of a mapped family. *)
Lemma union_list_map_to {X} `{Countable X} (f : term → gset X) ts :
  (forall x, x ∈ ts -> TInv x ∉ ts) ->
  ⋃ map f (SMS.to term_order TInv ts) = ⋃ map f ts.
Proof.
move=> nc; apply: union_list_permutation_proper_L; apply: Permutation_map.
exact: to_perm_id.
Qed.

Lemma cancel_invs1 {t} : negb (is_mul t) -> SMS.to term_order TInv [t] = [t].
Proof. move=> Nm; exact: (SMS.to_singleton term_order TInv t (TInv_Nid Nm) (TInvK t)). Qed.

Lemma is_exp_TExpN t ts :
  negb (is_exp t) -> atomic ts -> (forall t', t' ∈ ts -> TInv t' ∉ ts) ->
  is_exp (TExpN t ts) = negb (bool_decide (ts = [])).
Proof.
move => Nxt atom nc.
have atomU : Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts).
  exact: (atomic_unfold _ atom).
rewrite /TExpN is_exp_unfold unfold_TExp.
rewrite (PreTerm.is_exp_exp _ _ (wf_unfold_term t)).
rewrite (PreTerm.expo_expN _); last by rewrite -is_exp_unfold.
rewrite unfold_TMulN -[PreTerm.PTMul []]/(PreTerm.mul []).
rewrite (PreTerm.mul_mul2 [] (unfold_term <$> ts) ltac:(constructor) (wf_unfold_terms ts)) app_nil_l.
congr negb. apply: bool_decide_ext.
rewrite (PreTerm.mul_eq_unit _ atomU (no_inv_unfold ts nc)).
split; [move=> /fmap_nil_inv // | by move=> ->].
Qed.

Lemma TExpN0 : forall t, TExpN t [] = t.
Proof.
move => t; rewrite /TExpN; apply: unfold_term_inj.
rewrite unfold_TExp unfold_TMulN /=.
by rewrite (PreTerm.exp_unit _ (wf_unfold_term t)).
Qed.

Lemma TExpNK ts t :
  atomic ts -> atomic (TInv <$> ts) ->
  TExpN (TExpN t ts) (TInv <$> ts) = t.
Proof.
move => atom _.
rewrite TExpNA /TExpN (TMulN_TInv_cancel ts atom).
exact: (TExpN0 t).
Qed.

Lemma TExpK' t1 t2 :
  negb (is_mul (TInv t2)) -> negb (is_mul t2) ->
  TExp (TExp t1 (TInv t2)) t2 = t1.
Proof.
move => NmI2 Nm2.
have atom : atomic [TInv t2] by rewrite /atomic; apply/Forall_singleton.
have atomInv : atomic (TInv <$> [TInv t2]) by rewrite /= /atomic; apply/Forall_singleton; rewrite /= TInvK.
move: (TExpNK _ t1 atom atomInv) => H.
by rewrite /= TInvK /TExpN !TMulN1 in H.
Qed.

Lemma in_TInv_exps t1 t2 : t1 ∈ exps t2 -> TInv t1 ∉ exps t2.
Proof. exact: (no_inv_exps t2 t1). Qed.

Lemma in_TInv_expsV t1 t2 : TInv t1 ∈ exps t2 -> t1 ∉ exps t2.
Proof. by rewrite -{2}[t1]TInvK; exact: in_TInv_exps. Qed.

Lemma TExp_expsE t1 t2 : TExp t1 t2 = TExpN (base t1) (exps t1 ++ [t2]).
Proof. by rewrite -{1}(base_expsK t1) -TExpNA /TExpN TMulN1. Qed.

Lemma TExpN_injr t ts1 ts2 :
  atomic ts1 -> atomic ts2 ->
  TExpN t ts1 = TExpN t ts2 ->
  SMS.to term_order TInv ts1 = SMS.to term_order TInv ts2.
Proof.
move => atom1 atom2 /(f_equal exps).
rewrite (exps_TExpN _ _ atom1) (exps_TExpN _ _ atom2) => Hsort.
apply: (SMS.to_app_cancel_l term_order TInv (exps t) ts1 ts2).
- move=> x _; exact: TInvK.
- move=> x _; exact: TInvK.
- move=> x _; exact: TInvK.
- exact: Hsort.
Qed.

Lemma TExp_injr t t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) -> TExp t t1 = TExp t t2 -> t1 = t2.
Proof.
move => Nm1 Nm2 e.
have e' : TExpN t [t1] = TExpN t [t2] by rewrite /TExpN !TMulN1.
have a1 : atomic [t1] by rewrite /atomic; apply/Forall_singleton.
have a2 : atomic [t2] by rewrite /atomic; apply/Forall_singleton.
have Hperm := TExpN_injr _ _ _ a1 a2 e'.
have : t2 ∈ SMS.to term_order TInv [t2] by rewrite (cancel_invs1 Nm2); apply/list_elem_of_singleton.
rewrite -Hperm (cancel_invs1 Nm1) list_elem_of_singleton => ->; done.
Qed.

(** [exps (TExp t2 t3)] is the canonical (sorted, cancelled) form of [exps t2]
    extended by the atomic exponent [t3]. *)
Lemma exps_TExp t2 t3 :
  negb (is_mul t3) ->
  exps (TExp t2 t3) = SMS.to term_order TInv (exps t2 ++ [t3]).
Proof.
move=> Nm3.
have atom : Forall (fun t => negb (is_mul t)) (exps t2 ++ [t3]).
  apply/Forall_app; split; [exact: atom_exps | exact/Forall_singleton].
rewrite TExp_expsE (exps_TExpN _ _ atom).
by rewrite (exps_expN_bool _ (is_exp_base_bool t2)) app_nil_l.
Qed.

(** The signed exponent count [SMS.count TInv t (exps ts)] replaces the old
    [count_exp]: it is a genuine synonym for [SMS.count], so all the arithmetic
    comes from the generic [SMS.count_*] lemmas.  Only the structural facts
    (membership, and the effect of [TExp]) live here. *)

Lemma exps_count_gt0 (t ts : term) :
  (SMS.count TInv t (exps ts) > 0)%Z <-> t ∈ exps ts.
Proof.
rewrite /SMS.count; split.
- move=> H; apply/elem_of_count_mem.
  have := Nat2Z.is_nonneg (list_sort.count_mem (TInv t) (exps ts)); lia.
- move=> t_ts.
  have h1 : list_sort.count_mem t (exps ts) ≠ 0 by apply/elem_of_count_mem.
  have h2 : list_sort.count_mem (TInv t) (exps ts) = 0.
    apply/not_elem_of_count_mem; exact: (no_inv_exps ts t t_ts).
  move: h1 h2; lia.
Qed.

Lemma exps_count_TInv (t ts : term) :
  SMS.count TInv (TInv t) (exps ts) = (- SMS.count TInv t (exps ts))%Z.
Proof. rewrite /SMS.count TInvK; lia. Qed.

Lemma exps_count_TExp t1 t2 t3 :
  negb (is_mul t3) ->
  SMS.count TInv t1 (exps (TExp t2 t3)) =
  if decide (t1 = t3) then (SMS.count TInv t1 (exps t2) + 1)%Z
  else if decide (t1 = TInv t3) then (SMS.count TInv t1 (exps t2) - 1)%Z
  else SMS.count TInv t1 (exps t2).
Proof.
move=> Nm3.
have iK : forall x : term, x ∈ exps t2 ++ [t3] -> TInv (TInv x) = x by move=> *; exact: TInvK.
rewrite (exps_TExp _ _ Nm3).
rewrite (SMS.count_to term_order TInv t1 (exps t2 ++ [t3]) (TInvK t1) iK).
rewrite (SMS.count_app TInv t1 (exps t2) [t3]).
have KeyE : bool_decide (TInv t1 = t3) = bool_decide (t1 = TInv t3).
  apply: bool_decide_ext; split => e; by [rewrite -e TInvK | rewrite e TInvK].
have Hsing : SMS.count TInv t1 [t3]
           = (Z.b2z (bool_decide (t1 = t3)) - Z.b2z (bool_decide (t1 = TInv t3)))%Z.
  rewrite (SMS.count_cons TInv t1 t3 []) KeyE.
  have -> : SMS.count TInv t1 [] = 0%Z by rewrite /SMS.count /=; lia.
  ring.
rewrite Hsing.
case: (decide (t1 = t3)) => [e|nt3].
- rewrite (bool_decide_eq_true_2 (t1 = t3) e).
  rewrite (bool_decide_eq_false_2 (t1 = TInv t3)); last first.
    move=> e'; rewrite e in e'; exact: (TInv_Nid Nm3 (eq_sym e')).
  simpl; ring.
- rewrite (bool_decide_eq_false_2 (t1 = t3) nt3).
  case: (decide (t1 = TInv t3)) => [e|nt3V].
  + by rewrite (bool_decide_eq_true_2 (t1 = TInv t3) e) /=; ring.
  + by rewrite (bool_decide_eq_false_2 (t1 = TInv t3) nt3V) /=; ring.
Qed.

Lemma exps_count_TExp_eq t1 t2 :
  negb (is_mul t1) ->
  SMS.count TInv t1 (exps (TExp t2 t1)) = (SMS.count TInv t1 (exps t2) + 1)%Z.
Proof.
move=> Nm1; rewrite (exps_count_TExp t1 t2 t1 Nm1) (@decide_True _ (t1 = t1)) //.
Qed.

Lemma exps_count_TExpW t1 t2 t3 :
  negb (is_mul t3) ->
  t1 ≠ TInv t3 →
  (SMS.count TInv t1 (exps t2) ≤ SMS.count TInv t1 (exps (TExp t2 t3)))%Z.
Proof.
move=> Nm3 t1_t3; rewrite (exps_count_TExp _ _ _ Nm3) (@decide_False _ (t1 = TInv t3)) //.
by case: decide => ?; lia.
Qed.

Lemma StronglySorted_term_unfold l :
  StronglySorted pt_order (unfold_term <$> l) -> StronglySorted term_order l.
Proof.
elim: l => [|x l IH]; first by constructor.
rewrite fmap_cons => H; inversion H as [|a0 l0 Hss Hall]; subst.
constructor; first exact: (IH Hss).
apply/Forall_forall => y Hy; rewrite /term_order.
move: Hall => /Forall_forall Hall; apply: Hall; apply: list_elem_of_fmap_2; exact: Hy.
Qed.

Lemma exps_sorted t : StronglySorted term_order (exps t).
Proof.
apply: StronglySorted_term_unfold; rewrite unfold_exps.
exact: (PreTerm.exps_sorted _ (wf_unfold_term t)).
Qed.

Lemma mul_wf_list_eq ts :
  wf_mul_list ts ->
  PreTerm.mul (unfold_term <$> ts) = PreTerm.PTMul (unfold_term <$> ts).
Proof.
move => wf.
have Hwf : PreTerm.wf (PreTerm.PTMul (unfold_term <$> ts)).
  exact: (wf_mul_list_unfold ts wf).
have H := PreTerm.mul_factors _ Hwf.
by move: H; rewrite /PreTerm.factors.
Qed.

Lemma is_mul_TMulN ts : wf_mul_list ts -> is_mul (TMulN ts).
Proof. by move => wf; rewrite is_mul_unfold unfold_TMulN mul_wf_list_eq. Qed.

Lemma factors_TMulN ts : wf_mul_list ts -> factors (TMulN ts) = ts.
Proof.
move => wf; rewrite /factors unfold_TMulN mul_wf_list_eq //=.
rewrite -(list_fmap_compose unfold_term fold_term).
rewrite -{2}(list_fmap_id ts). apply: Forall_fmap_ext_1.
apply/Forall_forall => t' _; exact: unfold_termK.
Qed.

Lemma no_inv_factors t : forall t', t' ∈ factors t -> TInv t' ∉ factors t.
Proof.
move=> t' t't Hin.
have H := PreTerm.no_inv_factors _ (wf_unfold_term t).
move: H; rewrite -unfold_factors.
move=> /(_ (unfold_term t') (list_elem_of_fmap_2 unfold_term _ _ t't)) Hni.
apply: Hni; rewrite -unfold_TInv; exact: (list_elem_of_fmap_2 unfold_term _ _ Hin).
Qed.

Lemma wf_mul_list_factors t : is_mul t -> wf_mul_list (factors t).
Proof.
move=> xt; split; last split.
- exact: atom_factors.
- apply: wf_TInvI;
    [ exact: atom_factors
    | apply: StronglySorted_term_unfold; rewrite unfold_factors;
        exact: (PreTerm.sorted_factors _ (wf_unfold_term t))
    | exact: no_inv_factors ].
- rewrite /factors length_fmap.
  move: xt (wf_unfold_term t); rewrite is_mul_unfold /PreTerm.factors.
  case: (unfold_term t) => [o|o t'|o t1 t2|ts] //= _ wf'.
  by have /andb_True [_ /bool_decide_unpack Hlen] := wf'.
Qed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Global Instance TExpN_proper : Proper ((=) ==> (≡ₚ) ==> (=)) TExpN.
Proof. by move=> t _ <- ts1 ts2 ts12; apply: (TExpN_perm _ _ _ ts12). Qed.

Lemma TExpC2 g t1 t2 : TExpN g [t1; t2] = TExpN g [t2; t1].
Proof. by rewrite Permutation_swap. Qed.

Lemma subseteq_cancel_invs ts : SMS.to term_order TInv ts ⊆ ts.
Proof. apply/elem_of_subseteq => t; exact: mem_cancel_invs. Qed.
Global Arguments subseteq_cancel_invs ts : clear implicits.

Lemma not_elem_of_TInv_exps t1 t2 :
  negb (is_mul t1) ->
  TInv t1 ∉ exps t2 ↔ t1 ∈ exps (TExp t2 t1).
Proof.
move => Nm1.
rewrite -!exps_count_gt0 exps_count_TInv exps_count_TExp_eq //; lia.
Qed.

Lemma factors_TInv t : factors (TInv t) ≡ₚ TInv <$> factors t.
Proof.
rewrite /factors unfold_TInv (PreTerm.inv_factors (unfold_term t) (wf_unfold_term t)).
set F := PreTerm.factors (unfold_term t).
have wfF : Forall PreTerm.wf F := PreTerm.wf_factors _ (wf_unfold_term t).
have NmF : Forall (fun pt => negb (PreTerm.is_mul pt)) F :=
  PreTerm.Nmul_factors _ (wf_unfold_term t).
have cancF : forall q, q ∈ F -> PreTerm.inv q ∉ F :=
  PreTerm.no_inv_factors _ (wf_unfold_term t).
have wfMI : Forall PreTerm.wf (PreTerm.inv_aux <$> F).
  apply/Forall_fmap; apply/Forall_forall => x xF.
  apply: PreTerm.wf_inv_aux;
    [have /list.Forall_forall H := wfF; exact: (H x xF)
    |have /list.Forall_forall H := NmF; exact: (H x xF)].
have NmMI : Forall (fun pt => negb (PreTerm.is_mul pt)) (PreTerm.inv_aux <$> F).
  apply/Forall_fmap; apply/Forall_forall => x xF.
  by apply: PreTerm.is_mul_inv_aux; have /list.Forall_forall/(_ _ xF) H := wfF.
have cancMI :
  forall q, q ∈ (PreTerm.inv_aux <$> F) -> PreTerm.inv q ∉ (PreTerm.inv_aux <$> F)
  := PreTerm.no_inv_map_inv F wfF cancF.
rewrite (PreTerm.factors_mul (PreTerm.inv_aux <$> F) wfMI).
rewrite (PreTerm.flatten_factors_Nmul_id (PreTerm.inv_aux <$> F) NmMI).
rewrite (SMS.to_id_perm pt_order PreTerm.inv_aux (PreTerm.inv_aux <$> F)
           (PreTerm.no_inv_aux_of_no_inv _ NmMI cancMI)).
by rewrite (fmap_TInv_fold_term _ wfF NmF).
Qed.

Lemma factors_count_mul {t} X :
  is_mul t -> SMS.count TInv t (factors X) = 0%Z.
Proof.
move=> Mt; rewrite /SMS.count.
have /list.Forall_forall atomX := atom_factors X.
have tc : list_sort.count_mem t (factors X) = 0.
  apply/not_elem_of_count_mem => tin.
  exact: (proj1 (negb_True _) (atomX t tin) Mt).
have Tc : list_sort.count_mem (TInv t) (factors X) = 0.
  apply/not_elem_of_count_mem => tin.
  have Nm := Nmul_TInv (atomX (TInv t) tin); rewrite TInvK in Nm.
  exact: (proj1 (negb_True _) Nm Mt).
rewrite tc Tc; lia.
Qed.

Lemma TInv_fixed t : TInv t = t <-> t = TMulN [].
Proof.
split; last first.
  by move=> ->; apply/unfold_term_inj; rewrite unfold_TInv unfold_TMulN /=.
move=> E.
have Hperm := factors_TInv t; rewrite E in Hperm.
rewrite -(factorsK t); suff -> : factors t = [] by [].
case Ea: (factors t) => [//|a fs].
have a_t : a ∈ factors t by rewrite Ea; exact: list_elem_of_here.
have HTa : TInv a ∈ factors t.
  rewrite Hperm; apply: list_elem_of_fmap_2; exact: a_t.
exfalso; exact: (no_inv_factors t a a_t HTa).
Qed.
