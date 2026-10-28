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
Proof.
by rewrite /tsize; case: unfold_term => [o|o t'|o t1 t2|[] ps ns] /=; lia.
Qed.

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

Lemma sum_list_with_fold ps :
  Forall (λ p, PreTerm.wf p) ps →
  sum_list_with tsize (fold_term <$> ps) = sum_list_with PreTerm.tsize ps.
Proof.
elim: ps => [//|p ps IH] /Forall_cons [wfp /IH {}IH] /=.
by rewrite /tsize fold_termK // IH.
Qed.

Lemma tsize_factorsE t :
  tsize t =
  (if is_mul t then 1 else 0) +
  sum_list_with tsize (elements (factors t)).
Proof.
rewrite SMS.elements_car car_factors is_mul_unfold.
case Em: (PreTerm.is_mul (unfold_term t)); last first.
  rewrite PreTerm.factors_Nmul ?Em // SMS.car_singleton /= unfold_termK /=.
  lia.
have := wf_unfold_term t; rewrite /tsize.
case: (unfold_term t) Em => // -[] // ps ns _ wf_pt.
rewrite PreTerm.car_factors //.
move: wf_pt; rewrite PreTerm.wf_mulE.
move=> /andb_True [/andb_True [/forallb_True/list.Forall_forall H _] _].
have wfl p : p ∈ ps ++ ns → PreTerm.wf p by move=> /H /andb_True [].
rewrite /SMS.Internal.elements /= sum_list_with_app !sum_list_with_fold //.
- apply/list.Forall_forall => p p_ns; apply: wfl.
  by rewrite elem_of_app; right.
- apply/list.Forall_forall => p p_ps; apply: wfl.
  by rewrite elem_of_app; left.
Qed.

Lemma tsize_gfactorsE t :
  tsize t =
  (if is_gmul t then 1 else 0) +
  sum_list_with tsize (elements (gfactors t)).
Proof.
rewrite SMS.elements_car car_gfactors is_gmul_unfold.
case Em: (PreTerm.is_gmul (unfold_term t)); last first.
  rewrite PreTerm.gfactors_Ngmul ?Em // SMS.car_singleton /= unfold_termK /=.
  lia.
have := wf_unfold_term t; rewrite /tsize.
case: (unfold_term t) Em => // -[] // ps ns _ wf_pt.
rewrite PreTerm.car_gfactors //.
move: wf_pt; rewrite PreTerm.wf_gmulE.
move=> /andb_True [/andb_True [/forallb_True/list.Forall_forall H _] _].
have wfl p : p ∈ ps ++ ns → PreTerm.wf p by move=> /H /andb_True [].
rewrite /SMS.Internal.elements /= sum_list_with_app !sum_list_with_fold //.
- apply/list.Forall_forall => p p_ns; apply: wfl.
  by rewrite elem_of_app; right.
- apply/list.Forall_forall => p p_ps; apply: wfl.
  by rewrite elem_of_app; left.
Qed.

Lemma tsize_factors_le t t' : t ∈ factors t' → tsize t ≤ tsize t'.
Proof.
move=> t_t'; rewrite (tsize_factorsE t').
have := sum_list_with_in _ tsize _ t_t'; lia.
Qed.

Lemma tsize_factors_lt t' t : is_mul t → t' ∈ factors t → tsize t' < tsize t.
Proof.
move=> Mt t'_t; rewrite (tsize_factorsE t).
have := sum_list_with_in _ tsize _ t'_t.
by case: (is_mul t) Mt => //= _; lia.
Qed.

Lemma tsize_gfactors_le t t' : t ∈ gfactors t' → tsize t ≤ tsize t'.
Proof.
move=> t_t'; rewrite (tsize_gfactorsE t').
have := sum_list_with_in _ tsize _ t_t'; lia.
Qed.

Lemma tsize_gfactors_lt t' t : is_gmul t → t' ∈ gfactors t → tsize t' < tsize t.
Proof.
move=> Mt t'_t; rewrite (tsize_gfactorsE t).
have := sum_list_with_in _ tsize _ t'_t.
by case: (is_gmul t) Mt => //= _; lia.
Qed.

Lemma is_mul_TInv_atom t : negb (is_mul t) → is_mul (TInv t).
Proof.
move=> Nm; case E: (is_mul (TInv t)) => //.
have Nmi : negb (is_mul (TInv t)) by rewrite E.
have := factors_TInv t; rewrite (factors_Nmul _ Nmi) (factors_Nmul _ Nm).
move=> /(f_equal (λ s, (SMS.car s).1)).
by rewrite SMS.car_inv !SMS.car_singleton.
Qed.

Lemma tsize_TInv t : negb (is_mul t) → tsize (TInv t) = S (tsize t).
Proof.
move=> Nm; rewrite tsize_factorsE (_ : is_mul (TInv t) = true); last first.
  by case: (is_mul (TInv t)) (is_mul_TInv_atom t Nm).
rewrite factors_TInv (sum_list_with_Permutation _ _ _ (SMS.elements_inv _)).
rewrite (factors_Nmul _ Nm) SMS.elements_singleton /=; lia.
Qed.

Lemma is_gmul_TGInv_atom t : negb (is_gmul t) → is_gmul (TGInv t).
Proof.
move=> Nm; case E: (is_gmul (TGInv t)) => //.
have Nmi : negb (is_gmul (TGInv t)) by rewrite E.
have := gfactors_TGInv t; rewrite (gfactors_Ngmul _ Nmi) (gfactors_Ngmul _ Nm).
move=> /(f_equal (λ s, (SMS.car s).1)).
by rewrite SMS.car_inv !SMS.car_singleton.
Qed.

Lemma tsize_TGInv t : negb (is_gmul t) → tsize (TGInv t) = S (tsize t).
Proof.
move=> Nm; rewrite tsize_gfactorsE (_ : is_gmul (TGInv t) = true); last first.
  by case: (is_gmul (TGInv t)) (is_gmul_TGInv_atom t Nm).
rewrite gfactors_TGInv (sum_list_with_Permutation _ _ _ (SMS.elements_inv _)).
rewrite (gfactors_Ngmul _ Nm) SMS.elements_singleton /=; lia.
Qed.

(* The base must not be a group product: [TExp] distributes over those, and
   the result is not an exponential at all.  A *scalar* product in the base is
   fine — it is an atom. *)
Lemma tsize_TExp t1 t2 :
  negb (is_exp t1) → negb (is_gmul t1) → t2 ≠ TMul ∅ →
  tsize (TExp t1 t2) = S (tsize t1 + tsize t2).
Proof.
rewrite /tsize is_exp_unfold is_gmul_unfold unfold_TExp => Nx1 Nm1 N12.
rewrite (PreTerm.exp_Ngmul _ _ (wf_unfold_term _) (wf_unfold_term _) Nm1).
rewrite /PreTerm.exp_aux (PreTerm.base_expN _ Nx1) (PreTerm.expo_expN _ Nx1).
rewrite PreTerm.mul_unit_l PreTerm.mul1; last exact: wf_unfold_term.
rewrite /PreTerm.mk_exp bool_decide_eq_false_2 //.
move=> e; apply: N12; apply: (inj unfold_term).
by rewrite unfold_TMul_make e.
Qed.

(* The negative check the group/exponent split exists to make true: a *scalar*
   product in a base is an atom.  [TExp] does not distribute over it, so
   [TExp (t1 * t2) e] is a genuine exponential node whose size is the sum.  The
   same statement with [TGMul] in place of [TMul] is false --- there [TExp]
   distributes, and at the group unit it even collapses ([TExp_gunit]). *)
Lemma tsize_TExp_TMul2 t1 t2 e :
  negb (is_mul t1) -> negb (is_mul t2) -> e ≠ TMul ∅ ->
  tsize (TExp (TMul {[+ t1; t2 +]}) e)
  = S (tsize (TMul {[+ t1; t2 +]}) + tsize e).
Proof.
move=> Nm1 Nm2 eN0.
have Xm : is_mul (TMul {[+ t1; t2 +]}) := is_mul_TMul2 _ _ Nm1 Nm2.
by apply: tsize_TExp => //; [exact: is_mul_Nexp | exact: is_mul_Ngmul].
Qed.

Lemma tsize_TMul s :
  (∀ u, u ∈ s → negb (is_mul u)) →
  tsize (TMul s) =
  (if is_mul (TMul s) then 1 else 0) + sum_list_with tsize (elements s).
Proof. by move=> Hs; rewrite tsize_factorsE factors_TMul_atoms. Qed.

Definition tsizeE :=
  (tsize_TInv, tsize_TGInv, tsize_TExp, tsize_TMul, tsize_eq).

(* Adding an exponent factor that does not cancel grows the exponent. *)
Lemma elements_factors_TMul2 e t :
  negb (is_mul t) → t ∉ SMS.neg (factors e) →
  elements (factors (TMul {[+ e; t +]})) ≡ₚ
  t :: elements (factors e).
Proof.
move=> Nm t_e; rewrite factors_TMul SMS.bind_disj_union !SMS.bind_singleton.
rewrite (factors_Nmul _ Nm) SMS.elements_disj_union.
- by rewrite SMS.elements_singleton Permutation_app_comm.
- by rewrite SMS.neg_singleton; set_solver.
- by rewrite SMS.pos_singleton; set_solver.
Qed.

Lemma elements_factors_TMul2_inv e t :
  negb (is_mul t) → t ∉ SMS.pos (factors e) →
  elements (factors (TMul {[+ e; TInv t +]})) ≡ₚ
  t :: elements (factors e).
Proof.
move=> Nm t_e; rewrite factors_TMul SMS.bind_disj_union !SMS.bind_singleton.
rewrite factors_TInv (factors_Nmul _ Nm) SMS.elements_disj_union.
- by rewrite SMS.elements_inv SMS.elements_singleton Permutation_app_comm.
- by rewrite SMS.neg_inv SMS.pos_singleton; set_solver.
- by rewrite SMS.pos_inv SMS.neg_singleton; set_solver.
Qed.

Lemma elements_factors_nil e :
  elements (factors e) = [] → e = TMul ∅.
Proof.
move=> E; apply: count_inj => x _; rewrite count_TMul_empty.
apply: not_elem_of_count; rewrite -SMS.elem_of_elements E.
exact: not_elem_of_nil.
Qed.

Lemma tsize_factors_cons_lt e t u :
  elements (factors u) ≡ₚ t :: elements (factors e) →
  tsize t ≤ tsize u ∧ (e ≠ TMul ∅ → tsize e < tsize u).
Proof.
move=> E; split.
  apply: tsize_factors_le; rewrite -SMS.elem_of_elements E.
  exact: list_elem_of_here.
move=> eN1; rewrite (tsize_factorsE u) (tsize_factorsE e).
rewrite (sum_list_with_Permutation _ _ _ E) /=.
have ? := tsize_gt0 t.
case Mu: (is_mul u); first by case: (is_mul e); lia.
have Nmu : negb (is_mul u) by rewrite Mu.
have := Permutation_length E.
rewrite (factors_Nmul _ Nmu) SMS.elements_singleton /=.
move=> [] H0.
have := nil_length_inv _ (eq_sym H0).
by move=> /elements_factors_nil /eN1.
Qed.

(* [t1] must not be a group product: [TExp (TGMul ∅) t2 = TGMul ∅], so the
   strict inequality fails at the group unit. *)
Lemma tsize_lt_TExp_gen t1 e2 a :
  negb (is_gmul t1) →
  elements (exps (TExp t1 e2)) ≡ₚ a :: elements (exps t1) →
  tsize t1 < tsize (TExp t1 e2) ∧ S (tsize a) < tsize (TExp t1 e2).
Proof.
move=> Nm1 E.
have [le1 lt2] := tsize_factors_cons_lt _ _ _ E.
have xN1 : expo (TExp t1 e2) ≠ TMul ∅.
  by move=> e; move: E;
     rewrite /exps e factors_TMul_empty => /Permutation_length.
have Nx : negb (is_exp (base t1)) := base_Nexp t1.
have Nmb : negb (is_gmul (base t1)) by rewrite is_gmul_base.
rewrite -[TExp t1 e2]TExp_base_expo base_TExp //.
rewrite (tsize_TExp _ _ Nx Nmb xN1).
have ? := tsize_gt0 (base t1); split; last lia.
rewrite -{1}[t1]TExp_base_expo.
case: (decide (expo t1 = TMul ∅)) => [->|n1]; first by rewrite TExp_unit; lia.
have := lt2 n1; rewrite (tsize_TExp _ _ Nx Nmb n1); lia.
Qed.

Lemma tsize_lt_TExp t1 t2 :
  negb (is_gmul t1) → negb (is_mul t2) → t2 ∉ SMS.neg (exps t1) →
  tsize t1 < tsize (TExp t1 t2) ∧ tsize t2 < tsize (TExp t1 t2).
Proof.
move=> Nm1 Nm2 t2_t1.
have [] // := @tsize_lt_TExp_gen t1 t2 t2 Nm1; last lia.
by rewrite /exps (expo_TExp _ _ Nm1) elements_factors_TMul2.
Qed.

Lemma tsize_lt_TExp_inv t1 t2 :
  negb (is_gmul t1) → negb (is_mul t2) → t2 ∉ SMS.pos (exps t1) →
  tsize t1 < tsize (TExp t1 (TInv t2)) ∧ tsize t2 < tsize (TExp t1 (TInv t2)).
Proof.
move=> Nm1 Nm2 t2_t1.
have [] // := @tsize_lt_TExp_gen t1 (TInv t2) t2 Nm1; last lia.
by rewrite /exps (expo_TExp _ _ Nm1) elements_factors_TMul2_inv.
Qed.

(* Removing an exponent factor shrinks an exponential. *)
Lemma tsize_TExp_pos t p :
  p ∈ SMS.pos (exps t) →
  tsize p < tsize t ∧ tsize (TExp t (TInv p)) < tsize t.
Proof.
move=> H.
have p_t : p ∈ exps t := SMS.elem_of_pos _ _ H.
have Nmp : negb (is_mul p) := Nmul_factors _ _ p_t.
have xt : is_exp t := is_exp_of_exps p_t.
have Nmt := is_exp_Ngmul _ xt.
set t' := TExp t (TInv p).
have tE : t = TExp t' p by rewrite /t' TExpKV.
have Nm' : negb (is_gmul t') := Ngmul_TExp _ _ Nmt.
have p_t' : p ∉ SMS.neg (exps t').
  move=> /count_lt0; move: H => /count_gt0.
  rewrite /exps /t' (expo_TExp _ _ Nmt) count_TMul_disj_union !TMul_singleton.
  rewrite count_TInv count_diag.
  by case: is_mul Nmp => //= _; lia.
have [lt1 lt2] := tsize_lt_TExp t' p Nm' Nmp p_t'.
by rewrite -tE in lt1 lt2; split; lia.
Qed.

Lemma tsize_TExp_neg t n :
  n ∈ SMS.neg (exps t) →
  tsize n < tsize t ∧ tsize (TExp t n) < tsize t.
Proof.
move=> H.
have n_t : n ∈ exps t := SMS.elem_of_neg _ _ H.
have Nmn : negb (is_mul n) := Nmul_factors _ _ n_t.
have xt : is_exp t := is_exp_of_exps n_t.
have Nmt := is_exp_Ngmul _ xt.
set t' := TExp t n.
have tE : t = TExp t' (TInv n) by rewrite /t' TExpK.
have Nm' : negb (is_gmul t') := Ngmul_TExp _ _ Nmt.
have n_t' : n ∉ SMS.pos (exps t').
  move=> /count_gt0; move: H => /count_lt0.
  rewrite /exps /t' (expo_TExp _ _ Nmt) count_TMul_disj_union !TMul_singleton.
  rewrite count_diag.
  by case: is_mul Nmn => //= _; lia.
have [lt1 lt2] := tsize_lt_TExp_inv t' n Nm' Nmn n_t'.
by rewrite -tE in lt1 lt2; split; lia.
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

Lemma term_lt_ind (T : term -> Prop) :
  (forall t, (forall t', (tsize t' < tsize t) -> T t') -> T t) ->
  forall t, T t.
Proof. exact: term_lt_rect. Qed.

Lemma tsize_base_lt t : is_exp t → tsize (base t) < tsize t.
Proof.
rewrite is_exp_unfold => xt.
rewrite /tsize unfold_base; move: xt.
by case: (unfold_term t) => [o|o t'|[||] t1 t2|[] ps ns] //= _; lia.
Qed.

Lemma tsize_expo_lt t : is_exp t → tsize (expo t) < tsize t.
Proof.
rewrite /tsize is_exp_unfold unfold_expo.
case: unfold_term (wf_unfold_term t) => //=; try lia.
case=> //=; try lia.
Qed.

Lemma tsize_exps_lt t' t : t' ∈ exps t → tsize t' < tsize t.
Proof.
move=> t'_t; have xt := is_exp_of_exps t'_t.
have := tsize_expo_lt t xt; have := tsize_factors_le _ _ t'_t; lia.
Qed.

(** * Occurs-check: an exponent too big to be inside [X]

    If [u] is an exponent of [w] and [u] is strictly bigger than [X], then no
    group factor of [X ^ c] can be [w], so [w] survives in any group product
    [X ^ c] is multiplied into.

    This is the symbolic form of HMQV's argument: the multiplier [e = H(X, …)]
    is built from [X], hence strictly bigger than it, so [X] cannot contain
    [e] — and any group factor of [X ^ c] equal to [w] would have to. *)

Lemma gcount_TExp_eq0 X c w u :
  u ∈ exps w -> u ∉ factors c -> tsize X < tsize u ->
  gcount w (TExp X c) = 0%Z.
Proof.
move=> u_w u_c ltX; apply: not_elem_of_gcount.
rewrite gfactors_TExp.
move=> /SMS.elem_of_map [v [e_w v_X]].
have Nmv := Ngmul_gfactors X v v_X.
move: u_w; rewrite /exps e_w (expo_TExp _ _ Nmv).
case/elem_of_factors_TMul2 => [u_v|//].
have := tsize_exps_lt _ _ u_v; have := tsize_gfactors_le _ _ v_X; lia.
Qed.
