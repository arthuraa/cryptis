From cryptis Require Import lib.
From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import sorting gmap.
From cryptis.lib Require Import list_sort mathcomp_compat.
From iris.heap_lang Require locations.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core Require Export pre_term.

(* [PreTerm.wf_term] is the [wf] boolean fixpoint; keep [simpl] from unfolding it
   into the recursive procedure, so the [wf_guard]-based reasoning about
   [fold_term_predef] below stays syntactic. *)
Arguments PreTerm.wf_term _ : simpl never.

(* The three "non-free" operations — inverse, exponentiation and product — are
   represented indirectly, by a well-formed pre-term whose head is one of
   [O1Inv] / [PTExp] / [PTMul].  [is_non_free] recognises exactly those heads. *)
Definition is_non_free (pt : PreTerm.pre_term) :=
  PreTerm.is_inv pt || PreTerm.is_exp pt || PreTerm.is_mul pt.

Unset Elimination Schemes.
Inductive term :=
| TInt of Z
| TPair of term & term
| TNonce of nonce
| TKey of key_type & term
| TSeal of term & term
| THash of term
| TNonFree pt of PreTerm.wf_term pt & is_non_free pt.

Record aenc_key := AEncKey {
  seed_of_aenc_key : term;
}.

Record sign_key := SignKey {
  seed_of_sign_key : term;
}.

Record senc_key := SEncKey {
  seed_of_senc_key : term;
}.
Set Elimination Schemes.

Coercion TNonce : nonce >-> term.

Definition term_of_aenc_key_def sk := TKey ADec (seed_of_aenc_key sk).
Fact term_of_aenc_key_key : unit. exact: tt. Qed.
Definition term_of_aenc_key :=
  locked_with term_of_aenc_key_key term_of_aenc_key_def.
Lemma term_of_aenc_keyE : term_of_aenc_key = term_of_aenc_key_def.
Proof. exact: locked_withE. Qed.
Coercion term_of_aenc_key : aenc_key >-> term.

Definition term_of_sign_key_def sk := TKey Sign (seed_of_sign_key sk).
Fact term_of_sign_key_key : unit. exact: tt. Qed.
Definition term_of_sign_key :=
  locked_with term_of_sign_key_key term_of_sign_key_def.
Lemma term_of_sign_keyE : term_of_sign_key = term_of_sign_key_def.
Proof. exact: locked_withE. Qed.
Coercion term_of_sign_key : sign_key >-> term.

Definition term_of_senc_key_def sk := TKey SEnc (seed_of_senc_key sk).
Fact term_of_senc_key_key : unit. exact: tt. Qed.
Definition term_of_senc_key :=
  locked_with term_of_senc_key_key term_of_senc_key_def.
Lemma term_of_senc_keyE : term_of_senc_key = term_of_senc_key_def.
Proof. exact: locked_withE. Qed.
Coercion term_of_senc_key : senc_key >-> term.

Definition keysE :=
  (term_of_aenc_keyE, term_of_sign_keyE, term_of_senc_keyE).

Lemma term_of_aenc_key_inj : Inj (=) (=) term_of_aenc_key.
Proof. rewrite keysE. by case=> [?] [?] [->]. Qed.

Lemma term_of_sign_key_inj : Inj (=) (=) term_of_sign_key.
Proof. rewrite keysE. by case=> [?] [?] [->]. Qed.

Lemma term_of_senc_key_inj : Inj (=) (=) term_of_senc_key.
Proof. rewrite keysE. by case=> [?] [?] [->]. Qed.

(* We use a different name for the default induction scheme, as it does not
   allow us to recurse under exponentials.  Later, we'll prove term_ind, which
   does allow this. *)
Scheme term_ind' := Induction for term Sort Prop.

Fixpoint unfold_term t :=
  match t with
  | TInt n => PreTerm.PT0 (O0Int n)
  | TPair t1 t2 => PreTerm.PT2 O2Pair (unfold_term t1) (unfold_term t2)
  | TNonce l => PreTerm.PT0 (O0Nonce l)
  | TKey kt t => PreTerm.PT1 (O1Key kt) (unfold_term t)
  | TSeal k t => PreTerm.PT2 O2Seal (unfold_term k) (unfold_term t)
  | THash t => PreTerm.PT1 O1Hash (unfold_term t)
  | TNonFree pt _ _ => pt
  end.

(* A [sumbool] guard on a [bool].  A [sumbool] carries no index, so reducing a
   match on it stays well-typed even when [PreTerm.wf_term] is left opaque. *)
Definition wf_guard (b : bool) : {Is_true b} + {¬ Is_true b} :=
  match b with true => left I | false => right (fun H => H) end.

Fixpoint fold_term_predef pt :=
  match pt with
  | PreTerm.PT0 (O0Int n) => TInt n
  | PreTerm.PT2 O2Pair pt1 pt2 => TPair (fold_term_predef pt1) (fold_term_predef pt2)
  | PreTerm.PT0 (O0Nonce l) => TNonce l
  | PreTerm.PT1 (O1Key kt) pt => TKey kt (fold_term_predef pt)
  | PreTerm.PT2 O2Seal k pt => TSeal (fold_term_predef k) (fold_term_predef pt)
  | PreTerm.PT1 O1Hash pt => THash (fold_term_predef pt)
  | PreTerm.PT1 O1Inv pt' =>
    if wf_guard (PreTerm.wf_term (PreTerm.PT1 O1Inv pt')) is left pf then
      TNonFree (PreTerm.PT1 O1Inv pt') pf I
    else TInt 0 (*should never*)
  | PreTerm.PTExp b e =>
    if wf_guard (PreTerm.wf_term (PreTerm.PTExp b e)) is left pf then
      TNonFree (PreTerm.PTExp b e) pf I
    else TInt 0 (*should never*)
  | PreTerm.PTMul ts =>
    if wf_guard (PreTerm.wf_term (PreTerm.PTMul ts)) is left pf then
      TNonFree (PreTerm.PTMul ts) pf I
    else TInt 0 (*should never*)
  end.

lock Definition fold_term pt := fold_term_predef (PreTerm.normalize pt).

(* [unfold_term] always produces well-formed pre-terms. *)
Lemma wf_unfold_term t : PreTerm.wf (unfold_term t).
Proof.
elim/term_ind': t.
- by move=> z.
- by move=> t1 IH1 t2 IH2 /=; apply/andb_True; split.
- by move=> a.
- by move=> kt t IH.
- by move=> t1 IH1 t2 IH2 /=; apply/andb_True; split.
- by move=> t IH.
- by move=> pt w nf; exact: (proj1 (PreTerm.wf_termE _) w).
Qed.

Lemma wf_unfold_term_b t : PreTerm.wf_term (unfold_term t).
Proof. exact: (proj2 (PreTerm.wf_termE _) (wf_unfold_term t)). Qed.

Lemma wf_unfold_terms ts : Forall (fun pt => PreTerm.wf pt) (unfold_term <$> ts).
Proof.
elim: ts => /= [|t ts IH]; first by constructor.
by constructor; [exact: wf_unfold_term|exact: IH].
Qed.

(* Bridge a [Forall] to a per-element fact indexed by stdpp membership [∈]. *)
Lemma Forall_mem {A} {P : A -> Prop} {l : list A} {x : A} :
  Forall P l -> x ∈ l -> P x.
Proof. move=> /Forall_forall H; exact: H. Qed.

Lemma TNonFree_irr pt (w1 w2 : PreTerm.wf_term pt) (n1 n2 : is_non_free pt) :
  TNonFree pt w1 n1 = TNonFree pt w2 n2.
Proof. by rewrite (proof_irrel w1 w2) (proof_irrel n1 n2). Qed.

Lemma fold_predef_NonFree {pt} (wf : PreTerm.wf_term pt) (nf : is_non_free pt) :
  fold_term_predef pt = TNonFree pt wf nf.
Proof.
case: pt wf nf => [o|[kt||] pt'|[||] b e|ts] wf nf.
1,2,3,5,6: by move: nf; rewrite /is_non_free /=.
- rewrite /=; case: (wf_guard (PreTerm.wf_term (PreTerm.PTInv pt'))) => [pf'|npf];
    last by case: (npf wf).
  exact: TNonFree_irr.
- rewrite /=; case: (wf_guard (PreTerm.wf_term (PreTerm.PTExp b e))) => [pf'|npf];
    last by case: (npf wf).
  exact: TNonFree_irr.
- rewrite /=; case: (wf_guard (PreTerm.wf_term (PreTerm.PTMul ts))) => [pf'|npf];
    last by case: (npf wf).
  exact: TNonFree_irr.
Qed.

Lemma unfold_termK t : fold_term (unfold_term t) = t.
Proof.
rewrite [fold_term]unlock (PreTerm.normalize_wf _ (wf_unfold_term t)).
elim /term_ind': t.
- by move=> z /=.
- by move=> t1 IH1 t2 IH2 /=; rewrite IH1 IH2.
- by move=> l /=.
- by move=> kt t IH /=; rewrite IH.
- by move=> k IH1 t IH2 /=; rewrite IH1 IH2.
- by move=> t IH /=; rewrite IH.
- by move=> pt wf nf; apply: fold_predef_NonFree.
Qed.

Lemma unfold_fold pt : unfold_term (fold_term pt) = PreTerm.normalize pt.
Proof.
rewrite [fold_term]unlock.
move: (PreTerm.wf_normalize pt). elim: (PreTerm.normalize pt) => //.
- by case.
- move => [?||] t IH wf_t; try by rewrite /= IH.
  by rewrite (fold_predef_NonFree (proj2 (PreTerm.wf_termE _) wf_t) I).
- move => [] t1 IH1 t2 IH2 wf.
  + by move: wf; rewrite /= => /andb_True [w1 w2]; rewrite (IH1 w1) (IH2 w2).
  + by move: wf; rewrite /= => /andb_True [w1 w2]; rewrite (IH1 w1) (IH2 w2).
  + by rewrite (fold_predef_NonFree (proj2 (PreTerm.wf_termE _) wf) I).
- by move => ts IHts wf; rewrite (fold_predef_NonFree (proj2 (PreTerm.wf_termE _) wf) I).
Qed.

Lemma fold_termK pt : PreTerm.wf pt -> unfold_term (fold_term pt) = pt.
Proof.
by move=> wf; rewrite unfold_fold (PreTerm.normalize_wf _ wf).
Qed.

(* [unfold_term <$> (fold_term <$> _)] is the identity on lists of well-formed
   pre-terms.  Used to bridge the [fold]/[unfold] round-trip through lists. *)
Lemma unfold_fold_map S :
  Forall (fun pt => PreTerm.wf pt) S ->
  unfold_term <$> (fold_term <$> S) = S.
Proof.
move=> wfS. rewrite -(list_fmap_compose fold_term unfold_term).
rewrite -{2}(list_fmap_id S). apply: Forall_fmap_ext_1.
apply/Forall_forall => pt Hpt; exact: (fold_termK pt (Forall_mem wfS Hpt)).
Qed.

Lemma fold_normalize pt : fold_term (PreTerm.normalize pt) = fold_term pt.
Proof. by rewrite -unfold_fold unfold_termK. Qed.

Global Instance unfold_term_inj : Inj (=) (=) unfold_term.
Proof. by move=> t1 t2 /(f_equal fold_term); rewrite !unfold_termK. Qed.

Implicit Types (t k : term) (ts : list term).

Section TInv.

lock Definition TInv t := fold_term (PreTerm.inv (unfold_term t)).

End TInv.

Section TExp.

lock Definition TExp b e :=
  fold_term (PreTerm.exp (unfold_term b) (unfold_term e)).

lock Definition TMulN ts :=
  fold_term (PreTerm.mul (unfold_term <$> ts)).

End TExp.

Definition TExpN t ts := TExp t (TMulN ts).

(** stdpp structure on [term] (replacing the mathcomp eqType/countType/orderType).
    Equality and countability factor through [unfold_term]; the total order is the
    pre-term order [pt_order] transported along [unfold_term]. *)

Global Instance term_eq_dec : EqDecision term :=
  inj_eq_dec unfold_term.

Global Instance term_countable : Countable term :=
  inj_countable' unfold_term fold_term unfold_termK.

Definition term_order : relation term :=
  fun t1 t2 => pt_order (unfold_term t1) (unfold_term t2).

Global Instance term_order_dec : RelDecision term_order.
Proof. rewrite /term_order => t1 t2; exact: pt_order_dec. Defined.
Global Instance term_order_refl : Reflexive term_order.
Proof. move=> t; apply: pt_order_refl. Qed.
Global Instance term_order_trans : Transitive term_order.
Proof. move=> x y z H1 H2; rewrite /term_order; eapply pt_order_trans; eassumption. Qed.
Global Instance term_order_total : Total term_order.
Proof. move=> x y; apply: pt_order_total. Qed.
Global Instance term_order_antisymm : AntiSymm eq term_order.
Proof.
move=> x y H1 H2; apply: unfold_term_inj.
by apply: (@anti_symm _ eq pt_order _).
Qed.

Global Instance aenc_key_eq_dec : EqDecision aenc_key.
Proof. solve_decision. Defined.
Global Instance aenc_key_countable : Countable aenc_key.
Proof. apply: (inj_countable' seed_of_aenc_key AEncKey); by case. Qed.

Global Instance sign_key_eq_dec : EqDecision sign_key.
Proof. solve_decision. Defined.
Global Instance sign_key_countable : Countable sign_key.
Proof. apply: (inj_countable' seed_of_sign_key SignKey); by case. Qed.

Global Instance senc_key_eq_dec : EqDecision senc_key.
Proof. solve_decision. Defined.
Global Instance senc_key_countable : Countable senc_key.
Proof. apply: (inj_countable' seed_of_senc_key SEncKey); by case. Qed.

Lemma normalize_unfold1 t :
  PreTerm.normalize (unfold_term t) = unfold_term t.
Proof. by rewrite (PreTerm.normalize_wf _ (wf_unfold_term t)). Qed.

Lemma normalize_unfoldn ts :
  PreTerm.normalize <$> (unfold_term <$> ts) = unfold_term <$> ts.
Proof.
rewrite -{2}(list_fmap_id (unfold_term <$> ts)).
apply: Forall_fmap_ext_1. apply/Forall_forall => pt.
move=> /list_elem_of_fmap [t [-> _]]; exact: normalize_unfold1.
Qed.

Lemma unfold_TInv t : unfold_term (TInv t) = PreTerm.inv (unfold_term t).
Proof.
by rewrite unlock unfold_fold
  (PreTerm.normalize_wf _ (PreTerm.wf_inv _ (wf_unfold_term t))).
Qed.

Lemma unfold_TExp b e :
  unfold_term (TExp b e) = PreTerm.exp (unfold_term b) (unfold_term e).
Proof.
by rewrite unlock unfold_fold
  (PreTerm.normalize_wf _ (PreTerm.wf_exp _ _ (wf_unfold_term b) (wf_unfold_term e))).
Qed.

Lemma unfold_TMulN ts :
  unfold_term (TMulN ts) = PreTerm.mul (unfold_term <$> ts).
Proof.
by rewrite unlock unfold_fold
  (PreTerm.normalize_wf _ (PreTerm.wf_mul _ (wf_unfold_terms ts))).
Qed.

Lemma unfold_TExpN t ts :
  unfold_term (TExpN t ts) =
  PreTerm.exp (unfold_term t) (PreTerm.mul (unfold_term <$> ts)).
Proof. by rewrite /TExpN unfold_TExp unfold_TMulN. Qed.

Lemma fold_termE pt :
  fold_term pt =
  match pt with
  | PreTerm.PT0 (O0Int n) => TInt n
  | PreTerm.PT2 O2Pair pt1 pt2 => TPair (fold_term pt1) (fold_term pt2)
  | PreTerm.PT0 (O0Nonce l) => TNonce l
  | PreTerm.PT1 (O1Key kt) pt => TKey kt (fold_term pt)
  | PreTerm.PT2 O2Seal k pt => TSeal (fold_term k) (fold_term pt)
  | PreTerm.PT1 O1Hash pt => THash (fold_term pt)
  | PreTerm.PT1 O1Inv pt => TInv (fold_term pt)
  | PreTerm.PTExp b e => TExp (fold_term b) (fold_term e)
  | PreTerm.PTMul ts => TMulN (fold_term <$> ts)
  end.
Proof.
apply /unfold_term_inj.
case: pt => /=; try by case =>> //=; rewrite ?unfold_TInv !unfold_fold.
- by move=> [] >; rewrite /= ?unfold_TExp !unfold_fold.
- move=> ts; rewrite unfold_fold unfold_TMulN.
  have -> : unfold_term <$> (fold_term <$> ts) = PreTerm.normalize <$> ts.
    rewrite -(list_fmap_compose fold_term unfold_term).
    apply: Forall_fmap_ext_1; apply/Forall_forall => pt _; exact: (unfold_fold pt).
  done.
Qed.

Definition base t := fold_term (PreTerm.base (unfold_term t)).
Definition exps t := fold_term <$> PreTerm.exps (unfold_term t).
Definition tfactors t := fold_term <$> PreTerm.factors (unfold_term t).

Definition is_mul t :=
  if t is TNonFree pt _ _ then PreTerm.is_mul pt else false.

Lemma is_mul_unfold t : is_mul t = PreTerm.is_mul (unfold_term t).
Proof. by case: t. Qed.

(** Bridge term-level atomicity ([~~ is_mul]) to pre-term atomicity through
    [unfold_term]. *)
Lemma map_unfold_Nmul ts :
  Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts) <->
  Forall (fun t => negb (is_mul t)) ts.
Proof.
rewrite Forall_fmap; apply: Forall_iff => t; by rewrite is_mul_unfold.
Qed.

Lemma unfold_base t : unfold_term (base t) = PreTerm.base (unfold_term t).
Proof.
by rewrite /base unfold_fold
  (PreTerm.normalize_wf _ (PreTerm.wf_base _ (wf_unfold_term t))).
Qed.

Lemma unfold_exps t :
  unfold_term <$> exps t = PreTerm.exps (unfold_term t).
Proof. rewrite /exps unfold_fold_map //; exact: (PreTerm.wf_exps _ (wf_unfold_term t)). Qed.

Lemma unfold_tfactors t :
  unfold_term <$> tfactors t = PreTerm.factors (unfold_term t).
Proof. rewrite /tfactors unfold_fold_map //; exact: (PreTerm.wf_factors _ (wf_unfold_term t)). Qed.

(* Only the identity [TMulN []] is its own inverse, so [TInv_Nid] needs the term
   to be a non-product. *)
Lemma TInv_Nid {t} : negb (is_mul t) -> TInv t ≠ t.
Proof.
rewrite is_mul_unfold => Nm E.
move: (f_equal unfold_term E); rewrite unfold_TInv (PreTerm.inv_Nmul _ Nm).
exact: PreTerm.inv_aux_Nid.
Qed.

Lemma TInvK t : TInv (TInv t) = t.
Proof.
apply: unfold_term_inj.
by rewrite !unfold_TInv (PreTerm.invK _ (wf_unfold_term t)).
Qed.

Global Instance TInv_inj : Inj (=) (=) TInv.
Proof. by move=> t1 t2 /(f_equal TInv); rewrite !TInvK. Qed.

Lemma TMulN_perm ts1 ts2 : ts1 ≡ₚ ts2 -> TMulN ts1 = TMulN ts2.
Proof.
move => peq; apply: unfold_term_inj; rewrite !unfold_TMulN.
apply: PreTerm.perm_mul; first exact: wf_unfold_terms.
by rewrite peq.
Qed.

Lemma TMulN1 t : TMulN [t] = t.
Proof.
by apply: unfold_term_inj;
   rewrite unfold_TMulN /= (PreTerm.mul_wf1 _ (wf_unfold_term t)).
Qed.

Lemma TMulN_cat ts ts' : TMulN (TMulN ts :: ts') = TMulN (ts ++ ts').
Proof.
apply: unfold_term_inj; rewrite !unfold_TMulN fmap_cons unfold_TMulN fmap_app.
by rewrite (PreTerm.mul_cat _ _ (wf_unfold_terms _) (wf_unfold_terms _)).
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

Definition cancel_invs ts :=
  fold_term <$> PreTerm.cancel_invs (unfold_term <$> ts).

Lemma unfold_TInv_Nmul {t} :
  negb (is_mul t) -> unfold_term (TInv t) = PreTerm.inv_aux (unfold_term t).
Proof.
rewrite is_mul_unfold => Nm.
by rewrite unfold_TInv (PreTerm.inv_Nmul _ Nm).
Qed.

Lemma Nmul_TInv {t} : negb (is_mul t) -> negb (is_mul (TInv t)).
Proof.
move => Nm; rewrite is_mul_unfold (unfold_TInv_Nmul Nm).
exact: (PreTerm.is_mul_inv_aux _ (wf_unfold_term t)).
Qed.

Lemma perm_cancel_invs ts1 ts2 :
  Forall (fun t => negb (is_mul t)) ts1 ->
  ts1 ≡ₚ ts2 -> cancel_invs ts1 ≡ₚ cancel_invs ts2.
Proof.
move => _ peq. rewrite /cancel_invs.
have H : PreTerm.cancel_invs (unfold_term <$> ts1)
       ≡ₚ PreTerm.cancel_invs (unfold_term <$> ts2).
  apply: PreTerm.perm_cancel_invs; first exact: wf_unfold_terms.
  by rewrite peq.
by rewrite H.
Qed.

Lemma mem_cancel_invs ts : forall t, t ∈ cancel_invs ts -> t ∈ ts.
Proof.
move=> t /list_elem_of_fmap [pt [-> /PreTerm.mem_cancel_invs pt_in]].
move: pt_in => /list_elem_of_fmap [t' [-> t'_ts]].
by rewrite unfold_termK.
Qed.

Lemma count_map_unfold t ts :
  list_sort.count_mem (unfold_term t) (unfold_term <$> ts) = list_sort.count_mem t ts.
Proof.
elim: ts => [//|t' ts IH] /=; rewrite IH.
rewrite (bool_decide_ext (unfold_term t = unfold_term t') (t = t')) //.
split; [exact: unfold_term_inj | by move=> ->].
Qed.

Lemma count_map_fold t pts :
  Forall (fun pt => PreTerm.wf pt) pts ->
  list_sort.count_mem t (fold_term <$> pts) = list_sort.count_mem (unfold_term t) pts.
Proof.
elim: pts => [//|pt' pts IH] /Forall_cons [wf' wfs] /=.
rewrite (IH wfs).
rewrite (bool_decide_ext (t = fold_term pt') (unfold_term t = pt')) //.
split.
- by move=> ->; rewrite (fold_termK _ wf').
- by move=> E; apply: unfold_term_inj; rewrite (fold_termK _ wf').
Qed.

Lemma count_mem_merge_sort t l :
  list_sort.count_mem t (merge_sort term_order l) = list_sort.count_mem t l.
Proof. apply: count_mem_Permutation; exact: (merge_sort_Permutation term_order l). Qed.

Lemma count_cancel t ts :
  negb (is_mul t) -> Forall (fun t => negb (is_mul t)) ts ->
  list_sort.count_mem t (cancel_invs ts) =
  list_sort.count_mem t ts - list_sort.count_mem (TInv t) ts.
Proof.
move => Nmt Nm.
have Nmt' : negb (PreTerm.is_mul (unfold_term t)) by rewrite -is_mul_unfold.
rewrite /cancel_invs
  (count_map_fold t _ (PreTerm.wf_cancel_invs _ (wf_unfold_terms ts))).
rewrite (PreTerm.count_cancel _ _ (wf_unfold_term t) Nmt' (wf_unfold_terms ts)).
by rewrite -(unfold_TInv_Nmul Nmt) !count_map_unfold.
Qed.

Lemma count_perm_cancel {ts1 ts2} :
  Forall (fun t => negb (is_mul t)) ts1 -> Forall (fun t => negb (is_mul t)) ts2 ->
  (forall t, negb (is_mul t) ->
        list_sort.count_mem t ts1 - list_sort.count_mem (TInv t) ts1 =
        list_sort.count_mem t ts2 - list_sort.count_mem (TInv t) ts2) <->
  cancel_invs ts1 ≡ₚ cancel_invs ts2.
Proof.
move => Nm1 Nm2; split.
- move => wt_eq. apply: Permutation_count_mem => t.
  case Hm: (is_mul t).
  + have z : forall ss, Forall (fun t => negb (is_mul t)) ss ->
             list_sort.count_mem t (cancel_invs ss) = 0.
      move=> ss Hss; apply/not_elem_of_count_mem => /mem_cancel_invs hin.
      have := Forall_mem Hss hin; by rewrite Hm.
    by rewrite (z _ Nm1) (z _ Nm2).
  + have Nmt : negb (is_mul t) by rewrite Hm.
    by rewrite (count_cancel _ _ Nmt Nm1) (count_cancel _ _ Nmt Nm2) wt_eq.
- move => peq t Nmt. rewrite -!count_cancel //.
  exact: (count_mem_Permutation _ _ _ peq).
Qed.

Lemma count_perm_cancel_redux {ts1 ts2} :
  Forall (fun t => negb (is_mul t)) ts1 -> Forall (fun t => negb (is_mul t)) ts2 ->
  (forall t, negb (is_mul t) ->
        list_sort.count_mem t ts1 + list_sort.count_mem (TInv t) ts2 =
        list_sort.count_mem t ts2 + list_sort.count_mem (TInv t) ts1) <->
  cancel_invs ts1 ≡ₚ cancel_invs ts2.
Proof.
move => Nm1 Nm2; rewrite -(count_perm_cancel Nm1 Nm2).
split => H t Nmt; have := H t Nmt; first lia.
have := H (TInv t) (Nmul_TInv Nmt); rewrite TInvK; lia.
Qed.

Lemma count_TInv_cancel {t ts} :
  negb (is_mul t) -> Forall (fun t => negb (is_mul t)) ts ->
  list_sort.count_mem t (cancel_invs ts) ≠ 0 ->
  list_sort.count_mem (TInv t) (cancel_invs ts) = 0.
Proof.
move => Nmt Nm.
rewrite (count_cancel _ _ Nmt Nm) (count_cancel _ _ (Nmul_TInv Nmt) Nm) TInvK.
lia.
Qed.

Lemma cancel_invs_cat ts1 ts2 :
  Forall (fun t => negb (is_mul t)) ts1 -> Forall (fun t => negb (is_mul t)) ts2 ->
  cancel_invs (cancel_invs ts1 ++ ts2) ≡ₚ cancel_invs (ts1 ++ ts2).
Proof.
move => Nm1 Nm2.
have Nmc1 : Forall (fun t => negb (is_mul t)) (cancel_invs ts1).
  apply/Forall_forall => t /mem_cancel_invs h; exact: (Forall_mem Nm1 h).
have H1 : Forall (fun t => negb (is_mul t)) (cancel_invs ts1 ++ ts2)
  by apply/Forall_app; split.
have H2 : Forall (fun t => negb (is_mul t)) (ts1 ++ ts2)
  by apply/Forall_app; split.
apply/(count_perm_cancel H1 H2) => t Nmt. rewrite !count_mem_app.
rewrite (count_cancel _ _ Nmt Nm1) (count_cancel _ _ (Nmul_TInv Nmt) Nm1) TInvK.
lia.
Qed.

Lemma perm_cancel_invs_catl ts1 ts2 ts :
  Forall (fun t => negb (is_mul t)) ts1 -> Forall (fun t => negb (is_mul t)) ts2 ->
  Forall (fun t => negb (is_mul t)) ts ->
  (cancel_invs (ts ++ ts1) ≡ₚ cancel_invs (ts ++ ts2)) <->
  (cancel_invs ts1 ≡ₚ cancel_invs ts2).
Proof.
move => Nm1 Nm2 Nm.
have Ntts1 : Forall (fun t => negb (is_mul t)) (ts ++ ts1) by apply/Forall_app; split.
have Ntts2 : Forall (fun t => negb (is_mul t)) (ts ++ ts2) by apply/Forall_app; split.
split => H.
- apply/(count_perm_cancel_redux Nm1 Nm2) => t Nmt.
  have := (proj2 (count_perm_cancel_redux Ntts1 Ntts2) H) t Nmt.
  rewrite !count_mem_app; lia.
- apply/(count_perm_cancel_redux Ntts1 Ntts2) => t Nmt.
  have := (proj2 (count_perm_cancel_redux Nm1 Nm2) H) t Nmt.
  rewrite !count_mem_app; lia.
Qed.

Lemma count_map_TInv t ts:
  list_sort.count_mem t (TInv <$> ts) = list_sort.count_mem (TInv t) ts.
Proof.
elim: ts => [//|t' ts IH] /=; rewrite IH.
rewrite (bool_decide_ext (t = TInv t') (TInv t = t')) //.
by split=> E; [rewrite E TInvK | rewrite -E TInvK].
Qed.

Lemma cancel_invs_cat_invs ts1 ts2 :
  Forall (fun t => negb (is_mul t)) ts1 -> Forall (fun t => negb (is_mul t)) ts2 ->
  cancel_invs (ts1 ++ ts2 ++ (TInv <$> ts2)) ≡ₚ cancel_invs ts1.
Proof.
move => Nm1 Nm2.
have NmT2 : Forall (fun t => negb (is_mul t)) (TInv <$> ts2).
  apply/Forall_fmap; apply/Forall_forall => s Hs; apply: Nmul_TInv; exact: (Forall_mem Nm2 Hs).
have H1 : Forall (fun t => negb (is_mul t)) (ts1 ++ ts2 ++ (TInv <$> ts2)).
  apply/Forall_app; split; first exact: Nm1.
  apply/Forall_app; split; [exact: Nm2 | exact: NmT2].
apply/(count_perm_cancel H1 Nm1) => t Nmt.
rewrite !count_mem_app !count_map_TInv TInvK; lia.
Qed.

Lemma unfold_cancel_invs ts :
  unfold_term <$> cancel_invs ts = PreTerm.cancel_invs (unfold_term <$> ts).
Proof.
rewrite /cancel_invs unfold_fold_map //.
exact: (PreTerm.wf_cancel_invs _ (wf_unfold_terms ts)).
Qed.

Lemma unfold_merge_sort s :
  unfold_term <$> merge_sort term_order s = merge_sort pt_order (unfold_term <$> s).
Proof. apply: merge_sort_fmap => x y; rewrite /term_order; reflexivity. Qed.

Lemma exps_TExpN_sort t ts :
  Forall (fun t => negb (is_mul t)) ts ->
  exps (TExpN t ts) = merge_sort term_order (cancel_invs (exps t ++ ts)).
Proof.
move => atom.
have atomU : Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts).
  exact/map_unfold_Nmul.
apply: (inj (fmap unfold_term)).
rewrite unfold_exps unfold_TExpN.
rewrite (PreTerm.exps_exp _ _ (wf_unfold_term t)
          (PreTerm.wf_mul _ (wf_unfold_terms ts))).
rewrite (PreTerm.factors_mul _ (wf_unfold_terms ts))
        (PreTerm.flatten_factors_Nmul_id _ atomU).
rewrite unfold_merge_sort unfold_cancel_invs fmap_app unfold_exps.
by rewrite (PreTerm.sortcancel_catr _ _
             (PreTerm.wf_exps _ (wf_unfold_term t))
             (PreTerm.Nmul_factors _ (PreTerm.wf_expo _ (wf_unfold_term t)))
             (wf_unfold_terms ts) atomU).
Qed.

Definition is_nonce t :=
  if t is TNonce _ then true else false.

Definition is_inv t :=
  if t is TNonFree pt _ _ then PreTerm.is_inv pt else false.

Definition is_exp t :=
  if t is TNonFree pt _ _ then PreTerm.is_exp pt else false.

Lemma is_nonce_unfold t : is_nonce t = PreTerm.is_nonce (unfold_term t).
Proof. by case: t => //= pt _ nf; move: nf; case: pt. Qed.

Lemma is_inv_unfold t : is_inv t = PreTerm.is_inv (unfold_term t).
Proof. by case: t. Qed.

Lemma is_inv_TInv t : negb (is_mul t) -> is_inv (TInv t) = negb (is_inv t).
Proof.
move => Nm; rewrite !is_inv_unfold (unfold_TInv_Nmul Nm).
move: (wf_unfold_term t); case: (unfold_term t) => [o|[k||] pt'|o t1 t2|ts] /= wf //.
by move: wf => /andb_True [/andb_True [/negb_True/Is_true_false_1 -> _] _].
Qed.

Lemma is_exp_unfold t : is_exp t = PreTerm.is_exp (unfold_term t).
Proof. by case: t. Qed.

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

Lemma base_exps_inj t1 t2 :
  base t1 = base t2 -> exps t1 ≡ₚ exps t2 -> t1 = t2.
Proof.
move=> eb ee; rewrite -(base_expsK t1) -(base_expsK t2) eb.
exact: TExpN_perm.
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
  have -> : PreTerm.mul [PreTerm.PTMul []; unfold_term t2]
          = PreTerm.mul [unfold_term t2].
    by rewrite /PreTerm.mul /= !app_nil_r.
  exact: (PreTerm.mul_wf1 _ (wf_unfold_term t2)).
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

Lemma TExpNC t ts1 ts2 : TExpN (TExpN t ts1) ts2 = TExpN (TExpN t ts2) ts1.
Proof. by move =>>; rewrite !TExpNA TExpN_catC. Qed.

Definition invs_canceled ts := PreTerm.invs_canceled (unfold_term <$> ts).

Definition atomic (ts : list term) : Prop := Forall (fun t => negb (is_mul t)) ts.

Definition wf_mul_list (ts : list term) : Prop :=
  atomic ts /\ StronglySorted term_order ts /\ invs_canceled ts /\ length ts ≠ 1.

Lemma atomic_unfold ts :
  atomic ts -> Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts).
Proof. rewrite /atomic; exact: (proj2 (map_unfold_Nmul ts)). Qed.

Lemma wf_mul_list_unfold ts :
  wf_mul_list ts -> PreTerm.wf_term (PreTerm.PTMul (unfold_term <$> ts)).
Proof.
move=> [atom [sorted [canc szN1]]].
apply/(PreTerm.wf_termE _). apply: PreTerm.wf_MulI.
- exact: wf_unfold_terms.
- exact: (atomic_unfold _ atom).
- apply: (StronglySorted_fmap unfold_term term_order pt_order); last exact: sorted.
  by move=> x y; rewrite /term_order.
- exact: canc.
- by rewrite length_fmap.
Qed.

Lemma invs_canceledE ts : invs_canceled ts <-> Forall (fun t => TInv t ∉ ts) ts.
Proof.
rewrite /invs_canceled PreTerm.invs_canceledP Forall_fmap.
apply: Forall_iff => t /=.
by rewrite -unfold_TInv list_elem_of_fmap_inj.
Qed.

Lemma TInv_fixed t : (TInv t = t) <-> (t = TMulN []).
Proof.
split.
- move=> E; apply/unfold_term_inj; rewrite unfold_TMulN /=.
  move: (f_equal unfold_term E); rewrite unfold_TInv.
  by move=> /(PreTerm.inv_fixed _ (wf_unfold_term t)).
- by move=> ->; apply/unfold_term_inj; rewrite unfold_TInv unfold_TMulN /=.
Qed.

Lemma invs_canceledP {ts} :
  invs_canceled ts <-> (forall t, t ∈ ts -> TInv t ∉ ts).
Proof. rewrite invs_canceledE Forall_forall //. Qed.

Lemma perm_invs_canceled ts1 ts2 :
  ts1 ≡ₚ ts2 -> invs_canceled ts1 <-> invs_canceled ts2.
Proof.
move => peq; rewrite !invs_canceledP.
split => H t Ht.
- rewrite -peq; apply: H; by rewrite peq.
- rewrite peq; apply: H; by rewrite -peq.
Qed.

Lemma Nmul_neq_unit {t} : negb (is_mul t) -> t ≠ TMulN [].
Proof.
move=> /negb_True Nm E; apply: Nm; rewrite E is_mul_unfold unfold_TMulN.
by [].
Qed.

Lemma invs_canceled1_iff t : invs_canceled [t] <-> t ≠ TMulN [].
Proof.
rewrite invs_canceledE Forall_singleton not_elem_of_cons; split.
- by move=> [H _] E; apply: H; rewrite E TInv_fixed.
- move=> H; split; last exact: not_elem_of_nil.
  by move=> E; apply: H; apply/TInv_fixed.
Qed.

Lemma invs_canceled_Nmul1 {t} : negb (is_mul t) -> invs_canceled [t].
Proof. by move=> Nm; apply/invs_canceled1_iff; exact: Nmul_neq_unit. Qed.

Lemma invs_canceled_cons {t ts} :
  negb (is_mul t) ->
  invs_canceled (t :: ts) <-> (TInv t ∉ ts /\ invs_canceled ts).
Proof.
move=> Nm; rewrite !invs_canceledP; split.
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

Lemma invs_canceled2_iff t1 t2 :
  invs_canceled [t1 ; t2] <-> (TInv t1 ≠ t2 /\ TMulN [] ∉ [t1; t2]).
Proof.
have NE2 : forall (x a b : term), x ∉ [a;b] <-> x ≠ a /\ x ≠ b.
  move=> x a b; have HC : x ∉ (@nil term) := not_elem_of_nil x.
  rewrite !not_elem_of_cons; tauto.
have Fx1 : (TInv t1 = t1) <-> (t1 = TMulN []) := TInv_fixed t1.
have Fx2 : (TInv t2 = t2) <-> (t2 = TMulN []) := TInv_fixed t2.
have K : (TInv t2 = t1) <-> (TInv t1 = t2).
  by split => <-; rewrite TInvK.
have S1 : (TMulN [] = t1) <-> (t1 = TMulN []) by split.
have S2 : (TMulN [] = t2) <-> (t2 = TMulN []) by split.
rewrite invs_canceledE Forall_cons Forall_singleton !NE2.
clear NE2; naive_solver.
Qed.

Lemma invs_canceled2_Nmul {t1 t2} :
  negb (is_mul t1) -> negb (is_mul t2) ->
  invs_canceled [t1 ; t2] <-> t1 ≠ TInv t2.
Proof.
move=> Nm1 Nm2; rewrite (invs_canceled_cons Nm1); split.
- move=> [H _] E; apply: H; rewrite list_elem_of_singleton E TInvK //.
- move=> H; split.
  + rewrite list_elem_of_singleton => E; apply: H; rewrite -E TInvK //.
  + exact: (invs_canceled_Nmul1 Nm2).
Qed.

Lemma parity_cancel_invs ts : Nat.odd (length (cancel_invs ts)) = Nat.odd (length ts).
Proof. by rewrite /cancel_invs length_fmap PreTerm.parity_cancel_invs length_fmap. Qed.

Lemma invs_canceled_exps t : invs_canceled (exps t).
Proof. by rewrite /invs_canceled unfold_exps; apply: PreTerm.invs_canceled_exps; exact: wf_unfold_term. Qed.

Lemma exps_Nmul t' t : t' ∈ exps t -> negb (is_mul t').
Proof.
move => t'_t; rewrite is_mul_unfold.
have H := PreTerm.Nmul_factors _ (PreTerm.wf_expo _ (wf_unfold_term t)).
apply: (Forall_mem H); rewrite -/(PreTerm.exps (unfold_term t)) -unfold_exps.
apply: list_elem_of_fmap_2; exact: t'_t.
Qed.

Lemma atom_exps t : atomic (exps t).
Proof. apply/Forall_forall => t' t't; exact: exps_Nmul t't. Qed.

Lemma invs_canceled_cons_exps {t1} t2 :
  negb (is_mul t1) ->
  invs_canceled (t1 :: exps t2) <-> (TInv t1 ∉ exps t2).
Proof.
move => Nm; rewrite (invs_canceled_cons Nm); split.
- by case.
- move=> H; split; [exact: H | exact: invs_canceled_exps].
Qed.

Lemma cancel_invs_canceled ts :
  atomic ts -> invs_canceled ts -> cancel_invs ts = ts.
Proof.
move=> atom canc.
rewrite /cancel_invs (PreTerm.cancel_invs_canceled _ (atomic_unfold _ atom) canc).
rewrite -(list_fmap_compose unfold_term fold_term).
rewrite -{2}(list_fmap_id ts). apply: Forall_fmap_ext_1.
apply/Forall_forall => t _; exact: unfold_termK.
Qed.

Lemma cancel_invs_exps t : cancel_invs (exps t) = exps t.
Proof. apply: cancel_invs_canceled; [exact: atom_exps | exact: invs_canceled_exps]. Qed.

Lemma cancel_invs1 t : cancel_invs [t] = [t].
Proof. by rewrite /cancel_invs /= unfold_termK. Qed.

Lemma invs_canceled_count {t} ts :
  invs_canceled ts ->
  list_sort.count_mem t ts - list_sort.count_mem (TInv t) ts = list_sort.count_mem t ts.
Proof.
move=> can_ts.
case: (decide (t ∈ ts)) => [t_ts|/not_elem_of_count_mem -> //].
have H : TInv t ∉ ts by move: can_ts => /invs_canceledP/(_ _ t_ts).
by rewrite (proj1 (not_elem_of_count_mem _ _) H) Nat.sub_0_r.
Qed.

Lemma is_exp_TExpN t ts :
  negb (is_exp t) -> atomic ts -> invs_canceled ts ->
  is_exp (TExpN t ts) = negb (bool_decide (ts = [])).
Proof.
move => Nxt atom canc.
have atomU : Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts).
  exact: (atomic_unfold _ atom).
rewrite /TExpN is_exp_unfold unfold_TExp.
rewrite (PreTerm.is_exp_exp _ _ (wf_unfold_term t)).
rewrite (PreTerm.expo_expN _); last by rewrite -is_exp_unfold.
rewrite unfold_TMulN -[PreTerm.PTMul []]/(PreTerm.mul []).
rewrite (PreTerm.mul_mul2 [] (unfold_term <$> ts) ltac:(constructor) (wf_unfold_terms ts)) app_nil_l.
congr negb. apply: bool_decide_ext.
rewrite (PreTerm.mul_eq_unit _ atomU canc).
split; [move=> /fmap_nil_inv // | by move=> ->].
Qed.

Lemma is_exp_TExp t1 t2 : negb (is_exp t1) -> negb (is_mul t2) -> is_exp (TExp t1 t2).
Proof.
move => Nx1 Nm2.
have -> : TExp t1 t2 = TExpN t1 [t2] by rewrite /TExpN TMulN1.
have atom : atomic [t2] by rewrite /atomic; apply/Forall_singleton.
rewrite (is_exp_TExpN _ _ Nx1 atom (invs_canceled_Nmul1 Nm2)).
by rewrite bool_decide_eq_false_2.
Qed.

Lemma TExpN0 : forall t, TExpN t [] = t.
Proof.
move => t; rewrite /TExpN; apply: unfold_term_inj.
rewrite unfold_TExp unfold_TMulN /=.
by rewrite (PreTerm.exp_unit _ (wf_unfold_term t)).
Qed.

Definition tsize t := PreTerm.tsize (unfold_term t).

Lemma tsize_gt0 t : 0 < tsize t. Proof. exact: PreTerm.tsize_gt0. Qed.

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

Lemma tsize_TInv t : negb (is_mul t) -> negb (is_inv t) -> tsize (TInv t) = S (tsize t).
Proof.
move => Nm Ni.
rewrite /tsize (unfold_TInv_Nmul Nm) PreTerm.tsize_inv // -is_inv_unfold //.
Qed.

Lemma tsize_TExp t1 t2 :
  negb (is_exp t1) -> negb (is_mul t2) -> tsize (TExp t1 t2) = S (tsize t1 + tsize t2).
Proof.
move => Nx1 Nm2.
rewrite is_exp_unfold in Nx1; rewrite is_mul_unfold in Nm2.
have neq : unfold_term t2 ≠ PreTerm.PTMul [].
  by move=> e; move: Nm2; rewrite e.
by rewrite /tsize unfold_TExp (PreTerm.tsize_exp_Nexp _ _ Nx1 (wf_unfold_term t2) neq).
Qed.

Definition tsizeE := (tsize_TInv, tsize_TExp, tsize_eq).

Lemma TExpNK ts t :
  atomic ts -> atomic (TInv <$> ts) ->
  TExpN (TExpN t ts) (TInv <$> ts) = t.
Proof.
move => atom atomInv.
rewrite TExpNA /TExpN.
have -> : TMulN (ts ++ (TInv <$> ts)) = TMulN [].
  apply: unfold_term_inj; rewrite !unfold_TMulN fmap_app.
  have -> : unfold_term <$> (TInv <$> ts) = PreTerm.inv_aux <$> (unfold_term <$> ts).
    rewrite -!(list_fmap_compose _ _ ts); apply: Forall_fmap_ext_1.
    apply/Forall_forall => x x_ts /=.
    exact: (unfold_TInv_Nmul (Forall_mem atom x_ts)).
  apply: PreTerm.mul_invs; first exact: wf_unfold_terms.
  apply/Forall_app; split.
  + exact: (atomic_unfold _ atom).
  + apply/Forall_fmap; apply/Forall_forall => pt /list_elem_of_fmap [t' [-> t'ts]] /=.
    rewrite -(unfold_TInv_Nmul (Forall_mem atom t'ts)) -is_mul_unfold.
    apply: (Forall_mem atomInv); apply: list_elem_of_fmap_2; exact: t'ts.
by apply: unfold_term_inj;
   rewrite unfold_TExp unfold_TMulN /= (PreTerm.exp_unit _ (wf_unfold_term t)).
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
Proof. move: (invs_canceled_exps t2) => /invs_canceledP H; exact: H. Qed.

Lemma in_TInv_expsV t1 t2 : TInv t1 ∈ exps t2 -> t1 ∉ exps t2.
Proof. by rewrite -{2}[t1]TInvK; exact: in_TInv_exps. Qed.

Lemma in_exps_TInv t1 t2 : (t1 ∉ exps t2) \/ (TInv t1 ∉ exps t2).
Proof.
case: (decide (t1 ∈ exps t2)) => [/in_TInv_exps H|H]; by [right|left].
Qed.

Lemma tsize_lt_TInv {t} : negb (is_mul t) -> tsize (TInv t) <= S (tsize t).
Proof.
move => Nm; have NmT := Nmul_TInv Nm.
case: (decide (Is_true (is_inv t))) => [inv_t|ninv_t].
- have Ni : negb (is_inv (TInv t)) by rewrite is_inv_TInv // negb_involutive.
  rewrite -{2}[t]TInvK (tsize_TInv _ NmT Ni); lia.
- rewrite (tsize_TInv _ Nm); first lia.
  by apply/negb_True.
Qed.

Lemma TExp_expsE t1 t2 : TExp t1 t2 = TExpN (base t1) (exps t1 ++ [t2]).
Proof. by rewrite -{1}(base_expsK t1) -TExpNA /TExpN TMulN1. Qed.

Lemma tsize_TExpN t ts :
  negb (is_exp t) -> atomic ts -> invs_canceled ts ->
  tsize (TExpN t ts) =
  (if bool_decide (ts ≠ []) then 1 else 0) + (if bool_decide (1 < length ts) then 1 else 0)
  + tsize t + sum_list_with tsize ts.
Proof.
move => Nxt atom canc.
have atomU : Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts).
  exact: (atomic_unfold _ atom).
case: (decide (ts = [])) => [->|tsN0].
  have H1 : bool_decide (@nil term ≠ []) = false.
    by apply: bool_decide_eq_false_2; move=> H; exact: (H eq_refl).
  have H2 : bool_decide (1 < length (@nil term)) = false.
    by apply: bool_decide_eq_false_2; rewrite /=; lia.
  rewrite TExpN0 H1 H2 /=; lia.
have eneq : PreTerm.mul (unfold_term <$> ts) ≠ PreTerm.PTMul [].
  by move=> H; apply: tsN0; apply: (inj (fmap unfold_term)); rewrite (proj1 (PreTerm.mul_eq_unit _ atomU canc) H).
have sumeq : sum_list_with PreTerm.tsize (unfold_term <$> ts) = sum_list_with tsize ts.
  by elim: ts {atom canc atomU tsN0 eneq} => [//|t' ts IH] /=; rewrite IH.
rewrite [tsize (TExpN t ts)]/tsize /TExpN unfold_TExp unfold_TMulN.
rewrite (PreTerm.tsize_exp_Nexp _ _ _ (PreTerm.wf_mul _ (wf_unfold_terms ts)) eneq);
  last by rewrite -is_exp_unfold.
rewrite (PreTerm.tsize_mul _ atomU canc); last first.
  by move=> H; apply: tsN0; apply: (inj (fmap unfold_term)); rewrite H.
rewrite length_fmap sumeq -[PreTerm.tsize (unfold_term t)]/(tsize t).
rewrite (bool_decide_eq_true_2 (ts ≠ [])) //; lia.
Qed.

Lemma tsize_lt_TExp_strong t1 t2 :
  negb (is_mul t2) -> TInv t2 ∉ exps t1 ->
  tsize t1 < tsize (TExp t1 t2) /\
  S (tsize t2) < tsize (TExp t1 t2).
Proof.
move => Nm2 t2_t1.
have atom : atomic (exps t1 ++ [t2]).
  by rewrite /atomic; apply/Forall_app; split; [exact: atom_exps | apply/Forall_singleton].
have canc : invs_canceled (exps t1 ++ [t2]).
  have pperm : exps t1 ++ [t2] ≡ₚ t2 :: exps t1 by rewrite -Permutation_cons_append.
  apply/(perm_invs_canceled _ _ pperm).
  by apply/(invs_canceled_cons Nm2); split; [exact: t2_t1 | exact: invs_canceled_exps].
have e1 : tsize t1 = (if bool_decide (exps t1 ≠ []) then 1 else 0)
                     + (if bool_decide (1 < length (exps t1)) then 1 else 0)
                     + tsize (base t1) + sum_list_with tsize (exps t1).
  by rewrite -{1}(base_expsK t1)
     (tsize_TExpN _ _ (is_exp_base_bool t1) (atom_exps t1) (invs_canceled_exps t1)).
rewrite TExp_expsE (tsize_TExpN _ _ (is_exp_base_bool t1) atom canc).
rewrite length_app sum_list_with_app /=.
have g1 := tsize_gt0 (base t1).
have g2 := tsize_gt0 t2.
have HP : exps t1 ++ [t2] ≠ [] by case: (exps t1).
have Hd : (if bool_decide (exps t1 ++ [t2] ≠ []) then 1 else 0) = 1
  by rewrite (bool_decide_eq_true_2 _ HP).
have Ha1 : (if bool_decide (exps t1 ≠ []) then 1 else 0) ≤ 1
  by case E: (bool_decide (exps t1 ≠ [])); simpl; lia.
have Hbc : (if bool_decide (1 < length (exps t1)) then 1 else 0)
        ≤ (if bool_decide (1 < length (exps t1) + 1) then 1 else 0).
  case E: (bool_decide (1 < length (exps t1)));
    case E': (bool_decide (1 < length (exps t1) + 1)); simpl; try lia.
  move/bool_decide_eq_true_1 in E; move/bool_decide_eq_false_1 in E'; lia.
rewrite e1 Hd; split; move: g1 g2 Ha1 Hbc; lia.
Qed.

Lemma tsize_lt_TExp t1 t2 :
  negb (is_mul t2) -> TInv t2 ∉ exps t1 ->
  tsize t1 < tsize (TExp t1 t2) /\
  tsize (TInv t2) < tsize (TExp t1 t2) /\
  tsize t2 < tsize (TExp t1 t2).
Proof.
move => Nm2 t2_t1; case: (tsize_lt_TExp_strong _ _ Nm2 t2_t1) => H1 H2.
have H3 := tsize_lt_TInv Nm2.
do !split; lia.
Qed.

Lemma TExpN_injr t ts1 ts2 :
  atomic ts1 -> atomic ts2 ->
  TExpN t ts1 = TExpN t ts2 ->
  cancel_invs ts1 ≡ₚ cancel_invs ts2.
Proof.
move => atom1 atom2 /(f_equal exps).
rewrite (exps_TExpN_sort _ _ atom1) (exps_TExpN_sort _ _ atom2) => Hsort.
have Hperm : cancel_invs (exps t ++ ts1) ≡ₚ cancel_invs (exps t ++ ts2).
  apply: (merge_sort_eq_Permutation term_order); exact: Hsort.
by apply/(perm_cancel_invs_catl _ _ _ atom1 atom2 (atom_exps t)); exact: Hperm.
Qed.

Lemma TExp_injr t t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) -> TExp t t1 = TExp t t2 -> t1 = t2.
Proof.
move => Nm1 Nm2 e.
have e' : TExpN t [t1] = TExpN t [t2] by rewrite /TExpN !TMulN1.
have a1 : atomic [t1] by rewrite /atomic; apply/Forall_singleton.
have a2 : atomic [t2] by rewrite /atomic; apply/Forall_singleton.
have Hperm := TExpN_injr _ _ _ a1 a2 e'.
have : t2 ∈ cancel_invs [t2] by rewrite cancel_invs1; apply/list_elem_of_singleton.
rewrite -Hperm cancel_invs1 list_elem_of_singleton => ->; done.
Qed.

Definition count_exp_nat t1 t2 := list_sort.count_mem t1 (exps t2).

Lemma count_exp_nat_eq0 t1 t2 : t1 ∉ exps t2 -> count_exp_nat t1 t2 = 0.
Proof. move=> t1V_t2; exact/not_elem_of_count_mem. Qed.

Lemma count_exp_nat_gt0 t1 t2 : (0 < count_exp_nat t1 t2) <-> (t1 ∈ exps t2).
Proof. rewrite /count_exp_nat elem_of_count_mem; lia. Qed.

Lemma count_exp_nat_TExp t1 t2 t3 :
  negb (is_mul t3) ->
  count_exp_nat t1 (TExp t2 t3) =
  if bool_decide (t1 = TInv t3) then pred (count_exp_nat t1 t2)
  else if bool_decide (t1 = t3)
       then S (count_exp_nat t1 t2) - (if bool_decide (TInv t1 ∈ exps t2) then 1 else 0)
       else count_exp_nat t1 t2.
Proof.
move => Nm3.
have single : forall (x y : term), list_sort.count_mem x [y] = if bool_decide (x = y) then 1 else 0.
  by move=> x y /=; rewrite Nat.add_0_r.
case Hm: (is_mul t1).
- have Mt1 : is_mul t1 by rewrite Hm.
  have z : forall X, count_exp_nat t1 X = 0.
    move => X; rewrite /count_exp_nat.
    have H : t1 ∉ exps X by move=> /exps_Nmul H'; rewrite Hm in H'.
    by rewrite (proj1 (not_elem_of_count_mem _ _) H).
  rewrite !z.
  rewrite (bool_decide_eq_false_2 (t1 = TInv t3)); last first.
    move=> e; subst t1; move: (Nmul_TInv Nm3) => /negb_True Hc; exact: (Hc Mt1).
  rewrite (bool_decide_eq_false_2 (t1 = t3)); last first.
    move=> e; subst t1; move: Nm3 => /negb_True Hc; exact: (Hc Mt1).
  done.
- have Nmt1 : negb (is_mul t1) by rewrite Hm.
  have atom : atomic ([t3] ++ exps t2).
    rewrite /atomic; apply/Forall_app; split; [by apply/Forall_singleton | exact: atom_exps].
  have KeyE : bool_decide (TInv t1 = t3) = bool_decide (t1 = TInv t3).
    apply: bool_decide_ext; split => e; [by rewrite -e TInvK | by rewrite e TInvK].
  have Hic1 := @invs_canceled_count t1 (exps t2) (invs_canceled_exps t2).
  rewrite -/(count_exp_nat t1 t2) -/(count_exp_nat (TInv t1) t2) in Hic1.
  rewrite /count_exp_nat TExp_expsE TExpN_catC.
  rewrite (exps_TExpN_sort _ _ atom) (exps_expN_bool _ (is_exp_base_bool t2)) app_nil_l count_mem_merge_sort.
  rewrite (count_cancel _ _ Nmt1 atom) !count_mem_app !single KeyE.
  rewrite -/(count_exp_nat t1 t2) -/(count_exp_nat (TInv t1) t2).
  case: (decide (t1 = TInv t3)) => [e|ne].
  + have ne2 : t1 ≠ t3.
      move=> e2; apply: (Nmul_neq_unit Nm3); apply/TInv_fixed; by rewrite -e e2.
    rewrite (bool_decide_eq_true_2 (t1 = TInv t3) e) (bool_decide_eq_false_2 (t1 = t3) ne2) /=.
    move: Hic1; lia.
  + rewrite (bool_decide_eq_false_2 (t1 = TInv t3) ne).
    case: (decide (t1 = t3)) => [e2|ne2].
    * rewrite (bool_decide_eq_true_2 (t1 = t3) e2) /=.
      case: (decide (TInv t1 ∈ exps t2)) => [t1_t2|t1_t2].
      -- rewrite (bool_decide_eq_true_2 (TInv t1 ∈ exps t2) t1_t2).
         have Ha0 : count_exp_nat t1 t2 = 0.
           apply: count_exp_nat_eq0; exact: (in_TInv_expsV _ _ t1_t2).
         have Hb : 0 < count_exp_nat (TInv t1) t2 by apply/count_exp_nat_gt0.
         move: Ha0 Hb; lia.
      -- rewrite (bool_decide_eq_false_2 (TInv t1 ∈ exps t2) t1_t2).
         have Hb0 : count_exp_nat (TInv t1) t2 = 0.
           by apply: count_exp_nat_eq0.
         move: Hb0; lia.
    * rewrite (bool_decide_eq_false_2 (t1 = t3) ne2) /=.
      move: Hic1; lia.
Qed.

Variant count_exp_nat_TExp_spec t1 t2 t3 : nat -> Type :=
| CountExpTExpSame0
  of t1 = t3 & TInv t3 ∈ exps t2
: count_exp_nat_TExp_spec t1 t2 t3 0

| CountExpTExpSame1
  of t1 = t3 & TInv t3 ∉ exps t2
: count_exp_nat_TExp_spec t1 t2 t3 (S (count_exp_nat t1 t2))

| CountExpTExpTInv
  of t1 = TInv t3
: count_exp_nat_TExp_spec t1 t2 t3 (pred (count_exp_nat t1 t2))

| CountExpTExpDiff
  of t1 ≠ t3 & t1 ≠ TInv t3
: count_exp_nat_TExp_spec t1 t2 t3 (count_exp_nat t1 t2).

Lemma count_exp_nat_TExpP t1 t2 t3 :
  negb (is_mul t3) ->
  count_exp_nat_TExp_spec t1 t2 t3 (count_exp_nat t1 (TExp t2 t3)).
Proof.
move => Nm3; rewrite (count_exp_nat_TExp t1 t2 t3 Nm3).
case: (decide (t1 = TInv t3)) => eV.
  rewrite bool_decide_eq_true_2 //; by constructor.
rewrite (bool_decide_eq_false_2 (t1 = TInv t3) eV).
case: (decide (t1 = t3)) => e; last first.
  rewrite (bool_decide_eq_false_2 (t1 = t3) e); by constructor.
rewrite (bool_decide_eq_true_2 (t1 = t3) e).
case: (decide (TInv t1 ∈ exps t2)) => t1_t2.
- rewrite bool_decide_eq_true_2 //.
  have -> : count_exp_nat t1 t2 = 0.
    apply: count_exp_nat_eq0; exact: (in_TInv_expsV _ _ t1_t2).
  rewrite /=; constructor => //; by rewrite -e.
- rewrite bool_decide_eq_false_2 // Nat.sub_0_r; constructor => //; by rewrite -e.
Qed.

Lemma tsize_TExp_TInv t1 t2 :
  negb (is_mul (TInv t2)) -> t2 ∈ exps t1 ->
  tsize t2 < tsize t1 /\
  tsize (TInv t2) < tsize t1 /\
  tsize (TExp t1 (TInv t2)) < tsize t1.
Proof.
move => NmI2 H.
have Nm2 : negb (is_mul t2) := exps_Nmul _ _ H.
rewrite -{1 2 4}(TExpK' t1 t2 NmI2 Nm2).
set t1' := TExp t1 _.
have {}H : TInv t2 ∉ exps t1'.
  have Hcount : count_exp_nat (TInv t2) t1' = 0.
    rewrite /t1' (count_exp_nat_TExp (TInv t2) t1 (TInv t2) NmI2).
    rewrite (bool_decide_eq_false_2 (TInv t2 = TInv (TInv t2))); last first.
      by move=> /(inj TInv) e; apply: (Nmul_neq_unit Nm2); apply/TInv_fixed.
    rewrite (bool_decide_eq_true_2 (TInv t2 = TInv t2) eq_refl) TInvK.
    have -> : count_exp_nat (TInv t2) t1 = 0 by apply: count_exp_nat_eq0; exact: (in_TInv_exps _ _ H).
    by rewrite (bool_decide_eq_true_2 (t2 ∈ exps t1) H).
  rewrite -count_exp_nat_gt0 Hcount; lia.
by case: (tsize_lt_TExp _ _ Nm2 H) => ? [] ??; eauto.
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

Lemma exps_Nnil t : is_exp t -> exps t ≠ [].
Proof.
move => xt E.
have Hexp : is_exp t = negb (bool_decide (exps t = [])).
  by rewrite -{1}(base_expsK t) (is_exp_TExpN _ _ (is_exp_base_bool t) (atom_exps t) (invs_canceled_exps t)).
move: xt; rewrite Hexp E /=; by move=> [].
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

Lemma tsize_in_sumn t' ts : t' ∈ ts -> tsize t' <= sum_list_with tsize ts.
Proof.
elim: ts => [|t ts IH]; first by rewrite elem_of_nil.
rewrite elem_of_cons => -[-> /=|/IH h /=]; lia.
Qed.

Lemma tsize_base_lt t : is_exp t -> tsize (base t) < tsize t.
Proof.
rewrite is_exp_unfold => xt.
rewrite /tsize unfold_base; move: xt.
by case: (unfold_term t) => [o|o t'|[||] t1 t2|ts] //= _; lia.
Qed.

Lemma tsize_exps_lt t' t : t' ∈ exps t -> tsize t' < tsize t.
Proof.
move => t'_t.
have en : exps t ≠ [] by move=> e; rewrite e elem_of_nil in t'_t.
have xt : is_exp t.
  case E: (is_exp t) => //; move: en; rewrite (exps_expN_bool _ _) //; by rewrite E.
rewrite -{1}(base_expsK t)
  (tsize_TExpN _ _ (is_exp_base_bool t) (atom_exps t) (invs_canceled_exps t)).
have Hle := tsize_in_sumn _ _ t'_t.
have Hb := tsize_gt0 (base t).
rewrite (bool_decide_eq_true_2 (exps t ≠ []) en) /=; lia.
Qed.

Lemma tfactorsK t : TMulN (tfactors t) = t.
Proof.
apply: unfold_term_inj; rewrite unfold_TMulN unfold_tfactors.
exact: (PreTerm.mul_factors _ (wf_unfold_term t)).
Qed.

Lemma mul_wf_list_eq ts :
  wf_mul_list ts ->
  PreTerm.mul (unfold_term <$> ts) = PreTerm.PTMul (unfold_term <$> ts).
Proof.
move => wf.
have Hwf : PreTerm.wf (PreTerm.PTMul (unfold_term <$> ts)).
  exact: (proj1 (PreTerm.wf_termE _) (wf_mul_list_unfold ts wf)).
have H := PreTerm.mul_factors _ Hwf.
by move: H; rewrite /PreTerm.factors.
Qed.

Lemma is_mul_TMulN ts : wf_mul_list ts -> is_mul (TMulN ts).
Proof. by move => wf; rewrite is_mul_unfold unfold_TMulN mul_wf_list_eq. Qed.

Lemma tfactors_TMulN ts : wf_mul_list ts -> tfactors (TMulN ts) = ts.
Proof.
move => wf; rewrite /tfactors unfold_TMulN mul_wf_list_eq //=.
rewrite -(list_fmap_compose unfold_term fold_term).
rewrite -{2}(list_fmap_id ts). apply: Forall_fmap_ext_1.
apply/Forall_forall => t' _; exact: unfold_termK.
Qed.

Lemma atom_tfactors t : atomic (tfactors t).
Proof.
apply/Forall_forall => x x_t; rewrite is_mul_unfold.
have H := PreTerm.Nmul_factors _ (wf_unfold_term t).
apply: (Forall_mem H); rewrite -unfold_tfactors; apply: list_elem_of_fmap_2; exact: x_t.
Qed.

Lemma invs_canceled_tfactors t : invs_canceled (tfactors t).
Proof.
rewrite /invs_canceled unfold_tfactors.
exact: PreTerm.invs_canceled_factors _ (wf_unfold_term t).
Qed.

Lemma tsize_TMulN ts :
  atomic ts -> invs_canceled ts -> ts ≠ [] ->
  tsize (TMulN ts) = (if bool_decide (1 < length ts) then 1 else 0) + sum_list_with tsize ts.
Proof.
move => atom canc tsN0.
have atomU : Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts).
  exact: (atomic_unfold _ atom).
rewrite /tsize /TMulN unfold_TMulN.
rewrite (PreTerm.tsize_mul _ atomU canc); last first.
  by move=> H; apply: tsN0; apply: (inj (fmap unfold_term)); rewrite H.
rewrite length_fmap; congr Nat.add.
by elim: ts {atom canc tsN0 atomU} => [//|t' ts IH] /=; rewrite IH.
Qed.

Lemma tsize_tfactors_lt t' t : is_mul t -> t' ∈ tfactors t -> tsize t' < tsize t.
Proof.
move => xt t'_t.
have tsN0 : tfactors t ≠ [] by move=> e; rewrite e elem_of_nil in t'_t.
rewrite -{1}(tfactorsK t)
  (tsize_TMulN _ (atom_tfactors t) (invs_canceled_tfactors t) tsN0).
have Hle := tsize_in_sumn _ _ t'_t.
have szge : 1 < length (tfactors t).
  have szN1 : length (tfactors t) ≠ 1.
    rewrite /tfactors length_fmap; move: xt; rewrite is_mul_unfold.
    case: (unfold_term t) (wf_unfold_term t) => // ts wf _.
    move: wf; rewrite PreTerm.wf_MulE !andb_True.
    move=> [[[[_ _] _] _] /bool_decide_unpack Hlen]; by rewrite /PreTerm.factors.
  have : tfactors t ≠ [] := tsN0.
  case: (tfactors t) szN1 => [|?[|??]] //=; lia.
rewrite (bool_decide_eq_true_2 (1 < length (tfactors t)) szge) /=; lia.
Qed.

Lemma term_rect (T : term -> Type)
  (H1 : forall n, T (TInt n))
  (H2 : forall t1, T t1 ->
        forall t2, T t2 ->
        T (TPair t1 t2))
  (H3 : forall a, T (TNonce a))
  (H4 : forall kt t, T t -> T (TKey kt t))
  (H5 : forall k, T k -> forall t, T t -> T (TSeal k t))
  (H6 : forall t, T t -> T (THash t))
  (H7 : forall t, T t -> negb (is_mul t) -> negb (is_inv t) -> T (TInv t))
  (H8 : forall t, T t -> negb (is_exp t) ->
        forall ts, foldr (fun t R => T t * R)%type unit ts ->
                   atomic ts ->
                   ts ≠ [] ->
                   StronglySorted term_order ts ->
                   invs_canceled ts ->
        T (TExpN t ts))
  (H9 : forall ts, foldr (fun t R => T t * R)%type unit ts ->
                   atomic ts ->
                   StronglySorted term_order ts ->
                   invs_canceled ts ->
                   length ts ≠ 1 ->
        T (TMulN ts)) :
  forall t, T t.
Proof.
elim/term_lt_rect => t IH.
have build : forall s, (forall t', t' ∈ s -> tsize t' < tsize t) ->
    foldr (fun t R => T t * R)%type unit s.
  elim => // x s' IHs h; split.
    by apply: IH; apply: h; apply/list_elem_of_here.
  by apply: IHs => t' t's; apply: h; apply/list_elem_of_further.
case: t IH build => [n|t1 t2|a|kt t|k t|t|pt wf nf] IH build.
- exact: H1.
- apply: H2; apply: IH; rewrite [tsize (TPair t1 t2)]tsize_eq; lia.
- exact: H3.
- apply: H4; apply: IH; rewrite [tsize (TKey kt t)]tsize_eq; lia.
- apply: H5; apply: IH; rewrite [tsize (TSeal k t)]tsize_eq; lia.
- apply: H6; apply: IH; rewrite [tsize (THash t)]tsize_eq; lia.
- case: pt wf nf IH build => [o|[kt||] operand|[||] b e|ts] wf nf IH build.
  1,2,3,5,6: by move: {IH build} nf; rewrite /is_non_free /=.
  + have /andb_True [/andb_True [Ninvpt Nmpt] wfpt] := wf.
    have e : TNonFree (PreTerm.PT1 O1Inv operand) wf nf = TInv (fold_term operand).
      apply: unfold_term_inj.
      by rewrite unfold_TInv (fold_termK operand wfpt) (PreTerm.inv_Nmul operand Nmpt)
         (PreTerm.inv_invN operand Ninvpt).
    have Ninv : negb (is_inv (fold_term operand)) by rewrite is_inv_unfold (fold_termK operand wfpt).
    have Nmf : negb (is_mul (fold_term operand)) by rewrite is_mul_unfold (fold_termK operand wfpt).
    rewrite e; apply: (H7 _ _ Nmf Ninv).
    apply: IH.
    rewrite (tsize_eq (TNonFree (PreTerm.PT1 O1Inv operand) wf nf))
            /tsize (fold_termK operand wfpt) /=; lia.
  + set t := TNonFree (PreTerm.PTExp b e) wf nf.
    have xt : is_exp t by [].
    rewrite -(base_expsK t).
    apply: H8.
    * apply: IH; exact: tsize_base_lt.
    * exact: is_exp_base_bool.
    * by apply: build => t' t'_t; exact: (tsize_exps_lt _ _ t'_t).
    * exact: atom_exps.
    * exact: exps_Nnil xt.
    * exact: exps_sorted.
    * exact: invs_canceled_exps.
  + set t := TNonFree (PreTerm.PTMul ts) wf nf.
    have xt : is_mul t by [].
    rewrite -(tfactorsK t).
    apply: H9.
    * by apply: build => t' t'_t; exact: (tsize_tfactors_lt _ _ xt t'_t).
    * exact: atom_tfactors.
    * apply: StronglySorted_term_unfold; rewrite unfold_tfactors.
      exact: (PreTerm.sorted_factors _ (wf_unfold_term t)).
    * exact: invs_canceled_tfactors.
    * rewrite /tfactors length_fmap /t /=.
      have /andb_True [_ /bool_decide_unpack Hlen] := wf.
      by rewrite /PreTerm.factors.
Qed.

Definition term_ind (P : term -> Prop) := @term_rect P.

Lemma term_lt_ind (T : term -> Prop) :
  (forall t, (forall t', (tsize t' < tsize t) -> T t') -> T t) ->
  forall t, T t.
Proof. exact: term_lt_rect. Qed.

Variant functionality := AENC | SIGN | SENC.

Definition func_of_key_type kt :=
  match kt with
  | AEnc | ADec => AENC
  | Sign | Verify => SIGN
  | SEnc => SENC
  end.

Definition func_of_term t :=
  match t with
  | TKey kt _ => Some (func_of_key_type kt)
  | _ => None
  end.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Canonical termO := leibnizO term.

(* Universal on wf lists: products pass through [cancel_invs] untouched and atoms
   cancel by count, both permutation-stable (see [PreTerm.perm_cancel_invs_wf]).
   [cancel_invs] only ever feeds [map unfold_term _], which is always wf. *)
Global Instance cancel_invs_proper : Proper ((≡ₚ) ==> (≡ₚ)) cancel_invs.
Proof.
move=> ts1 ts2 H12; rewrite /cancel_invs.
have H : PreTerm.cancel_invs (unfold_term <$> ts1)
       ≡ₚ PreTerm.cancel_invs (unfold_term <$> ts2).
  apply: PreTerm.perm_cancel_invs; first exact: wf_unfold_terms.
  by rewrite H12.
by rewrite H.
Qed.

Global Instance TExpN_proper : Proper ((=) ==> (≡ₚ) ==> (=)) TExpN.
Proof. by move=> t _ <- ts1 ts2 ts12; apply: (TExpN_perm _ _ _ ts12). Qed.

Lemma TExpC2 g t1 t2 : TExpN g [t1; t2] = TExpN g [t2; t1].
Proof. by rewrite Permutation_swap. Qed.

Global Instance term_inhabited : Inhabited term.
Proof. exact: (populate (TInt 0)). Qed.

Global Instance aenc_key_inhabited : Inhabited aenc_key :=
  populate (AEncKey inhabitant).

Global Instance sign_key_inhabited : Inhabited sign_key :=
  populate (SignKey inhabitant).

Global Instance senc_key_inhabited : Inhabited senc_key :=
  populate (SEncKey inhabitant).

Lemma subseteq_cancel_invs ts : cancel_invs ts ⊆ ts.
Proof. apply/elem_of_subseteq => t; exact: mem_cancel_invs. Qed.
Global Arguments subseteq_cancel_invs ts : clear implicits.

Lemma TInv_neq {t} : negb (is_mul t) -> TInv t ≠ t.
Proof. exact: TInv_Nid. Qed.

Lemma elem_of_TInv_exps t1 t2 : t1 ∈ exps t2 → TInv t1 ∉ exps t2.
Proof. exact: in_TInv_exps. Qed.

Lemma elem_of_TInv_exps' t1 t2 : TInv t1 ∈ exps t2 → t1 ∉ exps t2.
Proof. exact: in_TInv_expsV. Qed.

Definition count_exp (t ts : term) : Z :=
  (count_exp_nat t ts - count_exp_nat (TInv t) ts)%Z.

Lemma count_exp_eq0 t1 t2 :
  t1 ∉ exps t2 → TInv t1 ∉ exps t2 → count_exp t1 t2 = 0.
Proof. by move=> ??; rewrite /count_exp !count_exp_nat_eq0. Qed.

Lemma count_exp_gt0 t1 t2 : (count_exp t1 t2 > 0)%Z ↔ t1 ∈ exps t2.
Proof.
rewrite /count_exp; case: (decide (t1 ∈ exps t2)) => t1_t2.
  rewrite [count_exp_nat (TInv _) _]count_exp_nat_eq0; last first.
    exact: elem_of_TInv_exps.
  rewrite -count_exp_nat_gt0; lia.
rewrite count_exp_nat_eq0 //; split; first lia.
by case/t1_t2.
Qed.

Lemma count_exp_TInv (t ts : term) : count_exp (TInv t) ts = Z.opp (count_exp t ts).
Proof. rewrite /count_exp TInvK. lia. Qed.

Lemma count_exp_TExp_eq t1 t2 :
  negb (is_mul t1) ->
  count_exp t1 (TExp t2 t1) = (count_exp t1 t2 + 1)%Z.
Proof.
move => Nm1.
have Ht1 : t1 ≠ TInv t1 by move=> E; move: (TInv_Nid Nm1); rewrite -E.
have E1 : count_exp_nat t1 (TExp t2 t1)
        = S (count_exp_nat t1 t2) - (if bool_decide (TInv t1 ∈ exps t2) then 1 else 0).
  rewrite (count_exp_nat_TExp t1 t2 t1 Nm1).
  by rewrite (bool_decide_eq_false_2 (t1 = TInv t1) Ht1)
             (bool_decide_eq_true_2 (t1 = t1) eq_refl).
have E2 : count_exp_nat (TInv t1) (TExp t2 t1) = pred (count_exp_nat (TInv t1) t2).
  rewrite (count_exp_nat_TExp (TInv t1) t2 t1 Nm1).
  by rewrite (bool_decide_eq_true_2 (TInv t1 = TInv t1) eq_refl).
rewrite /count_exp E1 E2; clear E1 E2.
case_bool_decide as H.
- have Ha : count_exp_nat t1 t2 = 0 by apply: count_exp_nat_eq0; exact: (elem_of_TInv_exps' H).
  have Hb : count_exp_nat (TInv t1) t2 > 0 by apply/count_exp_nat_gt0.
  rewrite Ha; lia.
- have Hb : count_exp_nat (TInv t1) t2 = 0 by apply: count_exp_nat_eq0.
  rewrite Hb; lia.
Qed.

Lemma count_exp_TExp_TInv t1 t2 :
  negb (is_mul (TInv t1)) ->
  count_exp t1 (TExp t2 (TInv t1)) = (count_exp t1 t2 - 1)%Z.
Proof.
move => NmI1.
rewrite -{1}[t1]TInvK count_exp_TInv (count_exp_TExp_eq _ NmI1) count_exp_TInv.
lia.
Qed.

Lemma count_exp_TInv_TExp t1 t2 :
  negb (is_mul t1) ->
  count_exp (TInv t1) (TExp t2 t1) = (count_exp (TInv t1) t2 - 1)%Z.
Proof.
move => Nm1.
have h : negb (is_mul (TInv (TInv t1))) by rewrite TInvK.
by rewrite -{2}[t1]TInvK (count_exp_TExp_TInv _ h).
Qed.

Lemma count_exp_TExp_ne t1 t2 t3 :
  negb (is_mul t3) ->
  t1 ≠ t3 → t1 ≠ TInv t3 → count_exp t1 (TExp t2 t3) = count_exp t1 t2.
Proof.
move=> Nm3 t1_t3 t1_t3V.
have H1 : TInv t1 ≠ TInv t3 by move=> /TInv_inj E; exact: (t1_t3 E).
have H2 : TInv t1 ≠ t3 by move=> E; apply: t1_t3V; rewrite -E TInvK.
rewrite /count_exp (count_exp_nat_TExp t1 t2 t3 Nm3) (count_exp_nat_TExp (TInv t1) t2 t3 Nm3).
rewrite (bool_decide_eq_false_2 (t1 = TInv t3) t1_t3V) (bool_decide_eq_false_2 (t1 = t3) t1_t3).
by rewrite (bool_decide_eq_false_2 (TInv t1 = TInv t3) H1) (bool_decide_eq_false_2 (TInv t1 = t3) H2).
Qed.

Lemma count_exp_TExp t1 t2 t3 :
  negb (is_mul t3) ->
  count_exp t1 (TExp t2 t3) =
  if decide (t1 = t3) then
    (count_exp t1 t2 + 1)%Z
  else if decide (t1 = TInv t3) then
    (count_exp t1 t2 - 1)%Z
  else count_exp t1 t2.
Proof.
move => Nm3.
case: decide => [->|?]; first by rewrite count_exp_TExp_eq.
case: decide => [->|?]; first by rewrite count_exp_TInv_TExp.
by rewrite count_exp_TExp_ne.
Qed.

Lemma count_exp_TExpW t1 t2 t3 :
  negb (is_mul t3) ->
  t1 ≠ TInv t3 →
  (count_exp t1 t2 ≤ count_exp t1 (TExp t2 t3))%Z.
Proof.
move=> Nm3 t1_t3; rewrite count_exp_TExp // (@decide_False _ (t1 = TInv t3)) //.
by case: decide => ?; lia.
Qed.

Lemma not_elem_of_TInv_exps t1 t2 :
  negb (is_mul t1) ->
  TInv t1 ∉ exps t2 ↔ t1 ∈ exps (TExp t2 t1).
Proof.
move => Nm1.
rewrite -!count_exp_gt0 count_exp_TInv count_exp_TExp_eq //; lia.
Qed.

Lemma TExpN_appC t ts1 ts2 : TExpN t (ts1 ++ ts2) = TExpN t (ts2 ++ ts1).
Proof. exact: TExpN_catC. Qed.

Inductive subterm (t : term) : term → Prop :=
| STRefl : subterm t t
| STPair1 t1 t2 of subterm t t1 : subterm t (TPair t1 t2)
| STPair2 t1 t2 of subterm t t2 : subterm t (TPair t1 t2)
| STKey kt t' of subterm t t' : subterm t (TKey kt t')
| STSeal1 k t' of subterm t k : subterm t (TSeal k t')
| STSeal2 k t' of subterm t t' : subterm t (TSeal k t')
| STHash t' of subterm t t' : subterm t (THash t')
| STInv t' of negb (is_mul t') & negb (is_inv t') & subterm t t' : subterm t (TInv t')
| STExp1 t' ts of negb (is_exp t') & subterm t t' : subterm t (TExpN t' ts)
| STExp2 t' t'' ts of
    negb (is_exp t') &
    atomic ts &
    invs_canceled ts &
    subterm t t'' &
    t'' ∈ ts
  : subterm t (TExpN t' ts)
| STMul t'' ts of
    wf_mul_list ts &
    subterm t t'' &
    t'' ∈ ts
  : subterm t (TMulN ts).

Global Instance subterm_trans : Transitive subterm.
Proof.
move=> t1 t2 t3 sub12 sub13; elim: t3 / sub13;
by eauto using subterm.
Qed.

Section ValOfTerm.

Fixpoint val_of_term_rec t : val :=
  match t with
  | TInt n =>
    (#TOp0_tag, (#TInt_tag, #n))
  | TPair t1 t2 =>
    (#TOp2_tag, (#TPair_tag, val_of_term_rec t1, val_of_term_rec t2))%V
  | TNonce l =>
    (#TOp0_tag, (#TNonce_tag, #(nonce_loc l)))%V
  | TKey kt t =>
    (#TOp1_tag, ((#TKey_tag, repr kt), val_of_term_rec t))%V
  | TSeal t1 t2 =>
    (#TOp2_tag, (#TSeal_tag, val_of_term_rec t1, val_of_term_rec t2))%V
  | THash t =>
    (#TOp1_tag, ((#THash_tag, #()), val_of_term_rec t))%V
  | TNonFree pt _ _ => val_of_pre_term pt
  end.

Definition val_of_term_aux : seal val_of_term_rec. by eexists. Qed.
Definition val_of_term : term -> val := unseal val_of_term_aux.
Lemma val_of_term_unseal : val_of_term = val_of_term_rec.
Proof. exact: seal_eq. Qed.
Coercion val_of_term : term >-> val.
Global Instance repr_term : Repr term := val_of_term.

Global Instance repr_aenc_key : Repr aenc_key := λ k : aenc_key, val_of_term (term_of_aenc_key k).
Global Instance repr_senc_key : Repr senc_key := λ k : senc_key, val_of_term (term_of_senc_key k).
Global Instance repr_sign_key : Repr sign_key := λ k : sign_key, val_of_term (term_of_sign_key k).

Lemma val_of_pre_term_unfold t :
  val_of_pre_term (unfold_term t) = val_of_term t.
Proof.
rewrite val_of_term_unseal.
elim/term_ind': t => //=; try by move=> *; congruence.
Qed.

End ValOfTerm.

Global Instance val_of_term_inj : Inj (=) (=) val_of_term.
Proof.
move=> t1 t2 e_t1t2; apply: unfold_term_inj.
apply: val_of_pre_term_inj.
by rewrite !val_of_pre_term_unfold.
Qed.

Global Instance infinite_term : Infinite term.
Proof.
pose int_of_term (t : term) :=
  if t is TInt n then Some n else None.
apply (inj_infinite TInt int_of_term).
by move=> n; rewrite /int_of_term.
Qed.

Definition term_height t :=
  PreTerm.height (unfold_term t).

Definition nonces_of_term_def (t : term) :=
  nonces_of_pre_term (unfold_term t).
Arguments nonces_of_term_def /.
Definition nonces_of_term_aux : seal nonces_of_term_def. by eexists. Qed.
Definition nonces_of_term := unseal nonces_of_term_aux.
Lemma nonces_of_term_unseal : nonces_of_term = nonces_of_term_def.
Proof. exact: seal_eq. Qed.

Lemma nonces_of_termE' t :
  nonces_of_term t =
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | TNonce l => {[l]}
  | TKey _ t => nonces_of_term t
  | TSeal t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | THash t => nonces_of_term t
  | TNonFree pt _ _ => nonces_of_pre_term pt
  end.
Proof.
by rewrite nonces_of_term_unseal; case: t => //=.
Qed.

Lemma nonces_of_term_fold pt :
  PreTerm.wf pt -> nonces_of_term (fold_term pt) = nonces_of_pre_term pt.
Proof. move => wf. by rewrite nonces_of_term_unseal /nonces_of_term_def (@fold_termK pt wf). Qed.

Lemma nonces_of_pre_term_factors e :
  nonces_of_pre_term e = ⋃ map nonces_of_pre_term (PreTerm.factors e).
Proof. by case: e => [o|o1 e1|o2 e1 e2|es] //=; rewrite union_empty_r_L. Qed.

Lemma nonces_of_pre_term_inv_aux x :
  nonces_of_pre_term (PreTerm.inv_aux x) = nonces_of_pre_term x.
Proof. by case: x => [o|[kt||] e|o e1 e2|es] //=. Qed.

(* Local bridge: [merge_sort] only permutes, and [⋃ ∘ map f] is
   permutation-invariant, so sorting the list before mapping is transparent. *)
Lemma union_list_map_merge_sort {A X} `{Countable X} (f : A → gset X)
  (R : relation A) `{!RelDecision R} l :
  ⋃ map f (merge_sort R l) = ⋃ map f l.
Proof.
apply: union_list_permutation_proper_L; apply: Permutation_map.
exact: (merge_sort_Permutation R l).
Qed.

(* [inv] distributes [inv] over the factors and re-multiplies; [inv] preserves
   nonces, and (for wf [pt]) no cancellation occurs, so nonces are preserved. *)
Lemma nonces_of_pre_term_inv pt :
  PreTerm.wf pt ->
  nonces_of_pre_term (PreTerm.inv pt) = nonces_of_pre_term pt.
Proof.
move => wf.
rewrite (PreTerm.inv_factors pt wf) (nonces_of_pre_term_factors pt).
set F := PreTerm.factors pt.
have wfF : Forall PreTerm.wf F := PreTerm.wf_factors pt wf.
have NmF : Forall (fun pt => negb (PreTerm.is_mul pt)) F := PreTerm.Nmul_factors pt wf.
have cancF : PreTerm.invs_canceled F := PreTerm.invs_canceled_factors pt wf.
have wfMI : Forall PreTerm.wf (PreTerm.inv_aux <$> F).
  apply/Forall_fmap; apply/Forall_forall => x xF.
  apply: PreTerm.wf_inv_aux; [exact: (Forall_mem wfF xF) | exact: (Forall_mem NmF xF)].
have NmMI : Forall (fun pt => negb (PreTerm.is_mul pt)) (PreTerm.inv_aux <$> F).
  apply/Forall_fmap; apply/Forall_forall => x xF.
  apply: PreTerm.is_mul_inv_aux; exact: (Forall_mem wfF xF).
have cancMI : PreTerm.invs_canceled (PreTerm.inv_aux <$> F).
  exact: PreTerm.invs_canceled_map_inv F wfF cancF.
rewrite (nonces_of_pre_term_factors (PreTerm.mul (PreTerm.inv_aux <$> F))).
rewrite (PreTerm.factors_mul (PreTerm.inv_aux <$> F) wfMI).
rewrite (PreTerm.flatten_factors_Nmul_id (PreTerm.inv_aux <$> F) NmMI).
rewrite (PreTerm.cancel_invs_canceled (PreTerm.inv_aux <$> F) NmMI cancMI).
rewrite union_list_map_merge_sort.
rewrite /F; elim: (PreTerm.factors pt) => [//|x fs IH] /=.
by rewrite nonces_of_pre_term_inv_aux IH.
Qed.

Lemma nonces_of_term_TInv t : nonces_of_term (TInv t) = nonces_of_term t.
Proof.
rewrite !nonces_of_term_unseal /nonces_of_term_def unfold_TInv.
exact: nonces_of_pre_term_inv (wf_unfold_term t).
Qed.

(* Elementwise: folding the inverse of a well-formed atomic factor is [TInv] of
   the folded factor.  Stated as a standalone lemma to keep [fmap]'s typeclass
   instance resolved (a [have] with [<$>] in its type spuriously generalises it). *)
Lemma fmap_fold_inv_aux G :
  Forall PreTerm.wf G ->
  Forall (fun pt => negb (PreTerm.is_mul pt)) G ->
  fold_term <$> (PreTerm.inv_aux <$> G) = TInv <$> (fold_term <$> G).
Proof.
elim: G => [//|x fs IH] /Forall_cons [Wx wfs] /Forall_cons [Nmx Nms].
rewrite !fmap_cons (IH wfs Nms); congr cons.
apply: unfold_term_inj.
by rewrite unfold_TInv (fold_termK x Wx)
           (fold_termK (PreTerm.inv_aux x) (PreTerm.wf_inv_aux x Wx Nmx))
           (PreTerm.inv_Nmul x Nmx).
Qed.

(* [TInv] distributes over products: the canonical factor list of [TInv t] is
   a permutation of the inverses of the factors of [t].  Used to prove
   [public (TInv t) ⊣⊢ public t] for products by reducing to the factors. *)
Lemma tfactors_TInv t : tfactors (TInv t) ≡ₚ map TInv (tfactors t).
Proof.
rewrite /tfactors unfold_TInv (PreTerm.inv_factors (unfold_term t) (wf_unfold_term t)).
set F := PreTerm.factors (unfold_term t).
have wfF : Forall PreTerm.wf F := PreTerm.wf_factors _ (wf_unfold_term t).
have NmF : Forall (fun pt => negb (PreTerm.is_mul pt)) F := PreTerm.Nmul_factors _ (wf_unfold_term t).
have cancF : PreTerm.invs_canceled F := PreTerm.invs_canceled_factors _ (wf_unfold_term t).
have wfMI : Forall PreTerm.wf (PreTerm.inv_aux <$> F).
  apply/Forall_fmap; apply/Forall_forall => x xF.
  apply: PreTerm.wf_inv_aux; [exact: (Forall_mem wfF xF) | exact: (Forall_mem NmF xF)].
have NmMI : Forall (fun pt => negb (PreTerm.is_mul pt)) (PreTerm.inv_aux <$> F).
  apply/Forall_fmap; apply/Forall_forall => x xF.
  apply: PreTerm.is_mul_inv_aux; exact: (Forall_mem wfF xF).
have cancMI : PreTerm.invs_canceled (PreTerm.inv_aux <$> F).
  exact: PreTerm.invs_canceled_map_inv F wfF cancF.
rewrite (PreTerm.factors_mul (PreTerm.inv_aux <$> F) wfMI).
rewrite (PreTerm.flatten_factors_Nmul_id (PreTerm.inv_aux <$> F) NmMI).
rewrite (PreTerm.cancel_invs_canceled (PreTerm.inv_aux <$> F) NmMI cancMI).
rewrite (merge_sort_Permutation pt_order (PreTerm.inv_aux <$> F)).
by rewrite (fmap_fold_inv_aux wfF NmF).
Qed.

Lemma nonces_of_pre_term_base_expo pt :
  nonces_of_pre_term pt =
  nonces_of_pre_term (PreTerm.base pt) ∪ nonces_of_pre_term (PreTerm.expo pt).
Proof. by case: pt => [o|o1 e1|[||] e1 e2|es] //=; rewrite union_empty_r_L. Qed.

Lemma nonces_of_term_base_exps t :
  nonces_of_term t = nonces_of_term (base t) ∪ ⋃ map nonces_of_term (exps t).
Proof.
transitivity (nonces_of_pre_term (PreTerm.base (unfold_term t)) ∪
              ⋃ map nonces_of_pre_term (PreTerm.exps (unfold_term t))).
  rewrite {1}nonces_of_term_unseal /nonces_of_term_def.
  rewrite (nonces_of_pre_term_base_expo (unfold_term t)).
  by rewrite (nonces_of_pre_term_factors (PreTerm.expo (unfold_term t))).
congr (_ ∪ _).
  by rewrite /base (nonces_of_term_fold (PreTerm.wf_base _ (wf_unfold_term t))).
rewrite /exps.
have wfs : Forall PreTerm.wf (PreTerm.exps (unfold_term t)) := PreTerm.wf_exps _ (wf_unfold_term t).
elim: (PreTerm.exps (unfold_term t)) wfs => [//|pt pts IH] /Forall_cons [wpt wpts] /=.
by rewrite (nonces_of_term_fold wpt) (IH wpts).
Qed.

Lemma nonces_of_term_TExpN t ts :
  negb (is_exp t) -> atomic ts ->
  nonces_of_term (TExpN t ts) = nonces_of_term t ∪ ⋃ map nonces_of_term (cancel_invs ts).
Proof.
move => tNexp atom.
have nexp : negb (PreTerm.is_exp (unfold_term t)).
  by move: tNexp; rewrite is_exp_unfold.
have bt : base t = t by rewrite /base (PreTerm.base_expN _ nexp) unfold_termK.
have et : exps t = [] by rewrite /exps (PreTerm.exps_expN _ nexp).
rewrite (nonces_of_term_base_exps (TExpN t ts)) base_TExpN bt.
congr (_ ∪ _).
by rewrite (exps_TExpN_sort t ts atom) et app_nil_l union_list_map_merge_sort.
Qed.

Lemma nonces_flatten_factors us :
  ⋃ map nonces_of_pre_term (concat (PreTerm.factors <$> us)) =
  ⋃ map nonces_of_pre_term us.
Proof.
elim: us => [|u us IH] //=.
by rewrite map_app union_list_app_L -(nonces_of_pre_term_factors u) IH.
Qed.

(* [PreTerm.mul] cancels/sorts/flattens its argument, so its nonces are a subset
   of the union of the factors' nonces — no atomicity needed. *)
Lemma nonces_of_pre_term_mul_sub us :
  nonces_of_pre_term (PreTerm.mul us) ⊆ ⋃ map nonces_of_pre_term us.
Proof.
rewrite /PreTerm.mul.
set M := concat (PreTerm.factors <$> us).
rewrite (_ : nonces_of_pre_term _ =
             ⋃ map nonces_of_pre_term
                 (merge_sort pt_order (PreTerm.cancel_invs M))); last first.
  by case: (merge_sort pt_order (PreTerm.cancel_invs M)) => [|t [|t' l]] //=;
     rewrite union_empty_r_L.
rewrite union_list_map_merge_sort.
have HM : ⋃ map nonces_of_pre_term M = ⋃ map nonces_of_pre_term us
  by rewrite /M nonces_flatten_factors.
rewrite -HM.
move => a /elem_of_union_list [X [/list_elem_of_fmap [x [-> xL]] aX]].
apply/elem_of_union_list; exists (nonces_of_pre_term x); split => //.
apply/list_elem_of_fmap; exists x; split => //.
exact: (PreTerm.mem_cancel_invs M x xL).
Qed.

(* [PreTerm.exp] folds the new exponent into the base and cancels, so nonces are a
   subset of [nonces base ∪ nonces exponent] — no atomicity needed. *)
Lemma nonces_of_pre_term_exp_sub b e :
  nonces_of_pre_term (PreTerm.exp b e) ⊆ nonces_of_pre_term b ∪ nonces_of_pre_term e.
Proof.
rewrite /PreTerm.exp; cbv zeta.
have Hbe := nonces_of_pre_term_base_expo b.
case: (bool_decide (PreTerm.mul [PreTerm.expo b; e] = PreTerm.PTMul [])).
- set_solver.
- have Hmul := @nonces_of_pre_term_mul_sub [PreTerm.expo b; e].
  move: Hmul => /=; set_solver.
Qed.

(* The atomicity hypothesis is not needed: [TExpN t ts = TExp t (TMulN ts)], and the
   nonces of both [exp] and [mul] are subsets of their parts regardless of atomicity. *)
Lemma nonces_of_term_TExpN_subseteq t ts :
  nonces_of_term (TExpN t ts) ⊆ nonces_of_term t ∪ ⋃ map nonces_of_term ts.
Proof.
have Hts : ⋃ map nonces_of_term ts = ⋃ map nonces_of_pre_term (map unfold_term ts).
  congr union_list. elim: ts => [|t' ts IH] //=.
  by rewrite IH nonces_of_term_unseal /nonces_of_term_def.
rewrite Hts !nonces_of_term_unseal /nonces_of_term_def.
have -> : unfold_term (TExpN t ts) =
          PreTerm.exp (unfold_term t) (PreTerm.mul (map unfold_term ts)).
  by rewrite /TExpN unfold_TExp unfold_TMulN.
etrans; first exact: (@nonces_of_pre_term_exp_sub (unfold_term t)
                        (PreTerm.mul (map unfold_term ts))).
have Hmul := @nonces_of_pre_term_mul_sub (map unfold_term ts).
set_solver.
Qed.
Global Arguments nonces_of_term_TExpN_subseteq t ts : clear implicits.

Lemma nonces_of_term_TMulN ts :
  wf_mul_list ts ->
  nonces_of_term (TMulN ts) = ⋃ map nonces_of_term ts.
Proof.
move => wf; have wfU := wf_mul_list_unfold ts wf.
have e : TMulN ts = fold_term (PreTerm.PTMul (map unfold_term ts)).
  apply: unfold_term_inj; rewrite unfold_TMulN (@fold_termK _ wfU).
  exact: (PreTerm.mul_factors _ wfU).
rewrite {1}e (nonces_of_term_fold wfU) /=.
elim: ts {wf wfU e} => [//|t' ts' IH] /=.
rewrite -IH; congr (_ ∪ _).
by rewrite nonces_of_term_unseal.
Qed.

Lemma nonces_of_term_tfactors t :
  nonces_of_term t = ⋃ map nonces_of_term (tfactors t).
Proof.
rewrite nonces_of_term_unseal /nonces_of_term_def
  (nonces_of_pre_term_factors (unfold_term t)) /tfactors.
congr union_list.
elim: (PreTerm.factors (unfold_term t)) (PreTerm.wf_factors _ (wf_unfold_term t))
  => [//|pt pts IH] /Forall_cons [wpt wpts] /=.
by rewrite (fold_termK pt wpt) (IH wpts).
Qed.

Definition nonces_of_termE :=
  (nonces_of_term_TInv, nonces_of_term_TExpN, nonces_of_term_TMulN, nonces_of_termE').

Fixpoint ssubterms_pre_def (t : PreTerm.pre_term) : gset term :=
  let subterms_pre_def (t : PreTerm.pre_term) := {[fold_term t]} ∪ ssubterms_pre_def t in
  match t with
  | PreTerm.PT0 (O0Int _) => ∅
  | PreTerm.PT2 O2Pair t1 t2 => subterms_pre_def t1 ∪ subterms_pre_def t2
  | PreTerm.PT0 (O0Nonce _) => ∅
  | PreTerm.PT1 (O1Key _) t => subterms_pre_def t
  | PreTerm.PT2 O2Seal t1 t2 => subterms_pre_def t1 ∪ subterms_pre_def t2
  | PreTerm.PT1 O1Hash t => subterms_pre_def t
  | PreTerm.PT1 O1Inv t => subterms_pre_def t
  | PreTerm.PTExp b (PreTerm.PTMul us) =>
    subterms_pre_def b ∪ ⋃ map subterms_pre_def us
  | PreTerm.PTExp b e => subterms_pre_def b ∪ subterms_pre_def e
  | PreTerm.PTMul ts => ⋃ map subterms_pre_def ts
  end.

Definition subterms_def t := {[t]} ∪ ssubterms_pre_def (unfold_term t).
Arguments subterms_def /.
Definition subterms_aux : seal subterms_def. by eexists. Qed.
Definition subterms := unseal subterms_aux.
Lemma subterms_unseal : subterms = subterms_def.
Proof. exact: seal_eq. Qed.

Definition subterms_pre pt := {[fold_term pt]} ∪ ssubterms_pre_def pt.

Lemma subterms_preE pt :
  subterms_pre pt =
  {[fold_term pt]} ∪
  match pt with
  | PreTerm.PT0 _ => ∅
  | PreTerm.PT1 (O1Key _) t => subterms_pre t
  | PreTerm.PT1 O1Hash t => subterms_pre t
  | PreTerm.PT1 O1Inv t => subterms_pre t
  | PreTerm.PT2 O2Pair t1 t2 => subterms_pre t1 ∪ subterms_pre t2
  | PreTerm.PT2 O2Seal t1 t2 => subterms_pre t1 ∪ subterms_pre t2
  | PreTerm.PTExp b e => subterms_pre b ∪ ⋃ map subterms_pre (PreTerm.factors e)
  | PreTerm.PTMul ts => ⋃ map subterms_pre ts
  end.
Proof.
rewrite /subterms_pre; case: pt => [o|o e|[||] e1 e2|es] //=.
- by case: o.
- case: e2 => //= *; set_solver.
Qed.

Lemma subterms_fold pt :
  PreTerm.wf pt -> subterms (fold_term pt) = subterms_pre pt.
Proof. move => wf; by rewrite subterms_unseal /subterms_def /subterms_pre (@fold_termK pt wf). Qed.

Lemma subterms_via_pre t : subterms t = subterms_pre (unfold_term t).
Proof. by rewrite subterms_unseal /subterms_def /subterms_pre unfold_termK. Qed.

Lemma subterms_pre_base_exps pt :
  subterms_pre pt =
  {[fold_term pt]} ∪ subterms_pre (PreTerm.base pt) ∪ ⋃ map subterms_pre (PreTerm.exps pt).
Proof.
case E: (PreTerm.is_exp pt).
- case: pt E => [o|o e|[||] e1 e2|es] //= E; rewrite subterms_preE /=; set_solver.
- have Nxp : negb (PreTerm.is_exp pt) by rewrite E.
  rewrite (PreTerm.base_expN pt Nxp) (PreTerm.exps_expN pt Nxp) /=.
  rewrite /subterms_pre; set_solver.
Qed.

Lemma subterms_base_exps t :
  subterms t = {[t]} ∪ subterms (base t) ∪ ⋃ map subterms (exps t).
Proof.
have hb : subterms_pre (PreTerm.base (unfold_term t)) = subterms (base t).
  by rewrite /base (subterms_fold (PreTerm.wf_base _ (wf_unfold_term t))).
have he : ⋃ map subterms_pre (PreTerm.exps (unfold_term t)) = ⋃ map subterms (exps t).
  rewrite /exps.
  have wfs : Forall PreTerm.wf (PreTerm.exps (unfold_term t)) := PreTerm.wf_exps _ (wf_unfold_term t).
  elim: (PreTerm.exps (unfold_term t)) wfs => [//|pt pts IH] /Forall_cons [wpt wpts] /=.
  by rewrite (subterms_fold wpt) (IH wpts).
by rewrite (subterms_via_pre t) (subterms_pre_base_exps (unfold_term t)) unfold_termK hb he.
Qed.

Lemma subtermsE' t :
  subterms t =
  {[t]} ∪
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => subterms t1 ∪ subterms t2
  | TNonce _ => ∅
  | TKey _ t => subterms t
  | TSeal t1 t2 => subterms t1 ∪ subterms t2
  | THash t => subterms t
  | TNonFree pt _ _ => ssubterms_pre_def pt
  end.
Proof.
rewrite subterms_unseal /=.
case: t =>> //=; try by rewrite ?unfold_termK.
Qed.

Lemma subterms_TInv t :
  negb (is_mul t) -> negb (is_inv t) ->
  subterms (TInv t) = {[TInv t]} ∪ subterms t.
Proof.
move => Nm Ni.
have Ni' : negb (PreTerm.is_inv (unfold_term t)) by rewrite -is_inv_unfold.
rewrite subterms_unseal /subterms_def.
by rewrite (unfold_TInv_Nmul Nm) (PreTerm.inv_invN _ Ni') /= unfold_termK.
Qed.

Lemma subterms_TExpN t ts :
  negb (is_exp t) -> atomic ts ->
  subterms (TExpN t ts) = {[TExpN t ts]} ∪ subterms t ∪ ⋃ map subterms (cancel_invs ts).
Proof.
move => tNexp atom.
have nexp : negb (PreTerm.is_exp (unfold_term t)).
  by move: tNexp; rewrite is_exp_unfold.
have bt : base t = t by rewrite /base (PreTerm.base_expN _ nexp) unfold_termK.
have et : exps t = [] by rewrite /exps (PreTerm.exps_expN _ nexp).
rewrite (subterms_base_exps (TExpN t ts)) base_TExpN bt.
by rewrite (exps_TExpN_sort t ts atom) et app_nil_l union_list_map_merge_sort.
Qed.

Lemma subterms_TMulN ts :
  wf_mul_list ts ->
  subterms (TMulN ts) = {[TMulN ts]} ∪ ⋃ map subterms ts.
Proof.
move => wf; have wfU := wf_mul_list_unfold ts wf.
have e : TMulN ts = fold_term (PreTerm.PTMul (map unfold_term ts)).
  apply: unfold_term_inj; rewrite unfold_TMulN (@fold_termK _ wfU).
  exact: (PreTerm.mul_factors _ wfU).
rewrite {1}e (subterms_fold wfU) subterms_preE -e /=.
congr (_ ∪ _).
elim: ts {wf wfU e} => [//|t' ts' IH] /=.
rewrite -IH; congr (_ ∪ _).
by rewrite subterms_via_pre.
Qed.

Lemma subterms_nonce t : is_nonce t → subterms t = {[t]}.
Proof.
by case: t => //= ? _; rewrite subtermsE' right_id_L.
Qed.

Definition subtermsE := (subterms_TInv, subterms_TExpN, subterms_TMulN, subtermsE').

Ltac solve_subtermsP :=
  intros;
  repeat match goal with
  | H : context[subterms (?X ?Y)] |- _ =>
      rewrite [subterms (X Y)]subtermsE /= in H
  | H : _ ∈ {[_]} |- _ =>
      rewrite elem_of_singleton in H;
      rewrite {}H
  | H : _ ∈ _ ∪ _ |- _ =>
      rewrite elem_of_union in H;
      destruct H
  | H : _ ∈ ∅ |- _ =>
      rewrite elem_of_empty in H;
      destruct H
  | H1 : ?P, H2 : ?P -> ?Q |- _ =>
      move/(_ H1) in H2
  end;
  eauto using subterm.

Lemma subtermsP t1 t2 : subterm t1 t2 ↔ t1 ∈ subterms t2.
Proof.
split.
- elim: t2 /; try by intros; rewrite subtermsE //; set_solver.
  + move => t' ts Nexp sub IH.
    have bt' : base t' = t'.
      rewrite /base; move: Nexp; rewrite is_exp_unfold => n.
      by rewrite (PreTerm.base_expN _ n) unfold_termK.
    rewrite (subterms_base_exps (TExpN t' ts)) base_TExpN bt'; set_solver.
  + move => t' t'' ts Nexp atom canc sub IH t''_ts.
    rewrite (subterms_TExpN Nexp atom).
    rewrite (cancel_invs_canceled ts atom canc) !elem_of_union; right.
    rewrite elem_of_union_list; exists (subterms t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
  + move => t'' ts wf sub IH t''_ts.
    rewrite (subterms_TMulN wf) elem_of_union; right.
    rewrite elem_of_union_list; exists (subterms t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
- elim: t2; try by solve_subtermsP.
  + move => t IHt Nexp ts IHts atom tsN0 sort canc.
    rewrite subtermsE //.
    rewrite (cancel_invs_canceled ts atom canc).
    rewrite !elem_of_union elem_of_union_list elem_of_singleton.
    case => [[-> | /IHt sub] | [X [/list_elem_of_fmap [t' [-> t'_ts]] t1_t']]].
    * exact: STRefl.
    * apply: STExp1; [exact: Nexp|exact: sub].
    * have sub' : subterm t1 t'.
        move: IHts t'_ts t1_t'; elim: (ts) => /= [_ /elem_of_nil //|t0 ts0 IH0 [IH1 IHrest]].
        rewrite elem_of_cons; case => [-> //|/(IH0 IHrest)] // h ?; exact: h.
      apply: (STExp2 Nexp atom canc sub' t'_ts).
  + move => ts IHts atom sort canc szN1.
    have wf : wf_mul_list ts := conj atom (conj sort (conj canc szN1)).
    rewrite (subterms_TMulN wf).
    rewrite elem_of_union elem_of_union_list elem_of_singleton.
    case => [-> | [X [/list_elem_of_fmap [t' [-> t'_ts]] t1_t']]].
    * exact: STRefl.
    * have sub' : subterm t1 t'.
        move: IHts t'_ts t1_t'; elim: (ts) => /= [_ /elem_of_nil //|t0 ts0 IH0 [IH1 IHrest]].
        rewrite elem_of_cons; case => [-> //|/(IH0 IHrest)] // h ?; exact: h.
      apply: (STMul wf sub' t'_ts).
Qed.

Ltac solve_nonces_of_termP :=
  intros;
  repeat match goal with
  | H : context[nonces_of_term (?X ?Y)] |- _ =>
      rewrite [nonces_of_term (X Y)]nonces_of_termE /= in H
  | H : _ ∈ {[_]} |- _ =>
      rewrite elem_of_singleton in H;
      rewrite {}H
  | H : _ ∈ _ ∪ _ |- _ =>
      rewrite elem_of_union in H;
      destruct H
  | H : _ ∈ ∅ |- _ =>
      rewrite elem_of_empty in H;
      destruct H
  | H1 : ?P, H2 : ?P -> ?Q |- _ =>
      move/(_ H1) in H2
  end;
  eauto using subterm.

Lemma nonces_of_termP (a : nonce) t : subterm (TNonce a) t ↔ a ∈ nonces_of_term t.
Proof.
split.
- elim: t /; try by intros; rewrite nonces_of_termE; set_solver.
  + move => t' ts Nexp sub IH.
    have bt' : base t' = t'.
      rewrite /base; move: Nexp; rewrite is_exp_unfold => n.
      by rewrite (PreTerm.base_expN _ n) unfold_termK.
    rewrite (nonces_of_term_base_exps (TExpN t' ts)) base_TExpN bt'; set_solver.
  + move => t' t'' ts Nexp atom canc sub IH t''_ts.
    rewrite (nonces_of_term_TExpN Nexp atom).
    rewrite (cancel_invs_canceled ts atom canc) elem_of_union; right.
    rewrite elem_of_union_list; exists (nonces_of_term t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
  + move => t'' ts wf sub IH t''_ts.
    rewrite (nonces_of_term_TMulN wf) elem_of_union_list.
    exists (nonces_of_term t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
- elim: t; try by solve_nonces_of_termP.
  + move => t IHt Nexp ts IHts atom tsN0 sort canc.
    rewrite nonces_of_termE //.
    rewrite (cancel_invs_canceled ts atom canc) elem_of_union elem_of_union_list.
    case => [/IHt sub | [X [/list_elem_of_fmap [t' [-> t'_ts]] a_t']]].
    * apply: STExp1; [exact: Nexp|exact: sub].
    * have sub' : subterm (TNonce a) t'.
        move: IHts t'_ts a_t'; elim: (ts) => /= [_ /elem_of_nil //|t0 ts0 IH0 [IH1 IHrest]].
        rewrite elem_of_cons; case => [-> //|/(IH0 IHrest)] // h ?; exact: h.
      apply: (STExp2 Nexp atom canc sub' t'_ts).
  + move => ts IHts atom sort canc szN1.
    have wf : wf_mul_list ts := conj atom (conj sort (conj canc szN1)).
    rewrite (nonces_of_term_TMulN wf) elem_of_union_list.
    case => [X [/list_elem_of_fmap [t' [-> t'_ts]] a_t']].
    have sub' : subterm (TNonce a) t'.
      move: IHts t'_ts a_t'; elim: (ts) => /= [_ /elem_of_nil //|t0 ts0 IH0 [IH1 IHrest]].
      rewrite elem_of_cons; case => [-> //|/(IH0 IHrest)] // h ?; exact: h.
    apply: (STMul wf sub' t'_ts).
Qed.

Lemma subterm_nonces_of_term t1 t2 :
  subterm t1 t2 → nonces_of_term t1 ⊆ nonces_of_term t2.
Proof.
elim: t2 / => //; try by intros; rewrite [nonces_of_term (_ _)]nonces_of_termE; set_solver.
- move => t' ts Nexp sub IH.
  have bt' : base t' = t'.
    rewrite /base; move: Nexp; rewrite is_exp_unfold => n.
    by rewrite (PreTerm.base_expN _ n) unfold_termK.
  rewrite (nonces_of_term_base_exps (TExpN t' ts)) base_TExpN bt'; set_solver.
- move => t' t'' ts Nexp atom canc sub IH t''_ts.
  rewrite (nonces_of_term_TExpN Nexp atom).
  rewrite (cancel_invs_canceled ts atom canc).
  have sub2 : nonces_of_term t'' ⊆ ⋃ map nonces_of_term ts.
    move => x x_t''; rewrite elem_of_union_list; exists (nonces_of_term t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
  set_solver.
- move => t'' ts wf sub IH t''_ts.
  rewrite (nonces_of_term_TMulN wf).
  have sub2 : nonces_of_term t'' ⊆ ⋃ map nonces_of_term ts.
    move => x x_t''; rewrite elem_of_union_list; exists (nonces_of_term t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
  set_solver.
Qed.

Definition Tag_def (N : namespace) :=
  TInt (Zpos (encode N)).
Definition Tag_aux : seal Tag_def. by eexists. Qed.
Definition Tag := unseal Tag_aux.
Lemma Tag_unseal : Tag = Tag_def. Proof. exact: seal_eq. Qed.

Global Instance Tag_inj : Inj (=) (=) Tag.
Proof. by rewrite Tag_unseal => ?? [] /(inj _ _ _). Qed.

Module Spec.

Implicit Types N : term.

Definition is_seal_key k :=
  match k with
  | TKey AEnc _ | TKey Sign _ | TKey SEnc _ => true
  | _ => false
  end.

Definition public_key_type kt :=
  match kt with
  | AEnc | Verify => true
  | _ => false
  end.

Definition skey t :=
  match t with
  | TKey AEnc t => TKey ADec t
  | TKey Verify t => TKey Sign t
  | _ => t
  end.

Definition pkey t :=
  match t with
  | TKey ADec t => TKey AEnc t
  | TKey Sign t => TKey Verify t
  | _ => t
  end.

Lemma aenc_pkey_inj (sk1 sk2 : aenc_key) :
  pkey sk1 = pkey sk2 → sk1 = sk2.
Proof. by rewrite keysE; case: sk1 sk2 => [?] [?] [->]. Qed.

Lemma sign_pkey_inj (sk1 sk2 : sign_key) :
  pkey sk1 = pkey sk2 → sk1 = sk2.
Proof. by rewrite keysE; case: sk1 sk2 => [?] [?] [->]. Qed.

Lemma senc_pkey_inj (sk1 sk2 : senc_key) :
  pkey sk1 = pkey sk2 → sk1 = sk2.
Proof. by rewrite keysE; case: sk1 sk2 => [?] [?] [->]. Qed.

Definition tag_def N (t : term) :=
  TPair N t.
Definition tag_aux : seal tag_def. by eexists. Qed.
Definition tag := unseal tag_aux.
Lemma tag_unseal : tag = tag_def. Proof. exact: seal_eq. Qed.

Lemma is_nonce_tag N t : is_nonce (tag N t) = false.
Proof. by rewrite tag_unseal. Qed.

Lemma is_exp_tag N t : is_exp (tag N t) = false.
Proof. by rewrite tag_unseal. Qed.

Definition untag_def N (t : term) :=
  match t with
  | TPair N' t =>
    if decide (N = N') then Some t else None
  | _ => None
  end.
Definition untag_aux : seal untag_def. by eexists. Qed.
Definition untag := unseal untag_aux.
Lemma untag_unseal : untag = untag_def. Proof. exact: seal_eq. Qed.

Lemma tagK N t : untag N (tag N t) = Some t.
Proof.
rewrite untag_unseal tag_unseal /untag_def /tag_def /=.
by rewrite decide_True_pi.
Qed.

#[global]
Instance tag_inj : Inj2 (=) (=) (=) tag.
Proof.
rewrite tag_unseal /tag_def => c1 t1 c2 t2 [] e ->.
split=> //; by apply: inj e.
Qed.

Lemma untagK N t1 t2 :
  untag N t1 = Some t2 ->
  t1 = tag N t2.
Proof.
rewrite untag_unseal tag_unseal /=.
case: t1=> [] // N' t1 /=.
by case: decide => // <- [<-].
Qed.

Lemma untag_tag_ne N1 N2 t :
  N1 ≠ N2 →
  Spec.untag N1 (Spec.tag N2 t) = None.
Proof.
move=> neq; rewrite Spec.untag_unseal Spec.tag_unseal /=.
rewrite decide_False //.
Qed.

Variant untag_spec N t : option term → Type :=
| UntagSome t' of t = Spec.tag N t' : untag_spec N t (Some t')
| UntagNone of (∀ t', t ≠ Spec.tag N t') : untag_spec N t None.

Lemma untagP N t : untag_spec N t (Spec.untag N t).
Proof.
case e: (Spec.untag N t) => [t'|]; constructor.
- by rewrite (Spec.untagK e).
- move=> t' e'; by rewrite e' Spec.tagK in e.
Qed.

Definition to_int t :=
  if t is TInt n then Some n else None.

Variant to_int_spec t : option Z → Type :=
| AsIntSome n of t = TInt n : to_int_spec t (Some n)
| AsIntNone of (∀ n, t ≠ TInt n) : to_int_spec t None.

Lemma to_intP t : to_int_spec t (Spec.to_int t).
Proof. by case: t => *; constructor; congruence. Qed.

Definition untuple t :=
  match t with
  | TPair t1 t2 => Some (t1, t2)
  | _ => None
  end.

Fixpoint proj t n {struct t} :=
  match t, n with
  | TPair t _, 0 => Some t
  | TPair _ t, S n => proj t n
  | _, _ => None
  end.

Definition to_key k : option (key_type * term) :=
  match k with
  | TKey kt t => Some (kt, t)
  | _ => None
  end.

Definition open_key k : option term :=
  match to_key k with
  | Some (kt, t) =>
      match kt with
      | AEnc => Some (TKey ADec t)
      | Sign => Some (TKey Verify t)
      | SEnc => Some (TKey SEnc t)
      | _ => None
      end
  | _ => None
  end.

Lemma open_key_aenc (sk : aenc_key) :
  open_key (Spec.pkey sk) = @Some term sk.
Proof. by rewrite keysE. Qed.

Lemma open_key_sign (sk : sign_key) :
  open_key sk = Some (Spec.pkey sk).
Proof. by rewrite keysE. Qed.

Lemma open_key_senc (sk : senc_key) :
  open_key sk = @Some term sk.
Proof. by rewrite keysE. Qed.

Lemma open_key_aencK pk (sk : aenc_key) :
  open_key pk = @Some term sk → pk = pkey sk.
Proof.
rewrite keysE; case: sk => seed /=.
by case: pk => //= - [] // ?; case=> ->.
Qed.

Lemma open_key_signK k (sk : sign_key) :
  open_key k = Some (Spec.pkey sk) → k = sk.
Proof.
rewrite keysE; case: sk => seed /=.
by case: k => //= - [] // ?; case=> ->.
Qed.

Lemma open_key_sencK k' (k : senc_key) :
  open_key k' = @Some term k → k' = k.
Proof.
rewrite keysE; case: k => seed /=.
by case: k' => //= - [] // ?; case=> ->.
Qed.

Lemma open_key_tsize t1 t2 : open_key t1 = Some t2 → tsize t2 = tsize t1.
Proof.
by case: t1 => // - [] //= t [<-]; rewrite tsizeE.
Qed.

Definition open k t : option term :=
  match t with
  | TSeal k_t t =>
    if decide (open_key k_t = Some k) then Some t else None
  | _ => None
  end.

Variant open_spec k t : option term → Type :=
| OpenSome k_t t'
  of open_key k_t = Some k & t = TSeal k_t t'
  : open_spec k t (Some t')
| OpenNone : open_spec k t None.

Lemma openP k t : open_spec k t (open k t).
Proof.
case: t; eauto using open_spec => k_t t /=.
by case: decide => [e|_]; eauto using open_spec.
Qed.

Definition is_key t :=
  match t with
  | TKey kt _ => Some kt
  | _ => None
  end.

Variant is_key_spec t : option key_type → Type :=
| IsKeySome kt k of t = TKey kt k : is_key_spec t (Some kt)
| IsKeyNone of (∀ kt k, t ≠ TKey kt k) : is_key_spec t None.

Lemma is_keyP t : is_key_spec t (is_key t).
Proof.
case: t; try by right.
by move=> kt t; eleft.
Qed.

Definition has_key_type kt t :=
  match is_key t with
  | Some kt' => bool_decide (kt = kt')
  | None => false
  end.

Definition of_list_aux : seal (foldr TPair (TInt 0)). by eexists. Qed.
Definition of_list := unseal of_list_aux.
Lemma of_list_unseal : of_list = foldr TPair (TInt 0).
Proof. exact: seal_eq. Qed.

Lemma of_list_tsize t ts : t ∈ ts → tsize t < tsize (of_list ts).
Proof.
rewrite of_list_unseal; elim: ts => [/elem_of_nil |t' ts IH /elem_of_cons] //=.
rewrite [tsize (TPair _ _)]tsizeE; case=> [<-|/IH t_ts]; lia.
Qed.

Lemma is_nonce_of_list ts : is_nonce (of_list ts) = false.
Proof. by rewrite of_list_unseal; case: ts. Qed.

Lemma is_exp_of_list ts : is_exp (of_list ts) = false.
Proof. by rewrite of_list_unseal; case: ts. Qed.

Fixpoint to_list t : option (list term) :=
  match t with
  | TInt 0 => Some []
  | TPair t1 t2 =>
    match to_list t2 with
    | Some l => Some (t1 :: l)
    | None => None
    end
  | _ => None
  end.

Lemma of_listK l : to_list (of_list l) = Some l.
Proof. rewrite of_list_unseal; by elim: l => //= t l ->. Qed.

Lemma to_listK t ts :
  to_list t = Some ts →
  t = of_list ts.
Proof.
rewrite of_list_unseal /=; elim/term_ind': t ts => //.
  by case=> [] // _ [<-].
move=> t _ ts' IH /= ts.
case e: to_list => [ts''|] // [<-].
by rewrite /= (IH _ e).
Qed.

Inductive to_list_spec : term → option (list term) → Type :=
| ToListSome ts : to_list_spec (of_list ts) (Some ts)
| ToListNone t  : to_list_spec t None.

Lemma to_listP t : to_list_spec t (to_list t).
Proof.
case e: to_list => [ts|]; last constructor.
by rewrite (to_listK e); constructor.
Qed.

Lemma of_list_inj : Inj eq eq of_list.
Proof.
move=> ts1 ts2 e; apply: Some_inj.
by rewrite -of_listK e of_listK.
Qed.

Definition enc k c t := TSeal k (tag c t).

Definition dec k c t :=
  match open k t with
  | Some t => untag c t
  | None => None
  end.

Variant dec_spec k c t : option term → Type :=
| DecSome k_t t'
  of open_key k_t = Some k
  &  t = TSeal k_t (tag c t')
  : dec_spec k c t (Some t')
| DecNone : dec_spec k c t None.

Lemma decP k c t : dec_spec k c t (dec k c t).
Proof.
rewrite /dec.
case: openP; eauto using dec_spec.
move=> {}k_t {}t e ->.
case: untagP; eauto using dec_spec.
move=> {}t ->; eauto using dec_spec.
Qed.

Lemma decK k1 k2 c t t' :
  open_key k1 = Some k2 →
  dec k2 c t = Some t' →
  t = TSeal k1 (tag c t').
Proof.
rewrite /Spec.dec /=.
case: t => [] //= k_t t.
case: decide => // k_t_k2 k1_k2 /untagK <-.
rewrite /open_key in k_t_k2 k1_k2.
case: k_t k1 => [] // kt1 ? [] //= kt2 ? in k_t_k2 k1_k2 *.
case: kt1 kt2 => [] //= [] //= in k_t_k2 k1_k2 *; congruence.
Qed.

Definition zero : term := TInt 0.

End Spec.

Arguments repr_term /.
Arguments Spec.tag_def /.
Arguments Spec.untag_def /.

#[global]
Existing Instance Spec.of_list_inj.

Lemma subterm_tag c t1 t2 : subterm t1 t2 → subterm t1 (Spec.tag c t2).
Proof. by rewrite Spec.tag_unseal; eauto using subterm. Qed.

#[global]
Hint Resolve STRefl : core.

Global Instance invs_canceled_proper : Proper ((≡ₚ) ==> iff) invs_canceled.
Proof. move => ts1 ts2 e; exact: perm_invs_canceled. Qed.

Lemma invs_canceled1 t : negb (is_mul t) -> invs_canceled [t].
Proof. exact: invs_canceled_Nmul1. Qed.

Lemma invs_canceled2 t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) ->
  invs_canceled [t1 ; t2] ↔ (t1 ≠ TInv t2).
Proof. exact: invs_canceled2_Nmul. Qed.

Lemma exps_TExpN t ts :
  atomic ts -> exps (TExpN t ts) ≡ₚ cancel_invs (exps t ++ ts).
Proof.
move => atom.
rewrite (exps_TExpN_sort t ts atom).
exact: (merge_sort_Permutation term_order (cancel_invs (exps t ++ ts))).
Qed.

Lemma TExp_TExpN t1 ts1 t2 : TExp (TExpN t1 ts1) t2 = TExpN t1 (t2 :: ts1).
Proof.
have -> : TExp (TExpN t1 ts1) t2 = TExpN (TExpN t1 ts1) [t2].
  by rewrite /TExpN TMulN1.
rewrite TExpNA; apply: TExpN_perm.
by rewrite -Permutation_cons_append.
Qed.

Lemma count_exp_TExpNW t1 t2 ts :
  atomic ts ->
  (∀ t, t ∈ ts → t1 ≠ TInv t) →
  (count_exp t1 t2 ≤ count_exp t1 (TExpN t2 ts))%Z.
Proof.
elim: ts => [|t ts IH]; first by move => _ _; rewrite TExpN0; lia.
move => atom t1_ts.
move: atom => /Forall_cons [Nmt atom'].
rewrite -TExp_TExpN; set t2' := TExpN t2 ts.
have ?: (count_exp t1 t2' ≤ count_exp t1 (TExp t2' t))%Z.
  apply: (count_exp_TExpW Nmt); move/(_ t): t1_ts; apply.
  rewrite elem_of_cons; by eauto.
suff: (count_exp t1 t2 ≤ count_exp t1 t2')%Z by lia.
apply: (IH atom') => t' t'_ts; apply: t1_ts; rewrite elem_of_cons; eauto.
Qed.

Lemma elem_of_TExpN2l g t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) ->
  t1 ≠ TInv t2 →
  TInv t1 ∉ exps g →
  t1 ∈ exps (TExpN g [t1; t2]).
Proof.
move=> Nm1 Nm2 t1_t2 t1_g.
rewrite (not_elem_of_TInv_exps _ Nm1) -count_exp_gt0 in t1_g.
have e : TExpN g [t1; t2] = TExp (TExp g t1) t2.
  rewrite (_ : TExp g t1 = TExpN g [t1]); last by rewrite /TExpN TMulN1.
  rewrite TExp_TExpN; exact: TExpC2.
rewrite e -count_exp_gt0 (count_exp_TExp t1 (TExp g t1) Nm2).
rewrite (@decide_False _ (t1 = TInv t2)); last exact: t1_t2.
by case: decide; lia.
Qed.

Lemma elem_of_TExpN2r g t1 t2 :
  negb (is_mul t1) -> negb (is_mul t2) ->
  t1 ≠ TInv t2 →
  TInv t2 ∉ exps g →
  t2 ∈ exps (TExpN g [t1; t2]).
Proof.
move=> Nm1 Nm2 t1_t2 t2_g.
rewrite TExpC2.
apply: (elem_of_TExpN2l Nm2 Nm1); last exact: t2_g.
by move=> contra; apply: t1_t2; rewrite contra TInvK.
Qed.

Lemma base_expN t : ¬ is_exp t → base t = t.
Proof. move=> tNX; apply: base_expN_bool; apply/negb_True; exact: tNX. Qed.

Lemma exps_expN t : ¬ is_exp t → exps t = [].
Proof. move=> tNX; apply: exps_expN_bool; apply/negb_True; exact: tNX. Qed.

Lemma exps_TExpN' t ts :
  ¬ is_exp t -> atomic ts ->
  invs_canceled ts ->
  exps (TExpN t ts) ≡ₚ ts.
Proof.
move => tNexp atom canc.
by rewrite (@exps_TExpN t ts atom) (exps_expN tNexp) app_nil_l
   (cancel_invs_canceled ts atom canc).
Qed.

Lemma is_exp_base t : ¬ is_exp (base t).
Proof. apply/negb_True; exact: is_exp_base_bool. Qed.
Hint Resolve is_exp_base : core.

(* Re-export the [Set Implicit Arguments] argument structure that the old
   with_stdpp.v restatements provided for these lemmas, so downstream callers
   that pass only the hypotheses keep working. *)
Arguments cancel_invs_canceled {ts} _ _.
Arguments tsize_lt_TExp {t1 t2} _ _.
Arguments tsize_TExp_TInv {t1 t2} _ _.
