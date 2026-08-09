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
| TNonFree pt of PreTerm.wf pt & is_non_free pt.

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

Implicit Types (t k : term) (ts : list term).

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

Fixpoint fold_term_predef pt :=
  match pt with
  | PreTerm.PT0 (O0Int n) => TInt n
  | PreTerm.PT2 O2Pair pt1 pt2 => TPair (fold_term_predef pt1) (fold_term_predef pt2)
  | PreTerm.PT0 (O0Nonce l) => TNonce l
  | PreTerm.PT1 (O1Key kt) pt => TKey kt (fold_term_predef pt)
  | PreTerm.PT2 O2Seal k pt => TSeal (fold_term_predef k) (fold_term_predef pt)
  | PreTerm.PT1 O1Hash pt => THash (fold_term_predef pt)
  | PreTerm.PT1 O1Inv pt' =>
    if decide (PreTerm.wf (PreTerm.PT1 O1Inv pt')) is left pf then
      TNonFree (PreTerm.PT1 O1Inv pt') pf I
    else TInt 0 (*should never*)
  | PreTerm.PTExp b e =>
    if decide (PreTerm.wf (PreTerm.PTExp b e)) is left pf then
      TNonFree (PreTerm.PTExp b e) pf I
    else TInt 0 (*should never*)
  | PreTerm.PTMul ts =>
    if decide (PreTerm.wf (PreTerm.PTMul ts)) is left pf then
      TNonFree (PreTerm.PTMul ts) pf I
    else TInt 0 (*should never*)
  end.

lock Definition fold_term pt := fold_term_predef (PreTerm.normalize pt).

Lemma wf_unfold_term t : PreTerm.wf (unfold_term t).
Proof.
elim/term_ind': t.
- by move=> z.
- by move=> t1 IH1 t2 IH2 /=; apply/andb_True; split.
- by move=> a.
- by move=> kt t IH.
- by move=> t1 IH1 t2 IH2 /=; apply/andb_True; split.
- by move=> t IH.
- by move=> pt w nf; exact: w.
Qed.

Lemma wf_unfold_terms ts : Forall (fun pt => PreTerm.wf pt) (unfold_term <$> ts).
Proof.
elim: ts => /= [|t ts IH]; first by constructor.
by constructor; [exact: wf_unfold_term|exact: IH].
Qed.

Lemma TNonFree_irr pt (w1 w2 : PreTerm.wf pt) (n1 n2 : is_non_free pt) :
  TNonFree pt w1 n1 = TNonFree pt w2 n2.
Proof. by rewrite (proof_irrel w1 w2) (proof_irrel n1 n2). Qed.

Lemma fold_predef_NonFree {pt} (wf : PreTerm.wf pt) (nf : is_non_free pt) :
  fold_term_predef pt = TNonFree pt wf nf.
Proof.
case: pt wf nf => [o|[kt||] pt'|[||] b e|ts] wf nf.
1,2,3,5,6: by move: nf; rewrite /is_non_free /=.
- rewrite /=; case: (decide (PreTerm.wf (PreTerm.PTInv pt'))) => [pf'|npf];
    last by case: (npf wf).
  exact: TNonFree_irr.
- rewrite /=; case: (decide (PreTerm.wf (PreTerm.PTExp b e))) => [pf'|npf];
    last by case: (npf wf).
  exact: TNonFree_irr.
- rewrite /=; case: (decide (PreTerm.wf (PreTerm.PTMul ts))) => [pf'|npf];
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
  by rewrite (fold_predef_NonFree wf_t I).
- move => [] t1 IH1 t2 IH2 wf.
  + by move: wf; rewrite /= => /andb_True [w1 w2]; rewrite (IH1 w1) (IH2 w2).
  + by move: wf; rewrite /= => /andb_True [w1 w2]; rewrite (IH1 w1) (IH2 w2).
  + by rewrite (fold_predef_NonFree wf I).
- by move => ts IHts wf; rewrite (fold_predef_NonFree wf I).
Qed.

Lemma fold_termK pt : PreTerm.wf pt -> unfold_term (fold_term pt) = pt.
Proof.
by move=> wf; rewrite unfold_fold (PreTerm.normalize_wf _ wf).
Qed.

Lemma fmap_fold_termK pts :
  Forall (fun pt => PreTerm.wf pt) pts ->
  unfold_term <$> (fold_term <$> pts) = pts.
Proof.
move=> /list.Forall_forall wfs. rewrite -list_fmap_compose -[RHS]list_fmap_id.
by apply/Forall_fmap_ext/Forall_forall=> pt /wfs ?; rewrite /= fold_termK.
Qed.

Lemma fmap_unfold_termK ts : fold_term <$> (unfold_term <$> ts) = ts.
Proof.
rewrite -list_fmap_compose -[RHS]list_fmap_id.
apply/Forall_fmap_ext/list.Forall_forall => t _; exact: unfold_termK.
Qed.

Lemma fold_normalize pt : fold_term (PreTerm.normalize pt) = fold_term pt.
Proof. by rewrite -unfold_fold unfold_termK. Qed.

Global Instance unfold_term_inj : Inj (=) (=) unfold_term.
Proof. by move=> t1 t2 /(f_equal fold_term); rewrite !unfold_termK. Qed.

Global Instance term_eq_dec : EqDecision term :=
  inj_eq_dec unfold_term.

Global Instance term_countable : Countable term :=
  inj_countable' unfold_term fold_term unfold_termK.

Global Instance term_inhabited : Inhabited term.
Proof. exact: (populate (TInt 0)). Qed.

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

Canonical termO := leibnizO term.

Global Instance aenc_key_eq_dec : EqDecision aenc_key.
Proof. solve_decision. Defined.
Global Instance aenc_key_countable : Countable aenc_key.
Proof. apply: (inj_countable' seed_of_aenc_key AEncKey); by case. Qed.
Global Instance aenc_key_inhabited : Inhabited aenc_key :=
  populate (AEncKey inhabitant).

Global Instance sign_key_eq_dec : EqDecision sign_key.
Proof. solve_decision. Defined.
Global Instance sign_key_countable : Countable sign_key.
Proof. apply: (inj_countable' seed_of_sign_key SignKey); by case. Qed.
Global Instance sign_key_inhabited : Inhabited sign_key :=
  populate (SignKey inhabitant).

Global Instance senc_key_eq_dec : EqDecision senc_key.
Proof. solve_decision. Defined.
Global Instance senc_key_countable : Countable senc_key.
Proof. apply: (inj_countable' seed_of_senc_key SEncKey); by case. Qed.
Global Instance senc_key_inhabited : Inhabited senc_key :=
  populate (SEncKey inhabitant).

Lemma normalize_unfold t :
  PreTerm.normalize (unfold_term t) = unfold_term t.
Proof. by rewrite (PreTerm.normalize_wf _ (wf_unfold_term t)). Qed.

Lemma fmap_normalize_unfold ts :
  PreTerm.normalize <$> (unfold_term <$> ts) = unfold_term <$> ts.
Proof.
rewrite -{2}(list_fmap_id (unfold_term <$> ts)).
apply: Forall_fmap_ext_1. apply/Forall_forall => pt.
move=> /list_elem_of_fmap [t [-> _]]; exact: normalize_unfold.
Qed.

lock Definition TInv t := fold_term (PreTerm.inv (unfold_term t)).

lock Definition TExp b e :=
  fold_term (PreTerm.exp (unfold_term b) (unfold_term e)).

lock Definition TMulN ts :=
  fold_term (PreTerm.mul (unfold_term <$> ts)).

Definition TExpN t ts := TExp t (TMulN ts).

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
Definition factors t := fold_term <$> PreTerm.factors (unfold_term t).

Definition is_nonce t :=
  if t is TNonce _ then true else false.

Definition is_inv t :=
  if t is TNonFree pt _ _ then PreTerm.is_inv pt else false.

Definition is_exp t :=
  if t is TNonFree pt _ _ then PreTerm.is_exp pt else false.

Definition is_mul t :=
  if t is TNonFree pt _ _ then PreTerm.is_mul pt else false.

Lemma is_nonce_unfold t : is_nonce t = PreTerm.is_nonce (unfold_term t).
Proof. by case: t => //= pt _ nf; move: nf; case: pt. Qed.

Lemma is_inv_unfold t : is_inv t = PreTerm.is_inv (unfold_term t).
Proof. by case: t. Qed.

Lemma is_exp_unfold t : is_exp t = PreTerm.is_exp (unfold_term t).
Proof. by case: t. Qed.

Lemma is_mul_unfold t : is_mul t = PreTerm.is_mul (unfold_term t).
Proof. by case: t. Qed.

Lemma unfold_TInv_Nmul {t} :
  negb (is_mul t) -> unfold_term (TInv t) = PreTerm.inv_aux (unfold_term t).
Proof.
rewrite is_mul_unfold => Nm.
by rewrite unfold_TInv (PreTerm.inv_Nmul _ Nm).
Qed.

Lemma is_inv_TInv t : negb (is_mul t) -> is_inv (TInv t) = negb (is_inv t).
Proof.
move => Nm; rewrite !is_inv_unfold (unfold_TInv_Nmul Nm).
move: (wf_unfold_term t); case: (unfold_term t) => [o|[k||] pt'|o t1 t2|ts] /= wf //.
by move: wf => /andb_True [/andb_True [/negb_True/Is_true_false_1 -> _] _].
Qed.

Lemma is_exp_TInv t : negb (is_mul t) -> negb (is_inv t) -> negb (is_exp (TInv t)).
Proof.
move => Nm; rewrite is_inv_unfold => Ni.
by rewrite is_exp_unfold (unfold_TInv_Nmul Nm) (PreTerm.inv_invN _ Ni).
Qed.

Lemma Nmul_TInv {t} : negb (is_mul t) -> negb (is_mul (TInv t)).
Proof.
move => Nm; rewrite is_mul_unfold (unfold_TInv_Nmul Nm).
exact: (PreTerm.is_mul_inv_aux _ (wf_unfold_term t)).
Qed.

Lemma unfold_factors t :
  unfold_term <$> factors t = PreTerm.factors (unfold_term t).
Proof.
rewrite /factors fmap_fold_termK //.
exact: (PreTerm.wf_factors _ (wf_unfold_term t)).
Qed.

Lemma count_factors_unfold {t} Y :
  negb (is_mul t) ->
  SMS.count TInv t (factors Y) =
  SMS.count PreTerm.inv_aux (unfold_term t) (PreTerm.factors (unfold_term Y)).
Proof.
move=> Nt; rewrite -unfold_factors.
by rewrite (SMS.count_fmap TInv PreTerm.inv_aux unfold_term t (factors Y)
              (@unfold_term_inj) (unfold_TInv_Nmul Nt)).
Qed.

Lemma count_factors_TInv t t' :
  negb (is_mul t) →
  SMS.count TInv t (factors (TInv t')) = (- SMS.count TInv t (factors t'))%Z.
Proof.
move=> Nm; rewrite !count_factors_unfold // unfold_TInv.
rewrite PreTerm.count_factors_inv //; exact: wf_unfold_term.
Qed.

Lemma count_factors_TMulN t t' ts :
  negb (is_mul t) →
  SMS.count TInv t (factors (TMulN (t' :: ts))) =
  (SMS.count TInv t (factors t') + SMS.count TInv t (factors (TMulN ts)))%Z.
Proof.
move=> Nm.
rewrite (count_factors_unfold (TMulN (t' :: ts)) Nm)
        (count_factors_unfold t' Nm) (count_factors_unfold (TMulN ts) Nm)
        !unfold_TMulN fmap_cons.
exact: (PreTerm.count_factors_mul _ _ _
          (wf_unfold_term t) (wf_unfold_term t') (wf_unfold_terms ts)).
Qed.

Lemma count_factors_inj t1 t2 :
  (forall x, negb (is_mul x) ->
     SMS.count TInv x (factors t1) = SMS.count TInv x (factors t2)) ->
  t1 = t2.
Proof.
move=> ecount; apply: unfold_term_inj.
apply: (PreTerm.count_factors_inj _ _ (wf_unfold_term t1) (wf_unfold_term t2)).
move=> pt Npt wfpt.
have wfE : unfold_term (fold_term pt) = pt := fold_termK pt wfpt.
have Nx : negb (is_mul (fold_term pt)) by rewrite is_mul_unfold wfE.
rewrite -wfE -(count_factors_unfold t1 Nx) -(count_factors_unfold t2 Nx).
exact: (ecount _ Nx).
Qed.

Lemma unfold_base t : unfold_term (base t) = PreTerm.base (unfold_term t).
Proof.
by rewrite /base unfold_fold
  (PreTerm.normalize_wf _ (PreTerm.wf_base _ (wf_unfold_term t))).
Qed.

Lemma unfold_exps t :
  unfold_term <$> exps t = PreTerm.exps (unfold_term t).
Proof.
rewrite /exps fmap_fold_termK //.
exact: (PreTerm.wf_exps _ (wf_unfold_term t)).
Qed.

Lemma factors_one : factors (TMulN []) = [].
Proof.
have /list_fmap_eq_inj :
    unfold_term <$> factors (TMulN []) = unfold_term <$> [] => //.
by rewrite unfold_factors unfold_TMulN.
Qed.

Lemma map_unfold_Nmul ts :
  Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts) <->
  Forall (fun t => negb (is_mul t)) ts.
Proof.
rewrite Forall_fmap; apply: Forall_iff => t; by rewrite is_mul_unfold.
Qed.

Lemma factors_inj t1 t2 : factors t1 = factors t2 -> t1 = t2.
Proof.
move=> efactors; apply: unfold_term_inj.
apply: PreTerm.factors_inj.
- exact: wf_unfold_term.
- exact: wf_unfold_term.
by rewrite -!unfold_factors efactors.
Qed.

Lemma factors_atomic t : negb (is_mul t) -> factors t = [t].
Proof.
move=> Nt; apply: (inj (fmap unfold_term)); rewrite unfold_factors.
have Nt' : negb (PreTerm.is_mul (unfold_term t)) by rewrite -is_mul_unfold.
by rewrite (PreTerm.factorsN _ Nt').
Qed.

Lemma count_factors_TMulN_concat x ts :
  negb (is_mul x) ->
  SMS.count TInv x (factors (TMulN ts)) =
  SMS.count TInv x (concat (factors <$> ts)).
Proof.
move=> Nx; elim: ts => [|u ts IH].
- by rewrite factors_one.
- rewrite fmap_cons concat_cons (count_factors_TMulN x u ts Nx) IH.
  by rewrite (SMS.count_app TInv x (factors u) (concat (factors <$> ts))).
Qed.

Definition atomic (ts : list term) : Prop := Forall (fun t => negb (is_mul t)) ts.

Lemma atomic_unfold ts :
  atomic ts -> Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts).
Proof. rewrite /atomic; exact: (proj2 (map_unfold_Nmul ts)). Qed.

Lemma atom_factors t : atomic (factors t).
Proof.
apply/Forall_forall => x x_t; rewrite is_mul_unfold.
have /list.Forall_forall H := PreTerm.Nmul_factors _ (wf_unfold_term t).
apply: H; rewrite -unfold_factors; apply: list_elem_of_fmap_2; exact: x_t.
Qed.

Lemma fmap_TInv_fold_term pts :
  Forall PreTerm.wf pts ->
  Forall (fun pt => negb (PreTerm.is_mul pt)) pts ->
  TInv <$> (fold_term <$> pts) = fold_term <$> (PreTerm.inv_aux <$> pts).
Proof.
elim: pts => [//|pt pts IH] /Forall_cons [Wpt wfs] /Forall_cons [Nmpt Nms].
rewrite !fmap_cons (IH wfs Nms); congr cons.
apply: unfold_term_inj.
by rewrite unfold_TInv (fold_termK pt Wpt)
           (fold_termK (PreTerm.inv_aux pt) (PreTerm.wf_inv_aux pt Wpt Nmpt))
           (PreTerm.inv_Nmul pt Nmpt).
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
  (H8 : forall t1, T t1 ->
        forall t2, T t2 ->
                   negb (is_exp t1) ->
                   t2 ≠ TMulN [] ->
        T (TExp t1 t2))
  (H9 : forall ts, foldr (fun t R => T t * R)%type unit ts ->
                   atomic ts ->
                   (forall t', t' ∈ ts -> TInv t' ∉ ts) ->
                   length ts ≠ 1 ->
        T (TMulN ts)) :
  forall t, T t.
Proof.
move=> t; rewrite -(unfold_termK t).
elim: (unfold_term t) (wf_unfold_term t)=>
  {t} [o|o pt IHpt|o pt1 IHpt1 pt2 IHpt2|ts IHts] wfpt.
- case: o wfpt => [n|l] _; rewrite fold_termE /=; [exact: H1|exact: H3].
- case: o wfpt => [kt| |]; rewrite fold_termE /=.
  + by move=> wfpt; exact: (H4 kt _ (IHpt wfpt)).
  + by move=> wfpt; exact: (H6 _ (IHpt wfpt)).
  + move=> /andb_True [/andb_True [Ninv Nmul] wfpt].
    apply: (H7 _ (IHpt wfpt)).
    * by rewrite is_mul_unfold (fold_termK _ wfpt).
    * by rewrite is_inv_unfold (fold_termK _ wfpt).
- case: o wfpt => [||]; rewrite fold_termE /=.
  + by move=> /andb_True [w1 w2]; exact: (H2 _ (IHpt1 w1) _ (IHpt2 w2)).
  + by move=> /andb_True [w1 w2]; exact: (H5 _ (IHpt1 w1) _ (IHpt2 w2)).
  + move=> /andb_True [/andb_True [/andb_True [w1 Nexp1] w2] Hne].
    have pt2N : pt2 ≠ PreTerm.PTMul [] := bool_decide_unpack _ Hne.
    apply: (H8 _ (IHpt1 w1) _ (IHpt2 w2)).
    * by rewrite is_exp_unfold (fold_termK _ w1).
    * have E0 : TMulN [] = fold_term (PreTerm.PTMul []) by rewrite fold_termE.
      rewrite E0 => Heq; apply: pt2N.
      by move: (f_equal unfold_term Heq);
        rewrite (fold_termK _ w2) (fold_termK _ PreTerm.wf_nil) => ->.
- have [wfts [Nmts [sms lenN1]]] := PreTerm.wf_Mul_inv _ wfpt.
  rewrite fold_termE; apply: H9.
  + elim: ts IHts wfts {wfpt Nmts sms lenN1} => [//|pt ts' IH] /=.
    move=> [IHpt IHts'] /Forall_cons [w ws].
    by split; [exact: (IHpt w)|exact: (IH IHts' ws)].
  + move/list.Forall_forall in wfts.
    move/list.Forall_forall in Nmts.
    apply/Forall_fmap/list.Forall_forall => t t_ts /=.
    rewrite /= is_mul_unfold fold_termK //; eauto.
  + move=> _ /list_elem_of_fmap [t [] -> t_ts] tV_ts.
    move/SMS.wf_no_pairs in sms; apply: sms (t_ts) _.
    rewrite -[ts]fmap_fold_termK //; apply/list_elem_of_fmap.
    exists (TInv (fold_term t)); split => //.
    have wft: PreTerm.wf t by move/list.Forall_forall: wfts; exact.
    rewrite unfold_TInv_Nmul ?fold_termK //.
    rewrite is_mul_unfold // fold_termK //.
    move/list.Forall_forall: Nmts; exact.
  + by rewrite length_fmap.
Qed.

Definition term_ind (P : term -> Prop) := @term_rect P.
