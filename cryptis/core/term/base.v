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

(* The five "non-free" operations — the two inverses, the two products and
   exponentiation — are represented indirectly, by a well-formed pre-term whose
   head is one of [O1Inv] / [O1GInv] / [PTExp] / [PTMul] / [PTGMul].
   [is_non_free] recognises exactly those heads; it lives in [PreTerm] alongside
   [is_gnon_free], the smaller predicate [wf] uses for the base of a normal-form
   exponential. *)
Notation is_non_free := PreTerm.is_non_free.

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
  | PreTerm.PT1 O1GInv pt' =>
    if decide (PreTerm.wf (PreTerm.PT1 O1GInv pt')) is left pf then
      TNonFree (PreTerm.PT1 O1GInv pt') pf I
    else TInt 0 (*should never*)
  | PreTerm.PTExp b e =>
    if decide (PreTerm.wf (PreTerm.PTExp b e)) is left pf then
      TNonFree (PreTerm.PTExp b e) pf I
    else TInt 0 (*should never*)
  | PreTerm.PTMul ts =>
    if decide (PreTerm.wf (PreTerm.PTMul ts)) is left pf then
      TNonFree (PreTerm.PTMul ts) pf I
    else TInt 0 (*should never*)
  | PreTerm.PTGMul ts =>
    if decide (PreTerm.wf (PreTerm.PTGMul ts)) is left pf then
      TNonFree (PreTerm.PTGMul ts) pf I
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
Hint Resolve wf_unfold_term : core.

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
case: pt wf nf => [o|[kt|||] pt'|[||] b e|[|] ts] wf nf.
1,2,3,6,7: by move: nf; rewrite /is_non_free /=.
- rewrite /=; case: (decide (PreTerm.wf (PreTerm.PTInv pt'))) => [pf'|npf];
    last by case: (npf wf).
  exact: TNonFree_irr.
- rewrite /=; case: (decide (PreTerm.wf (PreTerm.PTGInv pt'))) => [pf'|npf];
    last by case: (npf wf).
  exact: TNonFree_irr.
- rewrite /=; case: (decide (PreTerm.wf (PreTerm.PTExp b e))) => [pf'|npf];
    last by case: (npf wf).
  exact: TNonFree_irr.
- rewrite /=; case: (decide (PreTerm.wf (PreTerm.PTMul ts))) => [pf'|npf];
    last by case: (npf wf).
  exact: TNonFree_irr.
- rewrite /=; case: (decide (PreTerm.wf (PreTerm.PTGMul ts))) => [pf'|npf];
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
- move => [?|||] t IH wf_t; try by rewrite /= IH.
  + by rewrite (fold_predef_NonFree wf_t I).
  + by rewrite (fold_predef_NonFree wf_t I).
- move => [] t1 IH1 t2 IH2 wf.
  + by move: wf; rewrite /= => /andb_True [w1 w2]; rewrite (IH1 w1) (IH2 w2).
  + by move: wf; rewrite /= => /andb_True [w1 w2]; rewrite (IH1 w1) (IH2 w2).
  + by rewrite (fold_predef_NonFree wf I).
- by move => [|] ts IHts wf; rewrite (fold_predef_NonFree wf I).
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

(* The Diffie-Hellman group: [TGInv] / [TGMulN] are the same construction as
   [TInv] / [TMulN] at the group operations.  They live in the *base* of an
   exponential, where [TExp] distributes over them; [TInv] / [TMulN] live in the
   exponent, where it does not. *)
lock Definition TGInv t := fold_term (PreTerm.ginv (unfold_term t)).

lock Definition TGMulN ts :=
  fold_term (PreTerm.gmul (unfold_term <$> ts)).

Definition TExpN t ts := TExp t (TMulN ts).

Lemma unfold_TInv t : unfold_term (TInv t) = PreTerm.inv (unfold_term t).
Proof.
rewrite unlock unfold_fold PreTerm.normalize_wf //.
rewrite -(PreTerm.normalize_wf (unfold_term t)) //.
apply: PreTerm.wf_inv.
exact: PreTerm.wf_normalize.
Qed.

Lemma unfold_TExp b e :
  unfold_term (TExp b e) = PreTerm.exp (unfold_term b) (unfold_term e).
Proof.
rewrite unlock unfold_fold PreTerm.normalize_wf //.
rewrite -(PreTerm.normalize_wf (unfold_term b)) //.
rewrite -(PreTerm.normalize_wf (unfold_term e)) //.
apply: PreTerm.wf_exp.
- exact: PreTerm.wf_normalize.
- exact: PreTerm.wf_normalize.
Qed.

Lemma unfold_TMulN ts :
  unfold_term (TMulN ts) = PreTerm.mul (unfold_term <$> ts).
Proof.
rewrite unlock unfold_fold PreTerm.normalize_wf //.
apply: PreTerm.wf_mul; rewrite Forall_fmap Forall_forall.
by eauto.
Qed.

Lemma unfold_TGInv t : unfold_term (TGInv t) = PreTerm.ginv (unfold_term t).
Proof.
rewrite unlock unfold_fold PreTerm.normalize_wf //.
rewrite -(PreTerm.normalize_wf (unfold_term t)) //.
apply: PreTerm.wf_ginv.
exact: PreTerm.wf_normalize.
Qed.

Lemma unfold_TGMulN ts :
  unfold_term (TGMulN ts) = PreTerm.gmul (unfold_term <$> ts).
Proof.
rewrite unlock unfold_fold PreTerm.normalize_wf //.
apply: PreTerm.wf_gmul; rewrite Forall_fmap Forall_forall.
by eauto.
Qed.

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
  | PreTerm.PT1 O1GInv pt => TGInv (fold_term pt)
  | PreTerm.PTExp b e => TExp (fold_term b) (fold_term e)
  | PreTerm.PTMul ts => TMulN (fold_term <$> ts)
  | PreTerm.PTGMul ts => TGMulN (fold_term <$> ts)
  end.
Proof.
have fmapE (ts : list PreTerm.pre_term) :
    unfold_term <$> (fold_term <$> ts) = PreTerm.normalize <$> ts.
  rewrite -(list_fmap_compose fold_term unfold_term).
  apply: Forall_fmap_ext_1; apply/Forall_forall => pt0 _; exact: (unfold_fold pt0).
apply /unfold_term_inj.
case: pt => /=;
  try by case =>> //=; rewrite ?unfold_TInv ?unfold_TGInv !unfold_fold.
- by move=> [] >; rewrite /= ?unfold_TExp !unfold_fold.
- by move=> [|] ts; rewrite unfold_fold ?unfold_TMulN ?unfold_TGMulN fmapE.
Qed.

Definition base t := fold_term (PreTerm.base (unfold_term t)).
Definition expo t := fold_term (PreTerm.expo (unfold_term t)).
Definition factors t := fold_term <$> PreTerm.factors (unfold_term t).
Definition gfactors t := fold_term <$> PreTerm.gfactors (unfold_term t).

Definition is_nonce t :=
  if t is TNonce _ then true else false.

Definition is_inv t :=
  if t is TNonFree pt _ _ then PreTerm.is_inv pt else false.

Definition is_exp t :=
  if t is TNonFree pt _ _ then PreTerm.is_exp pt else false.

Definition is_mul t :=
  if t is TNonFree pt _ _ then PreTerm.is_mul pt else false.

Definition is_ginv t :=
  if t is TNonFree pt _ _ then PreTerm.is_ginv pt else false.

Definition is_gmul t :=
  if t is TNonFree pt _ _ then PreTerm.is_gmul pt else false.

(* The exponent-side counterpart of [PreTerm.is_gnon_free]: the heads an
   exponent may have that are not free.  [is_non_free] collects all five
   operations, [is_gnon_free] the group ones ([TGInv], [TExp], [TGMul]), and
   [is_enon_free] the exponent ones ([TInv], [TMul]).  Nonces, hashes and the
   other free constructors satisfy [negb (is_enon_free _)], which is what makes
   the signed-count reasoning of [core/term/algebra.v] apply to them. *)
Definition is_enon_free t := is_inv t || is_mul t.

Lemma is_nonce_unfold t : is_nonce t = PreTerm.is_nonce (unfold_term t).
Proof. by case: t => //= pt _ nf; move: nf; case: pt. Qed.

Lemma is_inv_unfold t : is_inv t = PreTerm.is_inv (unfold_term t).
Proof. by case: t. Qed.

Lemma is_exp_unfold t : is_exp t = PreTerm.is_exp (unfold_term t).
Proof. by case: t. Qed.

Lemma is_mul_unfold t : is_mul t = PreTerm.is_mul (unfold_term t).
Proof. by case: t. Qed.

Lemma is_ginv_unfold t : is_ginv t = PreTerm.is_ginv (unfold_term t).
Proof. by case: t. Qed.

Lemma is_gmul_unfold t : is_gmul t = PreTerm.is_gmul (unfold_term t).
Proof. by case: t. Qed.

Lemma Nenf_Ninv t : negb (is_enon_free t) → negb (is_inv t).
Proof. by rewrite /is_enon_free; case: (is_inv t) => //=. Qed.

Lemma Nenf_Nmul t : negb (is_enon_free t) → negb (is_mul t).
Proof. by rewrite /is_enon_free; case: (is_inv t) => //=. Qed.

Lemma Nenf_TNonce a : negb (is_enon_free (TNonce a)).
Proof. by []. Qed.

Lemma Nenf_THash t : negb (is_enon_free (THash t)).
Proof. by []. Qed.

Lemma unfold_base t : unfold_term (base t) = PreTerm.base (unfold_term t).
Proof. rewrite /base fold_termK //; exact: PreTerm.wf_base. Qed.

Lemma unfold_expo t : unfold_term (expo t) = PreTerm.expo (unfold_term t).
Proof. rewrite /expo fold_termK //; exact: PreTerm.wf_expo. Qed.

Lemma unfold_factors t :
  unfold_term <$> factors t = PreTerm.factors (unfold_term t).
Proof.
rewrite /factors fmap_fold_termK //; apply/list.Forall_forall => t0 t0_in.
apply: PreTerm.wf_factors_wf t0_in.
exact: PreTerm.wf_wf_factors.
Qed.

Lemma unfold_gfactors t :
  unfold_term <$> gfactors t = PreTerm.gfactors (unfold_term t).
Proof.
rewrite /gfactors fmap_fold_termK //; apply/list.Forall_forall => t0 t0_in.
apply: PreTerm.wf_gfactors_wf t0_in.
exact: PreTerm.wf_wf_gfactors.
Qed.

Lemma is_mulE t : is_mul t = bool_decide (length (factors t) ≠ 1).
Proof.
rewrite -(length_fmap unfold_term) unfold_factors is_mul_unfold.
case: (unfold_term t) (wf_unfold_term t) => [o|o t'|o t1 t2|[|] ts] //=.
by rewrite andb_True; case=> _ /Is_true_true ->.
Qed.

Lemma is_gmulE t : is_gmul t = bool_decide (length (gfactors t) ≠ 1).
Proof.
rewrite -(length_fmap unfold_term) unfold_gfactors is_gmul_unfold.
case: (unfold_term t) (wf_unfold_term t) => [o|o t'|o t1 t2|[|] ts] //=.
by rewrite andb_True; case=> _ /Is_true_true ->.
Qed.

Lemma is_inv_TInv t : negb (is_mul t) → is_inv (TInv t) = negb (is_inv t).
Proof.
rewrite !is_inv_unfold is_mul_unfold unfold_TInv.
case: {t} (unfold_term t) (wf_unfold_term t) => [|||[|] ts] //=.
by case=> //= t; case: PreTerm.is_inv.
Qed.

Lemma is_ginv_TGInv t : negb (is_gmul t) → is_ginv (TGInv t) = negb (is_ginv t).
Proof.
rewrite !is_ginv_unfold is_gmul_unfold unfold_TGInv.
case: {t} (unfold_term t) (wf_unfold_term t) => [|||[|] ts] //=.
by case=> //= t; case: PreTerm.is_ginv.
Qed.

Lemma is_exp_TInv t : negb (is_mul t) → negb (is_inv t) → negb (is_exp (TInv t)).
Proof.
rewrite is_mul_unfold is_inv_unfold is_exp_unfold unfold_TInv.
move=> Nm Ni; rewrite PreTerm.inv_Nmul //.
case: (unfold_term t) Nm Ni => [|||[|] ts] //=.
by case=> //=.
Qed.

Lemma is_exp_TGInv t :
  negb (is_gmul t) → negb (is_ginv t) → negb (is_exp (TGInv t)).
Proof.
rewrite is_gmul_unfold is_ginv_unfold is_exp_unfold unfold_TGInv.
move=> Nm Ni; rewrite PreTerm.ginv_Ngmul //.
case: (unfold_term t) Nm Ni => [|||[|] ts] //=.
by case=> //=.
Qed.

Lemma factors_inj t1 t2 : factors t1 = factors t2 → t1 = t2.
Proof.
move/(f_equal (λ ts : list _, unfold_term <$> ts)).
rewrite !unfold_factors => e.
apply: unfold_term_inj => /=.
move: (unfold_term t2) (wf_unfold_term t2) => {}t2 wf2 in e *.
move: (unfold_term t1) (wf_unfold_term t1) => {}t1 wf1 in e *.
case: t1 t2 => [o1|o1 t1|o1 t11 t12|[|] ts1] [o2|o2 t2|o2 t21 t22|[|] ts2] //=
  in wf1 wf2 e *;
do 1?congruence;
by [rewrite -e /= andb_false_r in wf2 | rewrite e /= andb_false_r in wf1].
Qed.

Lemma gfactors_inj t1 t2 : gfactors t1 = gfactors t2 → t1 = t2.
Proof.
move/(f_equal (λ ts : list _, unfold_term <$> ts)).
rewrite !unfold_gfactors => e.
apply: unfold_term_inj => /=.
move: (unfold_term t2) (wf_unfold_term t2) => {}t2 wf2 in e *.
move: (unfold_term t1) (wf_unfold_term t1) => {}t1 wf1 in e *.
case: t1 t2 => [o1|o1 t1|o1 t11 t12|[|] ts1] [o2|o2 t2|o2 t21 t22|[|] ts2] //=
  in wf1 wf2 e *;
do 1?congruence;
by [rewrite -e /= andb_false_r in wf2 | rewrite e /= andb_false_r in wf1].
Qed.

Definition count t t' :=
  SMS.count PreTerm.inv_aux
    (unfold_term t) (PreTerm.factors (unfold_term t')).

Lemma count_inj t1 t2 :
  (∀ x, negb (is_mul x) → count x t1 = count x t2) →
  t1 = t2.
Proof.
move=> ecount; apply: factors_inj.
apply: (inj (fmap unfold_term : list _ → _)).
rewrite !unfold_factors.
set ts1 := PreTerm.factors (unfold_term t1).
set ts2 := PreTerm.factors (unfold_term t2).
have wfs1: PreTerm.wf_factors ts1 by exact: PreTerm.wf_wf_factors.
have wfs2: PreTerm.wf_factors ts2 by exact: PreTerm.wf_wf_factors.
have /SMS.to_id <- := PreTerm.wf_factors_sms _ wfs1.
have /SMS.to_id <- := PreTerm.wf_factors_sms _ wfs2.
apply: SMS.count_to_eq.
- move=> t t_ts; apply: PreTerm.inv_auxK; exact: PreTerm.wf_factors_wf t_ts.
- move=> t t_ts; apply: PreTerm.inv_auxK; exact: PreTerm.wf_factors_wf t_ts.
move=> t t_ts.
have [t' t_t'] : ∃ t', t ∈ PreTerm.factors (unfold_term t').
  case/elem_of_app: t_ts=> ?; eauto.
have wf_t: PreTerm.wf t.
  apply: PreTerm.wf_factors_wf t_t'.
  exact: PreTerm.wf_wf_factors.
have tNm: negb (PreTerm.is_mul t).
  apply: PreTerm.wf_factors_Nmul t_t'.
  exact: PreTerm.wf_wf_factors.
rewrite -[t]PreTerm.normalize_wf // -unfold_fold.
by apply: ecount; rewrite is_mul_unfold fold_termK.
Qed.

Definition gcount t t' :=
  SMS.count PreTerm.ginv_aux
    (unfold_term t) (PreTerm.gfactors (unfold_term t')).

Lemma gcount_inj t1 t2 :
  (∀ x, negb (is_gmul x) → gcount x t1 = gcount x t2) →
  t1 = t2.
Proof.
move=> ecount; apply: gfactors_inj.
apply: (inj (fmap unfold_term : list _ → _)).
rewrite !unfold_gfactors.
set ts1 := PreTerm.gfactors (unfold_term t1).
set ts2 := PreTerm.gfactors (unfold_term t2).
have wfs1: PreTerm.wf_gfactors ts1 by exact: PreTerm.wf_wf_gfactors.
have wfs2: PreTerm.wf_gfactors ts2 by exact: PreTerm.wf_wf_gfactors.
have /SMS.to_id <- := PreTerm.wf_gfactors_sms _ wfs1.
have /SMS.to_id <- := PreTerm.wf_gfactors_sms _ wfs2.
apply: SMS.count_to_eq.
- move=> t t_ts; apply: PreTerm.ginv_auxK; exact: PreTerm.wf_gfactors_wf t_ts.
- move=> t t_ts; apply: PreTerm.ginv_auxK; exact: PreTerm.wf_gfactors_wf t_ts.
move=> t t_ts.
have [t' t_t'] : ∃ t', t ∈ PreTerm.gfactors (unfold_term t').
  case/elem_of_app: t_ts=> ?; eauto.
have wf_t: PreTerm.wf t.
  apply: PreTerm.wf_gfactors_wf t_t'.
  exact: PreTerm.wf_wf_gfactors.
have tNm: negb (PreTerm.is_gmul t).
  apply: PreTerm.wf_gfactors_Ngmul t_t'.
  exact: PreTerm.wf_wf_gfactors.
rewrite -[t]PreTerm.normalize_wf // -unfold_fold.
by apply: ecount; rewrite is_gmul_unfold fold_termK.
Qed.

Lemma gcount_TGMulN t ts :
  gcount t (TGMulN ts) = foldr Z.add 0%Z (gcount t <$> ts).
Proof.
rewrite /gcount unfold_TGMulN /PreTerm.gmul PreTerm.gmul_auxK; last first.
  apply: PreTerm.wf_normalize_gfactors.
  by apply/Forall_fmap/list.Forall_forall=> ?? /=.
rewrite /PreTerm.normalize_gfactors list_fmap_bind SMS.count_to; last first.
- move=> t0 /list_elem_of_bind [t1 [] /= t0_t1 t1_ts].
  apply: PreTerm.ginv_auxK.
  apply: PreTerm.wf_gfactors_wf t0_t1.
  exact: PreTerm.wf_wf_gfactors.
- exact: PreTerm.ginv_auxK.
by elim: ts => //= t0 ts IH; rewrite SMS.count_app IH.
Qed.

Lemma count_TMulN t ts :
  count t (TMulN ts) = foldr Z.add 0%Z (count t <$> ts).
Proof.
rewrite /count unfold_TMulN /PreTerm.mul PreTerm.mul_auxK; last first.
  apply: PreTerm.wf_normalize_factors.
  by apply/Forall_fmap/list.Forall_forall=> ?? /=.
rewrite /PreTerm.normalize_factors list_fmap_bind SMS.count_to; last first.
- move=> t0 /list_elem_of_bind [t1 [] /= t0_t1 t1_ts].
  apply: PreTerm.inv_auxK.
  apply: PreTerm.wf_factors_wf t0_t1.
  exact: PreTerm.wf_wf_factors.
- exact: PreTerm.inv_auxK.
by elim: ts => //= t0 ts IH; rewrite SMS.count_app IH.
Qed.

Lemma TGInvE t : TGInv t = TGMulN (TGInv <$> gfactors t).
Proof.
apply: unfold_term_inj; rewrite unfold_TGMulN unfold_TGInv.
rewrite -list_fmap_compose.
have ->: unfold_term ∘ TGInv <$> gfactors t =
         PreTerm.ginv_aux ∘ unfold_term <$> gfactors t.
  apply/Forall_fmap_ext/list.Forall_forall.
  move=> t0 t0_in /=; rewrite unfold_TGInv PreTerm.ginv_Ngmul //.
  have {}t0_in: unfold_term t0 ∈ PreTerm.gfactors (unfold_term t).
    by rewrite -unfold_gfactors; apply/list_elem_of_fmap; eauto.
  apply: PreTerm.wf_gfactors_Ngmul t0_in.
  exact: PreTerm.wf_wf_gfactors.
rewrite list_fmap_compose unfold_gfactors /PreTerm.ginv.
case: (unfold_term t) (wf_unfold_term t) => [|||[|] ts] //=.
case => //= {}t /andb_True [] /andb_True [] tNV tNM wf_t.
by rewrite PreTerm.gmul1.
Qed.

Lemma TInvE t : TInv t = TMulN (TInv <$> factors t).
Proof.
apply: unfold_term_inj; rewrite unfold_TMulN unfold_TInv.
rewrite -list_fmap_compose.
have ->: unfold_term ∘ TInv <$> factors t =
         PreTerm.inv_aux ∘ unfold_term <$> factors t.
  apply/Forall_fmap_ext/list.Forall_forall.
  move=> t0 t0_in /=; rewrite unfold_TInv PreTerm.inv_Nmul //.
  have {}t0_in: unfold_term t0 ∈ PreTerm.factors (unfold_term t).
    by rewrite -unfold_factors; apply/list_elem_of_fmap; eauto.
  apply: PreTerm.wf_factors_Nmul t0_in.
  exact: PreTerm.wf_wf_factors.
rewrite list_fmap_compose unfold_factors /PreTerm.inv.
case: (unfold_term t) (wf_unfold_term t) => [|||[] ts] //=.
case => //= {}t /andb_True [] /andb_True [] tNV tNM wf_t.
by rewrite PreTerm.mul1.
Qed.

Lemma factors_Nmul t : negb (is_mul t) → factors t = [t].
Proof.
rewrite is_mul_unfold => tNm.
apply: (inj (fmap unfold_term : list _ → _)).
by rewrite /= unfold_factors PreTerm.factors_Nmul.
Qed.

Lemma gfactors_Ngmul t : negb (is_gmul t) → gfactors t = [t].
Proof.
rewrite is_gmul_unfold => tNm.
apply: (inj (fmap unfold_term : list _ → _)).
by rewrite /= unfold_gfactors PreTerm.gfactors_Ngmul.
Qed.

Lemma factorsK t : TMulN (factors t) = t.
Proof.
apply: unfold_term_inj; rewrite unfold_TMulN unfold_factors.
rewrite /PreTerm.mul PreTerm.normalize_factors_wf_factors.
- by rewrite PreTerm.factorsK.
- exact: PreTerm.wf_wf_factors.
Qed.

Lemma gfactorsK t : TGMulN (gfactors t) = t.
Proof.
apply: unfold_term_inj; rewrite unfold_TGMulN unfold_gfactors.
rewrite /PreTerm.gmul PreTerm.normalize_gfactors_wf_gfactors.
- by rewrite PreTerm.gfactorsK.
- exact: PreTerm.wf_wf_gfactors.
Qed.

Lemma gcount_TGInv t t' : gcount t (TGInv t') = (- gcount t t')%Z.
Proof.
rewrite TGInvE gcount_TGMulN -list_fmap_compose.
have ->: gcount t ∘ TGInv <$> gfactors t' =
         (λ t0, - gcount t t0)%Z <$> gfactors t'.
  apply/Forall_fmap_ext/list.Forall_forall=> t0 t0_in /=.
  rewrite -(list_elem_of_fmap_inj unfold_term) unfold_gfactors in t0_in.
  have t0_Nmul: negb (PreTerm.is_gmul (unfold_term t0)).
    apply: PreTerm.wf_gfactors_Ngmul t0_in.
    exact: PreTerm.wf_wf_gfactors.
  have t0V_Nmul: negb (PreTerm.is_gmul (PreTerm.ginv_aux (unfold_term t0))).
    case: (unfold_term t0) (wf_unfold_term t0) t0_Nmul {t0_in} => [|||[|] ts] //=.
    by case => //= ? /andb_True [] /andb_True [].
  rewrite /gcount unfold_TGInv PreTerm.ginv_Ngmul //.
  rewrite PreTerm.gfactors_Ngmul // PreTerm.gfactors_Ngmul //.
  rewrite -SMS.count_fmap_i //.
  - exact: PreTerm.ginv_auxK.
  - move=> ? /list_elem_of_singleton ->.
    exact: PreTerm.ginv_auxK.
rewrite -[t' in RHS]gfactorsK gcount_TGMulN.
elim: {t'} (gfactors t') => //= t' ts ->; rewrite /fmap; lia.
Qed.

Lemma count_TInv t t' : count t (TInv t') = (- count t t')%Z.
Proof.
rewrite TInvE count_TMulN -list_fmap_compose.
have ->: count t ∘ TInv <$> factors t' =
         (λ t0, - count t t0)%Z <$> factors t'.
  apply/Forall_fmap_ext/list.Forall_forall=> t0 t0_in /=.
  rewrite -(list_elem_of_fmap_inj unfold_term) unfold_factors in t0_in.
  have t0_Nmul: negb (PreTerm.is_mul (unfold_term t0)).
    apply: PreTerm.wf_factors_Nmul t0_in.
    exact: PreTerm.wf_wf_factors.
  have t0V_Nmul: negb (PreTerm.is_mul (PreTerm.inv_aux (unfold_term t0))).
    case: (unfold_term t0) (wf_unfold_term t0) t0_Nmul {t0_in} => [|||[] ts] //=.
    by case => //= ? /andb_True [] /andb_True [].
  rewrite /count unfold_TInv PreTerm.inv_Nmul //.
  rewrite PreTerm.factors_Nmul // PreTerm.factors_Nmul //.
  rewrite -SMS.count_fmap_i //.
  - exact: PreTerm.inv_auxK.
  - move=> ? /list_elem_of_singleton ->.
    exact: PreTerm.inv_auxK.
rewrite -[t' in RHS]factorsK count_TMulN.
elim: {t'} (factors t') => //= t' ts ->; rewrite /fmap; lia.
Qed.

Lemma Nmul_factors b t : t ∈ factors b -> negb (is_mul t).
Proof.
move=> t_b; rewrite is_mul_unfold.
have H : unfold_term t ∈ PreTerm.factors (unfold_term b).
  by rewrite -unfold_factors; apply/list_elem_of_fmap; exists t.
apply: (PreTerm.wf_factors_Nmul _ _ _ H); exact: PreTerm.wf_wf_factors.
Qed.

Lemma Ngmul_gfactors b t : t ∈ gfactors b -> negb (is_gmul t).
Proof.
move=> t_b; rewrite is_gmul_unfold.
have H : unfold_term t ∈ PreTerm.gfactors (unfold_term b).
  by rewrite -unfold_gfactors; apply/list_elem_of_fmap; exists t.
apply: (PreTerm.wf_gfactors_Ngmul _ _ _ H); exact: PreTerm.wf_wf_gfactors.
Qed.

Lemma TInv_Nid t : negb (is_mul t) → TInv t ≠ t.
Proof.
move=> tNm e.
have {}e : is_inv t = negb (is_inv t) by rewrite -{1}e is_inv_TInv.
by case: is_inv e.
Qed.

Lemma TGInv_Nid t : negb (is_gmul t) → TGInv t ≠ t.
Proof.
move=> tNm e.
have {}e : is_ginv t = negb (is_ginv t) by rewrite -{1}e is_ginv_TGInv.
by case: is_ginv e.
Qed.

Lemma TInvK t : TInv (TInv t) = t.
Proof. apply: count_inj=> t0 _; rewrite !count_TInv; lia. Qed.

Lemma TGInvK t : TGInv (TGInv t) = t.
Proof. apply: gcount_inj=> t0 _; rewrite !gcount_TGInv; lia. Qed.

Definition invs_canceled (ts : list term) : Prop :=
  ∀ t, t ∈ ts → TInv t ∉ ts ∧ negb (is_mul t).

Lemma invs_canceled0 : invs_canceled [].
Proof. by move=> ? /elem_of_nil. Qed.

Lemma invs_canceled_cons t ts :
  invs_canceled (t :: ts) ↔
  TInv t ∉ ts ∧ negb (is_mul t) ∧ invs_canceled ts.
Proof.
split.
- move=> ic.
  have /ic [Vnin tNm] : t ∈ t :: ts by rewrite elem_of_cons; eauto.
  do 2?split => //.
  + by move=> contra; apply: Vnin; apply/elem_of_cons; eauto.
  + move=> t0 t0_in.
    have /ic [V0nin t0Nm] : t0 ∈ t :: ts by rewrite elem_of_cons; eauto.
    by split=> // contra; apply: V0nin; apply/elem_of_cons; eauto.
- case=> Vnin [] tNm ic t0 /elem_of_cons [->|t0_in].
  + split=> // /elem_of_cons [e|//].
    exact: TInv_Nid.
  + have /ic [V0nin t0Nm] := t0_in.
    split => // /elem_of_cons [e|//].
    rewrite -e TInvK in Vnin; tauto.
Qed.

Definition ginvs_canceled (ts : list term) : Prop :=
  ∀ t, t ∈ ts → TGInv t ∉ ts ∧ negb (is_gmul t).

Lemma ginvs_canceled0 : ginvs_canceled [].
Proof. by move=> ? /elem_of_nil. Qed.

Lemma ginvs_canceled_cons t ts :
  ginvs_canceled (t :: ts) ↔
  TGInv t ∉ ts ∧ negb (is_gmul t) ∧ ginvs_canceled ts.
Proof.
split.
- move=> ic.
  have /ic [Vnin tNm] : t ∈ t :: ts by rewrite elem_of_cons; eauto.
  do 2?split => //.
  + by move=> contra; apply: Vnin; apply/elem_of_cons; eauto.
  + move=> t0 t0_in.
    have /ic [V0nin t0Nm] : t0 ∈ t :: ts by rewrite elem_of_cons; eauto.
    by split=> // contra; apply: V0nin; apply/elem_of_cons; eauto.
- case=> Vnin [] tNm ic t0 /elem_of_cons [->|t0_in].
  + split=> // /elem_of_cons [e|//].
    exact: TGInv_Nid.
  + have /ic [V0nin t0Nm] := t0_in.
    split => // /elem_of_cons [e|//].
    rewrite -e TGInvK in Vnin; tauto.
Qed.

Lemma wf_gfactors_ginvs_canceled (ts : list _) :
  PreTerm.wf_gfactors ts →
  ginvs_canceled (fold_term <$> ts).
Proof.
case/andb_True=> [] /forallb_True/Forall_forall wfts sms.
move=> _ /list_elem_of_fmap [t [] -> t_ts].
have /andb_True [wft tNm] := wfts _ t_ts.
rewrite is_gmul_unfold fold_termK //; split => //.
rewrite -(list_elem_of_fmap_inj unfold_term) unfold_TGInv fold_termK //.
rewrite PreTerm.ginv_Ngmul //.
have -> : unfold_term <$> (fold_term <$> ts) = ts.
  rewrite -[RHS]list_fmap_id -list_fmap_compose; apply/Forall_fmap_ext.
  apply/Forall_forall=> t0 /wfts/andb_True [wft0 ?].
  by rewrite /= fold_termK.
by move/SMS.wf_no_pairs/(_ _ t_ts) in sms.
Qed.

Lemma wf_factors_invs_canceled (ts : list _) :
  PreTerm.wf_factors ts →
  invs_canceled (fold_term <$> ts).
Proof.
case/andb_True=> [] /forallb_True/Forall_forall wfts sms.
move=> _ /list_elem_of_fmap [t [] -> t_ts].
have /andb_True [wft tNm] := wfts _ t_ts.
rewrite is_mul_unfold fold_termK //; split => //.
rewrite -(list_elem_of_fmap_inj unfold_term) unfold_TInv fold_termK //.
rewrite PreTerm.inv_Nmul //.
have -> : unfold_term <$> (fold_term <$> ts) = ts.
  rewrite -[RHS]list_fmap_id -list_fmap_compose; apply/Forall_fmap_ext.
  apply/Forall_forall=> t0 /wfts/andb_True [wft0 ?].
  by rewrite /= fold_termK.
by move/SMS.wf_no_pairs/(_ _ t_ts) in sms.
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
  (H7g : forall t, T t -> negb (is_gmul t) -> negb (is_ginv t) -> T (TGInv t))
  (* The base of a normal-form exponential is a *group* atom: [wf] rules out a
     group product and a group inverse there as well as an exponential, since
     [TExp] distributes over the first two.  A scalar product or scalar inverse
     in the base is fine -- [TExp] does not distribute over those. *)
  (H8 : forall t1, T t1 ->
        forall t2, T t2 ->
                   negb (is_exp t1) ->
                   negb (is_gmul t1) ->
                   negb (is_ginv t1) ->
                   t2 ≠ TMulN [] ->
        T (TExp t1 t2))
  (H9 : forall ts, foldr (fun t R => T t * R)%type unit ts ->
                   invs_canceled ts →
                   length ts ≠ 1 ->
        T (TMulN ts))
  (H9g : forall ts, foldr (fun t R => T t * R)%type unit ts ->
                    ginvs_canceled ts →
                    length ts ≠ 1 ->
        T (TGMulN ts)) :
  forall t, T t.
Proof.
move=> t; rewrite -(unfold_termK t).
elim: (unfold_term t) (wf_unfold_term t)=>
  {t} [o|o pt IHpt|o pt1 IHpt1 pt2 IHpt2|[|] ts IHts] wfpt.
- case: o wfpt => [n|l] _; rewrite fold_termE /=; [exact: H1|exact: H3].
- case: o wfpt => [kt| | |]; rewrite fold_termE /=.
  + by move=> wfpt; exact: (H4 kt _ (IHpt wfpt)).
  + by move=> wfpt; exact: (H6 _ (IHpt wfpt)).
  + move=> /andb_True [/andb_True [Ninv Nmul] wfpt].
    apply: (H7 _ (IHpt wfpt)).
    * by rewrite is_mul_unfold (fold_termK _ wfpt).
    * by rewrite is_inv_unfold (fold_termK _ wfpt).
  + move=> /andb_True [/andb_True [Ninv Nmul] wfpt].
    apply: (H7g _ (IHpt wfpt)).
    * by rewrite is_gmul_unfold (fold_termK _ wfpt).
    * by rewrite is_ginv_unfold (fold_termK _ wfpt).
- case: o wfpt => [||]; rewrite fold_termE /=.
  + by move=> /andb_True [w1 w2]; exact: (H2 _ (IHpt1 w1) _ (IHpt2 w2)).
  + by move=> /andb_True [w1 w2]; exact: (H5 _ (IHpt1 w1) _ (IHpt2 w2)).
  + move=> /andb_True [/andb_True [/andb_True [w1 Nnf1] w2] Hne].
    have pt2N : pt2 ≠ PreTerm.PTMul [] := bool_decide_unpack _ Hne.
    apply: (H8 _ (IHpt1 w1) _ (IHpt2 w2)).
    * rewrite is_exp_unfold (fold_termK _ w1); exact: (PreTerm.Ngnf_Nexp _ Nnf1).
    * rewrite is_gmul_unfold (fold_termK _ w1);
        exact: (PreTerm.Ngnf_Ngmul _ Nnf1).
    * rewrite is_ginv_unfold (fold_termK _ w1);
        exact: (PreTerm.Ngnf_Nginv _ Nnf1).
    * have E0 : TMulN [] = fold_term (PreTerm.PTMul []) by rewrite fold_termE.
      rewrite E0 => Heq; apply: pt2N.
      move/(f_equal unfold_term): Heq.
      by rewrite fold_termK // fold_termK.
- rewrite fold_termE.
  have [wff tsN1]: PreTerm.wf_factors ts ∧ length ts ≠ 1.
    by rewrite /= andb_True bool_decide_spec in wfpt; case: wfpt.
  apply: H9.
  + have {}wfts: Forall PreTerm.wf ts.
      by apply/list.Forall_forall => ?; apply: PreTerm.wf_factors_wf.
    elim: ts IHts wfts {wfpt wff tsN1} => [//|pt ts' IH] /=.
    move=> [IHpt IHts'] /Forall_cons [w ws].
    by split; [exact: (IHpt w)|exact: (IH IHts' ws)].
  + exact: wf_factors_invs_canceled.
  + by rewrite length_fmap.
- rewrite fold_termE.
  have [wff tsN1]: PreTerm.wf_gfactors ts ∧ length ts ≠ 1.
    by rewrite /= andb_True bool_decide_spec in wfpt; case: wfpt.
  apply: H9g.
  + have {}wfts: Forall PreTerm.wf ts.
      by apply/list.Forall_forall => ?; apply: PreTerm.wf_gfactors_wf.
    elim: ts IHts wfts {wfpt wff tsN1} => [//|pt ts' IH] /=.
    move=> [IHpt IHts'] /Forall_cons [w ws].
    by split; [exact: (IHpt w)|exact: (IH IHts' ws)].
  + exact: wf_gfactors_ginvs_canceled.
  + by rewrite length_fmap.
Qed.

Definition term_ind (P : term -> Prop) := @term_rect P.
