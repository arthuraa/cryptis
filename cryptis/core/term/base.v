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

(* The three "non-free" operations -- the two products and exponentiation --
   are represented indirectly, by a well-formed pre-term whose head is one of
   [PTExp] / [PTMul] / [PTGMul].  [is_non_free] recognises exactly those heads;
   it lives in [PreTerm] alongside [is_gnon_free], the smaller predicate [wf]
   uses for the base of a normal-form exponential. *)
Abbreviation is_non_free := PreTerm.is_non_free.

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

lock Definition term_of_aenc_key sk := TKey ADec (seed_of_aenc_key sk).
Coercion term_of_aenc_key : aenc_key >-> term.

lock Definition term_of_sign_key sk := TKey Sign (seed_of_sign_key sk).
Coercion term_of_sign_key : sign_key >-> term.

lock Definition term_of_senc_key sk := TKey SEnc (seed_of_senc_key sk).
Coercion term_of_senc_key : senc_key >-> term.

Lemma term_of_aenc_key_inj : Inj (=) (=) term_of_aenc_key.
Proof. rewrite unlock. by case=> [?] [?] [->]. Qed.

Lemma term_of_sign_key_inj : Inj (=) (=) term_of_sign_key.
Proof. rewrite unlock. by case=> [?] [?] [->]. Qed.

Lemma term_of_senc_key_inj : Inj (=) (=) term_of_senc_key.
Proof. rewrite unlock. by case=> [?] [?] [->]. Qed.

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
  | PreTerm.PT2 O2Pair pt1 pt2 =>
    TPair (fold_term_predef pt1) (fold_term_predef pt2)
  | PreTerm.PT0 (O0Nonce l) => TNonce l
  | PreTerm.PT1 (O1Key kt) pt => TKey kt (fold_term_predef pt)
  | PreTerm.PT2 O2Seal k pt => TSeal (fold_term_predef k) (fold_term_predef pt)
  | PreTerm.PT1 O1Hash pt => THash (fold_term_predef pt)
  | PreTerm.PTExp b e =>
    if decide (PreTerm.wf (PreTerm.PTExp b e)) is left pf then
      TNonFree (PreTerm.PTExp b e) pf I
    else TInt 0 (*should never*)
  | PreTerm.PTMul ps ns =>
    if decide (PreTerm.wf (PreTerm.PTMul ps ns)) is left pf then
      TNonFree (PreTerm.PTMul ps ns) pf I
    else TInt 0 (*should never*)
  | PreTerm.PTGMul ps ns =>
    if decide (PreTerm.wf (PreTerm.PTGMul ps ns)) is left pf then
      TNonFree (PreTerm.PTGMul ps ns) pf I
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
case: pt wf nf => [o|[kt|] pt'|[||] b e|[|] ps ns] wf nf.
1-5: by move: nf; rewrite /is_non_free /=.
- rewrite /=; case: (decide (PreTerm.wf (PreTerm.PTExp b e))) => [pf'|npf];
    last by case: (npf wf).
  exact: TNonFree_irr.
- rewrite /=; case: (decide (PreTerm.wf (PreTerm.PTMul ps ns))) => [pf'|npf];
    last by case: (npf wf).
  exact: TNonFree_irr.
- rewrite /=; case: (decide (PreTerm.wf (PreTerm.PTGMul ps ns))) => [pf'|npf];
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
- by move => [?|] t IH wf_t; rewrite /= IH.
- move => [] t1 IH1 t2 IH2 wf.
  + by move: wf; rewrite /= => /andb_True [w1 w2]; rewrite (IH1 w1) (IH2 w2).
  + by move: wf; rewrite /= => /andb_True [w1 w2]; rewrite (IH1 w1) (IH2 w2).
  + by rewrite (fold_predef_NonFree wf I).
- by move => [|] ps IHps ns IHns wf; rewrite (fold_predef_NonFree wf I).
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

#[global] Instance unfold_term_inj : Inj (=) (=) unfold_term.
Proof. by move=> t1 t2 /(f_equal fold_term); rewrite !unfold_termK. Qed.

#[global] Instance term_eq_dec : EqDecision term :=
  inj_eq_dec unfold_term.

#[global] Instance term_countable : Countable term :=
  inj_countable' unfold_term fold_term unfold_termK.

#[global] Instance term_inhabited : Inhabited term.
Proof. exact: (populate (TInt 0)). Qed.

Canonical termO := leibnizO term.

#[global] Instance aenc_key_eq_dec : EqDecision aenc_key.
Proof. solve_decision. Defined.
#[global] Instance aenc_key_countable : Countable aenc_key.
Proof. apply: (inj_countable' seed_of_aenc_key AEncKey); by case. Qed.
#[global] Instance aenc_key_inhabited : Inhabited aenc_key :=
  populate (AEncKey inhabitant).

#[global] Instance sign_key_eq_dec : EqDecision sign_key.
Proof. solve_decision. Defined.
#[global] Instance sign_key_countable : Countable sign_key.
Proof. apply: (inj_countable' seed_of_sign_key SignKey); by case. Qed.
#[global] Instance sign_key_inhabited : Inhabited sign_key :=
  populate (SignKey inhabitant).

#[global] Instance senc_key_eq_dec : EqDecision senc_key.
Proof. solve_decision. Defined.
#[global] Instance senc_key_countable : Countable senc_key.
Proof. apply: (inj_countable' seed_of_senc_key SEncKey); by case. Qed.
#[global] Instance senc_key_inhabited : Inhabited senc_key :=
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

(** Products are signed multisets of terms ([SMS.sms]), ordered through their
    pre-terms. *)
#[global] Instance term_lexico : Lexico term :=
  λ t1 t2, lexico (unfold_term t1) (unfold_term t2).

#[global] Instance term_lexico_strict : StrictOrder (@lexico term _).
Proof.
split; first by move=> t; exact: (irreflexivity lexico (unfold_term t)).
move=> t1 t2 t3; exact: (@transitivity _ (@lexico PreTerm.pre_term _) _).
Qed.

#[global] Instance term_lexico_trichotomyT : TrichotomyT (@lexico term _).
Proof.
refine (λ t1 t2,
  match trichotomyT lexico (unfold_term t1) (unfold_term t2) with
  | inleft (left p) => inleft (left p)
  | inleft (right e) => inleft (right _)
  | inright p => inright p
  end).
abstract (exact: unfold_term_inj e).
Defined.

Abbreviation term_order := (@SMS.Internal.le term _).

Lemma term_orderE t1 t2 :
  term_order t1 t2 ↔ SMS.Internal.le (unfold_term t1) (unfold_term t2).
Proof.
split; first by case=> [->|?]; [left|right].
by case=> [/unfold_term_inj ->|?]; [left|right].
Qed.

Abbreviation tsms := (SMS.sms term).

lock Definition TMul (s : tsms) :=
  fold_term (PreTerm.mul (SMS.map unfold_term s)).

(* The Diffie-Hellman group: [TGMul] is the same construction as [TMul] at the
   group operation.  It lives in the *base* of an exponential, where [TExp]
   distributes over it; [TMul] lives in the exponent, where it does not. *)
lock Definition TGMul (s : tsms) :=
  fold_term (PreTerm.gmul (SMS.map unfold_term s)).

lock Definition TExp b e :=
  fold_term (PreTerm.exp (unfold_term b) (unfold_term e)).

Definition TInv t := TMul (SMS.inv {[+ t +]}).
Definition TGInv t := TGMul (SMS.inv {[+ t +]}).

Arguments TInv : simpl never.
Arguments TGInv : simpl never.

Lemma unfold_TMul s :
  unfold_term (TMul s) = PreTerm.mul (SMS.map unfold_term s).
Proof.
rewrite unlock unfold_fold PreTerm.normalize_wf //.
apply: PreTerm.wf_mul => pt /SMS.elem_of_map [t [-> _]]; exact: wf_unfold_term.
Qed.

Lemma unfold_TGMul s :
  unfold_term (TGMul s) = PreTerm.gmul (SMS.map unfold_term s).
Proof.
rewrite unlock unfold_fold PreTerm.normalize_wf //.
apply: PreTerm.wf_gmul => pt /SMS.elem_of_map [t [-> _]]; exact: wf_unfold_term.
Qed.

Lemma unfold_TExp b e :
  unfold_term (TExp b e) = PreTerm.exp (unfold_term b) (unfold_term e).
Proof.
rewrite unlock unfold_fold PreTerm.normalize_wf //.
by apply: PreTerm.wf_exp.
Qed.

Lemma unfold_TMul_make X Y :
  unfold_term (TMul (SMS.make X Y)) =
  PreTerm.mul (SMS.make (unfold_term <$> X) (unfold_term <$> Y)).
Proof. by rewrite unfold_TMul SMS.map_make. Qed.

Lemma unfold_TGMul_make X Y :
  unfold_term (TGMul (SMS.make X Y)) =
  PreTerm.gmul (SMS.make (unfold_term <$> X) (unfold_term <$> Y)).
Proof. by rewrite unfold_TGMul SMS.map_make. Qed.

Lemma smap_unfold_fold P :
  (∀ x, x ∈ SMS.Internal.elements P → PreTerm.wf x) →
  SMS.Internal.smap unfold_term (SMS.Internal.smap fold_term P) = P.
Proof.
move=> wfP; rewrite SMS.Internal.smap_smap SMS.Internal.smap_id //.
by move=> x /wfP; exact: fold_termK.
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
  | PreTerm.PTExp b e => TExp (fold_term b) (fold_term e)
  | PreTerm.PTMul ps ns => TMul (SMS.make (fold_term <$> ps) (fold_term <$> ns))
  | PreTerm.PTGMul ps ns =>
    TGMul (SMS.make (fold_term <$> ps) (fold_term <$> ns))
  end.
Proof.
have fmapE (ts : list PreTerm.pre_term) :
    unfold_term <$> (fold_term <$> ts) = PreTerm.normalize <$> ts.
  rewrite -list_fmap_compose; apply: Forall_fmap_ext_1.
  by apply/Forall_forall => pt0 _; exact: unfold_fold.
apply /unfold_term_inj.
case: pt => /=;
  try by case =>> //=; rewrite !unfold_fold.
- by move=> [] >; rewrite /= ?unfold_TExp !unfold_fold.
- move=> [|] ps ns;
  by rewrite unfold_fold ?unfold_TMul_make ?unfold_TGMul_make !fmapE.
Qed.

Definition base t := fold_term (PreTerm.base (unfold_term t)).
Definition expo t := fold_term (PreTerm.expo (unfold_term t)).

Lemma wf_term_pair P :
  (∀ x, x ∈ SMS.Internal.elements P → PreTerm.wf x) →
  SMS.Internal.wf SMS.Internal.le P →
  SMS.Internal.wf term_order (SMS.Internal.smap fold_term P).
Proof.
move=> wfP wfP'.
apply/(SMS.Internal.wf_smap term_order SMS.Internal.le unfold_term _
         unfold_term_inj); first exact: term_orderE.
by rewrite smap_unfold_fold.
Qed.

Definition factors t : tsms :=
  SMS.map fold_term (PreTerm.factors (unfold_term t)).
Definition gfactors t : tsms :=
  SMS.map fold_term (PreTerm.gfactors (unfold_term t)).

Definition is_nonce t :=
  if t is TNonce _ then true else false.

Definition is_exp t :=
  if t is TNonFree pt _ _ then PreTerm.is_exp pt else false.

Definition is_mul t :=
  if t is TNonFree pt _ _ then PreTerm.is_mul pt else false.

Definition is_gmul t :=
  if t is TNonFree pt _ _ then PreTerm.is_gmul pt else false.

Lemma is_nonce_unfold t : is_nonce t = PreTerm.is_nonce (unfold_term t).
Proof. by case: t => //= pt _ nf; move: nf; case: pt. Qed.

Lemma is_exp_unfold t : is_exp t = PreTerm.is_exp (unfold_term t).
Proof. by case: t. Qed.

Lemma is_mul_unfold t : is_mul t = PreTerm.is_mul (unfold_term t).
Proof. by case: t. Qed.

Lemma is_gmul_unfold t : is_gmul t = PreTerm.is_gmul (unfold_term t).
Proof. by case: t. Qed.

Lemma unfold_base t : unfold_term (base t) = PreTerm.base (unfold_term t).
Proof. rewrite /base fold_termK //; exact: PreTerm.wf_base. Qed.

Lemma unfold_expo t : unfold_term (expo t) = PreTerm.expo (unfold_term t).
Proof. rewrite /expo fold_termK //; exact: PreTerm.wf_expo. Qed.

Lemma car_factors t :
  SMS.car (factors t) =
  SMS.Internal.smap fold_term (SMS.car (PreTerm.factors (unfold_term t))).
Proof.
rewrite /factors SMS.car_map SMS.Internal.to_id //.
apply: wf_term_pair; last exact: SMS.wf_car.
move=> x.
exact: PreTerm.wf_factors_wf (PreTerm.wf_wf_factors _ (wf_unfold_term t)).
Qed.

Lemma car_gfactors t :
  SMS.car (gfactors t) =
  SMS.Internal.smap fold_term (SMS.car (PreTerm.gfactors (unfold_term t))).
Proof.
rewrite /gfactors SMS.car_map SMS.Internal.to_id //.
apply: wf_term_pair; last exact: SMS.wf_car.
move=> x.
exact: PreTerm.wf_gfactors_wf (PreTerm.wf_wf_gfactors _ (wf_unfold_term t)).
Qed.

Lemma elements_factors t :
  elements (factors t) =
  fold_term <$> elements (PreTerm.factors (unfold_term t)).
Proof. by rewrite !SMS.elements_car car_factors SMS.Internal.elements_smap. Qed.

Lemma elements_gfactors t :
  elements (gfactors t) =
  fold_term <$> elements (PreTerm.gfactors (unfold_term t)).
Proof.
by rewrite !SMS.elements_car car_gfactors SMS.Internal.elements_smap.
Qed.

Lemma unfold_factors t :
  SMS.map unfold_term (factors t) = PreTerm.factors (unfold_term t).
Proof.
rewrite /factors SMS.map_map SMS.map_id_ext // => pt pt_in; apply: fold_termK.
exact: PreTerm.wf_factors_wf (PreTerm.wf_wf_factors _ (wf_unfold_term t)) pt_in.
Qed.

Lemma unfold_gfactors t :
  SMS.map unfold_term (gfactors t) = PreTerm.gfactors (unfold_term t).
Proof.
rewrite /gfactors SMS.map_map SMS.map_id_ext // => pt pt_in; apply: fold_termK.
exact: PreTerm.wf_gfactors_wf
         (PreTerm.wf_wf_gfactors _ (wf_unfold_term t)) pt_in.
Qed.

Lemma elem_of_factors_unfold x t :
  x ∈ factors t ↔ unfold_term x ∈ PreTerm.factors (unfold_term t).
Proof.
rewrite -!SMS.elem_of_elements !SMS.elements_car car_factors.
rewrite SMS.Internal.elements_smap list_elem_of_fmap.
have wfP := PreTerm.wf_wf_factors _ (wf_unfold_term t).
split=> [[p [-> p_P]]|x_P].
- by rewrite fold_termK //; apply: PreTerm.wf_factors_wf wfP p_P.
- by exists (unfold_term x); rewrite unfold_termK.
Qed.

Lemma elem_of_gfactors_unfold x t :
  x ∈ gfactors t ↔ unfold_term x ∈ PreTerm.gfactors (unfold_term t).
Proof.
rewrite -!SMS.elem_of_elements !SMS.elements_car car_gfactors.
rewrite SMS.Internal.elements_smap list_elem_of_fmap.
have wfP := PreTerm.wf_wf_gfactors _ (wf_unfold_term t).
split=> [[p [-> p_P]]|x_P].
- by rewrite fold_termK //; apply: PreTerm.wf_gfactors_wf wfP p_P.
- by exists (unfold_term x); rewrite unfold_termK.
Qed.

Lemma Nmul_factors t x : x ∈ factors t → negb (is_mul x).
Proof.
rewrite elem_of_factors_unfold is_mul_unfold.
exact: PreTerm.wf_factors_Nmul (PreTerm.wf_wf_factors _ (wf_unfold_term t)).
Qed.

Lemma Ngmul_gfactors t x :
  x ∈ gfactors t → negb (is_gmul x).
Proof.
rewrite elem_of_gfactors_unfold is_gmul_unfold.
exact: PreTerm.wf_gfactors_Ngmul (PreTerm.wf_wf_gfactors _ (wf_unfold_term t)).
Qed.

Lemma factors_Nmul t : negb (is_mul t) → factors t = {[+ t +]}.
Proof.
rewrite is_mul_unfold => Nm.
by rewrite /factors PreTerm.factors_Nmul // SMS.map_singleton unfold_termK.
Qed.

Lemma gfactors_Ngmul t :
  negb (is_gmul t) → gfactors t = {[+ t +]}.
Proof.
rewrite is_gmul_unfold => Nm.
by rewrite /gfactors PreTerm.gfactors_Ngmul // SMS.map_singleton unfold_termK.
Qed.

Lemma factorsK t : TMul (factors t) = t.
Proof.
apply: unfold_term_inj; rewrite unfold_TMul unfold_factors.
rewrite /PreTerm.mul PreTerm.bind_factors_wf.
- exact: PreTerm.factorsK.
- exact: PreTerm.wf_wf_factors.
Qed.

Lemma gfactorsK t : TGMul (gfactors t) = t.
Proof.
apply: unfold_term_inj; rewrite unfold_TGMul unfold_gfactors.
rewrite /PreTerm.gmul PreTerm.bind_gfactors_wf.
- exact: PreTerm.gfactorsK.
- exact: PreTerm.wf_wf_gfactors.
Qed.

Lemma factors_inj t1 t2 : factors t1 = factors t2 → t1 = t2.
Proof. by move=> e; rewrite -(factorsK t1) e factorsK. Qed.

Lemma gfactors_inj t1 t2 : gfactors t1 = gfactors t2 → t1 = t2.
Proof. by move=> e; rewrite -(gfactorsK t1) e gfactorsK. Qed.

(** [factors] is a homomorphism into the free abelian group on terms: the
    factors of a product are the product of the factors of its elements. *)
Lemma factors_TMul s :
  factors (TMul s) = SMS.bind factors s.
Proof.
rewrite {1}/factors unfold_TMul /PreTerm.mul PreTerm.mul_auxK; last first.
  apply: PreTerm.wf_bind_factors => pt /SMS.elem_of_map [t [-> _]].
  exact: wf_unfold_term.
by rewrite SMS.bind_map SMS.map_bind.
Qed.

Lemma gfactors_TGMul s :
  gfactors (TGMul s) = SMS.bind gfactors s.
Proof.
rewrite {1}/gfactors unfold_TGMul /PreTerm.gmul PreTerm.gmul_auxK; last first.
  apply: PreTerm.wf_bind_gfactors => pt /SMS.elem_of_map [t [-> _]].
  exact: wf_unfold_term.
by rewrite SMS.bind_map SMS.map_bind.
Qed.

Lemma factors_TMul_atoms s :
  (∀ x, x ∈ s → negb (is_mul x)) → factors (TMul s) = s.
Proof.
move=> Hs.
rewrite factors_TMul (SMS.bind_ext _ (λ x, {[+ x +]})).
- exact: SMS.bind_unit.
- by move=> x /Hs /factors_Nmul.
Qed.

Lemma gfactors_TGMul_atoms s :
  (∀ x, x ∈ s → negb (is_gmul x)) → gfactors (TGMul s) = s.
Proof.
move=> Hs.
rewrite gfactors_TGMul (SMS.bind_ext _ (λ x, {[+ x +]})).
- exact: SMS.bind_unit.
- by move=> x /Hs /gfactors_Ngmul.
Qed.

Definition count x t := SMS.count x (factors t).
Definition gcount x t := SMS.count x (gfactors t).

Lemma is_mul_count x t : is_mul x → count x t = 0%Z.
Proof.
move=> Mx; case: (decide (x ∈ factors t)) => x_t.
  by move/Nmul_factors: x_t; case: (is_mul x) Mx.
by move: x_t; rewrite SMS.elem_of_count /count; lia.
Qed.

Lemma is_gmul_gcount x t : is_gmul x → gcount x t = 0%Z.
Proof.
move=> Mx; case: (decide (x ∈ gfactors t)) => x_t.
  by move/Ngmul_gfactors: x_t; case: (is_gmul x) Mx.
by move: x_t; rewrite SMS.elem_of_count /gcount; lia.
Qed.

Lemma count_inj t1 t2 :
  (∀ x, negb (is_mul x) → count x t1 = count x t2) → t1 = t2.
Proof.
move=> e; apply: factors_inj; apply: SMS.count_inj => x.
case Ex: (is_mul x); last by apply: e; rewrite Ex.
by rewrite -/(count x t1) -/(count x t2) !is_mul_count ?Ex.
Qed.

Lemma gcount_inj t1 t2 :
  (∀ x, negb (is_gmul x) → gcount x t1 = gcount x t2) → t1 = t2.
Proof.
move=> e; apply: gfactors_inj; apply: SMS.count_inj => x.
case Ex: (is_gmul x); last by apply: e; rewrite Ex.
by rewrite -/(gcount x t1) -/(gcount x t2) !is_gmul_gcount ?Ex.
Qed.

Lemma factors_TInv t : factors (TInv t) = SMS.inv (factors t).
Proof. by rewrite /TInv factors_TMul SMS.bind_inv SMS.bind_singleton. Qed.

Lemma gfactors_TGInv t : gfactors (TGInv t) = SMS.inv (gfactors t).
Proof. by rewrite /TGInv gfactors_TGMul SMS.bind_inv SMS.bind_singleton. Qed.

Lemma count_TInv t t' : count t (TInv t') = (- count t t')%Z.
Proof. by rewrite /count factors_TInv SMS.count_inv. Qed.

Lemma gcount_TGInv t t' : gcount t (TGInv t') = (- gcount t t')%Z.
Proof. by rewrite /gcount gfactors_TGInv SMS.count_inv. Qed.

Lemma TInvK t : TInv (TInv t) = t.
Proof. by apply: factors_inj; rewrite !factors_TInv SMS.invK. Qed.

Lemma TGInvK t : TGInv (TGInv t) = t.
Proof. by apply: gfactors_inj; rewrite !gfactors_TGInv SMS.invK. Qed.

Lemma term_rect (T : term -> Type)
  (H1 : forall n, T (TInt n))
  (H2 : forall t1, T t1 ->
        forall t2, T t2 ->
        T (TPair t1 t2))
  (H3 : forall a, T (TNonce a))
  (H4 : forall kt t, T t -> T (TKey kt t))
  (H5 : forall k, T k -> forall t, T t -> T (TSeal k t))
  (H6 : forall t, T t -> T (THash t))
  (* The base of a normal-form exponential is neither an exponential nor a
     group product: [TExp] merges the former and distributes over the
     latter. *)
  (H7 : forall t1, T t1 ->
        forall t2, T t2 ->
                   negb (is_exp t1) ->
                   negb (is_gmul t1) ->
                   t2 ≠ TMul ∅ ->
        T (TExp t1 t2))
  (H8 : forall s, (forall t, t ∈ s -> T t) ->
                  (forall t, t ∈ s -> negb (is_mul t)) ->
                  (forall t, s ≠ {[+ t +]}) ->
        T (TMul s))
  (H8g : forall s, (forall t, t ∈ s -> T t) ->
                   (forall t, t ∈ s -> negb (is_gmul t)) ->
                   (forall t, s ≠ {[+ t +]}) ->
        T (TGMul s)) :
  forall t, T t.
Proof.
pose IH l := foldr (fun pt R => (PreTerm.wf pt -> T (fold_term pt)) * R)%type
  unit l.
have IH_app l1 l2 : IH l1 -> IH l2 -> IH (l1 ++ l2).
  by elim: l1 => [_ //|pt l1 IHl1] /= [IHpt {}/IHl1 IHl1] /IHl1.
have IH_elem_of l : IH l -> (forall pt, pt ∈ l -> PreTerm.wf pt) ->
    forall x, x ∈ fold_term <$> l -> T x.
  elim: l => [_ _ x /elem_of_nil []|pt l IHl /= [IHpt {}/IHl IHl] wfl x].
  move=> /elem_of_cons x_l.
  case: (decide (x = fold_term pt)) => [->|ne].
    by apply: IHpt; apply: wfl; set_solver.
  apply: IHl; first by move=> pt' pt'l; apply: wfl; set_solver.
  by case: x_l.
move=> t; rewrite -(unfold_termK t).
elim: (unfold_term t) (wf_unfold_term t)=>
  {t} [o|o pt IHpt|o pt1 IHpt1 pt2 IHpt2|o ps IHps ns IHns] wfpt.
- case: o wfpt => [n|l] _; rewrite fold_termE /=; [exact: H1|exact: H3].
- case: o wfpt => [kt|]; rewrite fold_termE /=.
  + by move=> wfpt; exact: (H4 kt _ (IHpt wfpt)).
  + by move=> wfpt; exact: (H6 _ (IHpt wfpt)).
- case: o wfpt => [||]; rewrite fold_termE /=.
  + by move=> /andb_True [w1 w2]; exact: (H2 _ (IHpt1 w1) _ (IHpt2 w2)).
  + by move=> /andb_True [w1 w2]; exact: (H5 _ (IHpt1 w1) _ (IHpt2 w2)).
  + move=> /andb_True [/andb_True [/andb_True [w1 Nnf1] w2] Hne].
    have pt2N : pt2 ≠ PreTerm.PTMul [] [] := bool_decide_unpack _ Hne.
    apply: (H7 _ (IHpt1 w1) _ (IHpt2 w2)).
    * rewrite is_exp_unfold (fold_termK _ w1).
      exact: (PreTerm.Ngnf_Nexp _ Nnf1).
    * rewrite is_gmul_unfold (fold_termK _ w1).
      exact: (PreTerm.Ngnf_Ngmul _ Nnf1).
    * have E0 : TMul ∅ = fold_term (PreTerm.PTMul [] []).
        by rewrite fold_termE.
      rewrite E0 => Heq; apply: pt2N.
      move/(f_equal unfold_term): Heq.
      by rewrite fold_termK // fold_termK //; exact: PreTerm.wf_one.
- have wfl : forall pt, pt ∈ ps ++ ns -> PreTerm.wf pt.
    move: wfpt; case: o; rewrite ?PreTerm.wf_mulE ?PreTerm.wf_gmulE;
      move=> /andb_True [/andb_True [/forallb_True/list.Forall_forall H _] _];
      by move=> pt /H /andb_True [].
  have IHs := IH_elem_of _ (IH_app _ _ IHps IHns) wfl.
  have {}wfl : forall x, x ∈ SMS.Internal.elements (ps, ns) -> PreTerm.wf x
    by [].
  have Nsingle : negb (PreTerm.single (ps, ns)).
    by case: o wfpt => [|] /= /andb_True [].
  have SMSwf : SMS.Internal.wf SMS.Internal.le (ps, ns).
    by case: o wfpt => [|] /=; case/andb_True=> /andb_True [].
  have carA := SMS.Internal.to_id _ _ (wf_term_pair _ wfl SMSwf).
  have elem_ofA x :
      x ∈ SMS.make (fold_term <$> ps) (fold_term <$> ns) ->
      x ∈ fold_term <$> ps ++ ns.
    by rewrite -SMS.elem_of_elements SMS.elements_car /= carA
      SMS.Internal.elements_smap.
  have Nsingle' x :
      SMS.make (fold_term <$> ps) (fold_term <$> ns) ≠ {[+ x +]}.
    move=> /(f_equal SMS.car); rewrite SMS.car_singleton.
    rewrite /= carA /SMS.Internal.smap /=.
    case=> /(f_equal length) + /(f_equal length); rewrite !length_fmap /=.
    by case: ps ns Nsingle {IHps IHns IHs wfl SMSwf carA elem_ofA wfpt}
      => [|? [|? ?]] [|? ?].
  case: o wfpt => wfpt; rewrite fold_termE.
  + apply: H8 => //; first by move=> x /elem_ofA; exact: IHs.
    move=> x /elem_ofA /list_elem_of_fmap [pt [-> pt_in]].
    rewrite is_mul_unfold fold_termK; last exact: wfl.
    move: wfpt; rewrite PreTerm.wf_mulE.
    move=> /andb_True [/andb_True [/forallb_True/list.Forall_forall H _] _].
    by case/andb_True: (H _ pt_in).
  + apply: H8g => //; first by move=> x /elem_ofA; exact: IHs.
    move=> x /elem_ofA /list_elem_of_fmap [pt [-> pt_in]].
    rewrite is_gmul_unfold fold_termK; last exact: wfl.
    move: wfpt; rewrite PreTerm.wf_gmulE.
    move=> /andb_True [/andb_True [/forallb_True/list.Forall_forall H _] _].
    by case/andb_True: (H _ pt_in).
Qed.

Register Scheme term_rect as rect_dep for term.

Definition term_ind (P : term -> Prop) := @term_rect P.

Register Scheme term_ind as ind_dep for term.
