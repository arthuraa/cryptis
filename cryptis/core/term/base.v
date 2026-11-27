From cryptis Require Import lib.
From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import sorting gmap.
From cryptis.lib Require Import list_sort mathcomp_compat mset sms poly frac.
From iris.heap_lang Require locations.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core Require Export pre_term.

(* The "non-free" operations -- arithmetic on exponents, the group product
   and exponentiation -- are represented indirectly, by a well-formed pre-term
   whose head is a field or group operation.  [is_non_free] recognises exactly
   those heads; it lives in [PreTerm] alongside [is_gnon_free], which
   recognises the group heads. *)
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


(* [simpl never], so that simplifying a fold never evaluates [wf]. *)
Definition fold_nonfree pt :=
  if decide (PreTerm.wf pt ∧ is_non_free pt) is left pf then
    TNonFree pt (proj1 pf) (proj2 pf)
  else TInt 0 (*should never*).
Arguments fold_nonfree : simpl never.

Fixpoint fold_term_predef pt :=
  match pt with
  | PreTerm.PT0 (O0Int n) => TInt n
  | PreTerm.PT2 O2Pair pt1 pt2 =>
    TPair (fold_term_predef pt1) (fold_term_predef pt2)
  | PreTerm.PT0 (O0Nonce l) => TNonce l
  | PreTerm.PT1 (O1Key kt) pt => TKey kt (fold_term_predef pt)
  | PreTerm.PT2 O2Seal k pt => TSeal (fold_term_predef k) (fold_term_predef pt)
  | PreTerm.PT1 O1Hash pt => THash (fold_term_predef pt)
  | _ => fold_nonfree pt
  end.

lock Definition fold_term pt := fold_term_predef (PreTerm.normalize pt).

Lemma wf_unfold_term t : PreTerm.wf (unfold_term t).
Proof.
elim/term_ind': t.
- by move=> z; apply: PreTerm.wf_free0.
- by move=> t1 IH1 t2 IH2; apply/PreTerm.wf_free2.
- by move=> a; apply: PreTerm.wf_free0.
- by move=> kt t IH; apply/PreTerm.wf_free1.
- by move=> t1 IH1 t2 IH2; apply/PreTerm.wf_free2.
- by move=> t IH; apply/PreTerm.wf_free1.
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
have -> : fold_term_predef pt = fold_nonfree pt.
  by case: pt wf nf => [[]|[] ?|[] ? ?].
rewrite /fold_nonfree; case: decide => [pf|npf]; last by case: npf.
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

Lemma unfold_fold_predef pt :
  PreTerm.wf pt → unfold_term (fold_term_predef pt) = pt.
Proof.
elim: pt => [o|o t IH|o t1 IH1 t2 IH2] w.
- case N: (is_non_free (PreTerm.PT0 o)).
    by rewrite (fold_predef_NonFree w ltac:(by rewrite N)).
  by case: o w N.
- case N: (is_non_free (PreTerm.PT1 o t)).
    by rewrite (fold_predef_NonFree w ltac:(by rewrite N)).
  have wt : PreTerm.wf t.
    by move: N; rewrite PreTerm.is_non_freeE => /orb_false_elim [M D];
      apply/(PreTerm.wf_free1 _ _ M D).
  by case: o w N => [kt| | | |] w N //=; rewrite IH.
- case N: (is_non_free (PreTerm.PT2 o t1 t2)).
    by rewrite (fold_predef_NonFree w ltac:(by rewrite N)).
  have [w1 w2] : PreTerm.wf t1 ∧ PreTerm.wf t2.
    by move: N; rewrite PreTerm.is_non_freeE => /orb_false_elim [M D];
      apply/(PreTerm.wf_free2 _ _ _ M D).
  rewrite PreTerm.is_non_freeE in N.
  by case: o w N => [| | | | |] w N //=; rewrite IH1 // IH2.
Qed.

Lemma unfold_fold pt : unfold_term (fold_term pt) = PreTerm.normalize pt.
Proof.
rewrite [fold_term]unlock unfold_fold_predef //.
exact: PreTerm.wf_normalize.
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

(** Products and sums of exponents are signed multisets of terms
    ([SMS.sms]), ordered through their pre-terms. *)
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

Abbreviation term_order := (@MSet.le term _).

Lemma term_orderE t1 t2 :
  term_order t1 t2 ↔ MSet.le (unfold_term t1) (unfold_term t2).
Proof.
split; first by case=> [->|?]; [left|right].
by case=> [/unfold_term_inj ->|?]; [left|right].
Qed.

Abbreviation tsms := (SMS.sms term).
Abbreviation tfrac := (Frac.frac term).

lock Definition TMul (s : tsms) :=
  fold_term (PreTerm.mul (SMS.map unfold_term s)).

lock Definition TSum (s : tsms) :=
  fold_term (PreTerm.sum (SMS.map unfold_term s)).

(* The Diffie-Hellman group: [TGMul] is the group operation.  It lives in the
   *base* of an exponential, where [TExp] distributes over it; [TMul] and
   [TSum] live in the exponent, where it does not. *)
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

Lemma unfold_TSum s :
  unfold_term (TSum s) = PreTerm.sum (SMS.map unfold_term s).
Proof.
rewrite unlock unfold_fold PreTerm.normalize_wf //.
apply: PreTerm.wf_sum => pt /SMS.elem_of_map [t [-> _]]; exact: wf_unfold_term.
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
  PreTerm.mul (SMS.make (MSet.map unfold_term X) (MSet.map unfold_term Y)).
Proof. by rewrite unfold_TMul SMS.map_make. Qed.

Lemma unfold_TGMul_make X Y :
  unfold_term (TGMul (SMS.make X Y)) =
  PreTerm.gmul (SMS.make (MSet.map unfold_term X) (MSet.map unfold_term Y)).
Proof. by rewrite unfold_TGMul SMS.map_make. Qed.

Definition base t := fold_term (PreTerm.base (unfold_term t)).
Definition expo t := fold_term (PreTerm.expo (unfold_term t)).

Definition factors t : tsms :=
  SMS.map fold_term (PreTerm.factors (unfold_term t)).
Definition gfactors t : tsms :=
  SMS.map fold_term (PreTerm.gfactors (unfold_term t)).

(** The atoms of an exponent are the variables of its fraction. *)
Definition atoms t : list term :=
  fold_term <$> PreTerm.atoms (unfold_term t).

Definition is_nonce t :=
  if t is TNonce _ then true else false.

Definition is_exp t :=
  if t is TNonFree pt _ _ then PreTerm.is_exp pt else false.

Definition is_mod t :=
  if t is TNonFree pt _ _ then PreTerm.is_mod pt else false.

Definition is_gmul t :=
  if t is TNonFree pt _ _ then PreTerm.is_gmul pt else false.

Lemma is_nonce_unfold t : is_nonce t = PreTerm.is_nonce (unfold_term t).
Proof. by case: t => //= pt _ nf; move: nf; case: pt => [[]|? ?|? ? ?]. Qed.

Lemma is_exp_unfold t : is_exp t = PreTerm.is_exp (unfold_term t).
Proof. by case: t. Qed.

Lemma is_mod_unfold t : is_mod t = PreTerm.is_mod (unfold_term t).
Proof. by case: t. Qed.

Lemma is_gmul_unfold t : is_gmul t = PreTerm.is_gmul (unfold_term t).
Proof. by case: t. Qed.

Lemma unfold_base t : unfold_term (base t) = PreTerm.base (unfold_term t).
Proof. rewrite /base fold_termK //; exact: PreTerm.wf_base. Qed.

Lemma unfold_expo t : unfold_term (expo t) = PreTerm.expo (unfold_term t).
Proof. rewrite /expo fold_termK //; exact: PreTerm.wf_expo. Qed.

Lemma unfold_factors t :
  SMS.map unfold_term (factors t) = PreTerm.factors (unfold_term t).
Proof.
rewrite /factors SMS.map_map SMS.map_id_ext // => pt pt_in; apply: fold_termK.
exact: (PreTerm.wf_factors _ _ (wf_unfold_term t) pt_in).
Qed.

Lemma unfold_gfactors t :
  SMS.map unfold_term (gfactors t) = PreTerm.gfactors (unfold_term t).
Proof.
rewrite /gfactors SMS.map_map SMS.map_id_ext // => pt pt_in; apply: fold_termK.
by have [] := PreTerm.gfactors_elem _ _ (wf_unfold_term t) pt_in.
Qed.

Lemma elements_factors t :
  elements (factors t) =
  fold_term <$> elements (PreTerm.factors (unfold_term t)).
Proof.
rewrite -unfold_factors (SMS.elements_map_mono _ _ unfold_term_inj
  (λ a b h, proj1 (term_orderE a b) h)) -list_fmap_compose; symmetry.
rewrite -{2}(list_fmap_id (elements (factors t))).
apply: Forall_fmap_ext_1; apply/Forall_forall => x _ /=.
exact: unfold_termK.
Qed.

Lemma elements_gfactors t :
  elements (gfactors t) =
  fold_term <$> elements (PreTerm.gfactors (unfold_term t)).
Proof.
rewrite -unfold_gfactors (SMS.elements_map_mono _ _ unfold_term_inj
  (λ a b h, proj1 (term_orderE a b) h)) -list_fmap_compose; symmetry.
rewrite -{2}(list_fmap_id (elements (gfactors t))).
apply: Forall_fmap_ext_1; apply/Forall_forall => x _ /=.
exact: unfold_termK.
Qed.

Lemma elem_of_factors_unfold x t :
  x ∈ factors t ↔ unfold_term x ∈ PreTerm.factors (unfold_term t).
Proof.
rewrite -unfold_factors !SMS.elem_of_count.
by rewrite (SMS.count_map_inj _ _ _ unfold_term_inj).
Qed.

Lemma elem_of_gfactors_unfold x t :
  x ∈ gfactors t ↔ unfold_term x ∈ PreTerm.gfactors (unfold_term t).
Proof.
rewrite -unfold_gfactors !SMS.elem_of_count.
by rewrite (SMS.count_map_inj _ _ _ unfold_term_inj).
Qed.

Lemma elem_of_atoms x t :
  x ∈ atoms t ↔
  ∃ y, x = fold_term y ∧ y ∈ PreTerm.atoms (unfold_term t).
Proof. by rewrite /atoms list_elem_of_fmap. Qed.

Lemma atoms_Nmod t x : x ∈ atoms t → negb (is_mod x).
Proof.
move=> /elem_of_atoms [y [-> yt]].
have [wy ny] := PreTerm.atoms_wf _ _ (wf_unfold_term t) yt.
by rewrite is_mod_unfold fold_termK.
Qed.

Lemma atoms_atom t x : negb (is_mod t) → x ∈ atoms t ↔ x = t.
Proof.
rewrite is_mod_unfold => nt; rewrite elem_of_atoms; split.
- by move=> [y [-> /(PreTerm.atoms_atom _ _ nt) ->]]; exact: unfold_termK.
- move=> ->; exists (unfold_term t); split; first by rewrite unfold_termK.
  exact/(PreTerm.atoms_atom _ _ nt).
Qed.

Lemma Ngmul_gfactors t x :
  x ∈ gfactors t → negb (is_gmul x).
Proof.
rewrite elem_of_gfactors_unfold is_gmul_unfold => h.
by have [] := PreTerm.gfactors_elem _ _ (wf_unfold_term t) h.
Qed.

Lemma factors_Nmod t : negb (is_mod t) → factors t = {[+ t +]}.
Proof.
rewrite is_mod_unfold => Nm.
by rewrite /factors PreTerm.factors_atom // SMS.map_singleton unfold_termK.
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
exact: PreTerm.factorsK.
Qed.

Lemma gfactorsK t : TGMul (gfactors t) = t.
Proof.
apply: unfold_term_inj; rewrite unfold_TGMul unfold_gfactors.
exact: PreTerm.gfactorsK.
Qed.

Lemma factors_inj t1 t2 : factors t1 = factors t2 → t1 = t2.
Proof. by move=> e; rewrite -(factorsK t1) e factorsK. Qed.

Lemma gfactors_inj t1 t2 : gfactors t1 = gfactors t2 → t1 = t2.
Proof. by move=> e; rewrite -(gfactorsK t1) e gfactorsK. Qed.

(** [frac_of t] is the fraction that [t] denotes, over its atoms.  It is
    injective ([frac_of_inj]) and turns products, sums and inverses into field
    operations, so identities between exponents follow from field identities.
    *)
Definition frac_of t : tfrac :=
  Frac.map fold_term (PreTerm.frac_of (unfold_term t)).

Abbreviation pre_frac t := (PreTerm.frac_of (unfold_term t)).

Definition expo_frac u := PreTerm.frac_of (PreTerm.expo (unfold_term u)).

Lemma unfold_frac_of t :
  Frac.map unfold_term (frac_of t) = PreTerm.frac_of (unfold_term t).
Proof.
apply: Frac.map_cancel => m x mr xm; apply: fold_termK.
by have /andb_True [] := PreTerm.frac_of_atoms _ (wf_unfold_term t) m x mr xm.
Qed.

Lemma frac_of_inj t1 t2 : frac_of t1 = frac_of t2 → t1 = t2.
Proof.
move=> /(f_equal (Frac.map unfold_term)); rewrite !unfold_frac_of.
move=> /(f_equal PreTerm.mod_of_frac); rewrite !PreTerm.mod_of_frac_frac_of //.
exact: unfold_term_inj.
Qed.

Lemma frac_of_Nmod t : negb (is_mod t) → frac_of t = Frac.var t.
Proof.
rewrite is_mod_unfold => nt.
apply: (Frac.map_inj unfold_term unfold_term_inj).
by rewrite unfold_frac_of Frac.map_var PreTerm.frac_of_var.
Qed.

Lemma frac_of_TMul s : frac_of (TMul s) = Frac.sprod frac_of s.
Proof.
apply: (Frac.map_inj unfold_term unfold_term_inj).
have W : ∀ pt, pt ∈ SMS.map unfold_term s → PreTerm.wf pt.
  by move=> pt /SMS.elem_of_map [t [-> _]].
rewrite unfold_frac_of unfold_TMul (PreTerm.frac_of_mul _ W).
rewrite (Frac.sprod_map unfold_term _ _ unfold_term_inj).
rewrite (Frac.map_sprod unfold_term unfold_term_inj).
by apply: Frac.sprod_ext => t _; rewrite unfold_frac_of.
Qed.

Lemma frac_of_TSum s : frac_of (TSum s) = Frac.ssum frac_of s.
Proof.
apply: (Frac.map_inj unfold_term unfold_term_inj).
have W : ∀ pt, pt ∈ SMS.map unfold_term s → PreTerm.wf pt.
  by move=> pt /SMS.elem_of_map [t [-> _]].
rewrite unfold_frac_of unfold_TSum (PreTerm.frac_of_sum _ W).
rewrite Frac.ssum_map (Frac.map_ssum unfold_term unfold_term_inj).
by apply: Frac.ssum_ext => t _; rewrite unfold_frac_of.
Qed.

Lemma frac_of_TInv t : frac_of (TInv t) = Frac.inv (frac_of t).
Proof. by rewrite /TInv frac_of_TMul Frac.sprod_inv Frac.sprod_singleton. Qed.

Lemma pre_frac_TInv t :
  PreTerm.frac_of (unfold_term (TInv t)) =
  Frac.inv (PreTerm.frac_of (unfold_term t)).
Proof.
rewrite -unfold_frac_of frac_of_TInv.
by rewrite (Frac.map_inv unfold_term unfold_term_inj) unfold_frac_of.
Qed.

Lemma pre_frac_TMul s :
  PreTerm.frac_of (unfold_term (TMul s)) =
  Frac.sprod (λ u, PreTerm.frac_of (unfold_term u)) s.
Proof.
rewrite -unfold_frac_of frac_of_TMul.
rewrite (Frac.map_sprod unfold_term unfold_term_inj).
by apply: Frac.sprod_ext => u _; rewrite unfold_frac_of.
Qed.

Lemma TInvK t : TInv (TInv t) = t.
Proof. by apply: frac_of_inj; rewrite !frac_of_TInv Frac.inv_inv. Qed.

(** A Laurent monomial is a product of atoms (with [1] the empty product): its
    factors are atoms.  On Laurent monomials, [factors] is a homomorphism into
    the free abelian group on atoms ([factors_TMul]). *)
Definition laurent t := ∀ x, x ∈ factors t → negb (is_mod x).

Lemma factors_TMul_atoms s :
  (∀ x, x ∈ s → negb (is_mod x)) → factors (TMul s) = s.
Proof.
move=> A.
have H : ∀ y, y ∈ SMS.map unfold_term s →
    PreTerm.wf y ∧ negb (PreTerm.is_mod y).
  move=> y /SMS.elem_of_map [x [-> xs]]; split=> //.
  by rewrite -is_mod_unfold; exact: A.
rewrite /factors unfold_TMul (PreTerm.factors_mul_atoms _ H).
by rewrite SMS.map_map SMS.map_id_ext // => x _; exact: unfold_termK.
Qed.

Lemma laurent_TMul_atoms s :
  (∀ x, x ∈ s → negb (is_mod x)) → laurent (TMul s).
Proof. by move=> A x; rewrite factors_TMul_atoms //; exact: A. Qed.

Lemma laurent_atom t : negb (is_mod t) → laurent t.
Proof.
by move=> nt x; rewrite factors_Nmod // => /SMS.elem_of_singleton ->.
Qed.

Lemma factors_TMul s :
  (∀ x, x ∈ s → laurent x) → factors (TMul s) = SMS.bind factors s.
Proof.
move=> L.
have A : ∀ y, y ∈ SMS.bind factors s → negb (is_mod y).
  by move=> y /SMS.elem_of_bind [x [xs yx]]; exact: L x xs y yx.
have NZ : ∀ x y, x ∈ s → y ∈ factors x → frac_of y ≠ Frac.zero.
  move=> x y xs yx; rewrite frac_of_Nmod; last exact: L x xs y yx.
  exact: Frac.var_neq0.
rewrite -(factors_TMul_atoms _ A); congr factors.
apply: frac_of_inj; rewrite !frac_of_TMul (Frac.sprod_bind _ _ _ NZ).
by apply: Frac.sprod_ext => x _; rewrite -frac_of_TMul factorsK.
Qed.

Definition count x t := SMS.count x (factors t).
Definition gcount x t := SMS.count x (gfactors t).

Lemma count_unfold x t :
  count x t = SMS.count (unfold_term x) (PreTerm.factors (unfold_term t)).
Proof.
by rewrite /count -unfold_factors (SMS.count_map_inj _ _ _ unfold_term_inj).
Qed.

(** On atoms, [count] is the valuation of the fraction. *)
Lemma count_valuation x t :
  negb (is_mod x) →
  count x t = Frac.valuation (unfold_term x) (PreTerm.frac_of (unfold_term t)).
Proof.
rewrite is_mod_unfold count_unfold => nx; exact: PreTerm.count_valuation.
Qed.

Lemma is_gmul_gcount x t : is_gmul x → gcount x t = 0%Z.
Proof.
move=> Mx; case: (decide (x ∈ gfactors t)) => x_t.
  by move/Ngmul_gfactors: x_t; case: (is_gmul x) Mx.
by move: x_t; rewrite SMS.elem_of_count /gcount; lia.
Qed.

Lemma count_inj t1 t2 :
  laurent t1 → laurent t2 →
  (∀ x, negb (is_mod x) → count x t1 = count x t2) → t1 = t2.
Proof.
move=> L1 L2 e; apply: factors_inj; apply: SMS.count_inj => x.
case Ex: (is_mod x); last by apply: e; rewrite Ex.
have N t : laurent t → SMS.count x (factors t) = 0%Z.
  move=> L; case: (decide (x ∈ factors t)) => xt.
    by move: (L x xt); rewrite Ex.
  by move: xt; rewrite SMS.elem_of_count; lia.
by rewrite !N.
Qed.

Lemma gcount_inj t1 t2 :
  (∀ x, negb (is_gmul x) → gcount x t1 = gcount x t2) → t1 = t2.
Proof.
move=> e; apply: gfactors_inj; apply: SMS.count_inj => x.
case Ex: (is_gmul x); last by apply: e; rewrite Ex.
by rewrite -/(gcount x t1) -/(gcount x t2) !is_gmul_gcount ?Ex.
Qed.

Lemma laurent_inv_singleton t :
  laurent t → ∀ x, x ∈ SMS.inv {[+ t +]} → laurent x.
Proof.
move=> L x /SMS.elem_of_count; rewrite SMS.count_inv => h.
have : x ∈ ({[+ t +]} : tsms) by apply/SMS.elem_of_count; lia.
by move/SMS.elem_of_singleton => ->.
Qed.

Lemma factors_TInv t : laurent t → factors (TInv t) = SMS.inv (factors t).
Proof.
move=> L; rewrite /TInv factors_TMul; last exact: laurent_inv_singleton.
by rewrite SMS.bind_inv SMS.bind_singleton.
Qed.

(** A group element has Laurent logarithms when each of its logarithms has a
    monomial denominator.  On such elements, [gfactors] is a homomorphism into
    the free abelian group on non-products ([gfactors_TGMul]). *)
Definition mono_den_logs t := PreTerm.mono_den_logs (unfold_term t).

Lemma gfactors_TGMul s :
  (∀ x, x ∈ s → mono_den_logs x) → gfactors (TGMul s) = SMS.bind gfactors s.
Proof.
move=> L.
have H : ∀ y, y ∈ SMS.map unfold_term s → PreTerm.wf y ∧
  PreTerm.mono_den_logs y.
  by move=> y /SMS.elem_of_map [x [-> /L lx]].
rewrite {1}/gfactors unfold_TGMul (PreTerm.gfactors_gmul _ H).
by rewrite SMS.bind_map SMS.map_bind.
Qed.

Lemma gfactors_TGInv t : gfactors (TGInv t) = SMS.inv (gfactors t).
Proof.
rewrite {1}/gfactors /TGInv unfold_TGMul SMS.map_inv SMS.map_singleton.
by rewrite PreTerm.gfactors_ginv // SMS.map_inv.
Qed.

Lemma TGInvK t : TGInv (TGInv t) = t.
Proof. by apply: gfactors_inj; rewrite !gfactors_TGInv SMS.invK. Qed.

Lemma gcount_TGInv t t' : gcount t (TGInv t') = (- gcount t t')%Z.
Proof. by rewrite /gcount gfactors_TGInv SMS.count_inv. Qed.

Lemma count_TInv x t : negb (is_mod x) → count x (TInv t) = (- count x t)%Z.
Proof.
move=> nx; rewrite !count_valuation // -!unfold_frac_of frac_of_TInv.
by rewrite (Frac.map_inv unfold_term unfold_term_inj) Frac.valuation_inv.
Qed.
