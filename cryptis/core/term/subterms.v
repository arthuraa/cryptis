From cryptis Require Import lib.
From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import sorting gmap.
From cryptis.lib Require Import list_sort mathcomp_compat mset sms.
From iris.heap_lang Require locations.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core Require Export pre_term.
From cryptis.core.term Require Import base algebra tsize repr nonces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Implicit Types (t k : term) (ts : list term).

(* subterms (the subterm set); subtermsP links it to the subterm relation in
   algebra.v. *)

Inductive subterm (t : term) : term → Prop :=
| STRefl : subterm t t
| STPair1 t1 t2 of subterm t t1 : subterm t (TPair t1 t2)
| STPair2 t1 t2 of subterm t t2 : subterm t (TPair t1 t2)
| STKey kt t' of subterm t t' : subterm t (TKey kt t')
| STSeal1 k t' of subterm t k : subterm t (TSeal k t')
| STSeal2 k t' of subterm t t' : subterm t (TSeal k t')
| STHash t' of subterm t t' : subterm t (THash t')
| STExp1 t' e of negb (is_exp t') & negb (is_gmul t') & subterm t t'
  : subterm t (TExp t' e)
| STExp2 t' t'' e of negb (is_exp t') & negb (is_gmul t') &
    subterm t t'' & t'' ∈ factors e
  : subterm t (TExp t' e)
| STMul t'' (s : tsms) of (∀ x, x ∈ s → negb (is_mul x)) &
    subterm t t'' & t'' ∈ s
  : subterm t (TMul s)
| STGMul t'' (s : tsms) of (∀ x, x ∈ s → negb (is_gmul x)) &
    subterm t t'' & t'' ∈ s
  : subterm t (TGMul s).

#[global] Instance subterm_refl : Reflexive subterm.
Proof. exact: STRefl. Qed.
#[global] Hint Resolve STRefl : core.

#[global] Instance subterm_trans : Transitive subterm.
Proof.
move=> t1 t2 t3 sub12 sub13; elim: t3 / sub13;
by eauto using subterm.
Qed.

(* The subterms of an exponential [b ^ x] are those of [b] and of the factors
   of [x]; those of a group product are those of its factors [b ^ x]. *)
Fixpoint ssubterms_pre_def (t : PreTerm.pre_term) : gset term :=
  let subterms_pre_def (t : PreTerm.pre_term) :=
    {[fold_term t]} ∪ ssubterms_pre_def t in
  let ssubterms_expo (x : PreTerm.pre_term) :=
    match x with
    | PreTerm.PTMul ps ns =>
      ⋃ map subterms_pre_def ps ∪ ⋃ map subterms_pre_def ns
    | _ => subterms_pre_def x
    end in
  let subterms_factor (b x : PreTerm.pre_term) :=
    match x with
    | PreTerm.PTMul [] [] => subterms_pre_def b
    | _ => {[fold_term (PreTerm.PTDH [(b, ([x], []))])]} ∪
           (subterms_pre_def b ∪ ssubterms_expo x)
    end in
  match t with
  | PreTerm.PT0 (O0Int _) => ∅
  | PreTerm.PT2 O2Pair t1 t2 => subterms_pre_def t1 ∪ subterms_pre_def t2
  | PreTerm.PT0 (O0Nonce _) => ∅
  | PreTerm.PT1 (O1Key _) t => subterms_pre_def t
  | PreTerm.PT2 O2Seal t1 t2 => subterms_pre_def t1 ∪ subterms_pre_def t2
  | PreTerm.PT1 O1Hash t => subterms_pre_def t
  | PreTerm.PTMul ps ns =>
    ⋃ map subterms_pre_def ps ∪ ⋃ map subterms_pre_def ns
  | PreTerm.PTDH [(b, ([x], []))] => subterms_pre_def b ∪ ssubterms_expo x
  | PreTerm.PTDH l =>
    ⋃ map (λ e, ⋃ map (subterms_factor e.1) e.2.1 ∪
                ⋃ map (subterms_factor e.1) e.2.2) l
  end.

lock Definition subterms t := {[t]} ∪ ssubterms_pre_def (unfold_term t).

Definition subterms_pre pt := {[fold_term pt]} ∪ ssubterms_pre_def pt.

Definition ssubterms_expo x :=
  match x with
  | PreTerm.PTMul ps ns => ⋃ map subterms_pre ps ∪ ⋃ map subterms_pre ns
  | _ => subterms_pre x
  end.

Definition subterms_factor b x :=
  match x with
  | PreTerm.PTMul [] [] => subterms_pre b
  | _ => {[fold_term (PreTerm.PTDH [(b, ([x], []))])]} ∪
         (subterms_pre b ∪ ssubterms_expo x)
  end.

Lemma ssubterms_pre_def_power b x :
  ssubterms_pre_def (PreTerm.PTDH [(b, ([x], []))]) =
  subterms_pre b ∪ ssubterms_expo x.
Proof. done. Qed.

Lemma ssubterms_pre_def_gmul l :
  PreTerm.is_gmul (PreTerm.PTDH l) →
  ssubterms_pre_def (PreTerm.PTDH l) =
  ⋃ map (λ e, ⋃ map (subterms_factor e.1) e.2.1 ∪
              ⋃ map (subterms_factor e.1) e.2.2) l.
Proof. by case: l => [|[b [[|x [|??]] [|??]]] [|??]]. Qed.

Lemma ssubterms_expoE x :
  PreTerm.wf x →
  ssubterms_expo x = ⋃ map subterms_pre (elements (PreTerm.factors x)).
Proof.
move=> wf_x; rewrite (PreTerm.elements_factors _ wf_x).
case: x {wf_x} => [o|o u|o u1 u2|ps ns|l] //=;
  rewrite ?map_app ?union_list_app_L /=; set_solver.
Qed.

Lemma subterms_pre_mk_exp b x :
  subterms_pre (PreTerm.mk_exp b x) = subterms_factor b x.
Proof.
rewrite /PreTerm.mk_exp.
case: (bool_decide_reflect (x = PreTerm.PTMul [] [])) => [->|nx] //.
rewrite /subterms_pre ssubterms_pre_def_power /subterms_factor.
by case: x nx => [?|??|???|[|??] [|??]|?] //; case.
Qed.

Lemma subterms_pre_dh_elements l :
  ⋃ map subterms_pre (PreTerm.dh_elements l) =
  ⋃ map (λ e, ⋃ map (subterms_factor e.1) e.2.1 ∪
              ⋃ map (subterms_factor e.1) e.2.2) l.
Proof.
have mapE b xs :
    ⋃ map subterms_pre (PreTerm.mk_exp b <$> xs) =
    ⋃ map (subterms_factor b) xs.
  by elim: xs => [//|x xs IH] /=; rewrite subterms_pre_mk_exp IH.
elim: l => [//|[b [ps ns]] l IH] /=.
by rewrite map_app union_list_app_L IH fmap_app map_app union_list_app_L
  !mapE.
Qed.

Lemma subterms_fold pt :
  PreTerm.wf pt -> subterms (fold_term pt) = subterms_pre pt.
Proof.
by move => wf; rewrite [subterms]unlock /subterms_pre (@fold_termK pt wf).
Qed.

Lemma subterms_via_pre t : subterms t = subterms_pre (unfold_term t).
Proof. by rewrite [subterms]unlock /subterms_pre unfold_termK. Qed.

(* [subterms_pre] of a pre-term is its own root plus the subterms of its
   factors (for a non-product the factor list is the singleton). *)
Lemma subterms_pre_factors pt :
  PreTerm.wf pt →
  subterms_pre pt =
  {[fold_term pt]} ∪ ⋃ map subterms_pre (elements (PreTerm.factors pt)).
Proof.
move=> wf_pt; rewrite (PreTerm.elements_factors _ wf_pt).
case: pt {wf_pt} => [o|o e|o e1 e2|ps ns|l] /=; rewrite /subterms_pre //=;
  rewrite ?map_app ?union_list_app_L; set_solver.
Qed.

Lemma subterms_pre_gfactors pt :
  PreTerm.wf pt →
  subterms_pre pt =
  {[fold_term pt]} ∪ ⋃ map subterms_pre (elements (PreTerm.gfactors pt)).
Proof.
move=> wf_pt; case Eg: (PreTerm.is_gmul pt); last first.
  rewrite PreTerm.gfactors_Ngmul ?Eg // SMS.elements_singleton /=.
  rewrite /subterms_pre; set_solver.
case: pt Eg wf_pt => // l Eg wf_l.
rewrite (union_list_permutation_proper_L _ _
           (Permutation_map _ (PreTerm.elements_gfactors _ wf_l))).
rewrite subterms_pre_dh_elements /subterms_pre ssubterms_pre_def_gmul //.
by rewrite Eg.
Qed.

Lemma subterms_pre_base_exps pt :
  PreTerm.wf pt →
  subterms_pre pt =
  {[fold_term pt]} ∪ subterms_pre (PreTerm.base pt) ∪
  ⋃ map subterms_pre (elements (PreTerm.factors (PreTerm.expo pt))).
Proof.
case: (PreTerm.is_expP pt) => [b x ->|Nxp -> ->] wf_pt.
- have [_ [_ [wf_x _]]] := proj1 (PreTerm.wf_dh_single b x) wf_pt.
  rewrite /= -(ssubterms_expoE wf_x) {1}/subterms_pre.
  by rewrite ssubterms_pre_def_power union_assoc_L.
- rewrite (PreTerm.elements_factors _ PreTerm.wf_one) /=.
  rewrite /subterms_pre; set_solver.
Qed.

Lemma union_list_map_subterms_fold (L : list PreTerm.pre_term) :
  (∀ x, x ∈ L → PreTerm.wf x) →
  ⋃ map subterms_pre L = ⋃ map subterms (fold_term <$> L).
Proof.
elim: L => [//|p ps IH] wfP /=.
rewrite subterms_fold ?IH //; last by apply: wfP; exact: list_elem_of_here.
by move=> x x_ps; apply: wfP; exact: list_elem_of_further.
Qed.

Lemma subterms_base_exps t :
  subterms t =
  {[t]} ∪ subterms (base t) ∪ ⋃ map subterms (elements (exps t)).
Proof.
have hb : subterms_pre (PreTerm.base (unfold_term t)) = subterms (base t).
  by rewrite /base (subterms_fold (PreTerm.wf_base _ (wf_unfold_term t))).
have he :
    ⋃ map subterms_pre
      (elements (PreTerm.factors (PreTerm.expo (unfold_term t)))) =
    ⋃ map subterms (elements (exps t)).
  rewrite /exps elements_factors unfold_expo.
  apply: union_list_map_subterms_fold => x /SMS.elem_of_elements.
  exact: PreTerm.wf_factors_wf
    (PreTerm.wf_wf_factors _ (PreTerm.wf_expo _ (wf_unfold_term t))).
rewrite (subterms_via_pre t) (subterms_pre_base_exps (wf_unfold_term t)).
by rewrite unfold_termK hb he.
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
rewrite [subterms]unlock /=.
case: t =>> //=; try by rewrite ?unfold_termK.
Qed.

Lemma subterms_TMul s :
  (∀ x, x ∈ s → negb (is_mul x)) →
  subterms (TMul s) = {[TMul s]} ∪ ⋃ map subterms (elements s).
Proof.
move=> Hs; rewrite subterms_via_pre (subterms_pre_factors (wf_unfold_term _)).
rewrite unfold_termK; congr (_ ∪ _).
rewrite -unfold_factors (factors_TMul_atoms _ Hs).
rewrite (SMS.elements_map_inj _ _ unfold_term_inj).
elim: (elements s) => [//|x xs IH] /=.
by rewrite IH subterms_via_pre.
Qed.

Lemma subterms_TGMul s :
  (∀ x, x ∈ s → negb (is_gmul x)) →
  subterms (TGMul s) = {[TGMul s]} ∪ ⋃ map subterms (elements s).
Proof.
move=> Hs; rewrite subterms_via_pre (subterms_pre_gfactors (wf_unfold_term _)).
rewrite unfold_termK; congr (_ ∪ _).
rewrite -unfold_gfactors (gfactors_TGMul_atoms _ Hs).
rewrite (SMS.elements_map_inj _ _ unfold_term_inj).
elim: (elements s) => [//|x xs IH] /=.
by rewrite IH subterms_via_pre.
Qed.

Lemma subterms_TInv t :
  negb (is_mul t) -> subterms (TInv t) = {[TInv t]} ∪ subterms t.
Proof.
have Et : elements (SMS.inv {[+ t +]}) = [t] by [].
move=> Nm; rewrite /TInv subterms_TMul; last first.
  by move=> x; rewrite -SMS.elem_of_elements Et => /list_elem_of_singleton ->.
rewrite Et.
by rewrite /= union_empty_r_L.
Qed.

Lemma subterms_TGInv t :
  negb (is_gmul t) -> subterms (TGInv t) = {[TGInv t]} ∪ subterms t.
Proof.
have Et : elements (SMS.inv {[+ t +]}) = [t] by [].
move=> Nm; rewrite /TGInv subterms_TGMul; last first.
  by move=> x; rewrite -SMS.elem_of_elements Et => /list_elem_of_singleton ->.
rewrite Et.
by rewrite /= union_empty_r_L.
Qed.

Lemma subterms_TExp t e :
  negb (is_exp t) -> negb (is_gmul t) ->
  subterms (TExp t e) =
  {[TExp t e]} ∪ subterms t ∪ ⋃ map subterms (elements (factors e)).
Proof.
move=> tNexp tNm.
rewrite (subterms_base_exps (TExp t e)) (base_TExp _ _ tNm) (base_expN _ tNexp).
by rewrite (exps_TExp_expN _ _ tNexp tNm).
Qed.

Lemma subterms_TExp_TMul t s :
  negb (is_exp t) -> negb (is_gmul t) ->
  (∀ u, u ∈ s → negb (is_mul u)) ->
  subterms (TExp t (TMul s)) =
  {[TExp t (TMul s)]} ∪ subterms t ∪ ⋃ map subterms (elements s).
Proof. by move=> tNexp tNm Hs; rewrite subterms_TExp // factors_TMul_atoms. Qed.

Lemma subterms_nonce t : is_nonce t → subterms t = {[t]}.
Proof.
by case: t => //= ? _; rewrite subtermsE' right_id_L.
Qed.

Lemma subterm_factors t b u : u ∈ factors b -> subterm t u -> subterm t b.
Proof.
move=> u_b sub; rewrite -(factorsK b).
by apply: (@STMul _ u) => // x; apply: Nmul_factors.
Qed.

Lemma subterm_gfactors t b u : u ∈ gfactors b -> subterm t u -> subterm t b.
Proof.
move=> u_b sub; rewrite -(gfactorsK b).
by apply: (@STGMul _ u) => // x; apply: Ngmul_gfactors.
Qed.

Definition subtermsE :=
  (subterms_TInv, subterms_TGInv, subterms_TExp_TMul, subterms_TMul,
   subterms_TGMul, subtermsE').

Lemma subtermsP t1 t2 : subterm t1 t2 ↔ t1 ∈ subterms t2.
Proof.
split.
- elim: t2 /; try by intros; rewrite subtermsE //; set_solver.
  + by move=> t' e Nexp Nm sub IH; rewrite subterms_TExp //; set_solver.
  + move => t' t'' e Nexp Nm sub IH t''_e.
    rewrite subterms_TExp // !elem_of_union; right.
    rewrite elem_of_union_list; exists (subterms t''); split => //.
    rewrite list_elem_of_fmap; exists t''; split=> //.
    exact/SMS.elem_of_elements.
  + move => t'' s Hs sub IH t''_s.
    rewrite (subterms_TMul Hs) elem_of_union; right.
    rewrite elem_of_union_list; exists (subterms t''); split => //.
    rewrite list_elem_of_fmap; exists t''; split=> //.
    exact/SMS.elem_of_elements.
  + move => t'' s Hs sub IH t''_s.
    rewrite (subterms_TGMul Hs) elem_of_union; right.
    rewrite elem_of_union_list; exists (subterms t''); split => //.
    rewrite list_elem_of_fmap; exists t''; split=> //.
    exact/SMS.elem_of_elements.
- elim/term_lt_ind: t2 => t2 IH.
  case: t2 IH => [n|ta tb|a|kt tt|kk tt|tt|pt wf nf] IH.
  + rewrite subtermsE' /=.
    by move => /elem_of_union [/elem_of_singleton -> | /elem_of_empty []].
  + rewrite subtermsE' /=.
    move => /elem_of_union [/elem_of_singleton -> | /elem_of_union [H|H]].
    * exact: STRefl.
    * apply: STPair1; apply: (IH ta _ H).
      by rewrite [tsize (TPair ta tb)]tsize_eq; lia.
    * apply: STPair2; apply: (IH tb _ H).
      by rewrite [tsize (TPair ta tb)]tsize_eq; lia.
  + rewrite subtermsE' /=.
    by move => /elem_of_union [/elem_of_singleton -> | /elem_of_empty []].
  + rewrite subtermsE' /=; move => /elem_of_union [/elem_of_singleton -> | H].
    * exact: STRefl.
    * apply: STKey; apply: (IH tt _ H).
      by rewrite [tsize (TKey kt tt)]tsize_eq; lia.
  + rewrite subtermsE' /=.
    move => /elem_of_union [/elem_of_singleton -> | /elem_of_union [H|H]].
    * exact: STRefl.
    * apply: STSeal1; apply: (IH kk _ H).
      by rewrite [tsize (TSeal kk tt)]tsize_eq; lia.
    * apply: STSeal2; apply: (IH tt _ H).
      by rewrite [tsize (TSeal kk tt)]tsize_eq; lia.
  + rewrite subtermsE' /=; move => /elem_of_union [/elem_of_singleton -> | H].
    * exact: STRefl.
    * apply: STHash; apply: (IH tt _ H).
      by rewrite [tsize (THash tt)]tsize_eq; lia.
  + case: pt wf nf IH => [o|[kt'|] operand|[|] u1 u2|ps ns|l] wf nf IH.
    1-5: by move: {IH} nf; rewrite /is_non_free /=.
    * set t2' := TNonFree (PreTerm.PTMul ps ns) wf nf.
      have xt : is_mul t2' by [].
      have Hs : ∀ x, x ∈ factors t2' → negb (is_mul x) by apply: Nmul_factors.
      rewrite -(factorsK t2') (subterms_TMul Hs).
      move => /elem_of_union [/elem_of_singleton -> | He].
      -- exact: STRefl.
      -- move: He => /elem_of_union_list
         [X [/list_elem_of_fmap [ff [-> /SMS.elem_of_elements ff_facts]] Hin]].
         apply: (STMul Hs _ ff_facts).
         apply: (IH ff _ Hin).
         exact: (tsize_factors_lt _ _ xt ff_facts).
    * set t2' := TNonFree (PreTerm.PTDH l) wf nf.
      case Ex: (PreTerm.is_exp (PreTerm.PTDH l)).
      ** have xt : is_exp t2' by rewrite is_exp_unfold Ex.
         have Nmb : negb (is_gmul (base t2')).
           by rewrite is_gmul_base; exact: (is_exp_Ngmul _ xt).
         rewrite (subterms_base_exps t2').
         move=> /elem_of_union
           [/elem_of_union [/elem_of_singleton -> | Hb] | He].
         -- exact: STRefl.
         -- rewrite -(TExp_base_expo t2').
            apply: STExp1; [exact: base_Nexp|exact: Nmb|].
            by apply: (IH (base t2') _ Hb); exact: (tsize_base_lt _ xt).
         -- move: He => /elem_of_union_list.
            move=> [X [/list_elem_of_fmap
              [ee [-> /SMS.elem_of_elements ee_exps]] Hin]].
            rewrite -(TExp_base_expo t2').
            apply: (STExp2 (base_Nexp t2') Nmb _ ee_exps).
            by apply: (IH ee _ Hin); exact: (tsize_exps_lt _ _ ee_exps).
      ** have xt : is_gmul t2'.
           rewrite is_gmul_unfold; move: (PreTerm.is_non_free_dh l).
           by rewrite /PreTerm.is_non_free Ex /=.
         have Hs : ∀ x, x ∈ gfactors t2' → negb (is_gmul x).
           by apply: Ngmul_gfactors.
         rewrite -(gfactorsK t2') (subterms_TGMul Hs).
         move => /elem_of_union [/elem_of_singleton -> | He].
         -- exact: STRefl.
         -- move: He => /elem_of_union_list [X [/list_elem_of_fmap
              [ff [-> /SMS.elem_of_elements ff_facts]] Hin]].
            apply: (STGMul Hs _ ff_facts).
            apply: (IH ff _ Hin).
            exact: (tsize_gfactors_lt _ _ xt ff_facts).
Qed.

Lemma subterm_base t : subterm (base t) t.
Proof.
by rewrite subtermsP subterms_base_exps !elem_of_union -subtermsP; auto.
Qed.

Lemma subterm_exps t1 t2 : t1 ∈ exps t2 → subterm t1 t2.
Proof.
rewrite subtermsP subterms_base_exps !elem_of_union.
move=> /SMS.elem_of_elements t1_t2.
right; rewrite elem_of_union_list; exists (subterms t1).
by rewrite -subtermsP; split => //; apply/list_elem_of_fmap; eauto.
Qed.

Lemma subterm_TExp_g g (x : nonce) :
  negb (is_exp g) → negb (is_gmul g) → subterm (TNonce x) (TExp g x).
Proof.
move=> gNX gNm; apply: (STExp2 gNX gNm (STRefl _)).
by rewrite elem_of_factors_Nmul.
Qed.

Lemma nonces_of_term_TMul s :
  (∀ x, x ∈ s → negb (is_mul x)) →
  nonces_of_term (TMul s) = ⋃ map nonces_of_term (elements s).
Proof. by move=> Hs; rewrite nonces_of_term_factors factors_TMul_atoms. Qed.

Lemma nonces_of_term_TGMul s :
  (∀ x, x ∈ s → negb (is_gmul x)) →
  nonces_of_term (TGMul s) = ⋃ map nonces_of_term (elements s).
Proof. by move=> Hs; rewrite nonces_of_term_gfactors gfactors_TGMul_atoms. Qed.

Lemma nonces_of_term_TExp t e :
  negb (is_exp t) -> negb (is_gmul t) ->
  nonces_of_term (TExp t e) =
  nonces_of_term t ∪ ⋃ map nonces_of_term (elements (factors e)).
Proof.
move=> tNexp tNm.
rewrite (nonces_of_term_base_exps (TExp t e)) (base_TExp _ _ tNm).
by rewrite (base_expN _ tNexp) (exps_TExp_expN _ _ tNexp tNm).
Qed.

Lemma nonces_of_termP (a : nonce) t :
  subterm (TNonce a) t ↔ a ∈ nonces_of_term t.
Proof.
split.
- elim: t /; try by intros; rewrite nonces_of_termE; set_solver.
  + by move=> t' e Nexp Nm sub IH; rewrite nonces_of_term_TExp //; set_solver.
  + move => t' t'' e Nexp Nm sub IH t''_e.
    rewrite nonces_of_term_TExp // elem_of_union; right.
    rewrite elem_of_union_list; exists (nonces_of_term t''); split => //.
    rewrite list_elem_of_fmap; exists t''; split=> //.
    exact/SMS.elem_of_elements.
  + move => t'' s Hs sub IH t''_s.
    rewrite (nonces_of_term_TMul Hs) elem_of_union_list.
    exists (nonces_of_term t''); split => //.
    rewrite list_elem_of_fmap; exists t''; split=> //.
    exact/SMS.elem_of_elements.
  + move => t'' s Hs sub IH t''_s.
    rewrite (nonces_of_term_TGMul Hs) elem_of_union_list.
    exists (nonces_of_term t''); split => //.
    rewrite list_elem_of_fmap; exists t''; split=> //.
    exact/SMS.elem_of_elements.
- elim/term_lt_ind: t => t IH.
  case: t IH => [n|ta tb|a'|kt tt|kk tt|tt|pt wf nf] IH.
  + by rewrite nonces_of_termE' /=; move => /elem_of_empty [].
  + rewrite nonces_of_termE' /=; move => /elem_of_union [H|H].
    * apply: STPair1; apply: (IH ta _ H).
      by rewrite [tsize (TPair ta tb)]tsize_eq; lia.
    * apply: STPair2; apply: (IH tb _ H).
      by rewrite [tsize (TPair ta tb)]tsize_eq; lia.
  + by rewrite nonces_of_termE' /=; move => /elem_of_singleton ->.
  + rewrite nonces_of_termE' /=; move => H.
    apply: STKey; apply: (IH tt _ H).
    by rewrite [tsize (TKey kt tt)]tsize_eq; lia.
  + rewrite nonces_of_termE' /=; move => /elem_of_union [H|H].
    * apply: STSeal1; apply: (IH kk _ H).
      by rewrite [tsize (TSeal kk tt)]tsize_eq; lia.
    * apply: STSeal2; apply: (IH tt _ H).
      by rewrite [tsize (TSeal kk tt)]tsize_eq; lia.
  + rewrite nonces_of_termE' /=; move => H.
    apply: STHash; apply: (IH tt _ H).
    by rewrite [tsize (THash tt)]tsize_eq; lia.
  + case: pt wf nf IH => [o|[kt'|] operand|[|] u1 u2|ps ns|l] wf nf IH.
    1-5: by move: {IH} nf; rewrite /is_non_free /=.
    * set t2' := TNonFree (PreTerm.PTMul ps ns) wf nf.
      have xt : is_mul t2' by [].
      have Hs : ∀ x, x ∈ factors t2' → negb (is_mul x) by apply: Nmul_factors.
      rewrite -(factorsK t2') (nonces_of_term_TMul Hs).
      move=> /elem_of_union_list
        [X [/list_elem_of_fmap [ff [-> /SMS.elem_of_elements ff_facts]] Hin]].
      apply: (STMul Hs _ ff_facts).
      apply: (IH ff _ Hin).
      exact: (tsize_factors_lt _ _ xt ff_facts).
    * set t2' := TNonFree (PreTerm.PTDH l) wf nf.
      case Ex: (PreTerm.is_exp (PreTerm.PTDH l)).
      ** have xt : is_exp t2' by rewrite is_exp_unfold Ex.
         have Nmb : negb (is_gmul (base t2')).
           by rewrite is_gmul_base; exact: (is_exp_Ngmul _ xt).
         rewrite (nonces_of_term_base_exps t2').
         move => /elem_of_union [Hb | He].
         -- rewrite -(TExp_base_expo t2').
            apply: STExp1; [exact: base_Nexp|exact: Nmb|].
            by apply: (IH (base t2') _ Hb); exact: (tsize_base_lt _ xt).
         -- move: He => /elem_of_union_list.
            move=> [X [/list_elem_of_fmap
              [ee [-> /SMS.elem_of_elements ee_exps]] Hin]].
            rewrite -(TExp_base_expo t2').
            apply: (STExp2 (base_Nexp t2') Nmb _ ee_exps).
            by apply: (IH ee _ Hin); exact: (tsize_exps_lt _ _ ee_exps).
      ** have xt : is_gmul t2'.
           rewrite is_gmul_unfold; move: (PreTerm.is_non_free_dh l).
           by rewrite /PreTerm.is_non_free Ex /=.
         have Hs : ∀ x, x ∈ gfactors t2' → negb (is_gmul x).
           by apply: Ngmul_gfactors.
         rewrite -(gfactorsK t2') (nonces_of_term_TGMul Hs).
         move=> /elem_of_union_list [X [/list_elem_of_fmap
           [ff [-> /SMS.elem_of_elements ff_facts]] Hin]].
         apply: (STGMul Hs _ ff_facts).
         apply: (IH ff _ Hin).
         exact: (tsize_gfactors_lt _ _ xt ff_facts).
Qed.

Lemma subterm_nonces_of_term t1 t2 :
  subterm t1 t2 → nonces_of_term t1 ⊆ nonces_of_term t2.
Proof.
have sub_union (u : term) (us : list term) :
    u ∈ us → nonces_of_term u ⊆ ⋃ map nonces_of_term us.
  move=> u_us x x_u; rewrite elem_of_union_list.
  exists (nonces_of_term u); split => //.
  by rewrite list_elem_of_fmap; exists u; split.
elim: t2 / => //; try by intros; rewrite [X in _ ⊆ X]nonces_of_termE; set_solver.
- by move=> t' e Nexp Nm sub IH; rewrite nonces_of_term_TExp //; set_solver.
- move => t' t'' e Nexp Nm sub IH /SMS.elem_of_elements t''_e.
  rewrite nonces_of_term_TExp //.
  have := sub_union _ _ t''_e; set_solver.
- move=> t'' s Hs sub IH /SMS.elem_of_elements t''_s.
  rewrite (nonces_of_term_TMul Hs).
  have := sub_union _ _ t''_s; set_solver.
- move=> t'' s Hs sub IH /SMS.elem_of_elements t''_s.
  rewrite (nonces_of_term_TGMul Hs).
  have := sub_union _ _ t''_s; set_solver.
Qed.
