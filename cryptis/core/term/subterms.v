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
From cryptis.core.term Require Import base algebra tsize repr nonces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Implicit Types (t k : term) (ts : list term).

(* subterms (the subterm set); subtermsP links it to the subterm relation in algebra.v.
   (Split out of the former monolithic core/term/base.v.) *)

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
    invs_canceled ts &
    subterm t t'' &
    t'' ∈ ts
  : subterm t (TExpN t' ts)
| STMul t'' ts of
    invs_canceled ts &
    subterm t t'' &
    t'' ∈ ts
  : subterm t (TMulN ts).

Global Instance subterm_trans : Transitive subterm.
Proof.
move=> t1 t2 t3 sub12 sub13; elim: t3 / sub13;
by eauto using subterm.
Qed.

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
  {[fold_term pt]} ∪ subterms_pre (PreTerm.base pt) ∪
  ⋃ map subterms_pre (PreTerm.factors (PreTerm.expo pt)).
Proof.
case E: (PreTerm.is_exp pt).
- case: pt E => [o|o e|[||] e1 e2|es] //= E; rewrite subterms_preE /=; set_solver.
- have Nxp : negb (PreTerm.is_exp pt) by rewrite E.
  rewrite (PreTerm.base_expN pt Nxp) (PreTerm.expo_expN pt Nxp) /=.
  rewrite /subterms_pre; set_solver.
Qed.

Lemma subterms_base_exps t :
  subterms t = {[t]} ∪ subterms (base t) ∪ ⋃ map subterms (exps t).
Proof.
have hb : subterms_pre (PreTerm.base (unfold_term t)) = subterms (base t).
  by rewrite /base (subterms_fold (PreTerm.wf_base _ (wf_unfold_term t))).
have he : ⋃ map subterms_pre (PreTerm.factors (PreTerm.expo (unfold_term t)))
        = ⋃ map subterms (exps t).
  rewrite /exps /factors unfold_expo.
  have wfs : Forall PreTerm.wf (PreTerm.factors (PreTerm.expo (unfold_term t))).
    apply/Forall_forall => x xin.
    apply: PreTerm.wf_factors_wf
      (PreTerm.wf_wf_factors _ (PreTerm.wf_expo _ (wf_unfold_term t))) xin.
  elim: (PreTerm.factors (PreTerm.expo (unfold_term t))) wfs
    => [//|pt pts IH] /Forall_cons [wpt wpts] /=.
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
have Nm' : negb (PreTerm.is_mul (unfold_term t)) by rewrite -is_mul_unfold.
rewrite subterms_unseal /subterms_def.
by rewrite unfold_TInv (PreTerm.inv_Nmul _ Nm') (PreTerm.inv_invN _ Ni')
   /= unfold_termK.
Qed.

(* Restated: [atomic] and [term_order] no longer exist.  [invs_canceled] plays
   the role of [atomic] together with the old no-inverse-pair side condition,
   and since [TMulN] is permutation-invariant there is no term order left to
   normalise the exponent list with. *)
Lemma subterms_TExpN t ts :
  negb (is_exp t) -> invs_canceled ts ->
  subterms (TExpN t ts) = {[TExpN t ts]} ∪ subterms t ∪ ⋃ map subterms ts.
Proof.
move=> tNexp ic.
rewrite (subterms_base_exps (TExpN t ts)) /TExpN base_TExp (base_expN _ tNexp).
congr (_ ∪ _).
rewrite /exps expo_TExp (expo_expN _ tNexp) TMulN_cat /= TMulN1.
(* [TMulN] sorts its factors, so [factors_TMulN] is only a permutation -- which
   is all the union over [subterms] needs. *)
by apply: union_list_permutation_proper_L; apply: Permutation_map;
   apply: factors_TMulN.
Qed.

(* [wf_mul_list] no longer exists; [invs_canceled] is its replacement. *)
Lemma subterms_TMulN ts :
  invs_canceled ts ->
  subterms (TMulN ts) = {[TMulN ts]} ∪ ⋃ map subterms ts.
Proof.
move=> ic.
(* [subterms_pre] of any pre-term is its own root plus the subterms of its
   factors (for a non-product the factor list is the singleton). *)
have preF : forall pt, subterms_pre pt
                     = {[fold_term pt]} ∪ ⋃ map subterms_pre (PreTerm.factors pt).
  move=> pt; case: pt => [o|o e|o e1 e2|es] //=.
  1-3: by rewrite /subterms_pre; set_solver.
have perm : PreTerm.factors (unfold_term (TMulN ts)) ≡ₚ unfold_term <$> ts.
  by rewrite -unfold_factors; apply: Permutation_map; apply: factors_TMulN.
rewrite subterms_via_pre preF unfold_termK.
congr (_ ∪ _).
transitivity (⋃ map subterms_pre (unfold_term <$> ts)).
  by apply: union_list_permutation_proper_L; apply: Permutation_map.
by elim: ts {ic perm} => [//|t l IH] /=; rewrite IH subterms_via_pre.
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
    rewrite (subterms_base_exps (TExpN t' ts)) /TExpN base_TExp bt'; set_solver.
  + move => t' t'' ts Nexp ic sub IH t''_ts.
    rewrite (subterms_TExpN Nexp ic) !elem_of_union; right.
    rewrite elem_of_union_list; exists (subterms t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
  + move => t'' ts ic sub IH t''_ts.
    rewrite (subterms_TMulN ic) elem_of_union; right.
    rewrite elem_of_union_list; exists (subterms t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
- elim/term_lt_ind: t2 => t2 IH.
  case: t2 IH => [n|ta tb|a|kt tt|kk tt|tt|pt wf nf] IH.
  + rewrite subtermsE' /=; move => /elem_of_union [/elem_of_singleton -> | /elem_of_empty []].
    exact: STRefl.
  + rewrite subtermsE' /=; move => /elem_of_union [/elem_of_singleton -> | /elem_of_union [H|H]].
    * exact: STRefl.
    * by apply: STPair1; apply: (IH ta _ H); rewrite [tsize (TPair ta tb)]tsize_eq; lia.
    * by apply: STPair2; apply: (IH tb _ H); rewrite [tsize (TPair ta tb)]tsize_eq; lia.
  + rewrite subtermsE' /=; move => /elem_of_union [/elem_of_singleton -> | /elem_of_empty []].
    exact: STRefl.
  + rewrite subtermsE' /=; move => /elem_of_union [/elem_of_singleton -> | H].
    * exact: STRefl.
    * by apply: STKey; apply: (IH tt _ H); rewrite [tsize (TKey kt tt)]tsize_eq; lia.
  + rewrite subtermsE' /=; move => /elem_of_union [/elem_of_singleton -> | /elem_of_union [H|H]].
    * exact: STRefl.
    * by apply: STSeal1; apply: (IH kk _ H); rewrite [tsize (TSeal kk tt)]tsize_eq; lia.
    * by apply: STSeal2; apply: (IH tt _ H); rewrite [tsize (TSeal kk tt)]tsize_eq; lia.
  + rewrite subtermsE' /=; move => /elem_of_union [/elem_of_singleton -> | H].
    * exact: STRefl.
    * by apply: STHash; apply: (IH tt _ H); rewrite [tsize (THash tt)]tsize_eq; lia.
  + case: pt wf nf IH => [o|[kt'||] operand|[||] b e|ts] wf nf IH.
    1,2,3,5,6: by move: {IH} nf; rewrite /is_non_free /=.
    * have /andb_True [/andb_True [Ninvpt Nmpt] wfpt] := wf.
      have E : TNonFree (PreTerm.PT1 O1Inv operand) wf nf = TInv (fold_term operand).
        apply: unfold_term_inj.
        by rewrite unfold_TInv (fold_termK operand wfpt) (PreTerm.inv_Nmul operand Nmpt)
           (PreTerm.inv_invN operand Ninvpt).
      have Ninv : negb (is_inv (fold_term operand)) by rewrite is_inv_unfold (fold_termK operand wfpt).
      have Nmf : negb (is_mul (fold_term operand)) by rewrite is_mul_unfold (fold_termK operand wfpt).
      rewrite E in IH *; rewrite (subterms_TInv Nmf Ninv).
      move => /elem_of_union [/elem_of_singleton -> | H].
      -- exact: STRefl.
      -- apply: (STInv Nmf Ninv); apply: (IH (fold_term operand) _ H).
         rewrite (tsize_TInv _ Nmf Ninv); lia.
    * set t2' := TNonFree (PreTerm.PTExp b e) wf nf.
      have xt : is_exp t2' by [].
      rewrite (subterms_base_exps t2').
      move => /elem_of_union [/elem_of_union [/elem_of_singleton -> | Hb] | He].
      -- exact: STRefl.
      -- rewrite -(base_expsK t2'); apply: STExp1; first exact: base_Nexp.
         by apply: (IH (base t2') _ Hb); exact: (tsize_base_lt _ xt).
      -- move: He => /elem_of_union_list [X [/list_elem_of_fmap [ee [-> ee_exps]] Hin]].
         rewrite -(base_expsK t2').
         apply: (STExp2 (base_Nexp t2') (invs_canceled_factors (expo t2')) _ ee_exps).
         by apply: (IH ee _ Hin); exact: (tsize_exps_lt _ _ ee_exps).
    * set t2' := TNonFree (PreTerm.PTMul ts) wf nf.
      have xt : is_mul t2' by [].
      have wfl : invs_canceled (factors t2') := invs_canceled_factors t2'.
      rewrite -(factorsK t2') (subterms_TMulN wfl).
      move => /elem_of_union [/elem_of_singleton -> | He].
      -- exact: STRefl.
      -- move: He => /elem_of_union_list [X [/list_elem_of_fmap [ff [-> ff_facts]] Hin]].
         apply: (STMul wfl _ ff_facts).
         apply: (IH ff _ Hin).
         exact: (tsize_factors_lt _ _ xt ff_facts).
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
    rewrite (nonces_of_term_base_exps (TExpN t' ts)) /TExpN base_TExp bt'; set_solver.
  + move => t' t'' ts Nexp ic sub IH t''_ts.
    rewrite (nonces_of_term_TExpN Nexp ic) elem_of_union; right.
    rewrite elem_of_union_list; exists (nonces_of_term t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
  + move => t'' ts ic sub IH t''_ts.
    rewrite (nonces_of_term_TMulN ic) elem_of_union_list.
    exists (nonces_of_term t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
- elim/term_lt_ind: t => t IH.
  case: t IH => [n|ta tb|a'|kt tt|kk tt|tt|pt wf nf] IH.
  + rewrite nonces_of_termE' /=; move => /elem_of_empty [].
  + rewrite nonces_of_termE' /=; move => /elem_of_union [H|H].
    * by apply: STPair1; apply: (IH ta _ H); rewrite [tsize (TPair ta tb)]tsize_eq; lia.
    * by apply: STPair2; apply: (IH tb _ H); rewrite [tsize (TPair ta tb)]tsize_eq; lia.
  + rewrite nonces_of_termE' /=; move => /elem_of_singleton ->; exact: STRefl.
  + rewrite nonces_of_termE' /=; move => H.
    by apply: STKey; apply: (IH tt _ H); rewrite [tsize (TKey kt tt)]tsize_eq; lia.
  + rewrite nonces_of_termE' /=; move => /elem_of_union [H|H].
    * by apply: STSeal1; apply: (IH kk _ H); rewrite [tsize (TSeal kk tt)]tsize_eq; lia.
    * by apply: STSeal2; apply: (IH tt _ H); rewrite [tsize (TSeal kk tt)]tsize_eq; lia.
  + rewrite nonces_of_termE' /=; move => H.
    by apply: STHash; apply: (IH tt _ H); rewrite [tsize (THash tt)]tsize_eq; lia.
  + case: pt wf nf IH => [o|[kt'||] operand|[||] b e|ts] wf nf IH.
    1,2,3,5,6: by move: {IH} nf; rewrite /is_non_free /=.
    * have /andb_True [/andb_True [Ninvpt Nmpt] wfpt] := wf.
      have E : TNonFree (PreTerm.PT1 O1Inv operand) wf nf = TInv (fold_term operand).
        apply: unfold_term_inj.
        by rewrite unfold_TInv (fold_termK operand wfpt) (PreTerm.inv_Nmul operand Nmpt)
           (PreTerm.inv_invN operand Ninvpt).
      have Ninv : negb (is_inv (fold_term operand)) by rewrite is_inv_unfold (fold_termK operand wfpt).
      have Nmf : negb (is_mul (fold_term operand)) by rewrite is_mul_unfold (fold_termK operand wfpt).
      rewrite E in IH *; rewrite nonces_of_term_TInv.
      move => H; apply: (STInv Nmf Ninv); apply: (IH (fold_term operand) _ H).
      rewrite (tsize_TInv _ Nmf Ninv); lia.
    * set t2' := TNonFree (PreTerm.PTExp b e) wf nf.
      have xt : is_exp t2' by [].
      rewrite (nonces_of_term_base_exps t2').
      move => /elem_of_union [Hb | He].
      -- rewrite -(base_expsK t2'); apply: STExp1; first exact: base_Nexp.
         by apply: (IH (base t2') _ Hb); exact: (tsize_base_lt _ xt).
      -- move: He => /elem_of_union_list [X [/list_elem_of_fmap [ee [-> ee_exps]] Hin]].
         rewrite -(base_expsK t2').
         apply: (STExp2 (base_Nexp t2') (invs_canceled_factors (expo t2')) _ ee_exps).
         by apply: (IH ee _ Hin); exact: (tsize_exps_lt _ _ ee_exps).
    * set t2' := TNonFree (PreTerm.PTMul ts) wf nf.
      have xt : is_mul t2' by [].
      have wfl : invs_canceled (factors t2') := invs_canceled_factors t2'.
      rewrite -(factorsK t2') (nonces_of_term_TMulN wfl).
      move => /elem_of_union_list [X [/list_elem_of_fmap [ff [-> ff_facts]] Hin]].
      apply: (STMul wfl _ ff_facts).
      apply: (IH ff _ Hin).
      exact: (tsize_factors_lt _ _ xt ff_facts).
Qed.

Lemma subterm_nonces_of_term t1 t2 :
  subterm t1 t2 → nonces_of_term t1 ⊆ nonces_of_term t2.
Proof.
elim: t2 / => //; try by intros; rewrite [nonces_of_term (_ _)]nonces_of_termE; set_solver.
- move => t' ts Nexp sub IH.
  have bt' : base t' = t'.
    rewrite /base; move: Nexp; rewrite is_exp_unfold => n.
    by rewrite (PreTerm.base_expN _ n) unfold_termK.
  rewrite (nonces_of_term_base_exps (TExpN t' ts)) /TExpN base_TExp bt'; set_solver.
- move => t' t'' ts Nexp ic sub IH t''_ts.
  rewrite (nonces_of_term_TExpN Nexp ic).
  have sub2 : nonces_of_term t'' ⊆ ⋃ map nonces_of_term ts.
    move => x x_t''; rewrite elem_of_union_list; exists (nonces_of_term t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
  set_solver.
- move => t'' ts ic sub IH t''_ts.
  rewrite (nonces_of_term_TMulN ic).
  have sub2 : nonces_of_term t'' ⊆ ⋃ map nonces_of_term ts.
    move => x x_t''; rewrite elem_of_union_list; exists (nonces_of_term t''); split => //.
    by rewrite list_elem_of_fmap; exists t''; split.
  set_solver.
Qed.

#[global]
Hint Resolve STRefl : core.
