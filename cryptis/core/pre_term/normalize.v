(** Self-contained development of pre-term normalization, phrased entirely in
    terms of stdpp's list and number operations: the [normalize] function, the
    definitions it depends on, and just the theory needed to prove that
    normalization is idempotent ([normalize_idem]).

    Unlike [theory.v] (which is built on mathcomp's [seq]/[order]/[bigop]), this
    file only uses the base ssreflect tactic language together with stdpp: lists
    are canonicalised with [merge_sort] for the total order [pt_order], well-
    formedness is expressed with [Forall]/[StronglySorted], and membership with
    [∈].  [pt_order] is the mathcomp order on pre-terms from [base.v], packaged
    as stdpp typeclasses (reflexivity, transitivity, …) in [with_stdpp.v].

    The same definitions also live in [theory.v]; they are kept here on purpose
    (nothing is moved out of [theory.v]). *)

From cryptis Require Import lib.
From cryptis.lib Require Import list_sort.
From mathcomp Require Import ssreflect.
From stdpp Require Import sorting list numbers.
From Stdlib Require Import Lia.
From cryptis.core.pre_term Require Export base with_stdpp.

Module PreTerm.
Import base.PreTerm.

(** Products are canonicalised by sorting their factors with [merge_sort] for
    the total order [pt_order], which is the mathcomp order on pre-terms from
    [base.v] packaged as stdpp typeclasses in [with_stdpp.v]. *)

Fixpoint height (pt : pre_term) : nat :=
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (height pt)
  | PT2 _ pt1 pt2 => S (Nat.max (height pt1) (height pt2))
  | PTMul ts => S (max_list_with height ts)
  end.

Definition is_inv pt := if pt is PTInv _ then true else false.
Definition is_exp pt := if pt is PTExp _ _ then true else false.
Definition is_mul pt := if pt is PTMul _ then true else false.

Definition base pt := if pt is PTExp b _ then b else pt.
Definition expo pt := if pt is PTExp _ e then e else PTMul [].
Definition factors pt := if pt is PTMul ts then ts else [pt].

(** We now define smart constructors for all the operations that validate
    non-trivial equations: [inv], [mul] and [exp].  The definitions work as
    follows:

    - [inv_aux] computes the inverse of terms that do not begin with [PTMul] by
      simply adding or removing a [PTInv].

    - [rem] removes the first occurrence of an element from a list, and
      [insert_factor] uses it to cancel a term against its inverse.

    - [mul] computes the product of a list of terms. It flattens inner terms
      that begin with [PTMul] (so that multiplication is associative) and then
      cancels out multiplicative inverses by using [inv_aux].  The remaining
      factors are sorted with [merge_sort] to obtain a canonical form.

    - [inv] computes the inverse of arbitrary terms by distributivity.

    - [exp] combines exponents using [mul].  If the resulting exponent is [1 =
      PTMul []], we simply return the base. *)

Definition inv_aux pt :=
  match pt with
  | PTInv t => t
  | _ => PTInv pt
  end.

Definition insert_factor pt pts :=
  if bool_decide (inv_aux pt ∈ pts) then rem (inv_aux pt) pts
  else pt :: pts.

Definition cancel_invs := foldr insert_factor [].

Definition mul ts :=
  match merge_sort pt_order (cancel_invs (concat (factors <$> ts))) with
  | [t] => t
  | l => PTMul l
  end.

Definition inv pt :=
  if pt is PTMul ts then mul (inv_aux <$> ts) else inv_aux pt.

Definition exp b e :=
  let e' := mul [expo b; e] in
  if bool_decide (e' = PTMul []) then base b
  else PTExp (base b) e'.

Fixpoint normalize pt :=
  match pt with
  | PT0 o => PT0 o
  | PTInv t => inv (normalize t)
  | PT1 o t => PT1 o (normalize t)
  | PTExp b e => exp (normalize b) (normalize e)
  | PT2 o t1 t2 => PT2 o (normalize t1) (normalize t2)
  | PTMul ts => mul (normalize <$> ts)
  end.

(** [invs_canceled pts] holds when all the inverses in [pts] have been canceled
    out. *)
Definition invs_canceled pts := Forall (fun pt => inv pt ∉ pts) pts.

Fixpoint wf_term pt : Prop :=
  match pt with
  | PT0 _ => True
  | PTInv pt => negb (is_inv pt) /\ negb (is_mul pt) /\ wf_term pt
  | PT1 _ pt => wf_term pt
  | PTExp b e => wf_term b /\ negb (is_exp b) /\ wf_term e /\ e ≠ PTMul []
  | PT2 _ pt1 pt2 => wf_term pt1 /\ wf_term pt2
  | PTMul ts => foldr (fun t acc => wf_term t /\ acc) True ts /\
                Forall (fun t => negb (is_mul t)) ts /\
                StronglySorted pt_order ts /\ invs_canceled ts /\ length ts ≠ 1
  end.

(** The well-formedness of the factors of a product is stated with an explicit
    [foldr] rather than [Forall wf_term] so that [wf_term] passes the guard
    checker; this bridge lemma recovers the [Forall] view. *)
Lemma wf_termsP ts :
  foldr (fun t acc => wf_term t /\ acc) True ts <-> Forall wf_term ts.
Proof.
elim: ts => [|t ts IH] /=.
- by split => _ //; constructor.
- split.
  + by move=> [? /IH ?]; constructor.
  + move=> H; split.
    * exact: (Forall_inv H).
    * apply/IH; exact: (Forall_inv_tail H).
Qed.

(** [ForallP] recovers the [∈]-based view of [Forall].  The [rem] and
    [merge_sort] helper lemmas used below are generic and come from
    [cryptis.lib.list_sort] (instantiated here at [pt_order]). *)
Lemma ForallP (P : pre_term -> Prop) l : Forall P l <-> (forall x, x ∈ l -> P x).
Proof. exact: list.Forall_forall. Qed.

Lemma mem_insert_factor pt pts z : z ∈ insert_factor pt pts -> z ∈ pt :: pts.
Proof.
rewrite /insert_factor; case_bool_decide as H.
- move=> /elem_of_rem ?; exact: list_elem_of_further.
- by [].
Qed.

Lemma mem_cancel_invs pts z : z ∈ cancel_invs pts -> z ∈ pts.
Proof.
rewrite /cancel_invs; elim: pts => [//|pt pts IH] /=.
move=> /mem_insert_factor; rewrite elem_of_cons => -[->|/IH ?].
- exact: list_elem_of_here.
- exact: list_elem_of_further.
Qed.

Lemma wf_nil : wf_term (PTMul []).
Proof.
rewrite /=. split => //. split; first by constructor.
split; first by constructor. split => //. by constructor.
Qed.

(** Structural facts about [base], [expo], [factors] and [inv_aux]. *)

Lemma wf_base pt : wf_term pt -> wf_term (base pt).
Proof. by case: pt => [o|o t|[||] t1 t2|ts] //= []. Qed.

Lemma base_expN pt : negb (is_exp pt) -> base pt = pt.
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

Lemma base_Nexp pt : wf_term pt -> negb (is_exp (base pt)).
Proof. by case: pt => [o|o t|[||] t1 t2|ts] //= [_ [? _]]. Qed.

Lemma expo_expN pt : negb (is_exp pt) -> expo pt = PTMul [].
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

Lemma wf_expo pt : wf_term pt -> wf_term (expo pt).
Proof.
case: pt => [o|o t|[||] t1 t2|ts] //=; try (move=> _; exact: wf_nil).
by move=> [_ [_ [? _]]].
Qed.

Lemma factorsN pt : negb (is_mul pt) -> factors pt = [pt].
Proof. by case: pt. Qed.

Lemma wf_factors pt : wf_term pt -> Forall wf_term (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /factors /=; try by apply/Forall_singleton.
by move: wf => [/wf_termsP ? _].
Qed.

Lemma Nmul_factors pt : wf_term pt -> Forall (fun t => negb (is_mul t)) (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /factors /=; try by apply/Forall_singleton.
by move: wf => [_ [? _]].
Qed.

Lemma wf_inv_aux pt : wf_term pt -> negb (is_mul pt) -> wf_term (inv_aux pt).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] //= wf Nm; try by (split=> //; split).
by case: wf => _ [_ ?].
Qed.

Lemma inv_aux_Nid pt : inv_aux pt ≠ pt.
Proof. by case: pt => [o|[k| |] t|o t1 t2|ts] /=; move=> /(f_equal height) /=; lia. Qed.

Lemma inv_invN pt : negb (is_inv pt) -> inv_aux pt = PTInv pt.
Proof. by case: pt => [o|[k| |] t|o t1 t2|ts]. Qed.

Lemma inv_auxK pt : wf_term pt -> inv_aux (inv_aux pt) = pt.
Proof. case: pt => [o|[k| |] t|o t1 t2|ts] //=. by move=> [/inv_invN -> _]. Qed.

Lemma inv_aux_eq_op pt1 pt2 : wf_term pt1 -> wf_term pt2 ->
  (inv_aux pt1 = pt2) <-> (pt1 = inv_aux pt2).
Proof.
move=> w1 w2; split=> e.
- by rewrite -e (inv_auxK _ w1).
- by rewrite e (inv_auxK _ w2).
Qed.

Lemma inv_Nmul pt : negb (is_mul pt) -> inv pt = inv_aux pt.
Proof. by case: pt. Qed.

(** Cancellation of inverses. *)

Lemma invs_canceled_sort pts :
  invs_canceled (merge_sort pt_order pts) <-> invs_canceled pts.
Proof.
rewrite /invs_canceled (Forall_merge_sort pt_order). apply: Forall_iff => pt.
by rewrite (merge_sort_Permutation pt_order pts).
Qed.

Lemma invs_canceled_atomic pts :
  Forall (fun pt => negb (is_mul pt)) pts ->
  invs_canceled pts <-> Forall (fun pt => inv_aux pt ∉ pts) pts.
Proof.
rewrite /invs_canceled => /Forall_forall atom.
rewrite !Forall_forall; split => H pt pt_pts; move: (H pt pt_pts);
  by rewrite (inv_Nmul _ (atom pt pt_pts)).
Qed.

Lemma no_pair_cons pt pts :
  Forall (fun q => inv_aux q ∉ (pt :: pts)) (pt :: pts) ->
  Forall (fun q => inv_aux q ∉ pts) pts.
Proof.
move=> H; apply: (Forall_impl _ _ (Forall_inv_tail H)) => q.
rewrite not_elem_of_cons; by case.
Qed.

Lemma insert_factor_id pt pts :
  Forall (fun q => inv_aux q ∉ (pt :: pts)) (pt :: pts) ->
  insert_factor pt pts = pt :: pts.
Proof.
move=> H; rewrite /insert_factor.
have Hhead := Forall_inv H.
move: Hhead; rewrite not_elem_of_cons => -[_ Hpts].
by rewrite (bool_decide_eq_false_2 _ Hpts).
Qed.

Lemma cancel_invs_id pts : Forall (fun q => inv_aux q ∉ pts) pts -> cancel_invs pts = pts.
Proof.
rewrite /cancel_invs; elim: pts => [//|pt pts IH] canceled /=.
rewrite (IH (no_pair_cons _ _ canceled)).
exact: (insert_factor_id _ _ canceled).
Qed.

Lemma cancel_invs_canceled pts :
  Forall (fun pt => negb (is_mul pt)) pts -> invs_canceled pts -> cancel_invs pts = pts.
Proof. move=> atom /(invs_canceled_atomic _ atom) H; exact: cancel_invs_id H. Qed.

Lemma invs_canceled1 t : negb (is_mul t) -> invs_canceled [t].
Proof.
move=> Nm.
have atom : Forall (fun pt => negb (is_mul pt)) [t] by apply/Forall_singleton.
apply/(invs_canceled_atomic _ atom).
apply/Forall_singleton. rewrite list_elem_of_singleton.
exact: inv_aux_Nid.
Qed.

Lemma invs_canceled_factors pt : wf_term pt -> invs_canceled (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /factors /=; try by apply: invs_canceled1.
by move: wf => [_ [_ [_ [? _]]]].
Qed.

Lemma sorted_factors pt : wf_term pt -> StronglySorted pt_order (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /factors; try by (repeat constructor).
by move: wf => [_ [_ [? _]]].
Qed.

Lemma insert_factor_no_pair pt pts :
  wf_term pt -> Forall wf_term pts ->
  Forall (fun q => inv_aux q ∉ pts) pts ->
  Forall (fun q => inv_aux q ∉ insert_factor pt pts) (insert_factor pt pts).
Proof.
move=> wfpt /ForallP wfs /ForallP canceled.
rewrite /insert_factor; case_bool_decide as Hin.
- apply/ForallP => q qin_rem.
  have qin := elem_of_rem qin_rem.
  move=> Hc; exact: (canceled q qin (elem_of_rem Hc)).
- apply/ForallP => q; rewrite elem_of_cons => -[-> | qin].
  + rewrite not_elem_of_cons; split; [exact: inv_aux_Nid | exact: Hin].
  + rewrite not_elem_of_cons; split; last exact: (canceled q qin).
    move=> eq; apply: Hin.
    by rewrite -(proj1 (inv_aux_eq_op q pt (wfs q qin) wfpt) eq).
Qed.

Lemma wf_cancel_invs pts : Forall wf_term pts -> Forall wf_term (cancel_invs pts).
Proof. move=> /ForallP H; apply/ForallP => q /mem_cancel_invs Hin; exact: (H q Hin). Qed.

Lemma Nmul_cancel_invs pts :
  Forall (fun t => negb (is_mul t)) pts ->
  Forall (fun t => negb (is_mul t)) (cancel_invs pts).
Proof. move=> /ForallP H; apply/ForallP => q /mem_cancel_invs Hin; exact: (H q Hin). Qed.

Lemma cancel_invs_no_pair pts :
  Forall wf_term pts ->
  Forall (fun q => inv_aux q ∉ cancel_invs pts) (cancel_invs pts).
Proof.
elim: pts => [_|pt pts IH]; first by constructor.
move=> H; have [wfpt wfpts] := Forall_cons_1 _ _ _ H.
apply: insert_factor_no_pair;
  [exact: wfpt | exact: (wf_cancel_invs _ wfpts) | exact: (IH wfpts)].
Qed.

Lemma invs_canceled_cancel_invs pts :
  Forall (fun pt => negb (is_mul pt)) pts -> Forall wf_term pts ->
  invs_canceled (cancel_invs pts).
Proof.
move=> atom wf.
apply/(invs_canceled_atomic _ (Nmul_cancel_invs _ atom)).
exact: (cancel_invs_no_pair _ wf).
Qed.

(* Multiplication *)

Lemma flatten_factors_wf ts :
  Forall wf_term ts -> Forall wf_term (concat (factors <$> ts)).
Proof.
elim: ts => [//|t ts IH] /=.
move=> H; have [wft wfts] := Forall_cons_1 _ _ _ H.
apply/Forall_app; split; [exact: wf_factors | exact: (IH wfts)].
Qed.

Lemma flatten_factors_Nmul ts :
  Forall wf_term ts -> Forall (fun t => negb (is_mul t)) (concat (factors <$> ts)).
Proof.
elim: ts => [//|t ts IH] /=.
move=> H; have [wft wfts] := Forall_cons_1 _ _ _ H.
apply/Forall_app; split; [exact: Nmul_factors | exact: (IH wfts)].
Qed.

Lemma wf_mul ts : Forall wf_term ts -> wf_term (mul ts).
Proof.
move=> wf; rewrite /mul.
set c := cancel_invs _.
have wf_c : Forall wf_term c by apply: wf_cancel_invs; exact: flatten_factors_wf.
have wf_sc : Forall wf_term (merge_sort pt_order c) by apply/(Forall_merge_sort pt_order).
have Nmul_sc : Forall (fun t => negb (is_mul t)) (merge_sort pt_order c).
{ apply/(Forall_merge_sort pt_order); apply: Nmul_cancel_invs; exact: flatten_factors_Nmul. }
have inv_sc : invs_canceled (merge_sort pt_order c).
{ apply/invs_canceled_sort; apply: invs_canceled_cancel_invs;
    [exact: flatten_factors_Nmul | exact: flatten_factors_wf]. }
case E: (merge_sort pt_order c) => [|t [|t' c']].
- exact: wf_nil.
- move: wf_sc; rewrite E => H; exact: (Forall_inv H).
- move: wf_sc Nmul_sc inv_sc; rewrite E => wf' Nmul' inv'.
  split; [apply/wf_termsP; exact: wf' |].
  split; [exact: Nmul' |].
  split; [rewrite -E; exact: (merge_sort_sorted pt_order c) |].
  split; [exact: inv' | done].
Qed.

Lemma mul_wf1 t : wf_term t -> mul [t] = t.
Proof.
move=> wf; rewrite /mul /= app_nil_r.
rewrite (cancel_invs_canceled _ (Nmul_factors _ wf) (invs_canceled_factors _ wf)).
rewrite (merge_sort_id pt_order _ (sorted_factors _ wf)).
case: t wf => [o|o t|o t1 t2|ts] //= wf.
move: wf => [_ [_ [_ [_ Hlen]]]].
by case: ts Hlen => [|t [|t' c']].
Qed.

Lemma wf_exp b e : wf_term b -> wf_term e -> wf_term (exp b e).
Proof.
move=> wfb wfe; rewrite /exp; case_bool_decide as Hf.
- exact: (wf_base _ wfb).
- have wf' : Forall wf_term [expo b; e]
    by constructor; [exact: (wf_expo _ wfb) | constructor; [exact: wfe | constructor]].
  split; [exact: (wf_base _ wfb) |].
  split; [exact: (base_Nexp _ wfb) |].
  split; [exact: (wf_mul _ wf') | exact: Hf].
Qed.

Lemma wf_inv pt : wf_term pt -> wf_term (inv pt).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] wf; rewrite /inv /=.
- done.
- by split; [done | split; [done | exact: wf]].
- by split; [done | split; [done | exact: wf]].
- by move: wf => [_ [_ ?]].
- by split; [done | split; [done | exact: wf]].
- apply: wf_mul; apply/Forall_fmap.
  move: wf => [/wf_termsP /ForallP wf_ts [/ForallP Nm_ts _]].
  apply/ForallP => t t_ts.
  exact: (wf_inv_aux _ (wf_ts t t_ts) (Nm_ts t t_ts)).
Qed.

Lemma wf_normalize pt : wf_term (normalize pt).
Proof.
elim: pt => //=.
- move=> [k| |] t IH /=; [exact: IH | exact: IH | exact: (wf_inv _ IH)].
- move=> o t1 IH1 t2 IH2; case: o => /=;
    [by split | by split | exact: (wf_exp _ _ IH1 IH2)].
- move=> ts IHts; apply: wf_mul; apply/Forall_fmap.
  elim: ts IHts => [|t ts' IH] /=;
    [by move=> _; constructor
    |by move=> [wt wts]; constructor; [exact: wt | exact: IH wts]].
Qed.

Lemma normalize_wf pt : wf_term pt -> normalize pt = pt.
Proof.
elim: pt => //=.
- move=> [k| |] t IH /=.
  + by move=> wf; rewrite (IH wf).
  + by move=> wf; rewrite (IH wf).
  + by move=> [ni [nm wf]]; rewrite (IH wf) (inv_Nmul _ nm) (inv_invN _ ni).
- move=> o t1 IH1 t2 IH2; case: o => /=.
  + by move=> [/IH1 -> /IH2 ->].
  + by move=> [/IH1 -> /IH2 ->].
  + move=> [wfb [Nxb [wfe eN0]]].
    rewrite (IH1 wfb) (IH2 wfe) /exp (expo_expN _ Nxb) (base_expN _ Nxb).
    have -> : mul [PTMul []; t2] = t2.
    { have -> : mul [PTMul []; t2] = mul [t2] by rewrite /mul /= !app_nil_r.
      exact: (mul_wf1 _ wfe). }
    by rewrite (bool_decide_eq_false_2 _ eN0).
- move=> ts IHts [wfF [Nmul_ts [sorted_ts [inv_ts sizeN1]]]].
  have wf_ts := proj1 (wf_termsP ts) wfF.
  have Nts : normalize <$> ts = ts.
  { elim: ts IHts wf_ts {wfF Nmul_ts sorted_ts inv_ts sizeN1}
      => [//|t ts' IH] /= [IHt IHts'] Hwf.
    rewrite (IHt (Forall_inv Hwf)); f_equal.
    exact: (IH IHts' (Forall_inv_tail Hwf)). }
  rewrite Nts /mul.
  have ff : concat (factors <$> ts) = ts.
  { elim: ts Nmul_ts {IHts wf_ts wfF sorted_ts inv_ts sizeN1 Nts}
      => [//|t ts' IH] /= HNm.
    rewrite (factorsN _ (Forall_inv HNm)) /=; f_equal.
    exact: (IH (Forall_inv_tail HNm)). }
  rewrite ff (cancel_invs_canceled _ Nmul_ts inv_ts) (merge_sort_id pt_order _ sorted_ts).
  by case: ts sizeN1 {IHts wf_ts wfF Nmul_ts sorted_ts inv_ts Nts ff}
    => [|t [|t' ts'']].
Qed.

Lemma normalize_idem pt : normalize (normalize pt) = normalize pt.
Proof. apply: normalize_wf; exact: wf_normalize. Qed.

End PreTerm.
