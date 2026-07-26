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

From stdpp Require Import sorting list numbers.
From cryptis Require Import lib.
From cryptis.lib Require Import list_sort.
From mathcomp Require Import ssreflect.
From Stdlib Require Import Lia.
From cryptis.core.pre_term Require Export base with_stdpp.

Module PreTerm.
Import base.PreTerm.

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
Definition is_nonce pt := if pt is PT0 (O0Nonce _) then true else false.

Definition base pt := if pt is PTExp b _ then b else pt.
Definition expo pt := if pt is PTExp _ e then e else PTMul [].
Definition factors pt := if pt is PTMul ts then ts else [pt].

(** We now define smart constructors for all the operations that validate
    non-trivial equations: [inv], [mul] and [exp].  The definitions work as
    follows:

    - [inv_aux] computes the inverse of terms that do not begin with [PTMul] by
      simply adding or removing a [PTInv].

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

(** [wf] is a genuine [bool] (so it doubles as the proof-irrelevant
    well-formedness field of the [term] datatype downstream, via
    [bool_irrelevance]).  The recursive well-formedness of the factors of a
    product is written with [forallb wf ts] — that keeps [wf] structurally
    recursive (unlike [Forall wf ts]) and gives it good reduction behaviour.
    [StronglySorted] and [invs_canceled] are only decidable predicates, so we
    reflect them with [bool_decide]. *)

Fixpoint wf (pt : pre_term) : bool :=
  match pt with
  | PT0 _ => true
  | PTInv pt => negb (is_inv pt) && negb (is_mul pt) && wf pt
  | PT1 _ pt => wf pt
  | PTExp b e =>
    wf b && negb (is_exp b) && wf e && bool_decide (e ≠ PTMul [])
  | PT2 _ pt1 pt2 => wf pt1 && wf pt2
  | PTMul ts =>
    forallb wf ts && forallb (fun t => negb (is_mul t)) ts
    && bool_decide (StronglySorted pt_order ts)
    && bool_decide (invs_canceled ts) && bool_decide (length ts ≠ 1)
  end.

Lemma forallbP {A} (p : A -> bool) (l : list A) : forallb p l <-> Forall p l.
Proof.
elim: l => [|x l IH] /=.
- by split => _; [constructor|].
- rewrite andb_True IH; split.
  + by move=> [??]; constructor.
  + by move=> H; split; [exact: (Forall_inv H)|exact: (Forall_inv_tail H)].
Qed.

Lemma wfsP ts : forallb wf ts <-> Forall wf ts.
Proof. exact: forallbP. Qed.

(* Definitional unfoldings of [wf] at each non-free head, so that proofs can
   expose the underlying [&&] and destructure it with [andb_True]. *)
Lemma wf_InvE pt :
  wf (PTInv pt) = (negb (is_inv pt) && negb (is_mul pt) && wf pt).
Proof. by []. Qed.
Lemma wf_ExpE b e :
  wf (PTExp b e)
  = (wf b && negb (is_exp b) && wf e && bool_decide (e ≠ PTMul [])).
Proof. by []. Qed.
Lemma wf_MulE ts :
  wf (PTMul ts)
  = (forallb wf ts && forallb (fun t => negb (is_mul t)) ts
     && bool_decide (StronglySorted pt_order ts)
     && bool_decide (invs_canceled ts) && bool_decide (length ts ≠ 1)).
Proof. by []. Qed.

(** The [term] datatype uses [wf_term] as its well-formedness field; keep it as
    an alias so downstream code that already refers to [wf_term] keeps working. *)
Definition wf_term := wf.
Lemma wf_termE pt : wf_term pt <-> wf pt.
Proof. by rewrite /wf_term. Qed.

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

Lemma wf_nil : wf (PTMul []).
Proof. by rewrite /wf !andb_True; split_and!. Qed.

(** Structural facts about [base], [expo], [factors] and [inv_aux]. *)

Lemma wf_base pt : wf pt -> wf (base pt).
Proof.
case: pt => [o|o t|[||] b e|ts] wf_pt //.
by move: wf_pt; rewrite wf_ExpE !andb_True => - [[[? _] _] _].
Qed.

Lemma base_expN pt : negb (is_exp pt) -> base pt = pt.
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

Lemma base_Nexp pt : wf pt -> negb (is_exp (base pt)).
Proof.
case: pt => [o|o t|[||] b e|ts] wf_pt //=.
by move: wf_pt; rewrite wf_ExpE !andb_True => - [[[_ ?] _] _].
Qed.

Lemma expo_expN pt : negb (is_exp pt) -> expo pt = PTMul [].
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

Lemma wf_expo pt : wf pt -> wf (expo pt).
Proof.
case: pt => [o|o t|[||] b e|ts]; try (move=> _; exact: wf_nil).
by move=> wf_pt; move: wf_pt; rewrite wf_ExpE !andb_True => - [[[_ _] ?] _].
Qed.

Lemma factorsN pt : negb (is_mul pt) -> factors pt = [pt].
Proof. by case: pt. Qed.

Lemma wf_factors pt : wf pt -> Forall wf (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf_pt; rewrite /factors /=;
  try by rewrite Forall_singleton.
by move: wf_pt; rewrite wf_MulE !andb_True => - [[[[H _] _] _] _]; rewrite -wfsP.
Qed.

Lemma Nmul_factors pt : wf pt -> Forall (fun t => negb (is_mul t)) (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf_pt; rewrite /factors /=;
  try by rewrite Forall_singleton.
by move: wf_pt; rewrite wf_MulE !andb_True => - [[[[_ H] _] _] _]; rewrite -forallbP.
Qed.

Lemma wf_inv_aux pt : wf pt -> negb (is_mul pt) -> wf (inv_aux pt).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] wf_pt Nm //=.
by move: wf_pt; rewrite wf_InvE !andb_True => - [[_ _] ?].
Qed.

Lemma inv_aux_Nid pt : inv_aux pt ≠ pt.
Proof. by case: pt => [o|[k| |] t|o t1 t2|ts] /=; move=> /(f_equal height) /=; lia. Qed.

Lemma inv_invN pt : negb (is_inv pt) -> inv_aux pt = PTInv pt.
Proof. by case: pt => [o|[k| |] t|o t1 t2|ts]. Qed.

Lemma inv_auxK pt : wf pt -> inv_aux (inv_aux pt) = pt.
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] //=.
by rewrite !andb_True => - [[/inv_invN -> _] _].
Qed.

Lemma inv_aux_eq_op pt1 pt2 : wf pt1 -> wf pt2 ->
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

Lemma invs_canceled_factors pt : wf pt -> invs_canceled (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf_pt; rewrite /factors /=;
  try by apply: invs_canceled1.
move: wf_pt; rewrite wf_MulE !andb_True => - [[[[_ _] _] H] _].
exact: (bool_decide_unpack _ H).
Qed.

Lemma sorted_factors pt : wf pt -> StronglySorted pt_order (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf_pt; rewrite /factors;
  try by (repeat constructor).
move: wf_pt; rewrite wf_MulE !andb_True => - [[[[_ _] H] _] _].
exact: (bool_decide_unpack _ H).
Qed.

Lemma insert_factor_no_pair pt pts :
  wf pt -> Forall wf pts ->
  Forall (fun q => inv_aux q ∉ pts) pts ->
  Forall (fun q => inv_aux q ∉ insert_factor pt pts) (insert_factor pt pts).
Proof.
move=> wfpt /list.Forall_forall wfs /list.Forall_forall canceled.
rewrite /insert_factor; case_bool_decide as Hin.
- apply/list.Forall_forall => q qin_rem.
  have qin := elem_of_rem qin_rem.
  move=> Hc; exact: (canceled q qin (elem_of_rem Hc)).
- apply/list.Forall_forall => q; rewrite elem_of_cons => -[-> | qin].
  + rewrite not_elem_of_cons; split; [exact: inv_aux_Nid | exact: Hin].
  + rewrite not_elem_of_cons; split; last exact: (canceled q qin).
    move=> eq; apply: Hin.
    by rewrite -(proj1 (inv_aux_eq_op q pt (wfs q qin) wfpt) eq).
Qed.

Lemma wf_cancel_invs pts : Forall wf pts -> Forall wf (cancel_invs pts).
Proof.
move=> /list.Forall_forall H; apply/list.Forall_forall=> q /mem_cancel_invs Hin.
exact: H.
Qed.

Lemma Nmul_cancel_invs pts :
  Forall (fun t => negb (is_mul t)) pts ->
  Forall (fun t => negb (is_mul t)) (cancel_invs pts).
Proof.
move=> /list.Forall_forall H; apply/list.Forall_forall => q /mem_cancel_invs Hin.
exact: (H q Hin).
Qed.

Lemma cancel_invs_no_pair pts :
  Forall wf pts ->
  Forall (fun q => inv_aux q ∉ cancel_invs pts) (cancel_invs pts).
Proof.
elim: pts => [_|pt pts IH]; first by constructor.
move=> H; have [wfpt wfpts] := Forall_cons_1 _ _ _ H.
apply: insert_factor_no_pair;
  [exact: wfpt | exact: (wf_cancel_invs _ wfpts) | exact: (IH wfpts)].
Qed.

Lemma invs_canceled_cancel_invs pts :
  Forall (fun pt => negb (is_mul pt)) pts -> Forall wf pts ->
  invs_canceled (cancel_invs pts).
Proof.
move=> atom wf.
apply/(invs_canceled_atomic _ (Nmul_cancel_invs _ atom)).
exact: (cancel_invs_no_pair _ wf).
Qed.

(* Multiplication *)

Lemma flatten_factors_wf ts :
  Forall wf ts -> Forall wf (concat (factors <$> ts)).
Proof.
elim: ts => [//|t ts IH] /=.
move=> H; have [wft wfts] := Forall_cons_1 _ _ _ H.
apply/Forall_app; split; [exact: wf_factors | exact: (IH wfts)].
Qed.

Lemma flatten_factors_Nmul ts :
  Forall wf ts -> Forall (fun t => negb (is_mul t)) (concat (factors <$> ts)).
Proof.
elim: ts => [//|t ts IH] /=.
move=> H; have [wft wfts] := Forall_cons_1 _ _ _ H.
apply/Forall_app; split; [exact: Nmul_factors | exact: (IH wfts)].
Qed.

(* Introduction rule for [wf (PTMul ts)].  Stated with an *abstract* [ts] so
   that [forallb wf ts] stays folded — otherwise [andb_True] would split it into
   its per-element conjuncts. *)
Lemma wf_MulI ts :
  Forall wf ts -> Forall (fun t => negb (is_mul t)) ts ->
  StronglySorted pt_order ts -> invs_canceled ts -> length ts ≠ 1 ->
  wf (PTMul ts).
Proof.
move=> H1 H2 H3 H4 H5; rewrite wf_MulE !andb_True; repeat split.
- exact: (proj2 (wfsP _) H1).
- exact: (proj2 (forallbP _ _) H2).
- by apply: bool_decide_pack.
- by apply: bool_decide_pack.
- by apply: bool_decide_pack.
Qed.

Lemma wf_mul ts : Forall wf ts -> wf (mul ts).
Proof.
move=> wf_ts; rewrite /mul.
set c := cancel_invs _.
have wf_c : Forall wf c by apply: wf_cancel_invs; exact: flatten_factors_wf.
have wf_sc : Forall wf (merge_sort pt_order c) by apply/(Forall_merge_sort pt_order).
have Nmul_sc : Forall (fun t => negb (is_mul t)) (merge_sort pt_order c).
{ apply/(Forall_merge_sort pt_order); apply: Nmul_cancel_invs; exact: flatten_factors_Nmul. }
have inv_sc : invs_canceled (merge_sort pt_order c).
{ apply/invs_canceled_sort; apply: invs_canceled_cancel_invs;
    [exact: flatten_factors_Nmul | exact: flatten_factors_wf]. }
case E: (merge_sort pt_order c) => [|t [|t' c']].
- exact: wf_nil.
- move: wf_sc; rewrite E => H; exact: (Forall_inv H).
- move: wf_sc Nmul_sc inv_sc; rewrite E => wf' Nmul' inv'.
  apply: wf_MulI => //.
  by rewrite -E; exact: (merge_sort_sorted pt_order c).
Qed.

Lemma mul_wf1 t : wf t -> mul [t] = t.
Proof.
move=> wf; rewrite /mul /= app_nil_r.
rewrite (cancel_invs_canceled _ (Nmul_factors _ wf) (invs_canceled_factors _ wf)).
rewrite (merge_sort_id pt_order _ (sorted_factors _ wf)).
case: t wf => [o|o t|o t1 t2|ts] //= wf.
move: wf; rewrite !andb_True => - [[[[_ _] _] _] Hlen].
by case: ts Hlen => [|t [|t' c']].
Qed.

(* Introduction rules for [wf] at the [PTInv] and [PTExp] heads.  Abstract [pt]
   / [b], [e] keep the recursive [wf] calls folded. *)
Lemma wf_InvI pt : negb (is_inv pt) -> negb (is_mul pt) -> wf pt -> wf (PTInv pt).
Proof. by move=> H1 H2 H3; rewrite wf_InvE !andb_True; repeat split. Qed.

Lemma wf_ExpI b e :
  wf b -> negb (is_exp b) -> wf e -> bool_decide (e ≠ PTMul []) ->
  wf (PTExp b e).
Proof. by move=> H1 H2 H3 H4; rewrite wf_ExpE !andb_True; repeat split. Qed.

Lemma wf_exp b e : wf b -> wf e -> wf (exp b e).
Proof.
move=> wfb wfe; rewrite /exp; case_bool_decide as Hf.
- exact: (wf_base _ wfb).
- have wf' : Forall wf [expo b; e]
    by constructor; [exact: (wf_expo _ wfb) | constructor; [exact: wfe | constructor]].
  apply: wf_ExpI.
  + exact: (wf_base _ wfb).
  + exact: (base_Nexp _ wfb).
  + exact: (wf_mul _ wf').
  + by apply: bool_decide_pack.
Qed.

Lemma wf_inv pt : wf pt -> wf (inv pt).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] wf; rewrite /inv.
- by apply: wf_InvI.
- by apply: wf_InvI.
- by apply: wf_InvI.
- by move: wf; rewrite wf_InvE !andb_True => - [[_ _] ?].
- by apply: wf_InvI.
- apply: wf_mul; apply/Forall_fmap.
  move: wf; rewrite wf_MulE !andb_True
    => - [[[[/wfsP /list.Forall_forall wf_ts
             /forallbP /list.Forall_forall Nm_ts] _] _] _].
  apply/list.Forall_forall => t t_ts.
  exact: (wf_inv_aux _ (wf_ts t t_ts) (Nm_ts t t_ts)).
Qed.

Lemma wf_normalize pt : wf (normalize pt).
Proof.
elim: pt => //=.
- move=> [k| |] t IH /=; [exact: IH | exact: IH | exact: (wf_inv _ IH)].
- move=> o t1 IH1 t2 IH2; case: o => /=;
    [by rewrite andb_True; split
    |by rewrite andb_True; split
    |exact: (wf_exp _ _ IH1 IH2)].
- move=> ts IHts; apply: wf_mul; apply/Forall_fmap.
  elim: ts IHts => [|t ts' IH] /=;
    [by move=> _; constructor
    |by move=> [wt wts]; constructor; [exact: wt | exact: IH wts]].
Qed.

Lemma normalize_wf pt : wf pt -> normalize pt = pt.
Proof.
elim: pt => //=.
- move=> [k| |] t IH /=.
  + by move=> wf; rewrite (IH wf).
  + by move=> wf; rewrite (IH wf).
  + by rewrite !andb_True => - [[ni nm] wf];
      rewrite (IH wf) (inv_Nmul _ nm) (inv_invN _ ni).
- move=> o t1 IH1 t2 IH2; case: o => /=.
  + by rewrite andb_True => - [/IH1 -> /IH2 ->].
  + by rewrite andb_True => - [/IH1 -> /IH2 ->].
  + rewrite !andb_True => - [[[wfb Nxb] wfe] /bool_decide_unpack eN0].
    rewrite (IH1 wfb) (IH2 wfe) /exp (expo_expN _ Nxb) (base_expN _ Nxb).
    have -> : mul [PTMul []; t2] = t2.
    { have -> : mul [PTMul []; t2] = mul [t2] by rewrite /mul /= !app_nil_r.
      exact: (mul_wf1 _ wfe). }
    by rewrite (bool_decide_eq_false_2 _ eN0).
- move=> ts IHts; rewrite !andb_True
    => - [[[[wfF Nmul_ts] /bool_decide_unpack sorted_ts]
           /bool_decide_unpack inv_ts] /bool_decide_unpack sizeN1].
  have wf_ts := proj1 (wfsP ts) wfF.
  have Nmul_F := proj1 (forallbP _ _) Nmul_ts.
  have Nts : normalize <$> ts = ts.
  { elim: ts IHts wf_ts {wfF Nmul_ts Nmul_F sorted_ts inv_ts sizeN1}
      => [//|t ts' IH] /= [IHt IHts'] Hwf.
    rewrite (IHt (Forall_inv Hwf)); f_equal.
    exact: (IH IHts' (Forall_inv_tail Hwf)). }
  rewrite Nts /mul.
  have ff : concat (factors <$> ts) = ts.
  { elim: ts Nmul_F {IHts wf_ts wfF Nmul_ts sorted_ts inv_ts sizeN1 Nts}
      => [//|t ts' IH] /= HNm.
    rewrite (factorsN _ (Forall_inv HNm)) /=; f_equal.
    exact: (IH (Forall_inv_tail HNm)). }
  rewrite ff (cancel_invs_canceled _ Nmul_F inv_ts) (merge_sort_id pt_order _ sorted_ts).
  by case: ts sizeN1 {IHts wf_ts wfF Nmul_ts Nmul_F sorted_ts inv_ts Nts ff}
    => [|t [|t' ts'']].
Qed.

Lemma normalize_idem pt : normalize (normalize pt) = normalize pt.
Proof. apply: normalize_wf; exact: wf_normalize. Qed.

(** ** Additional theory ported from [theory.v]

    Everything below is the remaining pre-term theory of [theory.v], reproved on
    top of stdpp instead of mathcomp's [seq]/[order]/[bigop].  [count_mem] and
    the multiset characterisation of permutations live in [lib/list_sort.v]. *)

(** The size of a pre-term, used as a termination measure. *)
Fixpoint tsize (pt : pre_term) : nat :=
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (tsize pt)
  | PT2 _ t1 t2 => S (tsize t1 + tsize t2)
  | PTMul ts => S (sum_list_with tsize ts)
  end.

Lemma tsize_gt0 pt : 0 < tsize pt.
Proof. case: pt => * /=; lia. Qed.

Lemma tsize_inv pt : negb (is_inv pt) -> tsize (inv_aux pt) = S (tsize pt).
Proof. by move=> H; rewrite (inv_invN _ H). Qed.

(** The exponents of a pre-term. *)
Definition exps pt := factors (expo pt).

Lemma wf_exps pt : wf pt -> Forall wf (exps pt).
Proof. move=> wf; rewrite /exps; apply: wf_factors; exact: (wf_expo _ wf). Qed.

Lemma exps_expN pt : negb (is_exp pt) -> exps pt = [].
Proof. move=> H; rewrite /exps (expo_expN _ H) //. Qed.

Lemma exps_base pt : wf pt -> exps (base pt) = [].
Proof. move=> wf; exact: (exps_expN _ (base_Nexp _ wf)). Qed.

Lemma base_idem pt : wf pt -> base (base pt) = base pt.
Proof. move=> wf; exact: (base_expN _ (base_Nexp _ wf)). Qed.

Lemma base_expoK pt : is_exp pt -> PTExp (base pt) (expo pt) = pt.
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

Lemma expo_exp b : expo b ≠ PTMul [] -> is_exp b.
Proof. by case: b => [o|o t|[||] t1 t2|ts] //= H; case: (H eq_refl). Qed.

Lemma expo_unit_Nexp b : wf b -> expo b = PTMul [] -> negb (is_exp b).
Proof.
case: b => [o|o t|[||] t1 t2|ts] //= wf e0.
move: wf; rewrite !andb_True => - [[[_ _] _] /bool_decide_unpack eN0].
exfalso; apply: eN0; exact: e0.
Qed.

Lemma is_mul_inv_aux pt : wf pt -> negb (is_mul (inv_aux pt)).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] wf //=.
by move: wf; rewrite wf_InvE !andb_True => - [[_ H] _].
Qed.

Lemma inv_inv_aux pt : wf pt -> inv (inv_aux pt) = pt.
Proof.
move=> wf; have Nm := is_mul_inv_aux _ wf.
have -> : inv (inv_aux pt) = inv_aux (inv_aux pt).
{ rewrite /inv; by case: (inv_aux pt) Nm => [o|o t|o t1 t2|ts]. }
exact: (inv_auxK _ wf).
Qed.

Lemma invs_canceled_inv_aux pts :
  Forall wf pts -> invs_canceled pts -> Forall (fun pt => inv_aux pt ∉ pts) pts.
Proof.
move=> /list.Forall_forall wfs /list.Forall_forall canc.
apply/list.Forall_forall => pt pt_pts inv_aux_in.
move: (canc _ inv_aux_in); rewrite (inv_inv_aux _ (wfs _ pt_pts)) => H.
exact: (H pt_pts).
Qed.

Lemma invs_canceled_cons pt pts : invs_canceled (pt :: pts) -> invs_canceled pts.
Proof.
rewrite /invs_canceled => H.
apply: (Forall_impl _ _ (Forall_inv_tail H)) => q.
rewrite not_elem_of_cons; by case.
Qed.

Lemma invs_canceled_exps pt : wf pt -> invs_canceled (exps pt).
Proof. move=> wf; rewrite /exps; exact: (invs_canceled_factors _ (wf_expo _ wf)). Qed.

Lemma exps_sorted pt : wf pt -> StronglySorted pt_order (exps pt).
Proof. move=> wf; rewrite /exps; exact: (sorted_factors _ (wf_expo _ wf)). Qed.

Lemma cancel_invs_exps pt : wf pt -> cancel_invs (exps pt) = exps pt.
Proof.
move=> wf; apply: cancel_invs_canceled; last exact: (invs_canceled_exps _ wf).
rewrite /exps; exact: (Nmul_factors _ (wf_expo _ wf)).
Qed.

Lemma base_exp b e : wf b -> base (exp b e) = base b.
Proof.
move=> wf; rewrite /exp; case_bool_decide as H.
- exact: (base_idem _ wf).
- done.
Qed.

Lemma flatten_factors_Nmul_id us :
  Forall (fun t => negb (is_mul t)) us -> concat (factors <$> us) = us.
Proof.
elim: us => [//|u us' IH] /= H.
have [Nu Nus'] := Forall_cons_1 _ _ _ H.
by rewrite (factorsN _ Nu) (IH Nus').
Qed.

(** [cancel_invs] as a sub-multiset (stdpp's [⊆+], the analogue of mathcomp's
    [subseq] for the membership facts we need). *)

Lemma insert_factor_subseq pt pts : insert_factor pt pts ⊆+ pt :: pts.
Proof.
rewrite /insert_factor; case_bool_decide as H.
- apply: submseteq_cons; exact: rem_submseteq.
- reflexivity.
Qed.

Lemma cancel_invs_cons pt pts :
  cancel_invs (pt :: pts) = insert_factor pt (cancel_invs pts).
Proof. by rewrite /cancel_invs /=. Qed.

Lemma cancel_invs_subseq pts : cancel_invs pts ⊆+ pts.
Proof.
elim: pts => [|pt pts IH]; first exact: submseteq_nil_l.
rewrite cancel_invs_cons.
etrans; first exact: insert_factor_subseq.
apply: submseteq_skip; exact: IH.
Qed.

(** Parity of the number of factors is preserved by cancellation. *)

Lemma parity_insert_factor pt pts :
  Nat.odd (length (insert_factor pt pts)) = negb (Nat.odd (length pts)).
Proof.
rewrite /insert_factor; case_bool_decide as H.
- rewrite (length_rem _ _ H).
  case: pts H => [|a pts'] H; first by move: H; rewrite elem_of_nil.
  by rewrite /= Nat.sub_0_r Nat.odd_succ Nat.negb_even.
- by rewrite /= Nat.odd_succ -Nat.negb_odd.
Qed.

Lemma parity_cancel_invs pts :
  Nat.odd (length (cancel_invs pts)) = Nat.odd (length pts).
Proof.
elim: pts => [//|pt pts IH].
by rewrite cancel_invs_cons parity_insert_factor IH Nat.odd_succ Nat.negb_odd.
Qed.

(** Counting occurrences under cancellation. *)

Lemma count_insert_factor pt1 pt2 pts :
  count_mem pt1 (insert_factor pt2 pts) =
  if bool_decide (inv_aux pt2 ∈ pts) then
    count_mem pt1 pts - (if bool_decide (pt1 = inv_aux pt2) then 1 else 0)
  else
    count_mem pt1 pts + (if bool_decide (pt1 = pt2) then 1 else 0).
Proof.
rewrite /insert_factor; case_bool_decide as H.
- exact: (count_mem_rem pt1 (inv_aux pt2) pts).
- rewrite /=; lia.
Qed.

Lemma count_cancel pt pts :
  wf pt -> negb (is_mul pt) -> Forall wf pts ->
  count_mem pt (cancel_invs pts) = count_mem pt pts - count_mem (inv_aux pt) pts.
Proof.
elim: pts pt => [|pt' pts' IH] pt wfpt Nmpt wfpts.
- rewrite /cancel_invs /=; lia.
- have [wfpt' wfpts'] := Forall_cons_1 _ _ _ wfpts.
  have Hpt := IH pt wfpt Nmpt wfpts'.
  have Hinv : count_mem (inv_aux pt) (cancel_invs pts')
            = count_mem (inv_aux pt) pts' - count_mem pt pts'.
  { have H := IH (inv_aux pt) (wf_inv_aux _ wfpt Nmpt) (is_mul_inv_aux _ wfpt) wfpts'.
    rewrite (inv_auxK _ wfpt) in H; exact: H. }
  have Hni : pt ≠ inv_aux pt by move=> e; apply: (inv_aux_Nid pt); rewrite -e.
  rewrite cancel_invs_cons count_insert_factor.
  have Hcm1 : count_mem pt (pt' :: pts')
            = (if bool_decide (pt = pt') then 1 else 0) + count_mem pt pts' by [].
  have Hcm2 : count_mem (inv_aux pt) (pt' :: pts')
            = (if bool_decide (inv_aux pt = pt') then 1 else 0)
              + count_mem (inv_aux pt) pts' by [].
  rewrite Hcm1 Hcm2; clear Hcm1 Hcm2.
  case: (decide (pt = pt')) => [Hpp | Hpp].
  + subst pt'.
    rewrite (bool_decide_eq_false_2 _ Hni).
    rewrite !(bool_decide_eq_true_2 (pt = pt) eq_refl).
    rewrite (bool_decide_eq_false_2 (inv_aux pt = pt) (inv_aux_Nid pt)).
    case_bool_decide as Hmem.
    * have Hne : count_mem (inv_aux pt) (cancel_invs pts') ≠ 0.
      { exact: (proj1 (elem_of_count_mem _ _) Hmem). }
      rewrite Hinv in Hne; rewrite Hpt; lia.
    * have Heq : count_mem (inv_aux pt) (cancel_invs pts') = 0.
      { exact: (proj1 (not_elem_of_count_mem _ _) Hmem). }
      rewrite Hinv in Heq; rewrite Hpt; lia.
  + rewrite (bool_decide_eq_false_2 (pt = pt') Hpp).
    case: (decide (pt = inv_aux pt')) => [Q | Q].
    * have Ee : inv_aux pt = pt' by rewrite Q (inv_auxK _ wfpt').
      rewrite (bool_decide_eq_true_2 (inv_aux pt = pt') Ee).
      rewrite (bool_decide_eq_true_2 (pt = inv_aux pt') Q).
      have HM : inv_aux pt' = pt by rewrite -Q.
      rewrite HM.
      case_bool_decide as Hmem.
      -- have Hne : count_mem pt (cancel_invs pts') ≠ 0.
         { exact: (proj1 (elem_of_count_mem _ _) Hmem). }
         rewrite Hpt in Hne; rewrite Hpt; lia.
      -- have Heq : count_mem pt (cancel_invs pts') = 0.
         { exact: (proj1 (not_elem_of_count_mem _ _) Hmem). }
         rewrite Hpt in Heq; rewrite Hpt; lia.
    * rewrite (bool_decide_eq_false_2 (pt = inv_aux pt') Q).
      have Eop : bool_decide (inv_aux pt = pt') = false.
      { apply: bool_decide_eq_false_2 => e; apply: Q; by rewrite -e (inv_auxK _ wfpt). }
      rewrite Eop; clear Eop.
      case_bool_decide as Hmem; rewrite Hpt; lia.
Qed.

Lemma not_wf_inv_aux_mul pt : is_mul pt -> wf (inv_aux pt) -> False.
Proof. by case: pt => [o|o t|o t1 t2|ts] //= _ [_ [H _]]; case: H. Qed.

Lemma count_cancel_mul pt pts :
  is_mul pt -> Forall wf pts ->
  count_mem pt (cancel_invs pts) = count_mem pt pts.
Proof.
move=> Mpt; elim: pts => [//|pt' pts' IH] wfpts.
have [wfpt' wfpts'] := Forall_cons_1 _ _ _ wfpts.
rewrite cancel_invs_cons count_insert_factor (IH wfpts').
have Hcm : count_mem pt (pt' :: pts')
         = (if bool_decide (pt = pt') then 1 else 0) + count_mem pt pts' by [].
rewrite Hcm; clear Hcm.
have Ne : bool_decide (pt = inv_aux pt') = false.
{ apply: bool_decide_eq_false_2 => e.
  have Hnm := is_mul_inv_aux _ wfpt'; rewrite -e in Hnm.
  by move: Mpt Hnm; case: (pt) => [o|o t|o t1 t2|ts]. }
rewrite Ne; clear Ne.
case Em: (bool_decide (inv_aux pt' ∈ cancel_invs pts')).
- move/bool_decide_eq_true_1: Em => Hin.
  have Hpp : bool_decide (pt = pt') = false.
  { apply: bool_decide_eq_false_2 => e; rewrite -e in Hin.
    have wfI : wf (inv_aux pt).
    { move: (wf_cancel_invs _ wfpts') => /list.Forall_forall H; exact: (H _ Hin). }
    exact: (not_wf_inv_aux_mul _ Mpt wfI). }
  rewrite Hpp; lia.
- lia.
Qed.

Lemma count_perm_cancel pts1 pts2 :
  Forall wf pts1 -> Forall (fun t => negb (is_mul t)) pts1 ->
  Forall wf pts2 -> Forall (fun t => negb (is_mul t)) pts2 ->
  (forall pt, wf pt -> negb (is_mul pt) ->
     count_mem pt pts1 - count_mem (inv_aux pt) pts1 =
     count_mem pt pts2 - count_mem (inv_aux pt) pts2) ->
  cancel_invs pts1 ≡ₚ cancel_invs pts2.
Proof.
move=> wfs1 Nms1 wfs2 Nms2 wt_eq.
apply: Permutation_count_mem => pt.
case: (decide (pt ∈ cancel_invs pts1)) => H1.
- have wfpt : wf pt.
  { move: (wf_cancel_invs _ wfs1) => /list.Forall_forall H; exact: (H _ H1). }
  have Nmpt : negb (is_mul pt).
  { move: (Nmul_cancel_invs _ Nms1) => /list.Forall_forall H; exact: (H _ H1). }
  rewrite (count_cancel _ _ wfpt Nmpt wfs1) (count_cancel _ _ wfpt Nmpt wfs2).
  exact: (wt_eq pt wfpt Nmpt).
- case: (decide (pt ∈ cancel_invs pts2)) => H2.
  + have wfpt : wf pt.
    { move: (wf_cancel_invs _ wfs2) => /list.Forall_forall H; exact: (H _ H2). }
    have Nmpt : negb (is_mul pt).
    { move: (Nmul_cancel_invs _ Nms2) => /list.Forall_forall H; exact: (H _ H2). }
    rewrite (count_cancel _ _ wfpt Nmpt wfs1) (count_cancel _ _ wfpt Nmpt wfs2).
    exact: (wt_eq pt wfpt Nmpt).
  + by rewrite (proj1 (not_elem_of_count_mem _ _) H1)
               (proj1 (not_elem_of_count_mem _ _) H2).
Qed.

Lemma perm_cancel_invs pts1 pts2 :
  Forall wf pts1 -> pts1 ≡ₚ pts2 -> cancel_invs pts1 ≡ₚ cancel_invs pts2.
Proof.
move=> wf1 peq.
have wf2 : Forall wf pts2 by rewrite -peq.
apply: Permutation_count_mem => pt.
case Hm: (is_mul pt).
- have Mpt : is_mul pt by rewrite Hm.
  rewrite (count_cancel_mul _ _ Mpt wf1) (count_cancel_mul _ _ Mpt wf2).
  exact: (count_mem_Permutation pt _ _ peq).
- have Nmpt : negb (is_mul pt) by rewrite Hm.
  case: (decide (pt ∈ cancel_invs pts1)) => H1.
  + have wfpt : wf pt.
    { move: (wf_cancel_invs _ wf1) => /list.Forall_forall H; exact: (H _ H1). }
    rewrite (count_cancel _ _ wfpt Nmpt wf1) (count_cancel _ _ wfpt Nmpt wf2).
    by rewrite (count_mem_Permutation pt _ _ peq)
               (count_mem_Permutation (inv_aux pt) _ _ peq).
  + case: (decide (pt ∈ cancel_invs pts2)) => H2.
    * have wfpt : wf pt.
      { move: (wf_cancel_invs _ wf2) => /list.Forall_forall H; exact: (H _ H2). }
      rewrite (count_cancel _ _ wfpt Nmpt wf1) (count_cancel _ _ wfpt Nmpt wf2).
      by rewrite (count_mem_Permutation pt _ _ peq)
                 (count_mem_Permutation (inv_aux pt) _ _ peq).
    * by rewrite (proj1 (not_elem_of_count_mem _ _) H1)
                 (proj1 (not_elem_of_count_mem _ _) H2).
Qed.

Lemma mulP ts1 ts2 :
  cancel_invs (concat (factors <$> ts1)) ≡ₚ cancel_invs (concat (factors <$> ts2)) ->
  mul ts1 = mul ts2.
Proof. by move=> H; rewrite /mul (merge_sort_Permutation_eq pt_order _ _ H). Qed.

Lemma factors_mul ts :
  Forall wf ts ->
  factors (mul ts) = merge_sort pt_order (cancel_invs (concat (factors <$> ts))).
Proof.
move=> wf; rewrite /mul; set c := cancel_invs _.
have Nmul_c : Forall (fun t => negb (is_mul t)) c.
{ apply/list.Forall_forall => x /mem_cancel_invs xin.
  move: (flatten_factors_Nmul _ wf) => /list.Forall_forall H; exact: (H _ xin). }
case E: (merge_sort pt_order c) => [|t [|t' c']] //=.
have Ht : t ∈ c.
{ rewrite -(elem_of_merge_sort pt_order) E; exact: list_elem_of_here. }
move: (Nmul_c) => /list.Forall_forall H.
by rewrite (factorsN _ (H _ Ht)).
Qed.

Lemma perm_mul ts1 ts2 :
  Forall wf ts1 -> ts1 ≡ₚ ts2 -> mul ts1 = mul ts2.
Proof.
move=> wf1 peq; apply: mulP; apply: perm_cancel_invs.
- exact: (flatten_factors_wf _ wf1).
- by rewrite peq.
Qed.

Lemma mul_factors pt : wf pt -> mul (factors pt) = pt.
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /factors; try exact: (mul_wf1 _ wf).
move: wf; rewrite wf_MulE !andb_True
  => - [[[[_ /forallbP Nmul] /bool_decide_unpack sorted_ts]
         /bool_decide_unpack inv_ts] /bool_decide_unpack sizeN1].
rewrite /mul.
rewrite (flatten_factors_Nmul_id _ Nmul) (cancel_invs_canceled _ Nmul inv_ts)
        (merge_sort_id pt_order _ sorted_ts).
by case: ts sizeN1 {Nmul sorted_ts inv_ts} => [|x [|y ts']] // sizeN1; case: (sizeN1 erefl).
Qed.

Lemma exp_unit b : wf b -> exp b (PTMul []) = b.
Proof.
move=> wf; rewrite /exp.
have -> : mul [expo b; PTMul []] = expo b.
{ have -> : mul [expo b; PTMul []] = mul [expo b] by rewrite /mul /= !app_nil_r.
  exact: (mul_wf1 _ (wf_expo _ wf)). }
case: (decide (expo b = PTMul [])) => [e0 | eN0].
- rewrite (bool_decide_eq_true_2 _ e0).
  by rewrite (base_expN _ (expo_unit_Nexp _ wf e0)).
- rewrite (bool_decide_eq_false_2 _ eN0).
  by rewrite (base_expoK _ (expo_exp _ eN0)).
Qed.

Lemma expo_exp_eq b e : wf b -> expo (exp b e) = mul [expo b; e].
Proof.
move=> wfb; rewrite /exp.
case: (decide (mul [expo b; e] = PTMul [])) => [heq | hne].
- rewrite (bool_decide_eq_true_2 _ heq) heq.
  by rewrite (expo_expN _ (base_Nexp _ wfb)).
- by rewrite (bool_decide_eq_false_2 _ hne).
Qed.

Lemma exp_base_expo pt : wf pt -> exp (base pt) (expo pt) = pt.
Proof.
case: pt => [o|o t|[||] t1 t2|ts] wf; rewrite /base /expo; try exact: (exp_unit _ wf).
move: wf; rewrite wf_ExpE !andb_True => - [[[wfb Nxb] wfe] /bool_decide_unpack eN0].
rewrite /exp (expo_expN _ Nxb) (base_expN _ Nxb).
have -> : mul [PTMul []; t2] = t2.
{ have -> : mul [PTMul []; t2] = mul [t2] by rewrite /mul /= !app_nil_r.
  exact: (mul_wf1 _ wfe). }
by rewrite (bool_decide_eq_false_2 _ eN0).
Qed.

Lemma tsize_exp_Nexp b e :
  negb (is_exp b) -> wf e -> e ≠ PTMul [] ->
  tsize (exp b e) = S (tsize b + tsize e).
Proof.
move=> Nxb wfe eN0; rewrite /exp.
have -> : mul [expo b; e] = e.
{ rewrite (expo_expN _ Nxb).
  have -> : mul [PTMul []; e] = mul [e] by rewrite /mul /= !app_nil_r.
  exact: (mul_wf1 _ wfe). }
by rewrite (bool_decide_eq_false_2 _ eN0) (base_expN _ Nxb).
Qed.

Lemma exps_exp b e :
  wf b -> wf e ->
  exps (exp b e) = merge_sort pt_order (cancel_invs (exps b ++ factors e)).
Proof.
move=> wfb wfe.
have wf' : Forall wf [expo b; e]
  by constructor; [exact: (wf_expo _ wfb) | constructor; [exact: wfe | constructor]].
rewrite /exps (expo_exp_eq _ _ wfb) (factors_mul _ wf') /=.
by rewrite app_nil_r.
Qed.

Lemma is_exp_exp b e :
  wf b -> is_exp (exp b e) = negb (bool_decide (mul [expo b; e] = PTMul [])).
Proof.
move=> wfb; rewrite /exp.
case: (decide (mul [expo b; e] = PTMul [])) => [heq | hne].
- rewrite !(bool_decide_eq_true_2 _ heq).
  move: (base_Nexp _ wfb) => Hb; by case: (is_exp (base b)) Hb.
- by rewrite !(bool_decide_eq_false_2 _ hne).
Qed.

Lemma inv_factors pt : wf pt -> inv pt = mul (inv_aux <$> factors pt).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] wf; rewrite /inv /factors //.
all: rewrite fmap_cons fmap_nil (mul_wf1 _ (wf_inv_aux _ wf ltac:(done))) //.
Qed.

Lemma cancel_invs_cat pts1 pts2 :
  Forall wf pts1 -> Forall (fun t => negb (is_mul t)) pts1 ->
  Forall wf pts2 -> Forall (fun t => negb (is_mul t)) pts2 ->
  cancel_invs (cancel_invs pts1 ++ pts2) ≡ₚ cancel_invs (pts1 ++ pts2).
Proof.
move=> wf1 Nm1 wf2 Nm2; apply: count_perm_cancel.
- apply/Forall_app; split; [exact: (wf_cancel_invs _ wf1) | exact: wf2].
- apply/Forall_app; split; [exact: (Nmul_cancel_invs _ Nm1) | exact: Nm2].
- apply/Forall_app; split; [exact: wf1 | exact: wf2].
- apply/Forall_app; split; [exact: Nm1 | exact: Nm2].
- move=> pt wfpt Nmpt; rewrite !count_mem_app
    (count_cancel _ _ wfpt Nmpt wf1)
    (count_cancel _ _ (wf_inv_aux _ wfpt Nmpt) (is_mul_inv_aux _ wfpt) wf1)
    (inv_auxK _ wfpt); lia.
Qed.

Lemma mul_cat ts1 ts2 :
  Forall wf ts1 -> Forall wf ts2 -> mul (mul ts1 :: ts2) = mul (ts1 ++ ts2).
Proof.
move=> wf1 wf2; apply: mulP.
rewrite fmap_cons /= (factors_mul _ wf1) fmap_app concat_app.
etrans; last exact: (cancel_invs_cat _ _ (flatten_factors_wf _ wf1) (flatten_factors_Nmul _ wf1)
                                         (flatten_factors_wf _ wf2) (flatten_factors_Nmul _ wf2)).
apply: perm_cancel_invs.
- apply/Forall_app; split.
  + rewrite (Forall_merge_sort pt_order); exact: (wf_cancel_invs _ (flatten_factors_wf _ wf1)).
  + exact: (flatten_factors_wf _ wf2).
- by rewrite (merge_sort_Permutation pt_order).
Qed.

Lemma sortcancel_catr A B :
  Forall wf A -> Forall (fun t => negb (is_mul t)) A ->
  Forall wf B -> Forall (fun t => negb (is_mul t)) B ->
  merge_sort pt_order (cancel_invs (A ++ merge_sort pt_order (cancel_invs B)))
  = merge_sort pt_order (cancel_invs (A ++ B)).
Proof.
move=> wfA NmA wfB NmB; apply: (merge_sort_Permutation_eq pt_order).
have wfcB := wf_cancel_invs _ wfB.
etrans.
{ apply: perm_cancel_invs.
  - apply/Forall_app; split;
      [exact: wfA | rewrite (Forall_merge_sort pt_order); exact: wfcB].
  - by rewrite (merge_sort_Permutation pt_order). }
etrans.
{ apply: perm_cancel_invs.
  - apply/Forall_app; split; [exact: wfA | exact: wfcB].
  - exact: Permutation_app_comm. }
etrans; first exact: (cancel_invs_cat _ _ wfB NmB wfA NmA).
apply: perm_cancel_invs.
- apply/Forall_app; split; [exact: wfB | exact: wfA].
- exact: Permutation_app_comm.
Qed.

Lemma expo_exp_eq_key b e1 e2 :
  wf b -> wf e1 -> wf e2 ->
  mul [mul [expo b; e1]; e2] = mul [expo b; mul [e1; e2]].
Proof.
move=> wfb wfe1 wfe2.
have wfeb : wf (expo b) := wf_expo _ wfb.
have wf_e12 : Forall wf [e1; e2]
  by constructor; [exact: wfe1 | constructor; [exact: wfe2 | constructor]].
have wfm : wf (mul [e1; e2]) := wf_mul _ wf_e12.
have wf_be1 : Forall wf [expo b; e1]
  by constructor; [exact: wfeb | constructor; [exact: wfe1 | constructor]].
have wf_e2l : Forall wf [e2] by constructor; [exact: wfe2 | constructor].
have wf_ebl : Forall wf [expo b] by constructor; [exact: wfeb | constructor].
have wf_bm : Forall wf [expo b; mul [e1; e2]]
  by constructor; [exact: wfeb | constructor; [exact: wfm | constructor]].
have wf_be1e2 : Forall wf [expo b; e1; e2]
  by constructor; [exact: wfeb | exact: wf_e12].
rewrite (mul_cat [expo b; e1] [e2] wf_be1 wf_e2l).
rewrite (perm_mul [expo b; mul [e1; e2]] [mul [e1; e2]; expo b] wf_bm
           (Permutation_swap (mul [e1; e2]) (expo b) [])).
rewrite (mul_cat [e1; e2] [expo b] wf_e12 wf_ebl).
apply: perm_mul; first exact: wf_be1e2.
exact: (Permutation_cons_append [e1; e2] (expo b)).
Qed.

Lemma expA b e1 e2 :
  wf b -> wf e1 -> wf e2 -> exp (exp b e1) e2 = exp b (mul [e1; e2]).
Proof.
move=> wfb wfe1 wfe2.
by rewrite {1}/exp (base_exp _ _ wfb) (expo_exp_eq _ _ wfb)
           (expo_exp_eq_key _ _ _ wfb wfe1 wfe2).
Qed.

Lemma mul_mul2 ts1 ts2 :
  Forall wf ts1 -> Forall wf ts2 -> mul [mul ts1; mul ts2] = mul (ts1 ++ ts2).
Proof.
move=> wf1 wf2.
have wfm2 : wf (mul ts2) := wf_mul _ wf2.
have wf1m : Forall wf (ts1 ++ [mul ts2])
  by apply/Forall_app; split; [exact: wf1 | constructor; [exact: wfm2 | constructor]].
have wfm2l : Forall wf [mul ts2] by constructor; [exact: wfm2 | constructor].
rewrite (mul_cat ts1 [mul ts2] wf1 wfm2l).
rewrite (perm_mul (ts1 ++ [mul ts2]) (mul ts2 :: ts1) wf1m
                  (Permutation_app_comm ts1 [mul ts2])).
rewrite (mul_cat ts2 ts1 wf2 wf1).
apply: perm_mul; first by apply/Forall_app; split; [exact: wf2 | exact: wf1].
exact: Permutation_app_comm.
Qed.

Lemma count_map_inv pt ts :
  wf pt -> Forall wf ts ->
  count_mem pt (inv_aux <$> ts) = count_mem (inv_aux pt) ts.
Proof.
move=> wfpt; elim: ts => [//|t ts IH] wfts.
have [wft wfts'] := Forall_cons_1 _ _ _ wfts.
rewrite fmap_cons /= (IH wfts').
have E : bool_decide (pt = inv_aux t) = bool_decide (inv_aux pt = t).
{ exact: (bool_decide_ext _ _ (iff_sym (inv_aux_eq_op _ _ wfpt wft))). }
by rewrite E.
Qed.

Lemma invs_canceled_map_inv ts :
  Forall wf ts -> invs_canceled ts -> invs_canceled (inv_aux <$> ts).
Proof.
move=> wf canc.
move: (wf) => /list.Forall_forall wfa; move: canc => /list.Forall_forall canca.
apply/list.Forall_forall => x /list_elem_of_fmap [t [-> t_ts]].
rewrite (inv_inv_aux _ (wfa _ t_ts)) => /list_elem_of_fmap [s [e s_ts]].
move: (canca _ t_ts); rewrite e (inv_inv_aux _ (wfa _ s_ts)) => Habs.
exact: (Habs s_ts).
Qed.

Lemma cancel_invs_invs ts :
  Forall wf ts -> Forall (fun t => negb (is_mul t)) ts ->
  cancel_invs (ts ++ (inv_aux <$> ts)) = [].
Proof.
move=> wfs Nm.
have wfinv : Forall wf (inv_aux <$> ts).
{ apply/Forall_fmap; move: (wfs) => /list.Forall_forall wfa; move: (Nm) => /list.Forall_forall Nma.
  apply/list.Forall_forall => t t_ts; exact: (wf_inv_aux _ (wfa _ t_ts) (Nma _ t_ts)). }
have Nminv : Forall (fun t => negb (is_mul t)) (inv_aux <$> ts).
{ apply/Forall_fmap; move: (wfs) => /list.Forall_forall wfa.
  apply/list.Forall_forall => t t_ts; exact: (is_mul_inv_aux _ (wfa _ t_ts)). }
apply/Permutation_nil_r.
apply: (count_perm_cancel _ []).
- by apply/Forall_app; split; [exact: wfs | exact: wfinv].
- by apply/Forall_app; split; [exact: Nm | exact: Nminv].
- by constructor.
- by constructor.
- move=> pt wfpt Nmpt.
  rewrite !count_mem_app (count_map_inv _ _ wfpt wfs)
          (count_map_inv _ _ (wf_inv_aux _ wfpt Nmpt) wfs) (inv_auxK _ wfpt).
  simpl; lia.
Qed.

Lemma mul_invs ts :
  Forall wf ts -> Forall (fun t => negb (is_mul t)) (ts ++ (inv_aux <$> ts)) ->
  mul (ts ++ (inv_aux <$> ts)) = PTMul [].
Proof.
move=> wf atom.
move: (atom) => /Forall_app [Nm _].
by rewrite /mul (flatten_factors_Nmul_id _ atom) (cancel_invs_invs _ wf Nm).
Qed.

Lemma mul_eq_unit ts :
  Forall (fun t => negb (is_mul t)) ts -> invs_canceled ts ->
  mul ts = PTMul [] <-> ts = [].
Proof.
move=> atom canc; split; last first.
{ move=> ->; by rewrite /mul. }
rewrite /mul (flatten_factors_Nmul_id _ atom) (cancel_invs_canceled _ atom canc).
case E: (merge_sort pt_order ts) => [|a [|b l]].
- move=> _.
  have Hlen : length ts = 0 by rewrite -(length_merge_sort pt_order ts) E.
  by move: Hlen; case: ts {atom canc E}.
- move=> Ha.
  have Hin : a ∈ ts.
  { rewrite -(elem_of_merge_sort pt_order) E; exact: list_elem_of_here. }
  move: (atom) => /list.Forall_forall H.
  by move: (H _ Hin); rewrite Ha /=.
- by move=> [].
Qed.

Lemma tsize_mul ts :
  Forall (fun t => negb (is_mul t)) ts -> invs_canceled ts -> ts ≠ [] ->
  tsize (mul ts) = (if bool_decide (1 < length ts) then 1 else 0) + sum_list_with tsize ts.
Proof.
move=> atom canc tsN0.
rewrite /mul (flatten_factors_Nmul_id _ atom) (cancel_invs_canceled _ atom canc).
have Hlen : length (merge_sort pt_order ts) = length ts.
{ exact: (length_merge_sort pt_order ts). }
have Hsum : sum_list_with tsize (merge_sort pt_order ts) = sum_list_with tsize ts.
{ exact: (sum_list_with_Permutation tsize _ _ (merge_sort_Permutation pt_order ts)). }
case E: (merge_sort pt_order ts) => [|a [|b l]].
- move: Hlen; rewrite E /= => Hlen0.
  by case: ts tsN0 Hlen0 {E atom canc Hsum} => [|x xs].
- move: Hlen Hsum; rewrite E /= => Hlen1 Hsum1.
  rewrite (bool_decide_eq_false_2 (1 < length ts)); last by rewrite -Hlen1; lia.
  by rewrite -Hsum1 /= Nat.add_0_r.
- move: Hlen Hsum; rewrite E /= => Hlen2 Hsum2.
  rewrite (bool_decide_eq_true_2 (1 < length ts)); last by rewrite -Hlen2; lia.
  rewrite -Hsum2 /=; lia.
Qed.

Lemma invK pt : wf pt -> inv (inv pt) = pt.
Proof.
move=> wfpt.
have fs_wf := wf_factors _ wfpt.
have fs_Nm := Nmul_factors _ wfpt.
have fs_canc := invs_canceled_factors _ wfpt.
have wfinv : Forall wf (inv_aux <$> factors pt).
{ apply/Forall_fmap; move: (fs_wf) => /list.Forall_forall wfa; move: (fs_Nm) => /list.Forall_forall Nma.
  apply/list.Forall_forall => t t_fs; exact: (wf_inv_aux _ (wfa _ t_fs) (Nma _ t_fs)). }
have Nminv : Forall (fun t => negb (is_mul t)) (inv_aux <$> factors pt).
{ apply/Forall_fmap; move: (fs_wf) => /list.Forall_forall wfa.
  apply/list.Forall_forall => t t_fs; exact: (is_mul_inv_aux _ (wfa _ t_fs)). }
have canc_inv := invs_canceled_map_inv _ fs_wf fs_canc.
have mapK : forall l, Forall wf l -> inv_aux <$> (inv_aux <$> l) = l.
{ elim=> [//|x xs IH] Hxs.
  have [wx wxs] := Forall_cons_1 _ _ _ Hxs.
  by rewrite !fmap_cons (inv_auxK _ wx) (IH wxs). }
rewrite (inv_factors _ wfpt) (inv_factors _ (wf_mul _ wfinv)).
rewrite (factors_mul _ wfinv) (flatten_factors_Nmul_id _ Nminv)
        (cancel_invs_canceled _ Nminv canc_inv).
rewrite -{2}(mul_factors _ wfpt).
apply: perm_mul.
- apply/Forall_fmap.
  move: (wfinv) => /list.Forall_forall wfia; move: (Nminv) => /list.Forall_forall Nmia.
  apply/list.Forall_forall => t; rewrite (elem_of_merge_sort pt_order) => t_in.
  exact: (wf_inv_aux _ (wfia _ t_in) (Nmia _ t_in)).
- rewrite -{2}(mapK (factors pt) fs_wf).
  by rewrite (merge_sort_Permutation pt_order (inv_aux <$> factors pt)).
Qed.

Lemma mul_map_inv_aux_neq us :
  Forall wf us -> Forall (fun t => negb (is_mul t)) us ->
  invs_canceled us -> us ≠ [] -> mul (inv_aux <$> us) ≠ PTMul us.
Proof.
move=> wfs atoms canc usN0.
have wfI : Forall wf (inv_aux <$> us).
{ apply/Forall_fmap; move: (wfs) => /list.Forall_forall wfa; move: (atoms) => /list.Forall_forall ata.
  apply/list.Forall_forall => t t_us; exact: (wf_inv_aux _ (wfa _ t_us) (ata _ t_us)). }
have atomI : Forall (fun t => negb (is_mul t)) (inv_aux <$> us).
{ apply/Forall_fmap; move: (wfs) => /list.Forall_forall wfa.
  apply/list.Forall_forall => t t_us; exact: (is_mul_inv_aux _ (wfa _ t_us)). }
have cancI := invs_canceled_map_inv _ wfs canc.
move=> E.
have factE : factors (mul (inv_aux <$> us)) = merge_sort pt_order (inv_aux <$> us).
{ by rewrite (factors_mul _ wfI) (flatten_factors_Nmul_id _ atomI)
             (cancel_invs_canceled _ atomI cancI). }
move: factE; rewrite E /= => sortE.
have perm_us : us ≡ₚ (inv_aux <$> us).
{ rewrite {1}sortE; exact: (merge_sort_Permutation pt_order _). }
have [u u_us] : exists u, u ∈ us.
{ case: us usN0 {wfs atoms canc wfI atomI cancI E sortE perm_us} => [//|x xs] _.
  exists x; exact: list_elem_of_here. }
have inus : inv_aux u ∈ us.
{ rewrite perm_us; apply/list_elem_of_fmap; exists u; split; [done | exact: u_us]. }
move: canc => /list.Forall_forall Hc; move: atoms => /list.Forall_forall ata.
move: (Hc _ u_us); rewrite (inv_Nmul _ (ata _ u_us)) => Habs.
exact: (Habs inus).
Qed.

Lemma inv_fixed pt : wf pt -> (inv pt = pt) <-> (pt = PTMul []).
Proof.
move=> wf; case Hm: (is_mul pt); last first.
- have Nm : negb (is_mul pt) by rewrite Hm.
  rewrite (inv_Nmul _ Nm); split.
  + move=> E; exfalso; apply: (inv_aux_Nid pt); exact: E.
  + by move=> E; move: Nm; rewrite E /=.
- have Mpt : is_mul pt by rewrite Hm.
  case: pt Mpt wf {Hm} => [o|o t|o t1 t2|us] //= _ wf.
  move: wf; rewrite !andb_True
    => - [[[[/wfsP wfs /forallbP atoms] _] /bool_decide_unpack canc] _].
  case: (decide (us = [])) => [-> | usN0].
  + split=> _; first done.
    by rewrite /mul.
  + split.
    * move=> E; exfalso; exact: (mul_map_inv_aux_neq _ wfs atoms canc usN0 E).
    * move=> E; exfalso; case: E => Hus; exact: (usN0 Hus).
Qed.

End PreTerm.
