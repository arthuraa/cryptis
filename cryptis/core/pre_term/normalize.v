(** Pre-term normalization

    This file defines a normalization function on pre-terms.  Two pre-terms have
    the same normal form if and only if they are equal according to the
    following equations:

    - [(g ^ a) ^ b = g ^ (a * b)]
    - [a * b = b * a]
    - [a * (b * c) = (a * b) * c]
    - [a * a^-1 = 1]
    - [a * 1 = a]
    - [g ^ 1 = g]

    where [1 := TMulN []], [g ^ x := TExp g x] and [a * b := TMulN [a; b]].
    From these equations, several other properties follow, such as

    - [a * b = a * c -> b = c]
    - [(a^-1)^-1 = a]
    - [(1^-1) = 1]
    - [(a * b)^-1 = a^-1 * b^-1]
    - [a^-1 * a = 1]
    - [1 * a = a]
    - [(g ^ a) ^ (a^-1) = g]
    - [(g ^ a) ^ b = (g ^ b) ^ a]

    The predicate [wf : pre_term -> bool] characterizes normal forms and is
    defined by structural recursion on the pre-term.  We have the following
    properties:

   - [normalize_wf : wf t -> normalize t = t]
   - [wf_normalize : wf (normalize t)]
   - [normalize_idem : normalize (normalize t) = normalize t]

*)

From stdpp Require Import sorting list numbers.
From cryptis Require Import lib.
From cryptis.lib Require Import list_sort sms.
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

Definition mul ts :=
  match SMS.to pt_order inv_aux (concat (factors <$> ts)) with
  | [t] => t
  | l => PTMul l
  end.

(* Keep [mul] folded under [simpl]; reason about it through its definition
   [SMS.to pt_order inv_aux (concat (factors <$> ts))] and the [SMS.to]/[SMS.count]
   theory, unfolding with [/mul] when a case split on the canonical factor list
   is needed. *)
Arguments mul : simpl never.

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
    && SMS.wf pt_order inv_aux ts && bool_decide (length ts ≠ 1)
  end.

Lemma wfsP ts : forallb wf ts <-> Forall wf ts.
Proof. exact: forallb_True. Qed.

Lemma inv_aux_Nid pt : inv_aux pt ≠ pt.
Proof. by case: pt => [o|[k| |] t|o t1 t2|ts] /=; move=> /(f_equal height) /=; lia. Qed.

(* On [inv_aux]-lists the fixed-point pruning inside [SMS.to] is vacuous
   ([inv_aux] has no fixed points, [inv_aux_Nid]), so [SMS.to] is just
   sort-after-cancel — the shape the executable primitives ([hl_mul]/[hl_exp])
   compute.  Lets those spec proofs unfold [SMS.to] without exposing [prune]. *)
Lemma to_inv_aux X :
  SMS.to pt_order inv_aux X = merge_sort pt_order (SMS.cancel inv_aux X).
Proof. by rewrite /SMS.to (SMS.prune_id inv_aux X (fun x _ => inv_aux_Nid x)). Qed.

Lemma inv_invN pt : negb (is_inv pt) -> inv_aux pt = PTInv pt.
Proof. by case: pt => [o|[k| |] t|o t1 t2|ts]. Qed.

Lemma inv_auxK pt : wf pt -> inv_aux (inv_aux pt) = pt.
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] //=.
by rewrite !andb_True => - [[/inv_invN -> _] _].
Qed.

Lemma wf_Mul_inv ts :
  wf (PTMul ts) ->
  Forall wf ts /\ Forall (fun t => negb (is_mul t)) ts /\
  SMS.wf pt_order inv_aux ts /\ length ts ≠ 1.
Proof.
rewrite /= => /andb_True [/andb_True [/andb_True [Hwf Hnm] Hsms] Hlen].
split_and!.
- exact: (proj1 (wfsP _) Hwf).
- exact: (proj1 (forallb_True _ _) Hnm).
- exact: Hsms.
- exact: (bool_decide_unpack _ Hlen).
Qed.

Lemma wf_nil : wf (PTMul []).
Proof. by rewrite /wf !andb_True; split_and!. Qed.

(** Facts about [base], [expo], [factors] and [inv_aux]. *)

Lemma wf_base pt : wf pt -> wf (base pt).
Proof.
case: pt => [o|o t|[||] b e|ts] wf_pt //.
by move: wf_pt; rewrite /= !andb_True => - [[[? _] _] _].
Qed.

Lemma base_expN pt : negb (is_exp pt) -> base pt = pt.
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

Lemma base_Nexp pt : wf pt -> negb (is_exp (base pt)).
Proof.
case: pt => [o|o t|[||] b e|ts] wf_pt //=.
by move: wf_pt; rewrite /= !andb_True => - [[[_ ?] _] _].
Qed.

Lemma expo_expN pt : negb (is_exp pt) -> expo pt = PTMul [].
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

Lemma wf_expo pt : wf pt -> wf (expo pt).
Proof.
case: pt => [o|o t|[||] b e|ts]; try (move=> _; exact: wf_nil).
by move=> wf_pt; move: wf_pt; rewrite /= !andb_True => - [[[_ _] ?] _].
Qed.

Lemma factorsN pt : negb (is_mul pt) -> factors pt = [pt].
Proof. by case: pt. Qed.

Lemma wf_factors pt : wf pt -> Forall wf (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf_pt; rewrite /factors /=;
  try by rewrite Forall_singleton.
by case: (wf_Mul_inv _ wf_pt).
Qed.

Lemma Nmul_factors pt : wf pt -> Forall (fun t => negb (is_mul t)) (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf_pt; rewrite /factors /=;
  try by rewrite Forall_singleton.
by case: (wf_Mul_inv _ wf_pt) => _ [? _].
Qed.

Lemma wf_inv_aux pt : wf pt -> negb (is_mul pt) -> wf (inv_aux pt).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] wf_pt Nm //=.
by move: wf_pt; rewrite /= !andb_True => - [[_ _] ?].
Qed.

Lemma inv_Nmul pt : negb (is_mul pt) -> inv pt = inv_aux pt.
Proof. by case: pt. Qed.

Lemma is_mul_inv_aux pt : wf pt -> negb (is_mul (inv_aux pt)).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] wf //=.
by move: wf; rewrite /= !andb_True => - [[_ H] _].
Qed.

(** Discharge the generic [SMS] involution hypothesis from well-formedness:
    [inv_aux] is an involution on every wf element ([inv_auxK]), so on a
    [Forall wf] list the per-element law [SMS] asks for holds. *)
Lemma wf_invol pts : Forall wf pts -> forall x, x ∈ pts -> inv_aux (inv_aux x) = x.
Proof. move=> /list.Forall_forall H x xin; exact: (inv_auxK _ (H _ xin)). Qed.

Lemma flatten_factors_wf ts :
  Forall wf ts -> Forall wf (concat (factors <$> ts)).
Proof.
elim: ts => [//|t ts IH] /=.
move=> H; have [wft wfts] := Forall_cons_1 _ _ _ H.
apply/Forall_app; split; [exact: wf_factors | exact: (IH wfts)].
Qed.

(** Two products are equal when their flattened factor lists carry the same
    signed [SMS.count] at every involution fixed point — the [SMS.to_eq]
    characterisation, with the per-list involution law discharged from
    well-formedness ([wf_invol]).  ([mul] depends on its arguments only
    through the canonical form [SMS.to] of the flattened factor list.) *)
Lemma mul_count_eq ts1 ts2 :
  Forall wf ts1 -> Forall wf ts2 ->
  (forall z, inv_aux (inv_aux z) = z ->
     SMS.count inv_aux z (concat (factors <$> ts1)) =
     SMS.count inv_aux z (concat (factors <$> ts2))) ->
  mul ts1 = mul ts2.
Proof.
move=> wf1 wf2 Hc.
have Heq : SMS.to pt_order inv_aux (concat (factors <$> ts1))
         = SMS.to pt_order inv_aux (concat (factors <$> ts2)).
  apply: (proj2 (SMS.to_eq pt_order inv_aux
                   (concat (factors <$> ts1)) (concat (factors <$> ts2))
                   (wf_invol _ (flatten_factors_wf _ wf1))
                   (wf_invol _ (flatten_factors_wf _ wf2)))).
  exact: Hc.
by rewrite /mul Heq.
Qed.

(** Canonicalising a suffix before concatenating does not change the canonical
    form of the whole: [SMS.to] absorbs an inner [SMS.to].  This is the generic
    engine behind [mul_cat] (and the [term]-layer [exps_TExpN]); it is the
    [pt_order]/[inv_aux] instance of [SMS.to_cat_to], with the involution laws
    discharged from well-formedness. *)
Lemma to_cat_to A B :
  Forall wf A -> Forall wf B ->
  SMS.to pt_order inv_aux (A ++ SMS.to pt_order inv_aux B)
  = SMS.to pt_order inv_aux (A ++ B).
Proof.
move=> wfA wfB.
exact: (SMS.to_cat_to pt_order inv_aux A B
          (wf_invol _ wfA) (wf_invol _ wfB)).
Qed.

(** No inverse pairs, spelled out as a first-order fact about [factors] (and, in
    the ported theory below, [exps]).  On the atomic factor lists [inv] and
    [inv_aux] coincide ([inv_Nmul]), so the [inv_aux]-cancellation carried by the
    generic [SMS.wf] conjunct is exactly "no [inv] pairs". *)

Lemma no_inv1 t : negb (is_mul t) -> forall q, q ∈ [t] -> inv q ∉ [t].
Proof.
move=> Nm q /list_elem_of_singleton -> Hin.
move: Hin; rewrite list_elem_of_singleton (inv_Nmul _ Nm); exact: inv_aux_Nid.
Qed.

(* On an atomic list [inv] and [inv_aux] agree, so "no [inv] pairs" is exactly the
   [inv_aux]-form the generic [SMS.to]/[SMS.wf] lemmas consume. *)
Lemma no_inv_aux_of_no_inv X :
  Forall (fun t => negb (is_mul t)) X -> (forall q, q ∈ X -> inv q ∉ X) ->
  forall q, q ∈ X -> inv_aux q ∉ X.
Proof.
move=> /list.Forall_forall Nm H q qin.
rewrite -(inv_Nmul _ (Nm q qin)); exact: (H q qin).
Qed.

Lemma no_inv_factors pt : wf pt -> forall q, q ∈ factors pt -> inv q ∉ factors pt.
Proof.
case: pt => [o|o t|o t1 t2|ts] wf_pt; rewrite /factors; try by apply: no_inv1.
case: (wf_Mul_inv _ wf_pt) => _ [/list.Forall_forall Nm [swf _]].
move=> q qin; rewrite (inv_Nmul _ (Nm q qin)).
exact: (SMS.wf_no_pairs pt_order inv_aux ts swf q qin).
Qed.

Lemma sorted_factors pt : wf pt -> StronglySorted pt_order (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf_pt; rewrite /factors;
  try by (repeat constructor).
case: (wf_Mul_inv _ wf_pt) => _ [_ [swf _]].
exact: (SMS.wf_sorted pt_order inv_aux ts swf).
Qed.

(* The factor list of a well-formed pre-term is a well-formed signed multiset
   (sorted, no inverse pairs) — the bundled [SMS.wf] form of [sorted_factors] +
   [no_inv_factors], which [SMS.to_id] and friends consume directly. *)
Lemma wf_factors_sms pt : wf pt -> SMS.wf pt_order inv_aux (factors pt).
Proof.
move=> wf; apply: (SMS.wf_intro pt_order inv_aux (factors pt) (sorted_factors _ wf)).
- move=> q qin; have /list.Forall_forall H := Nmul_factors _ wf; rewrite -(inv_Nmul _ (H q qin)).
  exact: (no_inv_factors _ wf q qin).
- move=> q qin; have /list.Forall_forall H := wf_factors _ wf; exact: (inv_auxK _ (H q qin)).
- move=> q _; exact: inv_aux_Nid.
Qed.

(* Multiplication *)

Lemma flatten_factors_Nmul ts :
  Forall wf ts -> Forall (fun t => negb (is_mul t)) (concat (factors <$> ts)).
Proof.
elim: ts => [//|t ts IH] /=.
move=> H; have [wft wfts] := Forall_cons_1 _ _ _ H.
apply/Forall_app; split; [exact: Nmul_factors | exact: (IH wfts)].
Qed.

(* Introduction rule for [wf (PTMul ts)].  Stated with an *abstract* [ts] so
   that [forallb wf ts] stays folded — otherwise [andb_True] would split it into
   its per-element conjuncts.  "No inverse pairs" is the spelled-out [inv] form;
   the generic [SMS.wf] conjunct is rebuilt from it via [SMS.wf_intro]. *)
Lemma wf_MulI ts :
  Forall wf ts -> Forall (fun t => negb (is_mul t)) ts ->
  StronglySorted pt_order ts -> (forall q, q ∈ ts -> inv q ∉ ts) -> length ts ≠ 1 ->
  wf (PTMul ts).
Proof.
move=> H1 H2 H3 H4 H5; rewrite /=.
apply/andb_True; split; last by apply: bool_decide_pack.
apply/andb_True; split; last first.
{ apply: (SMS.wf_intro pt_order inv_aux ts H3).
  - move=> q qin; have /list.Forall_forall Hff := H2; rewrite -(inv_Nmul _ (Hff q qin)); exact: (H4 q qin).
  - move=> q qin; have /list.Forall_forall Hff := H1; exact: (inv_auxK _ (Hff q qin)).
  - move=> q _; exact: inv_aux_Nid. }
apply/andb_True; split.
- exact: (proj2 (wfsP _) H1).
- exact: (proj2 (forallb_True _ _) H2).
Qed.

Lemma wf_mul ts : Forall wf ts -> wf (mul ts).
Proof.
move=> wf_ts; rewrite /mul.
have wfX := flatten_factors_wf _ wf_ts.
have NmX := flatten_factors_Nmul _ wf_ts.
have swf : SMS.wf pt_order inv_aux (SMS.to pt_order inv_aux (concat (factors <$> ts))).
{ exact: (SMS.wf_to pt_order inv_aux _ (wf_invol _ wfX)). }
have wf_L : Forall wf (SMS.to pt_order inv_aux (concat (factors <$> ts))).
{ apply/list.Forall_forall => x /(SMS.mem_to pt_order inv_aux) xin.
  have /list.Forall_forall H := wfX; exact: (H x xin). }
have Nmul_L : Forall (fun t => negb (is_mul t)) (SMS.to pt_order inv_aux (concat (factors <$> ts))).
{ apply/list.Forall_forall => x /(SMS.mem_to pt_order inv_aux) xin.
  have /list.Forall_forall H := NmX; exact: (H x xin). }
case E: (SMS.to pt_order inv_aux (concat (factors <$> ts))) => [|t [|t' c']].
- exact: wf_nil.
- move: wf_L; rewrite E => H; exact: (Forall_inv H).
- move: wf_L Nmul_L swf; rewrite E => wf' Nmul' swf'.
  apply: wf_MulI.
  + exact: wf'.
  + exact: Nmul'.
  + exact: (SMS.wf_sorted pt_order inv_aux _ swf').
  + move=> q qin; have /list.Forall_forall H := Nmul'; rewrite (inv_Nmul _ (H q qin)).
    exact: (SMS.wf_no_pairs pt_order inv_aux _ swf' q qin).
  + by [].
Qed.

Lemma mul_wf1 t : wf t -> mul [t] = t.
Proof.
move=> wf; rewrite /mul /= app_nil_r.
rewrite (SMS.to_id pt_order inv_aux (factors t) (wf_factors_sms _ wf)).
case: t wf => [o|o t|o t1 t2|ts] //= wf.
move: wf; rewrite !andb_True => - [_ Hlen].
by case: ts Hlen => [|t [|t' c']].
Qed.

(* [PTMul []] is a unit for [mul]: dropping it from a two-element product does
   not change the flattened factor list, hence not [mul]. *)
Lemma mul_unit_r X : mul [X; PTMul []] = mul [X].
Proof. by rewrite /mul /= !app_nil_r. Qed.
Lemma mul_unit_l X : mul [PTMul []; X] = mul [X].
Proof. by rewrite /mul /= !app_nil_r. Qed.

(* Introduction rules for [wf] at the [PTInv] and [PTExp] heads.  Abstract [pt]
   / [b], [e] keep the recursive [wf] calls folded. *)
Lemma wf_InvI pt : negb (is_inv pt) -> negb (is_mul pt) -> wf pt -> wf (PTInv pt).
Proof. by move=> H1 H2 H3; rewrite /= !andb_True; repeat split. Qed.

Lemma wf_ExpI b e :
  wf b -> negb (is_exp b) -> wf e -> bool_decide (e ≠ PTMul []) ->
  wf (PTExp b e).
Proof. by move=> H1 H2 H3 H4; rewrite /= !andb_True; repeat split. Qed.

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
- by move: wf; rewrite /= !andb_True => - [[_ _] ?].
- by apply: wf_InvI.
- apply: wf_mul; apply/Forall_fmap.
  case: (wf_Mul_inv _ wf) => /list.Forall_forall wf_ts [/list.Forall_forall Nm_ts _].
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
    { rewrite mul_unit_l; exact: (mul_wf1 _ wfe). }
    by rewrite (bool_decide_eq_false_2 _ eN0).
- move=> ts IHts wf_pt.
  case: (wf_Mul_inv _ wf_pt) => wf_ts [Nmul_F [swf sizeN1]]; clear wf_pt.
  have Nts : normalize <$> ts = ts.
  { elim: ts IHts wf_ts {Nmul_F swf sizeN1}
      => [//|t ts' IH] /= [IHt IHts'] Hwf.
    rewrite (IHt (Forall_inv Hwf)); f_equal.
    exact: (IH IHts' (Forall_inv_tail Hwf)). }
  rewrite Nts /mul.
  have ff : concat (factors <$> ts) = ts.
  { elim: ts Nmul_F {IHts wf_ts swf sizeN1 Nts}
      => [//|t ts' IH] /= HNm.
    rewrite (factorsN _ (Forall_inv HNm)) /=; f_equal.
    exact: (IH (Forall_inv_tail HNm)). }
  rewrite ff (SMS.to_id pt_order inv_aux ts swf).
  by case: ts sizeN1 {IHts wf_ts Nmul_F swf Nts ff}
    => [|t [|t' ts'']].
Qed.

Lemma normalize_idem pt : normalize (normalize pt) = normalize pt.
Proof. apply: normalize_wf; exact: wf_normalize. Qed.

(** ** Additional theory on pre-terms. *)

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

Lemma inv_inv_aux pt : wf pt -> inv (inv_aux pt) = pt.
Proof.
move=> wf; have Nm := is_mul_inv_aux _ wf.
have -> : inv (inv_aux pt) = inv_aux (inv_aux pt).
{ rewrite /inv; by case: (inv_aux pt) Nm => [o|o t|o t1 t2|ts]. }
exact: (inv_auxK _ wf).
Qed.

Lemma no_inv_exps_pt pt : wf pt -> forall q, q ∈ exps pt -> inv q ∉ exps pt.
Proof. move=> wf; rewrite /exps; exact: (no_inv_factors _ (wf_expo _ wf)). Qed.

Lemma exps_sorted pt : wf pt -> StronglySorted pt_order (exps pt).
Proof. move=> wf; rewrite /exps; exact: (sorted_factors _ (wf_expo _ wf)). Qed.

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

Lemma factors_mul ts :
  Forall wf ts ->
  factors (mul ts) = SMS.to pt_order inv_aux (concat (factors <$> ts)).
Proof.
move=> wf; rewrite /mul; set c := concat (factors <$> ts).
have Nmul_c : Forall (fun t => negb (is_mul t)) (SMS.to pt_order inv_aux c).
{ apply/list.Forall_forall => x /(SMS.mem_to pt_order inv_aux) xin.
  have /list.Forall_forall H := flatten_factors_Nmul _ wf; exact: (H x xin). }
case E: (SMS.to pt_order inv_aux c) => [|t [|t' c']] //=.
have Ht : t ∈ SMS.to pt_order inv_aux c by rewrite E; exact: list_elem_of_here.
have /list.Forall_forall H := Nmul_c; by rewrite (factorsN _ (H t Ht)).
Qed.

Lemma perm_mul ts1 ts2 :
  Forall wf ts1 -> ts1 ≡ₚ ts2 -> mul ts1 = mul ts2.
Proof.
move=> wf1 peq.
have peq' : concat (factors <$> ts1) ≡ₚ concat (factors <$> ts2) by rewrite peq.
apply: mul_count_eq.
- exact: wf1.
- by rewrite -peq.
- by move=> z _; rewrite peq'.
Qed.

Lemma mul_factors pt : wf pt -> mul (factors pt) = pt.
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /factors; try exact: (mul_wf1 _ wf).
case: (wf_Mul_inv _ wf) => _ [Nmul [swf sizeN1]]; clear wf.
rewrite /mul (flatten_factors_Nmul_id _ Nmul) (SMS.to_id pt_order inv_aux ts swf).
by case: ts sizeN1 {Nmul swf} => [|x [|y ts']] // sizeN1; case: (sizeN1 erefl).
Qed.

Lemma exp_unit b : wf b -> exp b (PTMul []) = b.
Proof.
move=> wf; rewrite /exp.
have -> : mul [expo b; PTMul []] = expo b.
{ rewrite mul_unit_r; exact: (mul_wf1 _ (wf_expo _ wf)). }
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
move: wf; rewrite /= !andb_True => - [[[wfb Nxb] wfe] /bool_decide_unpack eN0].
rewrite /exp (expo_expN _ Nxb) (base_expN _ Nxb).
have -> : mul [PTMul []; t2] = t2.
{ rewrite mul_unit_l; exact: (mul_wf1 _ wfe). }
by rewrite (bool_decide_eq_false_2 _ eN0).
Qed.

Lemma tsize_exp_Nexp b e :
  negb (is_exp b) -> wf e -> e ≠ PTMul [] ->
  tsize (exp b e) = S (tsize b + tsize e).
Proof.
move=> Nxb wfe eN0; rewrite /exp.
have -> : mul [expo b; e] = e.
{ rewrite (expo_expN _ Nxb) mul_unit_l; exact: (mul_wf1 _ wfe). }
by rewrite (bool_decide_eq_false_2 _ eN0) (base_expN _ Nxb).
Qed.

Lemma exps_exp b e :
  wf b -> wf e ->
  exps (exp b e) = SMS.to pt_order inv_aux (exps b ++ factors e).
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

Lemma mul_cat ts1 ts2 :
  Forall wf ts1 -> Forall wf ts2 -> mul (mul ts1 :: ts2) = mul (ts1 ++ ts2).
Proof.
move=> wf1 wf2.
have wfX1 := flatten_factors_wf _ wf1.
apply: mul_count_eq.
- constructor; [exact: (wf_mul _ wf1) | exact: wf2].
- by apply/Forall_app.
- move=> z iKz.
  rewrite fmap_cons /= (factors_mul _ wf1) fmap_app concat_app.
  by rewrite !(SMS.count_app inv_aux) (SMS.count_to pt_order inv_aux z _ iKz (wf_invol _ wfX1)).
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
{ apply: bool_decide_ext; split=> e;
    [by rewrite e (inv_auxK _ wft) | by rewrite -e (inv_auxK _ wfpt)]. }
by rewrite E.
Qed.

Lemma no_inv_map_inv ts :
  Forall wf ts -> (forall q, q ∈ ts -> inv q ∉ ts) ->
  forall q, q ∈ (inv_aux <$> ts) -> inv q ∉ (inv_aux <$> ts).
Proof.
move=> /list.Forall_forall wfa canca x /list_elem_of_fmap [t [-> t_ts]].
rewrite (inv_inv_aux _ (wfa _ t_ts)) => /list_elem_of_fmap [s [e s_ts]].
move: (canca _ t_ts); rewrite e (inv_inv_aux _ (wfa _ s_ts)) => Habs.
exact: (Habs s_ts).
Qed.

Lemma mul_invs ts :
  Forall wf ts -> Forall (fun t => negb (is_mul t)) (ts ++ (inv_aux <$> ts)) ->
  mul (ts ++ (inv_aux <$> ts)) = PTMul [].
Proof.
move=> wfs atom.
move: (atom) => /Forall_app [Nm _].
have wfinv : Forall wf (inv_aux <$> ts).
{ apply/Forall_fmap; move: (wfs) => /list.Forall_forall wfa; move: (Nm) => /list.Forall_forall Nma.
  apply/list.Forall_forall => t t_ts; exact: (wf_inv_aux _ (wfa _ t_ts) (Nma _ t_ts)). }
have -> : PTMul [] = mul [] by rewrite /mul.
apply: mul_count_eq.
- by apply/Forall_app; split; [exact: wfs | exact: wfinv].
- by constructor.
- move=> z iKz.
  rewrite (flatten_factors_Nmul_id _ atom) (SMS.count_app inv_aux)
          (SMS.count_fmap_i inv_aux z ts iKz (wf_invol _ wfs)).
  rewrite /SMS.count /=; lia.
Qed.

Lemma mul_eq_unit ts :
  Forall (fun t => negb (is_mul t)) ts -> (forall q, q ∈ ts -> inv q ∉ ts) ->
  mul ts = PTMul [] <-> ts = [].
Proof.
move=> atom canc; split; last first.
{ move=> ->; by rewrite /mul. }
rewrite /mul (flatten_factors_Nmul_id _ atom).
have Hperm : SMS.to pt_order inv_aux ts ≡ₚ ts.
{ exact: (SMS.to_id_perm pt_order inv_aux ts (no_inv_aux_of_no_inv _ atom canc)). }
case E: (SMS.to pt_order inv_aux ts) => [|a [|b l]].
- move=> _.
  have Hlen : length ts = 0 by rewrite -(Permutation_length Hperm) E.
  by move: Hlen; case: ts {atom canc Hperm E}.
- move=> Ha.
  have Hin : a ∈ ts.
  { apply: (SMS.mem_to pt_order inv_aux); rewrite E; exact: list_elem_of_here. }
  by have /list.Forall_forall H := atom; move: (H a Hin); rewrite Ha /=.
- by move=> [].
Qed.

Lemma tsize_mul ts :
  Forall (fun t => negb (is_mul t)) ts -> (forall q, q ∈ ts -> inv q ∉ ts) -> ts ≠ [] ->
  tsize (mul ts) = (if bool_decide (1 < length ts) then 1 else 0) + sum_list_with tsize ts.
Proof.
move=> atom canc tsN0.
rewrite /mul (flatten_factors_Nmul_id _ atom).
have Hperm : SMS.to pt_order inv_aux ts ≡ₚ ts.
{ exact: (SMS.to_id_perm pt_order inv_aux ts (no_inv_aux_of_no_inv _ atom canc)). }
have Hlen : length (SMS.to pt_order inv_aux ts) = length ts by exact: Permutation_length Hperm.
have Hsum : sum_list_with tsize (SMS.to pt_order inv_aux ts) = sum_list_with tsize ts
  by exact: (sum_list_with_Permutation tsize _ _ Hperm).
case E: (SMS.to pt_order inv_aux ts) => [|a [|b l]].
- move: Hlen; rewrite E /= => Hlen0.
  by case: ts tsN0 Hlen0 {E atom canc Hperm Hsum} => [|x xs].
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
have fs_canc := no_inv_factors _ wfpt.
have wfinv : Forall wf (inv_aux <$> factors pt).
{ apply/Forall_fmap; move: (fs_wf) => /list.Forall_forall wfa; move: (fs_Nm) => /list.Forall_forall Nma.
  apply/list.Forall_forall => t t_fs; exact: (wf_inv_aux _ (wfa _ t_fs) (Nma _ t_fs)). }
have Nminv : Forall (fun t => negb (is_mul t)) (inv_aux <$> factors pt).
{ apply/Forall_fmap; move: (fs_wf) => /list.Forall_forall wfa.
  apply/list.Forall_forall => t t_fs; exact: (is_mul_inv_aux _ (wfa _ t_fs)). }
have canc_inv := no_inv_map_inv _ fs_wf fs_canc.
have mapK : forall l, Forall wf l -> inv_aux <$> (inv_aux <$> l) = l.
{ elim=> [//|x xs IH] Hxs.
  have [wx wxs] := Forall_cons_1 _ _ _ Hxs.
  by rewrite !fmap_cons (inv_auxK _ wx) (IH wxs). }
rewrite (inv_factors _ wfpt) (inv_factors _ (wf_mul _ wfinv)).
rewrite (factors_mul _ wfinv) (flatten_factors_Nmul_id _ Nminv).
rewrite -{2}(mul_factors _ wfpt).
apply: perm_mul.
- apply/Forall_fmap.
  move: (wfinv) => /list.Forall_forall wfia; move: (Nminv) => /list.Forall_forall Nmia.
  apply/list.Forall_forall => t /(SMS.mem_to pt_order inv_aux) t_in.
  exact: (wf_inv_aux _ (wfia _ t_in) (Nmia _ t_in)).
- rewrite -{2}(mapK (factors pt) fs_wf).
  apply: Permutation_map.
  exact: (SMS.to_id_perm pt_order inv_aux _ (no_inv_aux_of_no_inv _ Nminv canc_inv)).
Qed.

Lemma mul_map_inv_aux_neq us :
  Forall wf us -> Forall (fun t => negb (is_mul t)) us ->
  (forall q, q ∈ us -> inv q ∉ us) -> us ≠ [] -> mul (inv_aux <$> us) ≠ PTMul us.
Proof.
move=> wfs atoms canc usN0.
have wfI : Forall wf (inv_aux <$> us).
{ apply/Forall_fmap; move: (wfs) => /list.Forall_forall wfa; move: (atoms) => /list.Forall_forall ata.
  apply/list.Forall_forall => t t_us; exact: (wf_inv_aux _ (wfa _ t_us) (ata _ t_us)). }
have atomI : Forall (fun t => negb (is_mul t)) (inv_aux <$> us).
{ apply/Forall_fmap; move: (wfs) => /list.Forall_forall wfa.
  apply/list.Forall_forall => t t_us; exact: (is_mul_inv_aux _ (wfa _ t_us)). }
have cancI := no_inv_map_inv _ wfs canc.
move=> E.
have factE : factors (mul (inv_aux <$> us)) = SMS.to pt_order inv_aux (inv_aux <$> us).
{ by rewrite (factors_mul _ wfI) (flatten_factors_Nmul_id _ atomI). }
move: factE; rewrite E /= => sortE.
have perm_us : us ≡ₚ (inv_aux <$> us).
{ rewrite {1}sortE.
  exact: (SMS.to_id_perm pt_order inv_aux _ (no_inv_aux_of_no_inv _ atomI cancI)). }
have [u u_us] : exists u, u ∈ us.
{ case: us usN0 {wfs atoms canc wfI atomI cancI E sortE perm_us} => [//|x xs] _.
  exists x; exact: list_elem_of_here. }
have inus : inv_aux u ∈ us.
{ rewrite perm_us; apply/list_elem_of_fmap; exists u; split; [done | exact: u_us]. }
have /list.Forall_forall Hat := atoms; move: (canc _ u_us); rewrite (inv_Nmul _ (Hat u u_us)) => Habs.
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
  case: (wf_Mul_inv _ wf) => wfs [atoms [swf _]].
  have canc : forall q, q ∈ us -> inv q ∉ us.
  { move=> q qin; have /list.Forall_forall H := atoms; rewrite (inv_Nmul _ (H q qin)).
    exact: (SMS.wf_no_pairs pt_order inv_aux us swf q qin). }
  case: (decide (us = [])) => [-> | usN0].
  + split=> _; first done.
    by rewrite /mul.
  + split.
    * move=> E; exfalso.
      exact: (mul_map_inv_aux_neq _ wfs atoms canc usN0 E).
    * move=> E; exfalso; case: E => Hus; exact: (usN0 Hus).
Qed.

End PreTerm.
