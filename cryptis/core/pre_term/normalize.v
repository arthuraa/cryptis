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

    This file establishes only the normalization machinery.  The *fundamental*
    equations above (on well-formed pre-terms), and the theory of the
    destructors, are proved separately, in [laws.v].  The *derived* equations are
    not proved on pre-terms at all: they are consequences of the fundamentals and
    are proved once, at the [term] layer, in [core/term/base.v] ([TInvK],
    [TInv_fixed], [TMul_cancel], …).

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

(** No inverse pairs, spelled out as a first-order fact about [factors] (and, in
    the ported theory below, [exps]).  On the atomic factor lists [inv] and
    [inv_aux] coincide ([inv_Nmul]), so the [inv_aux]-cancellation carried by the
    generic [SMS.wf] conjunct is exactly "no [inv] pairs". *)

Lemma no_inv1 t : negb (is_mul t) -> forall q, q ∈ [t] -> inv q ∉ [t].
Proof.
move=> Nm q /list_elem_of_singleton -> Hin.
move: Hin; rewrite list_elem_of_singleton (inv_Nmul _ Nm); exact: inv_aux_Nid.
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

End PreTerm.
