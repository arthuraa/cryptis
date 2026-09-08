(** Pre-term normalization
    ======================

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

    This file establishes only the normalization machinery.  The basic equations
    above (on well-formed pre-terms), and the theory of the destructors, are
    proved separately, in [laws.v].  The derived equations are not proved on
    pre-terms at all: they are consequences of the fundamentals and are proved
    for terms in [core/term/base.v] ([TInvK], [TInv_fixed], [TMul_cancel], …).

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

Definition mul_aux ts :=
  match ts with
  | [t] => t
  | _ => PTMul ts
  end.

Definition normalize_factors ts :=
  SMS.to pt_order inv_aux (mbind factors ts).

Definition mul ts := mul_aux (normalize_factors ts).

Definition inv pt :=
  if pt is PTMul ts then mul (inv_aux <$> ts) else inv_aux pt.

Definition exp_aux b e :=
  if bool_decide (e = PTMul []) then b else PTExp b e.

Definition exp b e :=
  exp_aux (base b) (mul [expo b; e]).

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
    (forallb (λ t, wf t && negb (is_mul t)) ts
     && SMS.wf pt_order inv_aux ts)
    && bool_decide (length ts ≠ 1)
  end.

Definition wf_factors ts :=
  forallb (λ t, wf t && negb (is_mul t)) ts
  && SMS.wf pt_order inv_aux ts.

Lemma wf_factors_wf t ts : wf_factors ts → t ∈ ts → wf t.
Proof.
move=> /andb_True [/forallb_True/list.Forall_forall wf_ts _] t_ts.
by case/andb_True: (wf_ts _ t_ts).
Qed.

Lemma wf_factors_Nmul t ts : wf_factors ts → t ∈ ts → negb (is_mul t).
move=> /andb_True [/forallb_True/list.Forall_forall wf_ts _] t_ts.
by case/andb_True: (wf_ts _ t_ts).
Qed.

Lemma wf_factors_sms ts : wf_factors ts → SMS.wf pt_order inv_aux ts.
Proof. by case/andb_True. Qed.

Lemma inv_aux_Nid pt : inv_aux pt ≠ pt.
Proof.
by case: pt => [o|[k| |] t|o t1 t2|ts] /=; move=> /(f_equal height) /=; lia.
Qed.

Lemma inv_invN pt : negb (is_inv pt) -> inv_aux pt = PTInv pt.
Proof. by case: pt => [o|[k| |] t|o t1 t2|ts]. Qed.

Lemma inv_auxK pt : wf pt -> inv_aux (inv_aux pt) = pt.
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] //=.
by rewrite !andb_True => - [[/inv_invN -> _] _].
Qed.

Lemma wf_one : wf (PTMul []).
Proof. by rewrite /wf !andb_True; split_and!. Qed.

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
case: pt => [o|o t|[||] b e|ts]; try (move=> _; exact: wf_one).
by move=> wf_pt; move: wf_pt; rewrite /= !andb_True => - [[[_ _] ?] _].
Qed.

Lemma factors_Nmul pt : negb (is_mul pt) -> factors pt = [pt].
Proof. by case: pt. Qed.

Lemma wf_wf_factors pt : wf pt -> wf_factors (factors pt).
Proof.
case E: (is_mul pt) => wf_pt.
  by case: pt E wf_pt => //= pts _ /andb_True [].
rewrite /wf_factors factors_Nmul //= ?E //= 3!andb_True; do !split => //.
apply: SMS.wf_singleton.
- exact: inv_aux_Nid.
- by rewrite inv_auxK.
Qed.

Lemma wf_inv_aux pt : wf pt -> negb (is_mul pt) -> wf (inv_aux pt).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] wf_pt Nm //=.
by move: wf_pt; rewrite /= !andb_True => - [[_ _] ?].
Qed.

Lemma inv_Nmul pt : negb (is_mul pt) -> inv pt = inv_aux pt.
Proof. by case: pt. Qed.

Lemma wf_mul_aux ts : wf_factors ts → wf (mul_aux ts).
Proof.
case: (decide (length ts = 1)) => E.
  case: ts => [//|t [|//]] in E *.
  move=> /wf_factors_wf wf_t /=; apply: wf_t; exact/list_elem_of_singleton.
have ->: mul_aux ts = PTMul ts by case: ts => [|?[|??]] in E *.
move=> wf_ts; apply/andb_True; split => //.
exact/bool_decide_spec.
Qed.

Lemma wf_normalize_factors ts :
  Forall wf ts → wf_factors (normalize_factors ts).
Proof.
move=> wf_ts; rewrite /normalize_factors /wf_factors andb_True.
set ts1 := mbind factors ts.
set ts2 := SMS.to pt_order inv_aux ts1.
have wf_ts1: Forall (λ t, wf t && negb (is_mul t)) ts1.
  rewrite Forall_bind; apply: Forall_impl wf_ts => t /wf_wf_factors wf_t.
  apply/list.Forall_forall=> t' t'_t; apply/andb_True; split.
  - by apply: wf_factors_wf; eauto.
  - by apply: wf_factors_Nmul; eauto.
split.
- apply/forallb_True/list.Forall_forall=> t /(SMS.mem_to _ _ _).
  move/list.Forall_forall: wf_ts1; exact.
- apply: SMS.wf_to => t t_ts1; apply: inv_auxK.
  by case/list.Forall_forall/(_ _ t_ts1)/andb_True: wf_ts1.
Qed.

Lemma wf_mul ts : Forall wf ts -> wf (mul ts).
Proof.
move=> wf_ts; rewrite /mul.
apply: wf_mul_aux; exact: wf_normalize_factors.
Qed.

Lemma normalize_factors1 t : wf t → normalize_factors [t] = factors t.
Proof.
move=> wf_t; rewrite /normalize_factors /= app_nil_r.
rewrite (SMS.to_id pt_order inv_aux (factors t)) //.
apply: wf_factors_sms; exact: wf_wf_factors.
Qed.

Lemma factorsK t : wf t → mul_aux (factors t) = t.
Proof.
case: t => [o|o t|o t1 t2|ts] //= wf_t.
case/andb_True: wf_t=> _ Hlen.
by case: ts Hlen => [|t [|t' c']].
Qed.

Lemma mul_auxK ts : wf_factors ts → factors (mul_aux ts) = ts.
Proof.
case: ts => [| t [| ??]] //= wf_t; rewrite factors_Nmul //.
apply: wf_factors_Nmul; eauto; exact/list_elem_of_singleton.
Qed.

Lemma mul1 t : wf t -> mul [t] = t.
Proof.
by move=> wf_t; rewrite /mul normalize_factors1 // factorsK.
Qed.

Lemma mul_unit_l t : mul [PTMul []; t] = mul [t].
Proof. by []. Qed.

Lemma wf_exp_aux b e :
  negb (is_exp b) →
  wf b →
  wf e →
  wf (exp_aux b e).
Proof.
move=> bNx wf_b wf_e; rewrite /exp_aux; case_bool_decide as Hf => //=.
rewrite !andb_True bool_decide_spec; eauto.
Qed.

Lemma wf_exp b e : wf b -> wf e -> wf (exp b e).
Proof.
move=> wf_b wf_e; apply: wf_exp_aux => //.
- exact: base_Nexp.
- exact: wf_base.
- apply: wf_mul.
  by rewrite !list.Forall_cons list.Forall_nil; eauto using wf_expo.
Qed.

Lemma wf_inv t : wf t -> wf (inv t).
Proof.
move=> wf_t; case e: (is_mul t); last first.
  by rewrite inv_Nmul ?e //; apply: wf_inv_aux; rewrite // e.
case: t => //= ts in wf_t e *.
case/andb_True: wf_t => wf_ts tsN1.
apply: wf_mul; apply/list.Forall_forall=> _ /list_elem_of_fmap [t [] -> t_ts].
apply: wf_inv_aux.
- exact: wf_factors_wf t_ts.
- exact: wf_factors_Nmul t_ts.
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
Hint Resolve wf_normalize : core.

Lemma normalize_factors_wf_factors ts :
  wf_factors ts → normalize_factors ts = ts.
Proof.
move=> wf_ts; rewrite /normalize_factors.
have ->: mbind factors ts = ts.
  case/andb_True: wf_ts=> wf_ts _.
  elim: ts wf_ts => //= t ts IH.
  case/andb_True=> [/andb_True [wf_t Nm_t] /IH E].
  by rewrite factors_Nmul //= -[in RHS]E.
rewrite SMS.to_id //; exact: wf_factors_sms.
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
    rewrite IH1 // IH2 // /exp base_expN // expo_expN //.
    by rewrite mul_unit_l // mul1 // /exp_aux bool_decide_eq_false_2.
- move=> ts IHts /andb_True [wf_ts /bool_decide_spec tsN1].
  have {}IHts: Forall (λ t, wf t → normalize t = t) ts.
    by elim: (ts) IHts => //= t' ts' IH [? /IH ?]; eauto.
  have {IHts} ->: normalize <$> ts = ts.
    rewrite -[RHS]list_fmap_id; apply/Forall_fmap_ext.
    apply/list.Forall_forall => t t_ts.
    move/list.Forall_forall: IHts; apply => //.
    exact: wf_factors_wf t_ts.
  rewrite /mul normalize_factors_wf_factors //.
  by case: (ts) tsN1 => [|? [|??]].
Qed.

Lemma normalize_idem pt : normalize (normalize pt) = normalize pt.
Proof. exact: normalize_wf. Qed.

Lemma fmap_normalize_wf ts : Forall wf ts → normalize <$> ts = ts.
Proof.
move=> /list.Forall_forall wf_ts.
rewrite -[RHS]list_fmap_id; apply/Forall_fmap_ext/list.Forall_forall.
by move=> t t_ts'; apply: normalize_wf; eauto.
Qed.

End PreTerm.
