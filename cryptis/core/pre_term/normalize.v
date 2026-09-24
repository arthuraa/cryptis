(** Pre-term normalization
    ======================

    This file defines a normalization function on pre-terms.  Pre-terms carry
    *two* multiplicative structures:

    - the Diffie-Hellman group [PTGMul]/[PTGInv] (a symbolic model of a
      prime-order elliptic-curve group), which lives in the *base* of an
      exponential;
    - the exponent ring [PTMul]/[PTInv], which lives in the *exponent*.

    Two pre-terms have the same normal form if and only if they are equal
    according to the following equations.  Writing [1 := PTMul []],
    [1G := PTGMul []], [g ^ x := PTExp g x], [a * b := PTMul [a; b]] and
    [u ⋅ v := PTGMul [u; v]]:

    Group ([⋅], [PTGInv]):

    - [u ⋅ v = v ⋅ u]
    - [u ⋅ (v ⋅ w) = (u ⋅ v) ⋅ w]
    - [u ⋅ u^-1 = 1G]
    - [u ⋅ 1G = u]

    Exponents ([*], [PTInv]): the same four laws, at [PTMul]/[PTInv].

    Exponentiation, which links them:

    - [(g ^ a) ^ b = g ^ (a * b)]
    - [g ^ 1 = g]
    - [(u ⋅ v) ^ x = u^x ⋅ v^x]

    The last equation makes [_ ^ x] an endomorphism of the *group*.  From these
    equations, several other properties follow, such as

    - [u ⋅ v = u ⋅ w -> v = w]
    - [(u^-1)^-1 = u]
    - [(1G^-1) = 1G]
    - [(u ⋅ v)^-1 = u^-1 ⋅ v^-1]
    - [(g ^ a) ^ (a^-1) = g]
    - [(g ^ a) ^ b = (g ^ b) ^ a]
    - [1G ^ x = 1G]
    - [(u^-1) ^ x = (u ^ x)^-1]

    The last two are why [exp] distributes over [PTGInv] as well as [PTGMul],
    and why [wf] demands a *group atom* — neither group product, group inverse,
    nor exponential — in the base of an exponential: [(u^-1) ^ x] has normal
    form [(u ^ x)^-1].

    Note what is *not* here: [(a * b) ^ x] does not distribute.  A scalar
    product, or a scalar inverse, in the base of an exponential is an atom.
    Identifying the two structures is what forces exponentiation to degenerate
    (see [CLAUDE.md]); keeping them apart is the point of the split.

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
  | PTN _ ts => S (max_list_with height ts)
  end.

Definition is_inv pt := if pt is PTInv _ then true else false.
Definition is_ginv pt := if pt is PTGInv _ then true else false.
Definition is_exp pt := if pt is PTExp _ _ then true else false.
Definition is_mul pt := if pt is PTMul _ then true else false.
Definition is_gmul pt := if pt is PTGMul _ then true else false.
Definition is_nonce pt := if pt is PT0 (O0Nonce _) then true else false.

(** There are two multiplicative structures.  [PTGMul]/[PTGInv] are the
    Diffie-Hellman group -- a symbolic model of a prime-order elliptic-curve
    group -- and live in the *base* of an exponential.  [PTMul]/[PTInv] are the
    exponent ring and live in the *exponent*.  [exp] distributes over the group
    operations only; a scalar product or scalar inverse in a base is an atom.

    Accordingly there are two "non-free" predicates.  [is_non_free] collects
    every head that [term] represents indirectly (all five operations), and is
    what [core/term/base.v] uses for [TNonFree].  [is_gnon_free] collects the
    heads a normal-form exponential base may not have, and is what [wf] uses. *)
Definition is_non_free pt :=
  is_inv pt || is_ginv pt || is_exp pt || is_mul pt || is_gmul pt.

Definition is_gnon_free pt := is_ginv pt || is_exp pt || is_gmul pt.

Lemma Nnf_Ninv pt : negb (is_non_free pt) → negb (is_inv pt).
Proof. by case: pt => [o|[k| | |] t|[||] t1 t2|[|] ts]. Qed.

Lemma Nnf_Nginv pt : negb (is_non_free pt) → negb (is_ginv pt).
Proof. by case: pt => [o|[k| | |] t|[||] t1 t2|[|] ts]. Qed.

Lemma Nnf_Nexp pt : negb (is_non_free pt) → negb (is_exp pt).
Proof. by case: pt => [o|[k| | |] t|[||] t1 t2|[|] ts]. Qed.

Lemma Nnf_Nmul pt : negb (is_non_free pt) → negb (is_mul pt).
Proof. by case: pt => [o|[k| | |] t|[||] t1 t2|[|] ts]. Qed.

Lemma Nnf_Ngmul pt : negb (is_non_free pt) → negb (is_gmul pt).
Proof. by case: pt => [o|[k| | |] t|[||] t1 t2|[|] ts]. Qed.

Lemma Nnf_Ngnf pt : negb (is_non_free pt) → negb (is_gnon_free pt).
Proof. by case: pt => [o|[k| | |] t|[||] t1 t2|[|] ts]. Qed.

Lemma Ngnf_Nginv pt : negb (is_gnon_free pt) → negb (is_ginv pt).
Proof. by case: pt => [o|[k| | |] t|[||] t1 t2|[|] ts]. Qed.

Lemma Ngnf_Nexp pt : negb (is_gnon_free pt) → negb (is_exp pt).
Proof. by case: pt => [o|[k| | |] t|[||] t1 t2|[|] ts]. Qed.

Lemma Ngnf_Ngmul pt : negb (is_gnon_free pt) → negb (is_gmul pt).
Proof. by case: pt => [o|[k| | |] t|[||] t1 t2|[|] ts]. Qed.

Definition base pt := if pt is PTExp b _ then b else pt.
Definition expo pt := if pt is PTExp _ e then e else PTMul [].
Definition factors pt := if pt is PTMul ts then ts else [pt].
Definition gfactors pt := if pt is PTGMul ts then ts else [pt].

(** We now define smart constructors for all the operations that validate
    non-trivial equations.  The exponent structure ([inv], [mul]) and the group
    structure ([ginv], [gmul]) are the same construction at different
    operations; [SMS] is parameterised by its involution, so both reuse it.

    - [inv_aux] computes the inverse of terms that do not begin with [PTMul] by
      simply adding or removing a [PTInv]; [ginv_aux] is the same for [PTGInv].

    - [mul] computes the product of a list of terms. It flattens inner terms
      that begin with [PTMul] (so that multiplication is associative) and then
      cancels out multiplicative inverses by using [inv_aux].  The remaining
      factors are sorted with [merge_sort] to obtain a canonical form.  [gmul]
      is the same for the group.

    - [inv] / [ginv] compute the inverse of arbitrary terms by distributivity.

    - [mk_exp] builds an exponential, collapsing [g ^ 1] to [g].

    - [exp_aux] exponentiates terms that do not begin with [PTGMul].  It merges
      the exponents of an iterated exponentiation using the *scalar* [mul], and
      pushes through a leading [PTGInv]: exponentiation distributes over group
      inverses as well as group products, since [(a * a^-1) ^ x = 1] forces
      [(a^-1) ^ x = (a ^ x)^-1].

    - [exp] exponentiates arbitrary terms by distributivity, spreading
      [exp_aux] over the group factors.  No case analysis is needed:
      [gfactors] already returns [ts] on [PTGMul ts] and the singleton [[b]]
      otherwise, and [gmul] collapses that singleton back (see [exp_Ngmul]). *)

Definition inv_aux pt :=
  match pt with
  | PTInv t => t
  | _ => PTInv pt
  end.

Definition ginv_aux pt :=
  match pt with
  | PTGInv t => t
  | _ => PTGInv pt
  end.

Definition mul_aux ts :=
  match ts with
  | [t] => t
  | _ => PTMul ts
  end.

Definition gmul_aux ts :=
  match ts with
  | [t] => t
  | _ => PTGMul ts
  end.

Definition normalize_factors ts :=
  SMS.to pt_order inv_aux (mbind factors ts).

Definition normalize_gfactors ts :=
  SMS.to pt_order ginv_aux (mbind gfactors ts).

Definition mul ts := mul_aux (normalize_factors ts).

Definition gmul ts := gmul_aux (normalize_gfactors ts).

Definition inv pt :=
  if pt is PTMul ts then mul (inv_aux <$> ts) else inv_aux pt.

Definition ginv pt :=
  if pt is PTGMul ts then gmul (ginv_aux <$> ts) else ginv_aux pt.

Definition mk_exp b e :=
  if bool_decide (e = PTMul []) then b else PTExp b e.

Definition exp_aux b e :=
  if b is PTGInv t then ginv_aux (mk_exp (base t) (mul [expo t; e]))
  else mk_exp (base b) (mul [expo b; e]).

Definition exp b e := gmul ((λ t, exp_aux t e) <$> gfactors b).

Fixpoint normalize pt :=
  match pt with
  | PT0 o => PT0 o
  | PTInv t => inv (normalize t)
  | PTGInv t => ginv (normalize t)
  | PT1 o t => PT1 o (normalize t)
  | PTExp b e => exp (normalize b) (normalize e)
  | PT2 o t1 t2 => PT2 o (normalize t1) (normalize t2)
  | PTMul ts => mul (normalize <$> ts)
  | PTGMul ts => gmul (normalize <$> ts)
  end.

Fixpoint wf (pt : pre_term) : bool :=
  match pt with
  | PT0 _ => true
  | PTInv pt => negb (is_inv pt) && negb (is_mul pt) && wf pt
  | PTGInv pt => negb (is_ginv pt) && negb (is_gmul pt) && wf pt
  | PT1 _ pt => wf pt
  | PTExp b e =>
    wf b && negb (is_gnon_free b) && wf e && bool_decide (e ≠ PTMul [])
  | PT2 _ pt1 pt2 => wf pt1 && wf pt2
  | PTMul ts =>
    (forallb (λ t, wf t && negb (is_mul t)) ts
     && SMS.wf pt_order inv_aux ts)
    && bool_decide (length ts ≠ 1)
  | PTGMul ts =>
    (forallb (λ t, wf t && negb (is_gmul t)) ts
     && SMS.wf pt_order ginv_aux ts)
    && bool_decide (length ts ≠ 1)
  end.

Definition wf_factors ts :=
  forallb (λ t, wf t && negb (is_mul t)) ts
  && SMS.wf pt_order inv_aux ts.

Definition wf_gfactors ts :=
  forallb (λ t, wf t && negb (is_gmul t)) ts
  && SMS.wf pt_order ginv_aux ts.

Lemma wf_factors_wf t ts : wf_factors ts → t ∈ ts → wf t.
Proof.
move=> /andb_True [/forallb_True/list.Forall_forall wf_ts _] t_ts.
by case/andb_True: (wf_ts _ t_ts).
Qed.

Lemma wf_gfactors_wf t ts : wf_gfactors ts → t ∈ ts → wf t.
Proof.
move=> /andb_True [/forallb_True/list.Forall_forall wf_ts _] t_ts.
by case/andb_True: (wf_ts _ t_ts).
Qed.

Lemma wf_factors_Nmul t ts : wf_factors ts → t ∈ ts → negb (is_mul t).
move=> /andb_True [/forallb_True/list.Forall_forall wf_ts _] t_ts.
by case/andb_True: (wf_ts _ t_ts).
Qed.

Lemma wf_gfactors_Ngmul t ts : wf_gfactors ts → t ∈ ts → negb (is_gmul t).
Proof.
move=> /andb_True [/forallb_True/list.Forall_forall wf_ts _] t_ts.
by case/andb_True: (wf_ts _ t_ts).
Qed.

Lemma wf_gfactors_sms ts : wf_gfactors ts → SMS.wf pt_order ginv_aux ts.
Proof. by case/andb_True. Qed.

Lemma wf_factors_sms ts : wf_factors ts → SMS.wf pt_order inv_aux ts.
Proof. by case/andb_True. Qed.

Lemma inv_aux_Nid pt : inv_aux pt ≠ pt.
Proof.
by case: pt => [o|[k| | |] t|o t1 t2|[|] ts] /=; move=> /(f_equal height) /=; lia.
Qed.

Lemma ginv_aux_Nid pt : ginv_aux pt ≠ pt.
Proof.
by case: pt => [o|[k| | |] t|o t1 t2|[|] ts] /=; move=> /(f_equal height) /=; lia.
Qed.

Lemma ginv_invN pt : negb (is_ginv pt) -> ginv_aux pt = PTGInv pt.
Proof. by case: pt => [o|[k| | |] t|o t1 t2|[|] ts]. Qed.

Lemma inv_invN pt : negb (is_inv pt) -> inv_aux pt = PTInv pt.
Proof. by case: pt => [o|[k| | |] t|o t1 t2|[|] ts]. Qed.

Lemma inv_auxK pt : wf pt -> inv_aux (inv_aux pt) = pt.
Proof.
case: pt => [o|[k| | |] t|o t1 t2|[|] ts] //=.
by rewrite !andb_True => - [[/inv_invN -> _] _].
Qed.

Lemma ginv_auxK pt : wf pt -> ginv_aux (ginv_aux pt) = pt.
Proof.
case: pt => [o|[k| | |] t|o t1 t2|[|] ts] //=.
by rewrite !andb_True => - [[/ginv_invN -> _] _].
Qed.

Lemma wf_one : wf (PTMul []).
Proof. by rewrite /wf !andb_True; split_and!. Qed.

Lemma wf_gone : wf (PTGMul []).
Proof. by rewrite /wf !andb_True; split_and!. Qed.

Lemma wf_base pt : wf pt -> wf (base pt).
Proof.
case: pt => [o|o t|[||] b e|[|] ts] wf_pt //.
by move: wf_pt; rewrite /= !andb_True => - [[[? _] _] _].
Qed.

Lemma base_expN pt : negb (is_exp pt) -> base pt = pt.
Proof. by case: pt => [o|o t|[||] t1 t2|[|] ts]. Qed.

Lemma base_Nexp pt : wf pt -> negb (is_exp (base pt)).
Proof.
case: pt => [o|o t|[||] b e|[|] ts] wf_pt //=.
by move: wf_pt; rewrite /= !andb_True => - [[[_ /Ngnf_Nexp ?] _] _].
Qed.

(* [base] does not change the [is_gmul] / [is_ginv] head: for a non-exponential
   [base pt = pt], and for an exponential both sides are [false], since [wf]
   makes the base a *group* atom.  ([is_exp] is not like this: [is_exp (base
   pt)] is always false -- see [base_Nexp].)

   There is deliberately no scalar counterpart: [wf (PTExp (PTMul ts) e)] holds,
   so [is_mul (base pt) = is_mul pt] is false.  A scalar product in a base is an
   atom that [exp] does not distribute over. *)
Lemma is_gmul_base pt : wf pt -> is_gmul (base pt) = is_gmul pt.
Proof.
case: pt => [o|o t|[||] b e|[|] ts] //= wf_pt.
move: wf_pt; rewrite !andb_True => - [[[_ Nnf] _] _].
by case: (is_gmul b) (Ngnf_Ngmul _ Nnf).
Qed.

Lemma is_ginv_base pt : wf pt -> is_ginv (base pt) = is_ginv pt.
Proof.
case: pt => [o|o t|[||] b e|[|] ts] //= wf_pt.
move: wf_pt; rewrite !andb_True => - [[[_ Nnf] _] _].
by case: (is_ginv b) (Ngnf_Nginv _ Nnf).
Qed.

Lemma expo_expN pt : negb (is_exp pt) -> expo pt = PTMul [].
Proof. by case: pt => [o|o t|[||] t1 t2|[|] ts]. Qed.

Lemma wf_expo pt : wf pt -> wf (expo pt).
Proof.
case: pt => [o|o t|[||] b e|[|] ts]; try (move=> _; exact: wf_one).
by move=> wf_pt; move: wf_pt; rewrite /= !andb_True => - [[[_ _] ?] _].
Qed.

Lemma factors_Nmul pt : negb (is_mul pt) -> factors pt = [pt].
Proof. by case: pt => [o|o t|o t1 t2|[|] ts]. Qed.

Lemma gfactors_Ngmul pt : negb (is_gmul pt) -> gfactors pt = [pt].
Proof. by case: pt => [o|o t|o t1 t2|[|] ts]. Qed.

Lemma wf_wf_gfactors pt : wf pt -> wf_gfactors (gfactors pt).
Proof.
case E: (is_gmul pt) => wf_pt.
  by case: pt E wf_pt => [o|o t|o t1 t2|[|] ts] //= _ /andb_True [].
rewrite /wf_gfactors gfactors_Ngmul //= ?E //= 3!andb_True; do !split => //.
apply: SMS.wf_singleton.
- exact: ginv_aux_Nid.
- by rewrite ginv_auxK.
Qed.

Lemma wf_wf_factors pt : wf pt -> wf_factors (factors pt).
Proof.
case E: (is_mul pt) => wf_pt.
  by case: pt E wf_pt => [o|o t|o t1 t2|[|] ts] //= _ /andb_True [].
rewrite /wf_factors factors_Nmul //= ?E //= 3!andb_True; do !split => //.
apply: SMS.wf_singleton.
- exact: inv_aux_Nid.
- by rewrite inv_auxK.
Qed.

Lemma wf_inv_aux pt : wf pt -> negb (is_mul pt) -> wf (inv_aux pt).
Proof.
case: pt => [o|[k| | |] t|o t1 t2|[|] ts] wf_pt Nm //=.
by move: wf_pt; rewrite /= !andb_True => - [[_ _] ?].
Qed.

Lemma wf_ginv_aux pt : wf pt -> negb (is_gmul pt) -> wf (ginv_aux pt).
Proof.
case: pt => [o|[k| | |] t|o t1 t2|[|] ts] wf_pt Nm //=.
by move: wf_pt; rewrite /= !andb_True => - [[_ _] ?].
Qed.

Lemma inv_Nmul pt : negb (is_mul pt) -> inv pt = inv_aux pt.
Proof. by case: pt => [o|o t|o t1 t2|[|] ts]. Qed.

Lemma ginv_Ngmul pt : negb (is_gmul pt) -> ginv pt = ginv_aux pt.
Proof. by case: pt => [o|o t|o t1 t2|[|] ts]. Qed.

Lemma wf_mul_aux ts : wf_factors ts → wf (mul_aux ts).
Proof.
case: (decide (length ts = 1)) => E.
  case: ts => [//|t [|//]] in E *.
  move=> /wf_factors_wf wf_t /=; apply: wf_t; exact/list_elem_of_singleton.
have ->: mul_aux ts = PTMul ts by case: ts => [|?[|??]] in E *.
move=> wf_ts; apply/andb_True; split => //.
exact/bool_decide_spec.
Qed.

Lemma wf_gmul_aux ts : wf_gfactors ts → wf (gmul_aux ts).
Proof.
case: (decide (length ts = 1)) => E.
  case: ts => [//|t [|//]] in E *.
  move=> /wf_gfactors_wf wf_t /=; apply: wf_t; exact/list_elem_of_singleton.
have ->: gmul_aux ts = PTGMul ts by case: ts => [|?[|??]] in E *.
move=> wf_ts; apply/andb_True; split => //.
exact/bool_decide_spec.
Qed.

Lemma wf_normalize_gfactors ts :
  Forall wf ts → wf_gfactors (normalize_gfactors ts).
Proof.
move=> wf_ts; rewrite /normalize_gfactors /wf_gfactors andb_True.
set ts1 := mbind gfactors ts.
set ts2 := SMS.to pt_order ginv_aux ts1.
have wf_ts1: Forall (λ t, wf t && negb (is_gmul t)) ts1.
  rewrite Forall_bind; apply: Forall_impl wf_ts => t /wf_wf_gfactors wf_t.
  apply/list.Forall_forall=> t' t'_t; apply/andb_True; split.
  - by apply: wf_gfactors_wf; eauto.
  - by apply: wf_gfactors_Ngmul; eauto.
split.
- apply/forallb_True/list.Forall_forall=> t /(SMS.mem_to _ _ _).
  move/list.Forall_forall: wf_ts1; exact.
- apply: SMS.wf_to => t t_ts1; apply: ginv_auxK.
  by case/list.Forall_forall/(_ _ t_ts1)/andb_True: wf_ts1.
Qed.

Lemma wf_gmul ts : Forall wf ts -> wf (gmul ts).
Proof.
move=> wf_ts; rewrite /gmul.
apply: wf_gmul_aux; exact: wf_normalize_gfactors.
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
case: t => [o|o t|o t1 t2|[|] ts] //= wf_t.
case/andb_True: wf_t=> _ Hlen.
by case: ts Hlen => [|t [|t' c']].
Qed.

Lemma normalize_gfactors1 t : wf t → normalize_gfactors [t] = gfactors t.
Proof.
move=> wf_t; rewrite /normalize_gfactors /= app_nil_r.
rewrite (SMS.to_id pt_order ginv_aux (gfactors t)) //.
apply: wf_gfactors_sms; exact: wf_wf_gfactors.
Qed.

Lemma gfactorsK t : wf t → gmul_aux (gfactors t) = t.
Proof.
case: t => [o|o t|o t1 t2|[|] ts] //= wf_t.
case/andb_True: wf_t=> _ Hlen.
by case: ts Hlen => [|t [|t' c']].
Qed.

Lemma gmul_auxK ts : wf_gfactors ts → gfactors (gmul_aux ts) = ts.
Proof.
case: ts => [| t [| ??]] //= wf_t; rewrite gfactors_Ngmul //.
apply: wf_gfactors_Ngmul; eauto; exact/list_elem_of_singleton.
Qed.

Lemma gmul1 t : wf t -> gmul [t] = t.
Proof.
by move=> wf_t; rewrite /gmul normalize_gfactors1 // gfactorsK.
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

Lemma wf_mk_exp b e :
  negb (is_gnon_free b) →
  wf b →
  wf e →
  wf (mk_exp b e).
Proof.
move=> bNnf wf_b wf_e; rewrite /mk_exp; case_bool_decide as Hf => //=.
rewrite !andb_True bool_decide_spec; eauto.
Qed.

(* [base t] is a group atom as soon as [t] is well formed and is neither a group
   product nor a group inverse: either [t] is an exponential, and [wf] says so
   directly, or [base t = t].  Both exclusions are needed — [base (PTGInv u) =
   PTGInv u]. *)
Lemma base_Ngnf t :
  wf t -> negb (is_gmul t) -> negb (is_ginv t) -> negb (is_gnon_free (base t)).
Proof.
case: t => [o|[k| | |] t|[||] t1 t2|[|] ts] //= wf_t Nm Ni.
by move: wf_t; rewrite !andb_True => - [[[_ ?] _] _].
Qed.

Lemma exp_aux_Nginv b e :
  negb (is_ginv b) -> exp_aux b e = mk_exp (base b) (mul [expo b; e]).
Proof. by case: b => [o|[k| | |] t|[||] t1 t2|[|] ts]. Qed.

(* Each mapped exponentiation is well formed, so the [mul] in [exp] always
   receives a legal factor list. *)
Lemma wf_exp_aux t e : wf t -> negb (is_gmul t) -> wf e -> wf (exp_aux t e).
Proof.
move=> wf_t Nm wf_e.
have wf_mul_e u : wf u -> wf (mul [expo u; e]).
  move=> wf_u; apply: wf_mul.
  by rewrite !list.Forall_cons list.Forall_nil; eauto using wf_expo.
have main u : wf u -> negb (is_gmul u) -> negb (is_ginv u) ->
              wf (mk_exp (base u) (mul [expo u; e])).
  move=> wf_u Nm_u Ni_u.
  by apply: wf_mk_exp; [apply: base_Ngnf|apply: wf_base|apply: wf_mul_e].
case Ei: (is_ginv t); last first.
  have Ni : negb (is_ginv t) by rewrite Ei.
  by rewrite exp_aux_Nginv //; apply: main.
(* [t = PTGInv u]: exponentiate [u], then re-apply the group inverse. *)
case: t Ei wf_t Nm => [o|[k| | |] u|o t1 t2|[|] ts] // _ /=.
rewrite !andb_True => - [[Ni Nm] wf_u] _.
apply: wf_ginv_aux; last first.
  rewrite /mk_exp; case_bool_decide => //=.
  exact: (Ngnf_Ngmul _ (base_Ngnf _ wf_u Nm Ni)).
by apply: main.
Qed.

Lemma wf_exp b e : wf b -> wf e -> wf (exp b e).
Proof.
move=> wf_b wf_e; rewrite /exp; apply: wf_gmul.
apply/Forall_fmap/list.Forall_forall => t t_b.
have wf_fs := wf_wf_gfactors _ wf_b.
by apply: wf_exp_aux => //;
  [exact: wf_gfactors_wf t_b | exact: wf_gfactors_Ngmul t_b].
Qed.

(* On a non-group-product base the [gmul] of [exp] collapses, so [exp] agrees
   with [exp_aux].  Unlike [ginv_Ngmul], this needs well-formedness: the
   collapse goes through [gmul1]. *)
Lemma exp_Ngmul b e : wf b -> wf e -> negb (is_gmul b) -> exp b e = exp_aux b e.
Proof.
move=> wf_b wf_e Nm; rewrite /exp gfactors_Ngmul //= gmul1 //.
exact: wf_exp_aux.
Qed.

Lemma mul_unit_r t : wf t -> mul [t; PTMul []] = t.
Proof.
move=> wf_t.
rewrite -{2}(mul1 _ wf_t) /mul /normalize_factors /=.
by rewrite !app_nil_r.
Qed.

Lemma mk_exp_base_expo t : wf t -> mk_exp (base t) (expo t) = t.
Proof.
case: t => [o|o u|[||] c d|[|] ts] /= wf_t; rewrite /mk_exp;
  try by rewrite bool_decide_eq_true_2.
move: wf_t; rewrite !andb_True => - [_ /bool_decide_unpack dN0].
by rewrite bool_decide_eq_false_2.
Qed.

Lemma exp_aux_unit t : wf t -> negb (is_gmul t) -> exp_aux t (PTMul []) = t.
Proof.
move=> wf_t Nm.
case Ei: (is_ginv t).
  case: t Ei wf_t Nm => [o|[k| | |] u|o c d|[|] ts] // _ /=.
  rewrite !andb_True => - [[Ni Nm_u] wf_u] _.
  by rewrite (mul_unit_r _ (wf_expo _ wf_u)) (mk_exp_base_expo _ wf_u) (ginv_invN _ Ni).
have Ni : negb (is_ginv t) by rewrite Ei.
rewrite (exp_aux_Nginv _ _ Ni) (mul_unit_r _ (wf_expo _ wf_t)).
exact: mk_exp_base_expo.
Qed.

Lemma wf_inv t : wf t -> wf (inv t).
Proof.
move=> wf_t; case e: (is_mul t); last first.
  by rewrite inv_Nmul ?e //; apply: wf_inv_aux; rewrite // e.
case: t wf_t e => [o|o u|o c d|[|] ts] //= wf_t e.
case/andb_True: wf_t => wf_ts tsN1.
apply: wf_mul; apply/list.Forall_forall=> _ /list_elem_of_fmap [t [] -> t_ts].
apply: wf_inv_aux.
- exact: wf_factors_wf t_ts.
- exact: wf_factors_Nmul t_ts.
Qed.

Lemma wf_ginv t : wf t -> wf (ginv t).
Proof.
move=> wf_t; case e: (is_gmul t); last first.
  by rewrite ginv_Ngmul ?e //; apply: wf_ginv_aux; rewrite // e.
case: t wf_t e => [o|o u|o c d|[|] ts] //= wf_t e.
case/andb_True: wf_t => wf_ts tsN1.
apply: wf_gmul; apply/list.Forall_forall=> _ /list_elem_of_fmap [t [] -> t_ts].
apply: wf_ginv_aux.
- exact: wf_gfactors_wf t_ts.
- exact: wf_gfactors_Ngmul t_ts.
Qed.

Lemma wf_normalize pt : wf (normalize pt).
Proof.
elim: pt => //=.
- move=> [k| | |] t IH /=;
    [exact: IH | exact: IH | exact: (wf_inv _ IH) | exact: (wf_ginv _ IH)].
- move=> o t1 IH1 t2 IH2; case: o => /=;
    [by rewrite andb_True; split
    |by rewrite andb_True; split
    |exact: (wf_exp _ _ IH1 IH2)].
- move=> [|] ts IHts.
  + apply: wf_mul; apply/Forall_fmap.
    elim: ts IHts => [|t ts' IH] /=;
      [by move=> _; constructor
      |by move=> [wt wts]; constructor; [exact: wt | exact: IH wts]].
  + apply: wf_gmul; apply/Forall_fmap.
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

Lemma normalize_gfactors_wf_gfactors ts :
  wf_gfactors ts → normalize_gfactors ts = ts.
Proof.
move=> wf_ts; rewrite /normalize_gfactors.
have ->: mbind gfactors ts = ts.
  case/andb_True: wf_ts=> wf_ts _.
  elim: ts wf_ts => //= t ts IH.
  case/andb_True=> [/andb_True [wf_t Nm_t] /IH E].
  by rewrite gfactors_Ngmul //= -[in RHS]E.
rewrite SMS.to_id //; exact: wf_gfactors_sms.
Qed.

Lemma normalize_wf pt : wf pt -> normalize pt = pt.
Proof.
elim: pt => //=.
- move=> [k| | |] t IH /=.
  + by move=> wf; rewrite (IH wf).
  + by move=> wf; rewrite (IH wf).
  + by rewrite !andb_True => - [[ni nm] wf];
      rewrite (IH wf) (inv_Nmul _ nm) (inv_invN _ ni).
  + by rewrite !andb_True => - [[ni nm] wf];
      rewrite (IH wf) (ginv_Ngmul _ nm) (ginv_invN _ ni).
- move=> o t1 IH1 t2 IH2; case: o => /=.
  + by rewrite andb_True => - [/IH1 -> /IH2 ->].
  + by rewrite andb_True => - [/IH1 -> /IH2 ->].
  + rewrite !andb_True => - [[[wfb Nnfb] wfe] /bool_decide_unpack eN0].
    rewrite IH1 // IH2 // exp_Ngmul //; last exact: Ngnf_Ngmul.
    rewrite exp_aux_Nginv; last exact: Ngnf_Nginv.
    rewrite base_expN; last exact: Ngnf_Nexp.
    rewrite expo_expN; last exact: Ngnf_Nexp.
    by rewrite mul_unit_l mul1 // /mk_exp bool_decide_eq_false_2.
- move=> [|] ts IHts /andb_True [wf_ts /bool_decide_spec tsN1].
  + have {}IHts: Forall (λ t, wf t → normalize t = t) ts.
      by elim: (ts) IHts => //= t' ts' IH [? /IH ?]; eauto.
    have {IHts} ->: normalize <$> ts = ts.
      rewrite -[RHS]list_fmap_id; apply/Forall_fmap_ext.
      apply/list.Forall_forall => t t_ts.
      move/list.Forall_forall: IHts; apply => //.
      exact: wf_factors_wf t_ts.
    rewrite /mul normalize_factors_wf_factors //.
    by case: (ts) tsN1 => [|? [|??]].
  + have {}IHts: Forall (λ t, wf t → normalize t = t) ts.
      by elim: (ts) IHts => //= t' ts' IH [? /IH ?]; eauto.
    have {IHts} ->: normalize <$> ts = ts.
      rewrite -[RHS]list_fmap_id; apply/Forall_fmap_ext.
      apply/list.Forall_forall => t t_ts.
      move/list.Forall_forall: IHts; apply => //.
      exact: wf_gfactors_wf t_ts.
    rewrite /gmul normalize_gfactors_wf_gfactors //.
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

(* [g ^ 1 = g].  Every factor is fixed by [exp_aux _ 1], so the product is
   rebuilt unchanged.  Only [exp_base_expo] needs this; the term layer derives
   [TExp_unit] from [TExpA] instead. *)
Lemma exp_unit b : wf b -> exp b (PTMul []) = b.
Proof.
move=> wf_b; rewrite /exp.
have wf_fs := wf_wf_gfactors _ wf_b.
have -> : (λ t, exp_aux t (PTMul [])) <$> gfactors b = gfactors b.
  rewrite -[RHS]list_fmap_id; apply/Forall_fmap_ext/list.Forall_forall.
  move=> t t_b; apply: exp_aux_unit;
    [exact: wf_gfactors_wf t_b|exact: wf_gfactors_Ngmul t_b].
rewrite /gmul normalize_gfactors_wf_gfactors //.
exact: gfactorsK.
Qed.

Lemma exp_base_expo b : wf b -> exp (base b) (expo b) = b.
Proof.
move=> wf_b; case Ex: (is_exp b).
  case: b Ex wf_b => [o|o u|[||] c d|[|] ts] // _ /=.
  rewrite !andb_True => - [[[wf_c Nnf_c] wf_d] /bool_decide_unpack dN0].
  rewrite (exp_Ngmul _ _ wf_c wf_d (Ngnf_Ngmul _ Nnf_c)).
  rewrite (exp_aux_Nginv _ _ (Ngnf_Nginv _ Nnf_c)).
  rewrite (base_expN _ (Ngnf_Nexp _ Nnf_c)) (expo_expN _ (Ngnf_Nexp _ Nnf_c)).
  by rewrite mul_unit_l (mul1 _ wf_d) /mk_exp bool_decide_eq_false_2.
have Nx : negb (is_exp b) by rewrite Ex.
by rewrite (base_expN _ Nx) (expo_expN _ Nx) exp_unit.
Qed.

(* The destructors see through [exp] only when the base is neither a group
   product nor a group inverse — otherwise [exp] distributes and the result is
   not an exponential at all. *)
Lemma base_exp b e :
  wf b -> wf e -> negb (is_gmul b) -> negb (is_ginv b) ->
  base (exp b e) = base b.
Proof.
move=> wf_b wf_e Nm Ni.
rewrite (exp_Ngmul _ _ wf_b wf_e Nm) (exp_aux_Nginv _ _ Ni) /mk_exp.
case_bool_decide => //=.
exact: (base_expN _ (base_Nexp _ wf_b)).
Qed.

Lemma expo_exp b e :
  wf b -> wf e -> negb (is_gmul b) -> negb (is_ginv b) ->
  expo (exp b e) = mul [expo b; e].
Proof.
move=> wf_b wf_e Nm Ni.
rewrite (exp_Ngmul _ _ wf_b wf_e Nm) (exp_aux_Nginv _ _ Ni) /mk_exp.
case_bool_decide as H => //=.
by rewrite H (expo_expN _ (base_Nexp _ wf_b)).
Qed.

(* [_ ^ e] conjugates the group involution: this is [(a^-1) ^ x = (a ^ x)^-1] at
   the level of [exp_aux], and it is what makes [exp] commute with the
   cancellation inside [gmul]. *)
Lemma exp_aux_ginv_aux u e :
  wf u -> negb (is_gmul u) -> wf e ->
  exp_aux (ginv_aux u) e = ginv_aux (exp_aux u e).
Proof.
move=> wf_u Nm wf_e.
case Ei: (is_ginv u); last first.
  have Ni : negb (is_ginv u) by rewrite Ei.
  by rewrite (ginv_invN _ Ni) /= (exp_aux_Nginv _ _ Ni).
case: u Ei wf_u Nm => [o|[k| | |] v|o c d|[|] ts] // _ /=.
rewrite !andb_True => - [[Ni Nm_v] wf_v] _.
rewrite (exp_aux_Nginv _ _ Ni) ginv_auxK //.
apply: wf_mk_exp.
- exact: (base_Ngnf _ wf_v Nm_v Ni).
- exact: wf_base.
- apply: wf_mul; rewrite !list.Forall_cons list.Forall_nil.
  by split; [exact: wf_expo|].
Qed.

(* [exp] preserves "neither a group product nor a group inverse", so iterated
   exponentiation stays in the range where [base_exp]/[expo_exp] apply. *)
Lemma Ngmul_mk_exp X Y : negb (is_gmul X) -> negb (is_gmul (mk_exp X Y)).
Proof. by rewrite /mk_exp; case_bool_decide. Qed.

Lemma Nginv_mk_exp X Y : negb (is_ginv X) -> negb (is_ginv (mk_exp X Y)).
Proof. by rewrite /mk_exp; case_bool_decide. Qed.

(* The images of [exp_aux _ e] are never group products, so [mbind gfactors] is
   the identity on a mapped factor list and [gmul] sees the images directly. *)
Lemma exp_aux_Ngmul t e :
  wf t -> negb (is_gmul t) -> wf e -> negb (is_gmul (exp_aux t e)).
Proof.
move=> wf_t Nm wf_e.
case Ei: (is_ginv t); last first.
  have Ni : negb (is_ginv t) by rewrite Ei.
  rewrite (exp_aux_Nginv _ _ Ni); apply: Ngmul_mk_exp.
  exact: (Ngnf_Ngmul _ (base_Ngnf _ wf_t Nm Ni)).
case: t Ei wf_t Nm => [o|[k| | |] u|o c d|[|] ts] // _ /=.
rewrite !andb_True => - [[Ni Nm_u] wf_u] _.
have NnfB := base_Ngnf _ wf_u Nm_u Ni.
rewrite /mk_exp; case_bool_decide => /=.
- by rewrite (ginv_invN _ (Ngnf_Nginv _ NnfB)).
- by [].
Qed.

(* [(a^-1) ^ x = (a ^ x)^-1] at the level of [exp]/[ginv].  This is the form the
   term layer conjugates; [exp_aux_ginv_aux] is the [exp_aux]-level version it
   is proved from. *)
Lemma exp_ginv t e :
  wf t -> negb (is_gmul t) -> wf e -> exp (ginv t) e = ginv (exp t e).
Proof.
move=> wft Nm wfe.
have NmI : negb (is_gmul (ginv_aux t)).
  move: wft Nm; case: t => [o|[k| | |] u|o c d|[|] us] //=.
  by rewrite !andb_True => - [[_ ?] _].
rewrite (ginv_Ngmul _ Nm) (exp_Ngmul _ _ (wf_ginv_aux _ wft Nm) wfe NmI).
rewrite (exp_aux_ginv_aux _ _ wft Nm wfe) (exp_Ngmul _ _ wft wfe Nm).
by rewrite (ginv_Ngmul _ (exp_aux_Ngmul _ _ wft Nm wfe)).
Qed.

Lemma mbind_factors_Nmul ts :
  Forall (λ t, negb (is_mul t)) ts -> mbind factors ts = ts.
Proof.
elim: ts => [//|t ts IH]; rewrite list.Forall_cons => - [Nm NmL].
by rewrite bind_cons (factors_Nmul _ Nm) (IH NmL).
Qed.

Lemma mbind_gfactors_Ngmul ts :
  Forall (λ t, negb (is_gmul t)) ts -> mbind gfactors ts = ts.
Proof.
elim: ts => [//|t ts IH]; rewrite list.Forall_cons => - [Nm NmL].
by rewrite bind_cons (gfactors_Ngmul _ Nm) (IH NmL).
Qed.

(* [to] does not disturb a mapped list's signed counts, because [exp_aux _ e]
   conjugates [ginv_aux] ([exp_aux_ginv_aux]).  This is [SMS.count_fmap_to] at
   the pre-term instance. *)
Lemma to_fmap_exp_aux ts e :
  Forall wf ts -> Forall (λ t, negb (is_gmul t)) ts -> wf e ->
  SMS.to pt_order ginv_aux ((λ t, exp_aux t e) <$> SMS.to pt_order ginv_aux ts)
  = SMS.to pt_order ginv_aux ((λ t, exp_aux t e) <$> ts).
Proof.
move=> /list.Forall_forall wf_ts /list.Forall_forall Nm_ts wf_e.
have wff : forall t, t ∈ ts -> wf (exp_aux t e).
  by move=> t t_ts; apply: wf_exp_aux; auto.
have jKf : forall t, t ∈ ts -> ginv_aux (ginv_aux (exp_aux t e)) = exp_aux t e.
  by move=> t t_ts; apply: ginv_auxK; exact: wff.
have fij : forall t, t ∈ ts -> exp_aux (ginv_aux t) e = ginv_aux (exp_aux t e).
  by move=> t t_ts; apply: exp_aux_ginv_aux; auto.
have h : forall X : list pre_term, (forall t, t ∈ X -> t ∈ ts) ->
         forall x, x ∈ ((λ t, exp_aux t e) <$> X) -> ginv_aux (ginv_aux x) = x.
  by move=> X sub x /list_elem_of_fmap [t [-> t_X]]; exact: (jKf _ (sub _ t_X)).
apply/(SMS.to_eq pt_order ginv_aux _ _
        (h _ (fun t t_in => SMS.mem_to _ _ _ _ t_in)) (h _ (fun t t_in => t_in))).
move=> z jKz.
exact: (SMS.count_fmap_to pt_order ginv_aux ginv_aux
          (λ t, exp_aux t e) z ts jKz jKf fij).
Qed.

(* Distributivity, on a list of group atoms:
   [(t1 * … * tn) ^ e = t1^e * … * tn^e]. *)
Lemma exp_gmul ts e :
  Forall wf ts -> Forall (λ t, negb (is_gmul t)) ts -> wf e ->
  exp (gmul ts) e = gmul ((λ t, exp_aux t e) <$> ts).
Proof.
move=> wf_ts Nm_ts wf_e.
have Nmf : Forall (λ t, negb (is_gmul t)) ((λ t, exp_aux t e) <$> ts).
  apply/Forall_fmap/list.Forall_forall => t t_ts.
  apply: exp_aux_Ngmul => //; by [move/list.Forall_forall: wf_ts; apply
                                |move/list.Forall_forall: Nm_ts; apply].
rewrite /exp /gmul !gmul_auxK; first last.
- exact: wf_normalize_gfactors.
congr gmul_aux; rewrite /normalize_gfactors (mbind_gfactors_Ngmul _ Nm_ts).
have Nmf' : Forall (λ t, negb (is_gmul t))
              ((λ t, exp_aux t e) <$> SMS.to pt_order ginv_aux ts).
  apply/Forall_fmap/list.Forall_forall => t /(SMS.mem_to _ _ _ _) t_ts.
  apply: exp_aux_Ngmul => //; by [move/list.Forall_forall: wf_ts; apply
                                |move/list.Forall_forall: Nm_ts; apply].
rewrite (mbind_gfactors_Ngmul _ Nmf') (mbind_gfactors_Ngmul _ Nmf).
exact: to_fmap_exp_aux.
Qed.

Lemma Ngmul_exp b e :
  wf b -> wf e -> negb (is_gmul b) -> negb (is_gmul (exp b e)).
Proof.
move=> wf_b wf_e Nm; rewrite (exp_Ngmul _ _ wf_b wf_e Nm).
exact: exp_aux_Ngmul.
Qed.

Lemma Nginv_exp b e :
  wf b -> wf e -> negb (is_gmul b) -> negb (is_ginv b) ->
  negb (is_ginv (exp b e)).
Proof.
move=> wf_b wf_e Nm Ni.
rewrite (exp_Ngmul _ _ wf_b wf_e Nm) (exp_aux_Nginv _ _ Ni).
by apply: Nginv_mk_exp; exact: (Ngnf_Nginv _ (base_Ngnf _ wf_b Nm Ni)).
Qed.

End PreTerm.
