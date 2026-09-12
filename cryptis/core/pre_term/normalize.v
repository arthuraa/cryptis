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
    - [(a * b) ^ x = a^x * b^x]

    where [1 := TMulN []], [g ^ x := TExp g x] and [a * b := TMulN [a; b]].
    The last equation makes [_ ^ x] an endomorphism of the multiplicative
    group.  From these equations, several other properties follow, such as

    - [a * b = a * c -> b = c]
    - [(a^-1)^-1 = a]
    - [(1^-1) = 1]
    - [(a * b)^-1 = a^-1 * b^-1]
    - [a^-1 * a = 1]
    - [1 * a = a]
    - [(g ^ a) ^ (a^-1) = g]
    - [(g ^ a) ^ b = (g ^ b) ^ a]
    - [1 ^ x = 1]
    - [(a^-1) ^ x = (a ^ x)^-1]

    The last two are why [exp] distributes over [PTInv] as well as [PTMul], and
    why [wf] demands an *atom* — neither product, inverse, nor exponential — in
    the base of an exponential: [(a^-1) ^ x] has normal form [(a ^ x)^-1].

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

(** The three "non-free" operations: inverse, exponentiation and product.  A
    pre-term whose head is none of them is an *atom*.  Atoms are exactly the
    bases allowed in a normal-form exponential, since [exp] distributes over
    both products and inverses. *)
Definition is_non_free pt := is_inv pt || is_exp pt || is_mul pt.

Lemma Nnf_Ninv pt : negb (is_non_free pt) → negb (is_inv pt).
Proof. by case: pt => [o|[k| |] t|[||] t1 t2|ts]. Qed.

Lemma Nnf_Nexp pt : negb (is_non_free pt) → negb (is_exp pt).
Proof. by case: pt => [o|[k| |] t|[||] t1 t2|ts]. Qed.

Lemma Nnf_Nmul pt : negb (is_non_free pt) → negb (is_mul pt).
Proof. by case: pt => [o|[k| |] t|[||] t1 t2|ts]. Qed.

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

    - [mk_exp] builds an exponential, collapsing [g ^ 1] to [g].

    - [exp_aux] exponentiates terms that do not begin with [PTMul].  It merges
      the exponents of an iterated exponentiation using [mul], and pushes
      through a leading [PTInv]: exponentiation distributes over inverses as
      well as products, since [(a * a^-1) ^ x = 1] forces [(a^-1) ^ x =
      (a ^ x)^-1].

    - [exp] exponentiates arbitrary terms by distributivity, spreading
      [exp_aux] over the factors.  No case analysis is needed: [factors]
      already returns [ts] on [PTMul ts] and the singleton [[b]] otherwise, and
      [mul] collapses that singleton back (see [exp_Nmul]). *)

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

Definition mk_exp b e :=
  if bool_decide (e = PTMul []) then b else PTExp b e.

Definition exp_aux b e :=
  if b is PTInv t then inv_aux (mk_exp (base t) (mul [expo t; e]))
  else mk_exp (base b) (mul [expo b; e]).

Definition exp b e := mul ((λ t, exp_aux t e) <$> factors b).

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
    wf b && negb (is_non_free b) && wf e && bool_decide (e ≠ PTMul [])
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
by move: wf_pt; rewrite /= !andb_True => - [[[_ /Nnf_Nexp ?] _] _].
Qed.

(* [base] does not change the [is_mul] / [is_inv] head: for a non-exponential
   [base pt = pt], and for an exponential both sides are [false], since [wf]
   makes the base an atom.  ([is_exp] is not like this: [is_exp (base pt)] is
   always false -- see [base_Nexp].) *)
Lemma is_mul_base pt : wf pt -> is_mul (base pt) = is_mul pt.
Proof.
case: pt => [o|o t|[||] b e|ts] //= wf_pt.
move: wf_pt; rewrite !andb_True => - [[[_ Nnf] _] _].
by case: (is_mul b) (Nnf_Nmul _ Nnf).
Qed.

Lemma is_inv_base pt : wf pt -> is_inv (base pt) = is_inv pt.
Proof.
case: pt => [o|o t|[||] b e|ts] //= wf_pt.
move: wf_pt; rewrite !andb_True => - [[[_ Nnf] _] _].
by case: (is_inv b) (Nnf_Ninv _ Nnf).
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

Lemma wf_mk_exp b e :
  negb (is_non_free b) →
  wf b →
  wf e →
  wf (mk_exp b e).
Proof.
move=> bNnf wf_b wf_e; rewrite /mk_exp; case_bool_decide as Hf => //=.
rewrite !andb_True bool_decide_spec; eauto.
Qed.

(* [base t] is an atom as soon as [t] is well formed and is neither a product
   nor an inverse: either [t] is an exponential, and [wf] says so directly, or
   [base t = t].  Both exclusions are needed — [base (PTInv u) = PTInv u]. *)
Lemma base_Nnf t :
  wf t -> negb (is_mul t) -> negb (is_inv t) -> negb (is_non_free (base t)).
Proof.
case: t => [o|[k| |] t|[||] t1 t2|ts] //= wf_t Nm Ni.
by move: wf_t; rewrite !andb_True => - [[[_ ?] _] _].
Qed.

Lemma exp_aux_Ninv b e :
  negb (is_inv b) -> exp_aux b e = mk_exp (base b) (mul [expo b; e]).
Proof. by case: b => [o|[k| |] t|[||] t1 t2|ts]. Qed.

(* Each mapped exponentiation is well formed, so the [mul] in [exp] always
   receives a legal factor list. *)
Lemma wf_exp_aux t e : wf t -> negb (is_mul t) -> wf e -> wf (exp_aux t e).
Proof.
move=> wf_t Nm wf_e.
have wf_mul_e u : wf u -> wf (mul [expo u; e]).
  move=> wf_u; apply: wf_mul.
  by rewrite !list.Forall_cons list.Forall_nil; eauto using wf_expo.
have main u : wf u -> negb (is_mul u) -> negb (is_inv u) ->
              wf (mk_exp (base u) (mul [expo u; e])).
  move=> wf_u Nm_u Ni_u.
  by apply: wf_mk_exp; [apply: base_Nnf|apply: wf_base|apply: wf_mul_e].
case Ei: (is_inv t); last first.
  have Ni : negb (is_inv t) by rewrite Ei.
  by rewrite exp_aux_Ninv //; apply: main.
(* [t = PTInv u]: exponentiate [u], then re-apply the inverse. *)
case: t Ei wf_t Nm => [o|[k| |] u|o t1 t2|ts] // _ /=.
rewrite !andb_True => - [[Ni Nm] wf_u] _.
apply: wf_inv_aux; last first.
  rewrite /mk_exp; case_bool_decide => //=.
  exact: (Nnf_Nmul _ (base_Nnf _ wf_u Nm Ni)).
by apply: main.
Qed.

Lemma wf_exp b e : wf b -> wf e -> wf (exp b e).
Proof.
move=> wf_b wf_e; rewrite /exp; apply: wf_mul.
apply/Forall_fmap/list.Forall_forall => t t_b.
have wf_fs := wf_wf_factors _ wf_b.
by apply: wf_exp_aux => //;
  [exact: wf_factors_wf t_b | exact: wf_factors_Nmul t_b].
Qed.

(* On a non-product base the [mul] of [exp] collapses, so [exp] agrees with
   [exp_aux].  Unlike [inv_Nmul], this needs well-formedness: the collapse goes
   through [mul1]. *)
Lemma exp_Nmul b e : wf b -> wf e -> negb (is_mul b) -> exp b e = exp_aux b e.
Proof.
move=> wf_b wf_e Nm; rewrite /exp factors_Nmul //= mul1 //.
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
case: t => [o|o u|[||] c d|ts] /= wf_t; rewrite /mk_exp;
  try by rewrite bool_decide_eq_true_2.
move: wf_t; rewrite !andb_True => - [_ /bool_decide_unpack dN0].
by rewrite bool_decide_eq_false_2.
Qed.

Lemma exp_aux_unit t : wf t -> negb (is_mul t) -> exp_aux t (PTMul []) = t.
Proof.
move=> wf_t Nm.
case Ei: (is_inv t).
  case: t Ei wf_t Nm => [o|[k| |] u|o c d|ts] // _ /=.
  rewrite !andb_True => - [[Ni Nm_u] wf_u] _.
  by rewrite (mul_unit_r _ (wf_expo _ wf_u)) (mk_exp_base_expo _ wf_u) (inv_invN _ Ni).
have Ni : negb (is_inv t) by rewrite Ei.
rewrite (exp_aux_Ninv _ _ Ni) (mul_unit_r _ (wf_expo _ wf_t)).
exact: mk_exp_base_expo.
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
  + rewrite !andb_True => - [[[wfb Nnfb] wfe] /bool_decide_unpack eN0].
    rewrite IH1 // IH2 // exp_Nmul //; last exact: Nnf_Nmul.
    rewrite exp_aux_Ninv; last exact: Nnf_Ninv.
    rewrite base_expN; last exact: Nnf_Nexp.
    rewrite expo_expN; last exact: Nnf_Nexp.
    by rewrite mul_unit_l mul1 // /mk_exp bool_decide_eq_false_2.
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

(* [g ^ 1 = g].  Every factor is fixed by [exp_aux _ 1], so the product is
   rebuilt unchanged.  Only [exp_base_expo] needs this; the term layer derives
   [TExp_unit] from [TExpA] instead. *)
Lemma exp_unit b : wf b -> exp b (PTMul []) = b.
Proof.
move=> wf_b; rewrite /exp.
have wf_fs := wf_wf_factors _ wf_b.
have -> : (λ t, exp_aux t (PTMul [])) <$> factors b = factors b.
  rewrite -[RHS]list_fmap_id; apply/Forall_fmap_ext/list.Forall_forall.
  move=> t t_b; apply: exp_aux_unit;
    [exact: wf_factors_wf t_b|exact: wf_factors_Nmul t_b].
rewrite /mul normalize_factors_wf_factors //.
exact: factorsK.
Qed.

Lemma exp_base_expo b : wf b -> exp (base b) (expo b) = b.
Proof.
move=> wf_b; case Ex: (is_exp b).
  case: b Ex wf_b => [o|o u|[||] c d|ts] // _ /=.
  rewrite !andb_True => - [[[wf_c Nnf_c] wf_d] /bool_decide_unpack dN0].
  rewrite (exp_Nmul _ _ wf_c wf_d (Nnf_Nmul _ Nnf_c)).
  rewrite (exp_aux_Ninv _ _ (Nnf_Ninv _ Nnf_c)).
  rewrite (base_expN _ (Nnf_Nexp _ Nnf_c)) (expo_expN _ (Nnf_Nexp _ Nnf_c)).
  by rewrite mul_unit_l (mul1 _ wf_d) /mk_exp bool_decide_eq_false_2.
have Nx : negb (is_exp b) by rewrite Ex.
by rewrite (base_expN _ Nx) (expo_expN _ Nx) exp_unit.
Qed.

(* The destructors see through [exp] only when the base is neither a product
   nor an inverse — otherwise [exp] distributes and the result is not an
   exponential at all. *)
Lemma base_exp b e :
  wf b -> wf e -> negb (is_mul b) -> negb (is_inv b) ->
  base (exp b e) = base b.
Proof.
move=> wf_b wf_e Nm Ni.
rewrite (exp_Nmul _ _ wf_b wf_e Nm) (exp_aux_Ninv _ _ Ni) /mk_exp.
case_bool_decide => //=.
exact: (base_expN _ (base_Nexp _ wf_b)).
Qed.

Lemma expo_exp b e :
  wf b -> wf e -> negb (is_mul b) -> negb (is_inv b) ->
  expo (exp b e) = mul [expo b; e].
Proof.
move=> wf_b wf_e Nm Ni.
rewrite (exp_Nmul _ _ wf_b wf_e Nm) (exp_aux_Ninv _ _ Ni) /mk_exp.
case_bool_decide as H => //=.
by rewrite H (expo_expN _ (base_Nexp _ wf_b)).
Qed.

(* [_ ^ e] conjugates the involution: this is [(a^-1) ^ x = (a ^ x)^-1] at the
   level of [exp_aux], and it is what makes [exp] commute with the cancellation
   inside [mul]. *)
Lemma exp_aux_inv_aux u e :
  wf u -> negb (is_mul u) -> wf e ->
  exp_aux (inv_aux u) e = inv_aux (exp_aux u e).
Proof.
move=> wf_u Nm wf_e.
case Ei: (is_inv u); last first.
  have Ni : negb (is_inv u) by rewrite Ei.
  by rewrite (inv_invN _ Ni) /= (exp_aux_Ninv _ _ Ni).
case: u Ei wf_u Nm => [o|[k| |] v|o c d|ts] // _ /=.
rewrite !andb_True => - [[Ni Nm_v] wf_v] _.
rewrite (exp_aux_Ninv _ _ Ni) inv_auxK //.
apply: wf_mk_exp.
- exact: (base_Nnf _ wf_v Nm_v Ni).
- exact: wf_base.
- apply: wf_mul; rewrite !list.Forall_cons list.Forall_nil.
  by split; [exact: wf_expo|].
Qed.

(* [exp] preserves "neither a product nor an inverse", so iterated
   exponentiation stays in the range where [base_exp]/[expo_exp] apply. *)
Lemma Nmul_mk_exp X Y : negb (is_mul X) -> negb (is_mul (mk_exp X Y)).
Proof. by rewrite /mk_exp; case_bool_decide. Qed.

Lemma Ninv_mk_exp X Y : negb (is_inv X) -> negb (is_inv (mk_exp X Y)).
Proof. by rewrite /mk_exp; case_bool_decide. Qed.

(* The images of [exp_aux _ e] are never products, so [mbind factors] is the
   identity on a mapped factor list and [mul] sees the images directly. *)
Lemma exp_aux_Nmul t e :
  wf t -> negb (is_mul t) -> wf e -> negb (is_mul (exp_aux t e)).
Proof.
move=> wf_t Nm wf_e.
case Ei: (is_inv t); last first.
  have Ni : negb (is_inv t) by rewrite Ei.
  rewrite (exp_aux_Ninv _ _ Ni); apply: Nmul_mk_exp.
  exact: (Nnf_Nmul _ (base_Nnf _ wf_t Nm Ni)).
case: t Ei wf_t Nm => [o|[k| |] u|o c d|ts] // _ /=.
rewrite !andb_True => - [[Ni Nm_u] wf_u] _.
have NnfB := base_Nnf _ wf_u Nm_u Ni.
rewrite /mk_exp; case_bool_decide => /=.
- by rewrite (inv_invN _ (Nnf_Ninv _ NnfB)).
- by [].
Qed.

(* [(a^-1) ^ x = (a ^ x)^-1] at the level of [exp]/[inv].  This is the form the
   term layer conjugates; [exp_aux_inv_aux] is the [exp_aux]-level version it
   is proved from. *)
Lemma exp_inv t e :
  wf t -> negb (is_mul t) -> wf e -> exp (inv t) e = inv (exp t e).
Proof.
move=> wft Nm wfe.
have NmI : negb (is_mul (inv_aux t)).
  move: wft Nm; case: t => [o|[k| |] u|o c d|us] //=.
  by rewrite !andb_True => - [[_ ?] _].
rewrite (inv_Nmul _ Nm) (exp_Nmul _ _ (wf_inv_aux _ wft Nm) wfe NmI).
rewrite (exp_aux_inv_aux _ _ wft Nm wfe) (exp_Nmul _ _ wft wfe Nm).
by rewrite (inv_Nmul _ (exp_aux_Nmul _ _ wft Nm wfe)).
Qed.

Lemma mbind_factors_Nmul ts :
  Forall (λ t, negb (is_mul t)) ts -> mbind factors ts = ts.
Proof.
elim: ts => [//|t ts IH]; rewrite list.Forall_cons => - [Nm NmL].
by rewrite bind_cons (factors_Nmul _ Nm) (IH NmL).
Qed.

(* [to] does not disturb a mapped list's signed counts, because [exp_aux _ e]
   conjugates [inv_aux] ([exp_aux_inv_aux]).  This is [SMS.count_fmap_to] at the
   pre-term instance. *)
Lemma to_fmap_exp_aux ts e :
  Forall wf ts -> Forall (λ t, negb (is_mul t)) ts -> wf e ->
  SMS.to pt_order inv_aux ((λ t, exp_aux t e) <$> SMS.to pt_order inv_aux ts)
  = SMS.to pt_order inv_aux ((λ t, exp_aux t e) <$> ts).
Proof.
move=> /list.Forall_forall wf_ts /list.Forall_forall Nm_ts wf_e.
have wff : forall t, t ∈ ts -> wf (exp_aux t e).
  by move=> t t_ts; apply: wf_exp_aux; auto.
have jKf : forall t, t ∈ ts -> inv_aux (inv_aux (exp_aux t e)) = exp_aux t e.
  by move=> t t_ts; apply: inv_auxK; exact: wff.
have fij : forall t, t ∈ ts -> exp_aux (inv_aux t) e = inv_aux (exp_aux t e).
  by move=> t t_ts; apply: exp_aux_inv_aux; auto.
have h : forall X : list pre_term, (forall t, t ∈ X -> t ∈ ts) ->
         forall x, x ∈ ((λ t, exp_aux t e) <$> X) -> inv_aux (inv_aux x) = x.
  by move=> X sub x /list_elem_of_fmap [t [-> t_X]]; exact: (jKf _ (sub _ t_X)).
apply/(SMS.to_eq pt_order inv_aux _ _
        (h _ (fun t t_in => SMS.mem_to _ _ _ _ t_in)) (h _ (fun t t_in => t_in))).
move=> z jKz.
exact: (SMS.count_fmap_to pt_order inv_aux inv_aux
          (λ t, exp_aux t e) z ts jKz jKf fij).
Qed.

(* Distributivity, on a list of atoms: [(t1 * … * tn) ^ e = t1^e * … * tn^e]. *)
Lemma exp_mul ts e :
  Forall wf ts -> Forall (λ t, negb (is_mul t)) ts -> wf e ->
  exp (mul ts) e = mul ((λ t, exp_aux t e) <$> ts).
Proof.
move=> wf_ts Nm_ts wf_e.
have Nmf : Forall (λ t, negb (is_mul t)) ((λ t, exp_aux t e) <$> ts).
  apply/Forall_fmap/list.Forall_forall => t t_ts.
  apply: exp_aux_Nmul => //; by [move/list.Forall_forall: wf_ts; apply
                               |move/list.Forall_forall: Nm_ts; apply].
rewrite /exp /mul !mul_auxK; first last.
- exact: wf_normalize_factors.
congr mul_aux; rewrite /normalize_factors (mbind_factors_Nmul _ Nm_ts).
have Nmf' : Forall (λ t, negb (is_mul t))
              ((λ t, exp_aux t e) <$> SMS.to pt_order inv_aux ts).
  apply/Forall_fmap/list.Forall_forall => t /(SMS.mem_to _ _ _ _) t_ts.
  apply: exp_aux_Nmul => //; by [move/list.Forall_forall: wf_ts; apply
                               |move/list.Forall_forall: Nm_ts; apply].
rewrite (mbind_factors_Nmul _ Nmf') (mbind_factors_Nmul _ Nmf).
exact: to_fmap_exp_aux.
Qed.

Lemma Nmul_exp b e :
  wf b -> wf e -> negb (is_mul b) -> negb (is_mul (exp b e)).
Proof.
move=> wf_b wf_e Nm; rewrite (exp_Nmul _ _ wf_b wf_e Nm).
exact: exp_aux_Nmul.
Qed.

Lemma Ninv_exp b e :
  wf b -> wf e -> negb (is_mul b) -> negb (is_inv b) -> negb (is_inv (exp b e)).
Proof.
move=> wf_b wf_e Nm Ni; rewrite (exp_Nmul _ _ wf_b wf_e Nm) (exp_aux_Ninv _ _ Ni).
by apply: Ninv_mk_exp; exact: (Nnf_Ninv _ (base_Nnf _ wf_b Nm Ni)).
Qed.

End PreTerm.
