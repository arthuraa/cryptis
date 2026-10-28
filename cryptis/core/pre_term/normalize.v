(** Pre-term normalization
    ======================

    This file defines a normalization function on pre-terms.  Pre-terms carry
    *two* multiplicative structures:

    - the Diffie-Hellman group [PTGMul] (a symbolic model of a prime-order
      elliptic-curve group), which lives in the *base* of an exponential;
    - the exponent ring [PTMul], which lives in the *exponent*.

    Two pre-terms have the same normal form if and only if they are equal
    according to the following equations.  Writing [1 := PTMul [] []], [1G :=
    PTGMul [] []], [g ^ x := PTExp g x], [a * b := PTMul [a; b] []], [a^-1 :=
    PTMul [] [a]], [u ⋅ v := PTGMul [u; v] []] and [u^-1 := PTGMul [] [u]]:

    Group ([⋅], [_^-1]):

    - [u ⋅ v = v ⋅ u]
    - [u ⋅ (v ⋅ w) = (u ⋅ v) ⋅ w]
    - [u ⋅ u^-1 = 1G]
    - [u ⋅ 1G = u]

    Exponents ([*], [_^-1]): the same four laws, at [PTMul].

    Exponentiation, which links them:

    - [(g ^ a) ^ b = g ^ (a * b)]
    - [g ^ 1 = g]
    - [(u ⋅ v) ^ x = u^x ⋅ v^x]

    The last equation makes [_ ^ x] an endomorphism of the Diffie-Hellman group.
    (Notice that [(u * v) ^ x ≠ u^x * v^x] is not universally valid because this
    identity generally does not hold for groups of invertible integers modulo
    n.) From these equations, several other properties follow,
    such as

    - [u ⋅ v = u ⋅ w -> v = w]
    - [(u^-1)^-1 = u]
    - [(1G^-1) = 1G]
    - [(u ⋅ v)^-1 = u^-1 ⋅ v^-1]
    - [(g ^ a) ^ (a^-1) = g]
    - [(g ^ a) ^ b = (g ^ b) ^ a]
    - [1G ^ x = 1G]
    - [(u^-1) ^ x = (u ^ x)^-1]

    The last two are why [exp] distributes over both sides of a group product,
    and why [wf] demands a group atom -- neither a group product nor an
    exponential -- in the base of an exponential.

    This file establishes the normalization machinery and the pre-term forms of
    the exponentiation laws ([exp_unit], [exp_base_expo], [exp_gmul], ...).
    Products are signed multisets ([SMS]) and [SMS.Internal.to] is their
    canonical form, so the group laws follow from those of [SMS.sms].  The
    derived equations are proved for terms in [core/term/].

    The predicate [wf : pre_term -> bool] characterizes normal forms.  We have
    the following properties:

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
  | PTN _ ps ns =>
    S (Nat.max (max_list_with height ps) (max_list_with height ns))
  end.

Definition is_exp pt := if pt is PTExp _ _ then true else false.
Definition is_mul pt := if pt is PTMul _ _ then true else false.
Definition is_gmul pt := if pt is PTGMul _ _ then true else false.
Definition is_nonce pt := if pt is PT0 (O0Nonce _) then true else false.

(** [is_non_free] collects the heads that [term] represents indirectly, and is
    what [core/term/base.v] uses for [TNonFree].  [is_gnon_free] collects the
    heads a normal-form exponential base may not have, and is what [wf] uses: a
    scalar product in a base is an atom, since [exp] does not distribute over
    it. *)
Definition is_non_free pt := is_exp pt || is_mul pt || is_gmul pt.

Definition is_gnon_free pt := is_exp pt || is_gmul pt.

Lemma Nnf_Nexp pt : negb (is_non_free pt) → negb (is_exp pt).
Proof. by case: pt => [o|o t|[||] t1 t2|[|] ps ns]. Qed.

Lemma Nnf_Nmul pt : negb (is_non_free pt) → negb (is_mul pt).
Proof. by case: pt => [o|o t|[||] t1 t2|[|] ps ns]. Qed.

Lemma Nnf_Ngmul pt : negb (is_non_free pt) → negb (is_gmul pt).
Proof. by case: pt => [o|o t|[||] t1 t2|[|] ps ns]. Qed.

Lemma Nnf_Ngnf pt : negb (is_non_free pt) → negb (is_gnon_free pt).
Proof. by case: pt => [o|o t|[||] t1 t2|[|] ps ns]. Qed.

Lemma Ngnf_Nexp pt : negb (is_gnon_free pt) → negb (is_exp pt).
Proof. by case: pt => [o|o t|[||] t1 t2|[|] ps ns]. Qed.

Lemma Ngnf_Ngmul pt : negb (is_gnon_free pt) → negb (is_gmul pt).
Proof. by case: pt => [o|o t|[||] t1 t2|[|] ps ns]. Qed.

Definition base pt := if pt is PTExp b _ then b else pt.
Definition expo pt := if pt is PTExp _ e then e else PTMul [] [].
Definition factors pt : SMS.sms pre_term :=
  if pt is PTMul ps ns then SMS.make ps ns else {[+ pt +]}.
Definition gfactors pt : SMS.sms pre_term :=
  if pt is PTGMul ps ns then SMS.make ps ns else {[+ pt +]}.

(** We now define smart constructors for the operations that validate
    non-trivial equations.  Products are signed multisets ([SMS.sms]): [mul s]
    multiplies out the factors of the elements of [s] ([SMS.bind]), and
    [mul_aux] collapses a single positive factor.  [gmul] is the same for the
    group.  An inverse is a product with one negative factor.

    [exp] distributes over the group factors of its base, positive and negative
    alike ([(u^-1) ^ x = (u ^ x)^-1]); [exp_aux] exponentiates a group atom,
    merging iterated exponents with the scalar [mul], and [mk_exp] collapses
    [g ^ 1] to [g]. *)

Definition single (A : list pre_term * list pre_term) :=
  if A is ([_], []) then true else false.

Definition mul_aux (s : SMS.sms pre_term) :=
  if SMS.car s is ([t], []) then t else PTMul (SMS.pos s) (SMS.neg s).

Definition gmul_aux (s : SMS.sms pre_term) :=
  if SMS.car s is ([t], []) then t else PTGMul (SMS.pos s) (SMS.neg s).

Definition mul s := mul_aux (SMS.bind factors s).

Definition gmul s := gmul_aux (SMS.bind gfactors s).

Definition mk_exp b e :=
  if bool_decide (e = PTMul [] []) then b else PTExp b e.

Definition exp_aux b e := mk_exp (base b) (mul (SMS.make [expo b; e] [])).

Definition exp b e := gmul (SMS.map (λ t, exp_aux t e) (gfactors b)).

Fixpoint normalize pt :=
  match pt with
  | PT0 o => PT0 o
  | PT1 o t => PT1 o (normalize t)
  | PTExp b e => exp (normalize b) (normalize e)
  | PT2 o t1 t2 => PT2 o (normalize t1) (normalize t2)
  | PTMul ps ns => mul (SMS.make (normalize <$> ps) (normalize <$> ns))
  | PTGMul ps ns => gmul (SMS.make (normalize <$> ps) (normalize <$> ns))
  end.

Fixpoint wf (pt : pre_term) : bool :=
  match pt with
  | PT0 _ => true
  | PT1 _ pt => wf pt
  | PTExp b e =>
    wf b && negb (is_gnon_free b) && wf e && bool_decide (e ≠ PTMul [] [])
  | PT2 _ pt1 pt2 => wf pt1 && wf pt2
  | PTMul ps ns =>
    forallb (λ t, wf t && negb (is_mul t)) ps
    && forallb (λ t, wf t && negb (is_mul t)) ns
    && SMS.Internal.wf SMS.Internal.le (ps, ns) && negb (single (ps, ns))
  | PTGMul ps ns =>
    forallb (λ t, wf t && negb (is_gmul t)) ps
    && forallb (λ t, wf t && negb (is_gmul t)) ns
    && SMS.Internal.wf SMS.Internal.le (ps, ns) && negb (single (ps, ns))
  end.

Definition wf_factors (s : SMS.sms pre_term) :=
  forallb (λ t, wf t && negb (is_mul t)) (elements s).

Definition wf_gfactors (s : SMS.sms pre_term) :=
  forallb (λ t, wf t && negb (is_gmul t)) (elements s).

Lemma wf_mulE ps ns :
  wf (PTMul ps ns) =
  forallb (λ t, wf t && negb (is_mul t)) (ps ++ ns)
  && SMS.Internal.wf SMS.Internal.le (ps, ns) && negb (single (ps, ns)).
Proof. by rewrite /= forallb_app. Qed.

Lemma wf_gmulE ps ns :
  wf (PTGMul ps ns) =
  forallb (λ t, wf t && negb (is_gmul t)) (ps ++ ns)
  && SMS.Internal.wf SMS.Internal.le (ps, ns) && negb (single (ps, ns)).
Proof. by rewrite /= forallb_app. Qed.

Lemma wf_factorsP s : wf_factors s ↔ ∀ t, t ∈ s → wf t ∧ negb (is_mul t).
Proof.
rewrite /wf_factors forallb_True list.Forall_forall.
by split=> H t /H /andb_True.
Qed.

Lemma wf_gfactorsP s : wf_gfactors s ↔ ∀ t, t ∈ s → wf t ∧ negb (is_gmul t).
Proof.
rewrite /wf_gfactors forallb_True list.Forall_forall.
by split=> H t /H /andb_True.
Qed.

Lemma wf_factors_wf {s t} : wf_factors s → t ∈ s → wf t.
Proof. by move=> /wf_factorsP H /H []. Qed.

Lemma wf_factors_Nmul {s t} : wf_factors s → t ∈ s → negb (is_mul t).
Proof. by move=> /wf_factorsP H /H []. Qed.

Lemma wf_gfactors_wf {s t} : wf_gfactors s → t ∈ s → wf t.
Proof. by move=> /wf_gfactorsP H /H []. Qed.

Lemma wf_gfactors_Ngmul {s t} : wf_gfactors s → t ∈ s → negb (is_gmul t).
Proof. by move=> /wf_gfactorsP H /H []. Qed.

Lemma wf_one : wf (PTMul [] []).
Proof. by []. Qed.

Lemma wf_gone : wf (PTGMul [] []).
Proof. by []. Qed.

Lemma factors_Nmul pt : negb (is_mul pt) → factors pt = {[+ pt +]}.
Proof. by case: pt => [o|o t|o t1 t2|[|] ps ns]. Qed.

Lemma gfactors_Ngmul pt : negb (is_gmul pt) → gfactors pt = {[+ pt +]}.
Proof. by case: pt => [o|o t|o t1 t2|[|] ps ns]. Qed.

Lemma car_factors ps ns :
  wf (PTMul ps ns) → SMS.car (factors (PTMul ps ns)) = (ps, ns).
Proof.
rewrite wf_mulE => /andb_True [/andb_True [_ wfA] _].
by rewrite /= SMS.Internal.to_id.
Qed.

Lemma car_gfactors ps ns :
  wf (PTGMul ps ns) → SMS.car (gfactors (PTGMul ps ns)) = (ps, ns).
Proof.
rewrite wf_gmulE => /andb_True [/andb_True [_ wfA] _].
by rewrite /= SMS.Internal.to_id.
Qed.

Lemma car_factorsE pt :
  wf pt →
  SMS.car (factors pt) = if pt is PTMul ps ns then (ps, ns) else ([pt], []).
Proof.
case: pt => [o|o t|o t1 t2|[|] ps ns] wf_pt; try exact: SMS.car_singleton.
exact: car_factors.
Qed.

Lemma car_gfactorsE pt :
  wf pt →
  SMS.car (gfactors pt) = if pt is PTGMul ps ns then (ps, ns) else ([pt], []).
Proof.
case: pt => [o|o t|o t1 t2|[|] ps ns] wf_pt; try exact: SMS.car_singleton.
exact: car_gfactors.
Qed.

Lemma elements_factors pt :
  wf pt → elements (factors pt) = if pt is PTMul ps ns then ps ++ ns else [pt].
Proof.
case: pt => [o|o t|o t1 t2|[|] ps ns] wf_pt; try exact: SMS.elements_singleton.
by rewrite SMS.elements_car car_factors.
Qed.

Lemma elements_gfactors pt :
  wf pt →
  elements (gfactors pt) = if pt is PTGMul ps ns then ps ++ ns else [pt].
Proof.
case: pt => [o|o t|o t1 t2|[|] ps ns] wf_pt; try exact: SMS.elements_singleton.
by rewrite SMS.elements_car car_gfactors.
Qed.

Lemma wf_wf_factors pt : wf pt → wf_factors (factors pt).
Proof.
case E: (is_mul pt) => wf_pt; last first.
  rewrite factors_Nmul ?E //; apply/wf_factorsP => t /SMS.elem_of_singleton ->.
  by rewrite E.
case: pt E wf_pt => [o|o t|o t1 t2|[|] ps ns] // _ wf_pt.
rewrite /wf_factors SMS.elements_car car_factors //.
by move: wf_pt; rewrite wf_mulE => /andb_True [/andb_True [] ].
Qed.

Lemma wf_wf_gfactors pt : wf pt → wf_gfactors (gfactors pt).
Proof.
case E: (is_gmul pt) => wf_pt; last first.
  rewrite gfactors_Ngmul ?E //.
  apply/wf_gfactorsP => t /SMS.elem_of_singleton ->.
  by rewrite E.
case: pt E wf_pt => [o|o t|o t1 t2|[|] ps ns] // _ wf_pt.
rewrite /wf_gfactors SMS.elements_car car_gfactors //.
by move: wf_pt; rewrite wf_gmulE => /andb_True [/andb_True [] ].
Qed.

Lemma mul_aux_Nsingle s :
  negb (single (SMS.car s)) → mul_aux s = PTMul (SMS.pos s) (SMS.neg s).
Proof. by rewrite /mul_aux; case: (SMS.car s) => [[|? [|??]] [|??]]. Qed.

Lemma gmul_aux_Nsingle s :
  negb (single (SMS.car s)) → gmul_aux s = PTGMul (SMS.pos s) (SMS.neg s).
Proof. by rewrite /gmul_aux; case: (SMS.car s) => [[|? [|??]] [|??]]. Qed.

Lemma mul_aux_single s t : SMS.car s = ([t], []) → mul_aux s = t.
Proof. by rewrite /mul_aux => ->. Qed.

Lemma gmul_aux_single s t : SMS.car s = ([t], []) → gmul_aux s = t.
Proof. by rewrite /gmul_aux => ->. Qed.

Lemma single_car s : single (SMS.car s) → ∃ t, s = {[+ t +]}.
Proof.
case Es: (SMS.car s) => [[|t [|??]] [|??]] // _; exists t.
by apply: SMS.car_inj; rewrite Es SMS.car_singleton.
Qed.

Lemma wf_mul_aux s : wf_factors s → wf (mul_aux s).
Proof.
move=> wfs; case Es: (single (SMS.car s)).
  have [t e] := single_car s ltac:(by rewrite Es); rewrite e in wfs *.
  rewrite (mul_aux_single _ t) ?SMS.car_singleton //.
  by apply: (wf_factors_wf wfs); rewrite SMS.elem_of_singleton.
rewrite mul_aux_Nsingle ?Es // wf_mulE /SMS.pos /SMS.neg -surjective_pairing.
rewrite Es; apply/andb_True; split; last done.
by apply/andb_True; split; [exact: wfs|exact: SMS.wf_car].
Qed.

Lemma wf_gmul_aux s : wf_gfactors s → wf (gmul_aux s).
Proof.
move=> wfs; case Es: (single (SMS.car s)).
  have [t e] := single_car s ltac:(by rewrite Es); rewrite e in wfs *.
  rewrite (gmul_aux_single _ t) ?SMS.car_singleton //.
  by apply: (wf_gfactors_wf wfs); rewrite SMS.elem_of_singleton.
rewrite gmul_aux_Nsingle ?Es // wf_gmulE /SMS.pos /SMS.neg -surjective_pairing.
rewrite Es; apply/andb_True; split; last done.
by apply/andb_True; split; [exact: wfs|exact: SMS.wf_car].
Qed.

Lemma mul_auxK s : wf_factors s → factors (mul_aux s) = s.
Proof.
move=> wfs; case Es: (single (SMS.car s)).
  have [t e] := single_car s ltac:(by rewrite Es); rewrite e in wfs *.
  rewrite (mul_aux_single _ t) ?SMS.car_singleton // factors_Nmul //.
  by apply: (wf_factors_Nmul wfs); rewrite SMS.elem_of_singleton.
by rewrite mul_aux_Nsingle ?Es //; exact: SMS.make_pos_neg.
Qed.

Lemma gmul_auxK s : wf_gfactors s → gfactors (gmul_aux s) = s.
Proof.
move=> wfs; case Es: (single (SMS.car s)).
  have [t e] := single_car s ltac:(by rewrite Es); rewrite e in wfs *.
  rewrite (gmul_aux_single _ t) ?SMS.car_singleton // gfactors_Ngmul //.
  by apply: (wf_gfactors_Ngmul wfs); rewrite SMS.elem_of_singleton.
by rewrite gmul_aux_Nsingle ?Es //; exact: SMS.make_pos_neg.
Qed.

Lemma factorsK t : wf t → mul_aux (factors t) = t.
Proof.
case E: (is_mul t) => wf_t; last first.
  by rewrite factors_Nmul ?E // (mul_aux_single _ t) // SMS.car_singleton.
case: t E wf_t => [o|o t|o t1 t2|[|] ps ns] // _ wf_t.
rewrite mul_aux_Nsingle /SMS.pos /SMS.neg car_factors //.
by move: wf_t; rewrite wf_mulE => /andb_True [].
Qed.

Lemma gfactorsK t : wf t → gmul_aux (gfactors t) = t.
Proof.
case E: (is_gmul t) => wf_t; last first.
  by rewrite gfactors_Ngmul ?E // (gmul_aux_single _ t) // SMS.car_singleton.
case: t E wf_t => [o|o t|o t1 t2|[|] ps ns] // _ wf_t.
rewrite gmul_aux_Nsingle /SMS.pos /SMS.neg car_gfactors //.
by move: wf_t; rewrite wf_gmulE => /andb_True [].
Qed.

Lemma wf_bind_factors s : (∀ t, t ∈ s → wf t) → wf_factors (SMS.bind factors s).
Proof.
move=> wfs; apply/wf_factorsP => t /SMS.elem_of_bind [u [u_s t_u]].
have wfu := wf_wf_factors _ (wfs _ u_s).
by split; [apply: wf_factors_wf wfu t_u|apply: wf_factors_Nmul wfu t_u].
Qed.

Lemma wf_bind_gfactors s :
  (∀ t, t ∈ s → wf t) → wf_gfactors (SMS.bind gfactors s).
Proof.
move=> wfs; apply/wf_gfactorsP => t /SMS.elem_of_bind [u [u_s t_u]].
have wfu := wf_wf_gfactors _ (wfs _ u_s).
by split; [apply: wf_gfactors_wf wfu t_u|apply: wf_gfactors_Ngmul wfu t_u].
Qed.

Lemma wf_mul s : (∀ t, t ∈ s → wf t) → wf (mul s).
Proof. by move=> wfs; apply: wf_mul_aux; apply: wf_bind_factors. Qed.

Lemma wf_gmul s : (∀ t, t ∈ s → wf t) → wf (gmul s).
Proof. by move=> wfs; apply: wf_gmul_aux; apply: wf_bind_gfactors. Qed.

Lemma bind_factors_wf s : wf_factors s → SMS.bind factors s = s.
Proof.
move=> wfs; rewrite -[RHS]SMS.bind_unit; apply: SMS.bind_ext => t t_s.
by apply: factors_Nmul; apply: wf_factors_Nmul wfs t_s.
Qed.

Lemma bind_gfactors_wf s : wf_gfactors s → SMS.bind gfactors s = s.
Proof.
move=> wfs; rewrite -[RHS]SMS.bind_unit; apply: SMS.bind_ext => t t_s.
by apply: gfactors_Ngmul; apply: wf_gfactors_Ngmul wfs t_s.
Qed.

Lemma mul1 t : wf t → mul {[+ t +]} = t.
Proof. by move=> wf_t; rewrite /mul SMS.bind_singleton factorsK. Qed.

Lemma gmul1 t : wf t → gmul {[+ t +]} = t.
Proof. by move=> wf_t; rewrite /gmul SMS.bind_singleton gfactorsK. Qed.

Lemma mul_unit_l t : mul (SMS.make [PTMul [] []; t] []) = mul {[+ t +]}.
Proof.
rewrite /mul !SMS.bind_make_cons_l SMS.bind_empty.
by rewrite (right_id ∅ (⊎)) (left_id ∅ (⊎)).
Qed.

Lemma mul_unit_r t : wf t → mul (SMS.make [t; PTMul [] []] []) = t.
Proof.
move=> wf_t; rewrite /mul !SMS.bind_make_cons_l SMS.bind_empty.
by rewrite !(right_id ∅ (⊎)) factorsK.
Qed.

Lemma wf_mk_exp b e :
  negb (is_gnon_free b) → wf b → wf e → wf (mk_exp b e).
Proof.
move=> bNnf wf_b wf_e; rewrite /mk_exp; case_bool_decide as Hf => //=.
rewrite !andb_True bool_decide_spec; eauto.
Qed.

Lemma wf_base pt : wf pt → wf (base pt).
Proof.
case: pt => [o|o t|[||] b e|[|] ps ns] wf_pt //.
by move: wf_pt; rewrite /= !andb_True => - [[[? _] _] _].
Qed.

Lemma base_expN pt : negb (is_exp pt) → base pt = pt.
Proof. by case: pt => [o|o t|[||] t1 t2|[|] ps ns]. Qed.

Lemma base_Nexp pt : wf pt → negb (is_exp (base pt)).
Proof.
case: pt => [o|o t|[||] b e|[|] ps ns] wf_pt //=.
by move: wf_pt; rewrite /= !andb_True => - [[[_ /Ngnf_Nexp ?] _] _].
Qed.

(* There is deliberately no scalar counterpart: a scalar product in a base is
   an atom, so [is_mul (base pt) = is_mul pt] is false. *)
Lemma is_gmul_base pt : wf pt → is_gmul (base pt) = is_gmul pt.
Proof.
case: pt => [o|o t|[||] b e|[|] ps ns] //= wf_pt.
move: wf_pt; rewrite !andb_True => - [[[_ Nnf] _] _].
by case: (is_gmul b) (Ngnf_Ngmul _ Nnf).
Qed.

Lemma expo_expN pt : negb (is_exp pt) → expo pt = PTMul [] [].
Proof. by case: pt => [o|o t|[||] t1 t2|[|] ps ns]. Qed.

Lemma wf_expo pt : wf pt → wf (expo pt).
Proof.
case: pt => [o|o t|[||] b e|[|] ps ns]; try (move=> _; exact: wf_one).
by move=> wf_pt; move: wf_pt; rewrite /= !andb_True => - [[[_ _] ?] _].
Qed.

Lemma base_Ngnf t : wf t → negb (is_gmul t) → negb (is_gnon_free (base t)).
Proof.
case: t => [o|o t|[||] t1 t2|[|] ps ns] //= wf_t Nm.
by move: wf_t; rewrite !andb_True => - [[[_ ?] _] _].
Qed.

Lemma wf_exp_aux t e : wf t → negb (is_gmul t) → wf e → wf (exp_aux t e).
Proof.
move=> wf_t Nm wf_e; apply: wf_mk_exp.
- exact: base_Ngnf.
- exact: wf_base.
- apply: wf_mul => u /SMS.elem_of_make_nil_r.
  by rewrite elem_of_cons list_elem_of_singleton => -[->|->] //; exact: wf_expo.
Qed.

Lemma exp_aux_Ngmul t e :
  wf t → negb (is_gmul t) → negb (is_gmul (exp_aux t e)).
Proof.
move=> wf_t Nm; rewrite /exp_aux /mk_exp; case_bool_decide => //=.
exact: Ngnf_Ngmul (base_Ngnf _ wf_t Nm).
Qed.

Lemma wf_exp b e : wf b → wf e → wf (exp b e).
Proof.
move=> wf_b wf_e; rewrite /exp; apply: wf_gmul.
have wfg := wf_wf_gfactors _ wf_b.
move=> t /SMS.elem_of_map [u [-> u_b]].
by apply: wf_exp_aux => //; [exact: wf_gfactors_wf wfg u_b
                            |exact: wf_gfactors_Ngmul wfg u_b].
Qed.

(* On a base that is not a group product the [gmul] of [exp] collapses.  This
   needs well-formedness: the collapse goes through [gmul1]. *)
Lemma exp_Ngmul b e : wf b → wf e → negb (is_gmul b) → exp b e = exp_aux b e.
Proof.
move=> wf_b wf_e Nm; rewrite /exp gfactors_Ngmul // SMS.map_singleton.
exact: gmul1 (wf_exp_aux _ _ wf_b Nm wf_e).
Qed.

Lemma mk_exp_base_expo t : wf t → mk_exp (base t) (expo t) = t.
Proof.
case: t => [o|o u|[||] c d|[|] ps ns] /= wf_t; rewrite /mk_exp;
  try by rewrite bool_decide_eq_true_2.
move: wf_t; rewrite !andb_True => - [_ /bool_decide_unpack dN0].
by rewrite bool_decide_eq_false_2.
Qed.

Lemma exp_aux_unit t : wf t → exp_aux t (PTMul [] []) = t.
Proof.
move=> wf_t; rewrite /exp_aux (mul_unit_r _ (wf_expo _ wf_t)).
exact: mk_exp_base_expo.
Qed.

Fixpoint foldr_Forall (P : pre_term → Prop) ts :
  seq.foldr (λ t (R : Type), (P t * R)%type) unit ts → Forall P ts :=
  match ts with
  | [] => λ _, Forall_nil P
  | t :: ts => λ H, Forall_cons P t ts H.1 (foldr_Forall P ts H.2)
  end.

Lemma wf_normalize pt : wf (normalize pt).
Proof.
elim: pt => //=.
- move=> o t1 IH1 t2 IH2; case: o => /=;
    [by rewrite andb_True; split
    |by rewrite andb_True; split
    |exact: (wf_exp _ _ IH1 IH2)].
- move=> [|] ps /(foldr_Forall _ _) IHps ns /(foldr_Forall _ _) IHns;
    [apply: wf_mul|apply: wf_gmul] => t /SMS.elem_of_make;
    rewrite -fmap_app => /list_elem_of_fmap [u [-> u_in]];
    by move: u u_in; apply/list.Forall_forall/Forall_app.
Qed.
Hint Resolve wf_normalize : core.

Lemma normalize_wf pt : wf pt → normalize pt = pt.
Proof.
have fmapE (ts : list pre_term) :
    Forall (λ t, wf t → normalize t = t) ts → Forall wf ts →
    normalize <$> ts = ts.
  move=> /list.Forall_forall IH /list.Forall_forall wf_ts.
  rewrite -[RHS]list_fmap_id; apply/Forall_fmap_ext/list.Forall_forall.
  by move=> t t_ts; apply: IH => //; apply: wf_ts.
elim: pt => [o|o t IH|o t1 IH1 t2 IH2
            |[|] ps /(foldr_Forall _ _) IHps ns /(foldr_Forall _ _) IHns].
- by [].
- by move=> /= wf_t; rewrite IH.
- case: o => /=.
  + by rewrite andb_True => - [/IH1 -> /IH2 ->].
  + by rewrite andb_True => - [/IH1 -> /IH2 ->].
  + rewrite !andb_True => - [[[wfb Nnfb] wfe] /bool_decide_unpack eN0].
    rewrite IH1 // IH2 // exp_Ngmul //; last exact: Ngnf_Ngmul.
    rewrite /exp_aux base_expN; last exact: Ngnf_Nexp.
    rewrite expo_expN; last exact: Ngnf_Nexp.
    by rewrite mul_unit_l mul1 // /mk_exp bool_decide_eq_false_2.
- move=> wf_pt; have := wf_pt; rewrite wf_mulE /=.
  move=> /andb_True [/andb_True [/forallb_True/list.Forall_forall wfA _] _].
  have wf_in t : t ∈ ps ++ ns → wf t by move=> /wfA /andb_True [].
  rewrite !fmapE //; try (apply/list.Forall_forall => t t_in; apply: wf_in;
                           rewrite elem_of_app; by [left|right]).
  rewrite /mul bind_factors_wf; first exact: (factorsK (PTMul ps ns)).
  exact: (wf_wf_factors (PTMul ps ns)).
- move=> wf_pt; have := wf_pt; rewrite wf_gmulE /=.
  move=> /andb_True [/andb_True [/forallb_True/list.Forall_forall wfA _] _].
  have wf_in t : t ∈ ps ++ ns → wf t by move=> /wfA /andb_True [].
  rewrite !fmapE //; try (apply/list.Forall_forall => t t_in; apply: wf_in;
                           rewrite elem_of_app; by [left|right]).
  rewrite /gmul bind_gfactors_wf; first exact: (gfactorsK (PTGMul ps ns)).
  exact: (wf_wf_gfactors (PTGMul ps ns)).
Qed.

Lemma normalize_idem pt : normalize (normalize pt) = normalize pt.
Proof. exact: normalize_wf. Qed.

Lemma fmap_normalize_wf ts : Forall wf ts → normalize <$> ts = ts.
Proof.
move=> /list.Forall_forall wf_ts.
rewrite -[RHS]list_fmap_id; apply/Forall_fmap_ext/list.Forall_forall.
by move=> t t_ts'; apply: normalize_wf; eauto.
Qed.

Lemma exp_unit b : wf b → exp b (PTMul [] []) = b.
Proof.
move=> wf_b; have wfg := wf_wf_gfactors _ wf_b.
rewrite /exp SMS.map_id_ext.
- by rewrite /gmul bind_gfactors_wf // gfactorsK.
- by move=> u u_b; apply: exp_aux_unit; apply: wf_gfactors_wf wfg u_b.
Qed.

Lemma exp_base_expo b : wf b → exp (base b) (expo b) = b.
Proof.
move=> wf_b; case Ex: (is_exp b).
  case: b Ex wf_b => [o|o u|[||] c d|[|] ps ns] // _ /=.
  rewrite !andb_True => - [[[wf_c Nnf_c] wf_d] /bool_decide_unpack dN0].
  rewrite (exp_Ngmul _ _ wf_c wf_d (Ngnf_Ngmul _ Nnf_c)) /exp_aux.
  rewrite (base_expN _ (Ngnf_Nexp _ Nnf_c)) (expo_expN _ (Ngnf_Nexp _ Nnf_c)).
  by rewrite mul_unit_l (mul1 _ wf_d) /mk_exp bool_decide_eq_false_2.
have Nx : negb (is_exp b) by rewrite Ex.
by rewrite (base_expN _ Nx) (expo_expN _ Nx) exp_unit.
Qed.

(* The destructors see through [exp] only when the base is not a group product
   -- otherwise [exp] distributes and the result is not an exponential. *)
Lemma base_exp b e :
  wf b → wf e → negb (is_gmul b) → base (exp b e) = base b.
Proof.
move=> wf_b wf_e Nm.
rewrite (exp_Ngmul _ _ wf_b wf_e Nm) /exp_aux /mk_exp.
case_bool_decide => //=.
exact: (base_expN _ (base_Nexp _ wf_b)).
Qed.

Lemma expo_exp b e :
  wf b → wf e → negb (is_gmul b) →
  expo (exp b e) = mul (SMS.make [expo b; e] []).
Proof.
move=> wf_b wf_e Nm.
rewrite (exp_Ngmul _ _ wf_b wf_e Nm) /exp_aux /mk_exp.
case_bool_decide as H => //=.
by rewrite H (expo_expN _ (base_Nexp _ wf_b)).
Qed.

(* Distributivity on group atoms: [(t1 * … * tn) ^ e = t1^e * … * tn^e]. *)
Lemma exp_gmul s e :
  (∀ t, t ∈ s → wf t) → (∀ t, t ∈ s → negb (is_gmul t)) → wf e →
  exp (gmul s) e = gmul (SMS.map (λ t, exp_aux t e) s).
Proof.
move=> wfs Nms wf_e.
have wfs' : wf_gfactors s by apply/wf_gfactorsP => t t_s; split; auto.
by rewrite /exp /gmul (bind_gfactors_wf s) // gmul_auxK.
Qed.

Lemma Ngmul_exp b e :
  wf b → wf e → negb (is_gmul b) → negb (is_gmul (exp b e)).
Proof.
move=> wf_b wf_e Nm; rewrite (exp_Ngmul _ _ wf_b wf_e Nm).
exact: exp_aux_Ngmul.
Qed.

End PreTerm.
