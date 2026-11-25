(** Pre-term normalization
    ======================

    This file defines a normalization function on pre-terms.  Pre-terms carry
    *two* multiplicative structures:

    - the Diffie-Hellman group (a symbolic model of a prime-order
      elliptic-curve group), whose elements [PTDH] map bases to logarithms;
    - the exponent ring [PTMul], in which logarithms are formal sums.

    A Diffie-Hellman pre-term [PTDH l] denotes the product, over the entries
    [(b, (ps, ns))] of [l], of the powers [b ^ p] for [p] in [ps] and of the
    inverses [(b ^ n)^-1] for [n] in [ns].  Two pre-terms have the same
    normal form if and only if they are equal according to the following
    equations.  Writing [1 := PTMul [] []], [a * b := PTMul [a; b] []],
    [a^-1 := PTMul [] [a]], [1G := PTDH []], [g ^ x := PTDH [(g, ([x], []))]],
    [u ⋅ v] for the product of [u] and [v] and [u^-1] for the inverse of [u]:

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
    and why the bases of a normal form are group atoms -- neither group
    products nor exponentials.  A normal form [PTDH l] lists each base once,
    sorted, with its logarithm: a nonzero formal sum of exponents, stored as
    the sides of a signed multiset ([lists]).  For instance,
    [g ^ a ⋅ g ^ b ⋅ (h ^ c)^-1] is [PTDH [(g, ([a; b], [])); (h, ([], [c]))]].
    A single base with logarithm [1] is the base itself.

    This file establishes the normalization machinery and the pre-term forms of
    the exponentiation laws ([exp_unit], [exp_base_expo], [exp_gmul], ...).
    Products are signed multisets ([SMS]), whose sides a product pre-term
    lists ([lists]), so the group laws follow from those of [SMS.sms].  A group
    element is also the signed multiset of its factors [b ^ e] ([gfactors]),
    and [gmul_aux] groups factors by base ([SMS.curry]).  The derived
    equations are proved for terms in [core/term/].

    The predicate [wf : pre_term -> bool] characterizes normal forms.  We have
    the following properties:

   - [normalize_wf : wf t -> normalize t = t]
   - [wf_normalize : wf (normalize t)]
   - [normalize_idem : normalize (normalize t) = normalize t]

*)

From stdpp Require Import sorting list numbers.
From cryptis Require Import lib.
From cryptis.lib Require Import list_sort fmap mset sms.
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
  | PTMul ps ns =>
    S (Nat.max (max_list_with height ps) (max_list_with height ns))
  | PTDH l =>
    S (max_list_with (λ e, Nat.max (height e.1)
         (Nat.max (max_list_with height e.2.1)
                  (max_list_with height e.2.2))) l)
  end.

(* [is_exp] and [is_gmul] are exclusive: [public] recurses on the factors of a
   group product, and the only factor of an exponential is itself. *)
Definition is_exp pt := if pt is PTDH [(_, ([_], []))] then true else false.
Definition is_mul pt := if pt is PTMul _ _ then true else false.
Definition is_gmul pt :=
  match pt with
  | PTDH [(_, ([_], []))] => false
  | PTDH _ => true
  | _ => false
  end.
Definition is_nonce pt := if pt is PT0 (O0Nonce _) then true else false.

(** [is_non_free] collects the heads that [term] represents indirectly, and is
    what [core/term/base.v] uses for [TNonFree].  [is_gnon_free] collects the
    heads a normal-form base may not have, and is what [wf] uses: a scalar
    product in a base is an atom, since [exp] does not distribute over it. *)
Definition is_non_free pt := is_exp pt || is_mul pt || is_gmul pt.

Definition is_gnon_free pt := is_exp pt || is_gmul pt.

Lemma Nnf_Nexp pt : negb (is_non_free pt) → negb (is_exp pt).
Proof.
by rewrite /is_non_free; case: (is_exp pt); case: (is_mul pt);
  case: (is_gmul pt).
Qed.

Lemma Nnf_Nmul pt : negb (is_non_free pt) → negb (is_mul pt).
Proof.
by rewrite /is_non_free; case: (is_exp pt); case: (is_mul pt);
  case: (is_gmul pt).
Qed.

Lemma Nnf_Ngmul pt : negb (is_non_free pt) → negb (is_gmul pt).
Proof.
by rewrite /is_non_free; case: (is_exp pt); case: (is_mul pt);
  case: (is_gmul pt).
Qed.

Lemma Nnf_Ngnf pt : negb (is_non_free pt) → negb (is_gnon_free pt).
Proof.
by rewrite /is_non_free /is_gnon_free; case: (is_exp pt); case: (is_mul pt);
  case: (is_gmul pt).
Qed.

Lemma Ngnf_Nexp pt : negb (is_gnon_free pt) → negb (is_exp pt).
Proof. by rewrite /is_gnon_free; case: (is_exp pt); case: (is_gmul pt). Qed.

Lemma Ngnf_Ngmul pt : negb (is_gnon_free pt) → negb (is_gmul pt).
Proof. by rewrite /is_gnon_free; case: (is_exp pt); case: (is_gmul pt). Qed.

Lemma is_non_free_dh l : is_non_free (PTDH l).
Proof. by case: l => [|[b [[|e [|??]] [|??]]] [|??]]. Qed.

Definition base pt := if pt is PTDH [(b, ([_], []))] then b else pt.
Definition expo pt := if pt is PTDH [(_, ([e], []))] then e else PTMul [] [].

Lemma base_expN pt : negb (is_exp pt) → base pt = pt.
Proof. by case: pt => // -[|[b [[|e [|??]] [|??]]] [|??]]. Qed.

Lemma expo_expN pt : negb (is_exp pt) → expo pt = PTMul [] [].
Proof. by case: pt => // -[|[b [[|e [|??]] [|??]]] [|??]]. Qed.

Variant is_exp_spec pt : bool → Prop :=
| IsExp b e of pt = PTDH [(b, ([e], []))] : is_exp_spec pt true
| NotExp of negb (is_exp pt) & base pt = pt & expo pt = PTMul [] [] :
  is_exp_spec pt false.

Lemma is_expP pt : is_exp_spec pt (is_exp pt).
Proof.
case Ex: (is_exp pt).
  by case: pt Ex => // -[|[b [[|e [|??]] [|??]]] [|??]] // _; econstructor.
have Nx : negb (is_exp pt) by rewrite Ex.
by constructor; [|exact: base_expN|exact: expo_expN].
Qed.

Lemma is_exp_Ngmul pt : is_exp pt → negb (is_gmul pt).
Proof. by case: (is_expP pt) => [?? ->|]. Qed.

Lemma is_exp_Nmul pt : is_exp pt → negb (is_mul pt).
Proof. by case: (is_expP pt) => [?? ->|]. Qed.

Lemma is_mul_Ngmul pt : is_mul pt → negb (is_gmul pt).
Proof. by case: pt. Qed.

(* A product pre-term stores the sides of its signed multiset of factors as
   sorted lists. *)
Definition lists (s : SMS.sms pre_term) : list pre_term * list pre_term :=
  (elements (SMS.pos s), elements (SMS.neg s)).

Definition wf_lists (A : list pre_term * list pre_term) : bool :=
  MSet.wf A.1 && MSet.wf A.2 && bool_decide (A.1 ## A.2).

Definition of_lists (A : list pre_term * list pre_term) : SMS.sms pre_term :=
  SMS.make (MSet.of_list A.1) (MSet.of_list A.2).

Definition factors pt : SMS.sms pre_term :=
  if pt is PTMul ps ns then SMS.make (MSet.of_list ps) (MSet.of_list ns)
  else {[+ pt +]}.

Definition mk_exp b e :=
  if bool_decide (e = PTMul [] []) then b else PTDH [(b, ([e], []))].

Definition dh_factors (l : list (pre_term * (list pre_term * list pre_term))) :=
  foldr (λ e s, SMS.map (mk_exp e.1) (of_lists e.2) ⊎ s) ∅ l.

Definition gfactors pt : SMS.sms pre_term :=
  match pt with
  | PTDH [(_, ([_], []))] => {[+ pt +]}
  | PTDH l => dh_factors l
  | _ => {[+ pt +]}
  end.

(** We now define smart constructors for the operations that validate
    non-trivial equations.  Products are signed multisets ([SMS.sms]): [mul s]
    multiplies out the factors of the elements of [s] ([SMS.bind]), and
    [mul_aux] collapses a single positive factor.  [gmul] is the same for the
    group, whose factors are powers [b ^ e] of atoms: [gmul_aux] turns them
    into pairs [(b, e)] and groups these by base ([SMS.curry]), and [dh_of]
    collapses a single power.  An inverse is a product with one negative
    factor.

    [exp] distributes over the group factors of its base, positive and negative
    alike ([(u^-1) ^ x = (u ^ x)^-1]); [exp_aux] exponentiates a group atom,
    merging iterated exponents with the scalar [mul], and [mk_exp] collapses
    [g ^ 1] to [g]. *)

Definition single (A : list pre_term * list pre_term) :=
  if A is ([_], []) then true else false.

Definition dhmap := FMap.fmap pre_term (SMS.sms pre_term) ∅.

Definition entries (m : dhmap) :=
  (λ p, (p.1, lists p.2)) <$> FMap.to_list m.

Definition dh_of (m : dhmap) :=
  if entries m is [(b, ([e], []))] then mk_exp b e else PTDH (entries m).

Definition to_pairs (s : SMS.sms pre_term) : SMS.sms (pre_term * pre_term) :=
  SMS.map (λ t, (base t, expo t)) s.

Definition of_pairs (P : SMS.sms (pre_term * pre_term)) : SMS.sms pre_term :=
  SMS.map (λ p, mk_exp p.1 p.2) P.

Definition mul_aux (s : SMS.sms pre_term) :=
  if lists s is ([t], []) then t else PTMul (lists s).1 (lists s).2.

Definition gmul_aux (s : SMS.sms pre_term) := dh_of (SMS.curry (to_pairs s)).

Definition mul s := mul_aux (SMS.bind factors s).

Lemma mulE s : mul s = mul_aux (SMS.bind factors s).
Proof. done. Qed.

(* Tactics that reduce a goal to head normal form, such as ssreflect's [apply:],
   would otherwise compute with [mul] on symbolic arguments. *)
#[global] Opaque mul.

Definition gmul s := gmul_aux (SMS.bind gfactors s).

Definition exp_aux b e := mk_exp (base b) (mul {[+ expo b; e +]}).

Definition exp b e := gmul (SMS.map (λ t, exp_aux t e) (gfactors b)).

Fixpoint normalize pt :=
  match pt with
  | PT0 o => PT0 o
  | PT1 o t => PT1 o (normalize t)
  | PT2 o t1 t2 => PT2 o (normalize t1) (normalize t2)
  | PTMul ps ns =>
    mul (SMS.make (MSet.of_list (normalize <$> ps))
                  (MSet.of_list (normalize <$> ns)))
  | PTDH l =>
    gmul (foldr (λ e s,
      SMS.map (exp (normalize e.1))
        (SMS.make (MSet.of_list (normalize <$> e.2.1))
                  (MSet.of_list (normalize <$> e.2.2))) ⊎ s) ∅ l)
  end.

Definition trivial_dh (l : list (pre_term * (list pre_term * list pre_term))) :=
  if l is [(_, ([e], []))] then bool_decide (e = PTMul [] []) else false.

Fixpoint wf (pt : pre_term) : bool :=
  match pt with
  | PT0 _ => true
  | PT1 _ pt => wf pt
  | PT2 _ pt1 pt2 => wf pt1 && wf pt2
  | PTMul ps ns =>
    forallb (λ t, wf t && negb (is_mul t)) ps
    && forallb (λ t, wf t && negb (is_mul t)) ns
    && wf_lists (ps, ns) && negb (single (ps, ns))
  | PTDH l =>
    forallb (λ e, wf e.1 && negb (is_gnon_free e.1)
                  && forallb wf e.2.1 && forallb wf e.2.2 && wf_lists e.2) l
    && FMap.wf ([], []) l && negb (trivial_dh l)
  end.

Definition wf_entry (e : pre_term * (list pre_term * list pre_term)) :=
  wf e.1 && negb (is_gnon_free e.1) && forallb wf e.2.1 && forallb wf e.2.2
  && wf_lists e.2.

Definition wf_factors (s : SMS.sms pre_term) :=
  forallb (λ t, wf t && negb (is_mul t)) (elements s).

Definition wf_gfactors (s : SMS.sms pre_term) :=
  forallb (λ t, wf t && negb (is_gmul t)) (elements s).

Lemma wf_mulE ps ns :
  wf (PTMul ps ns) =
  forallb (λ t, wf t && negb (is_mul t)) (ps ++ ns)
  && wf_lists (ps, ns) && negb (single (ps, ns)).
Proof. by rewrite /= forallb_app. Qed.

Lemma wf_dhE l :
  wf (PTDH l) =
  forallb wf_entry l && FMap.wf ([], []) l && negb (trivial_dh l).
Proof. done. Qed.

Lemma wf_factorsP s : wf_factors s ↔ ∀ t, t ∈ s → wf t ∧ negb (is_mul t).
Proof.
rewrite /wf_factors forallb_True list.Forall_forall.
by split=> H t /SMS.elem_of_elements /H /andb_True.
Qed.

Lemma wf_gfactorsP s : wf_gfactors s ↔ ∀ t, t ∈ s → wf t ∧ negb (is_gmul t).
Proof.
rewrite /wf_gfactors forallb_True list.Forall_forall.
by split=> H t /SMS.elem_of_elements /H /andb_True.
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

Lemma wf_gone : wf (PTDH []).
Proof. by rewrite wf_dhE; apply/andb_True; split. Qed.

Lemma wf_dh_single b e :
  wf (PTDH [(b, ([e], []))]) ↔
  wf b ∧ negb (is_gnon_free b) ∧ wf e ∧ e ≠ PTMul [] [].
Proof.
have wf_A : wf_lists ([e], []).
  apply/andb_True; split; first (apply/andb_True; split).
  - by apply: bool_decide_pack; constructor; constructor.
  - by apply: bool_decide_pack; constructor.
  - by apply: bool_decide_pack => x /list_elem_of_singleton _ /elem_of_nil.
have wf_l : FMap.wf (([], []) : list pre_term * list pre_term)
              [(b, ([e], []))].
  apply: bool_decide_pack; split; first by constructor; constructor.
  by constructor; [|constructor].
rewrite wf_dhE /trivial_dh /wf_entry; cbn [forallb fst snd].
move/Is_true_true: wf_A => ->; move/Is_true_true: wf_l => ->.
case: (wf b); case: (is_gnon_free b); case: (wf e);
  case: (bool_decide_reflect (e = PTMul [] [])) => ? /=; intuition.
Qed.

Lemma factors_Nmul pt : negb (is_mul pt) → factors pt = {[+ pt +]}.
Proof. by case: pt. Qed.

Lemma gfactors_Ngmul pt : negb (is_gmul pt) → gfactors pt = {[+ pt +]}.
Proof. by case: pt => // -[|[b [[|e [|??]] [|??]]] [|??]]. Qed.

Lemma factors_PTMul ps ns :
  factors (PTMul ps ns) = SMS.make (MSet.of_list ps) (MSet.of_list ns).
Proof. done. Qed.

Lemma elements_lists s : elements s = (lists s).1 ++ (lists s).2.
Proof. done. Qed.

Lemma wf_lists_lists s : wf_lists (lists s).
Proof.
apply/andb_True; split; first (apply/andb_True; split).
- exact: (MSet.wf_car (SMS.pos s)).
- exact: (MSet.wf_car (SMS.neg s)).
- apply: bool_decide_pack; exact: (SMS.pos_neg_disj s).
Qed.

Lemma lists_singleton t : lists {[+ t +]} = ([t], []).
Proof.
rewrite /lists SMS.pos_singleton SMS.neg_singleton.
by rewrite MSet.elements_singleton MSet.elements_empty.
Qed.

Lemma lists_make ps ns :
  wf_lists (ps, ns) →
  lists (SMS.make (MSet.of_list ps) (MSet.of_list ns)) = (ps, ns).
Proof.
case/andb_True => /andb_True [wps wns] /bool_decide_unpack d.
rewrite /lists SMS.pos_make SMS.neg_make.
rewrite !MSet.difference_disjoint_l ?MSet.elements_of_list_wf //;
  apply: MSet.of_list_disjoint => // x h1 h2; exact: d x h2 h1.
Qed.

Lemma lists_of_lists A : wf_lists A → lists (of_lists A) = A.
Proof. by case: A => ps ns; exact: lists_make. Qed.

Lemma of_lists_lists s : of_lists (lists s) = s.
Proof.
rewrite /of_lists /lists; cbn [fst snd].
by rewrite !MSet.of_list_elements SMS.make_pos_neg.
Qed.

Lemma lists_empty_inv s : lists s = ([], []) → s = ∅.
Proof. by move=> e; rewrite -(of_lists_lists s) e. Qed.

Lemma of_lists_single t : of_lists ([t], []) = {[+ t +]}.
Proof. done. Qed.

Lemma lists_factors ps ns :
  wf (PTMul ps ns) → lists (factors (PTMul ps ns)) = (ps, ns).
Proof.
rewrite wf_mulE => /andb_True [/andb_True [_ wfA] _].
by rewrite factors_PTMul lists_make.
Qed.

Lemma lists_factorsE pt :
  wf pt →
  lists (factors pt) = if pt is PTMul ps ns then (ps, ns) else ([pt], []).
Proof.
case: pt => [o|o t|o t1 t2|ps ns|l] wf_pt; try exact: lists_singleton.
exact: lists_factors.
Qed.

Lemma elements_factors pt :
  wf pt → elements (factors pt) = if pt is PTMul ps ns then ps ++ ns else [pt].
Proof.
case: pt => [o|o t|o t1 t2|ps ns|l] wf_pt; try exact: SMS.elements_singleton.
by rewrite elements_lists lists_factors.
Qed.

Lemma wf_wf_factors pt : wf pt → wf_factors (factors pt).
Proof.
case E: (is_mul pt) => wf_pt; last first.
  rewrite factors_Nmul ?E //; apply/wf_factorsP => t /SMS.elem_of_singleton ->.
  by rewrite E.
case: pt E wf_pt => [o|o t|o t1 t2|ps ns|l] // _ wf_pt.
rewrite /wf_factors elements_lists lists_factors //.
by move: wf_pt; rewrite wf_mulE => /andb_True [/andb_True [] ].
Qed.

Lemma mul_aux_Nsingle s :
  negb (single (lists s)) → mul_aux s = PTMul (lists s).1 (lists s).2.
Proof. by rewrite /mul_aux; case: (lists s) => [[|? [|??]] [|??]]. Qed.

Lemma mul_aux_single s t : lists s = ([t], []) → mul_aux s = t.
Proof. by rewrite /mul_aux => ->. Qed.

Lemma single_lists s : single (lists s) → ∃ t, s = {[+ t +]}.
Proof.
case Es: (lists s) => [[|t [|??]] [|??]] // _; exists t.
move: Es; rewrite /lists => - [eP eN]; apply: SMS.sms_eq.
- by rewrite SMS.pos_singleton -(MSet.of_list_elements (SMS.pos s)) eP.
- by rewrite SMS.neg_singleton -(MSet.of_list_elements (SMS.neg s)) eN.
Qed.

Lemma wf_mul_aux s : wf_factors s → wf (mul_aux s).
Proof.
move=> wfs; case Es: (single (lists s)).
  have [t e] := single_lists s ltac:(by rewrite Es); rewrite e in wfs *.
  rewrite (mul_aux_single _ t) ?lists_singleton //.
  by apply: (wf_factors_wf wfs); rewrite SMS.elem_of_singleton.
rewrite mul_aux_Nsingle ?Es // wf_mulE -surjective_pairing.
rewrite Es; apply/andb_True; split; last done.
by apply/andb_True; split; [exact: wfs|exact: wf_lists_lists].
Qed.

Lemma make_lists s :
  SMS.make (MSet.of_list (lists s).1) (MSet.of_list (lists s).2) = s.
Proof. exact: of_lists_lists. Qed.

Lemma mul_auxK s : wf_factors s → factors (mul_aux s) = s.
Proof.
move=> wfs; case Es: (single (lists s)).
  have [t e] := single_lists s ltac:(by rewrite Es); rewrite e in wfs *.
  rewrite (mul_aux_single _ t) ?lists_singleton // factors_Nmul //.
  by apply: (wf_factors_Nmul wfs); rewrite SMS.elem_of_singleton.
by rewrite mul_aux_Nsingle ?Es // factors_PTMul make_lists.
Qed.

Lemma factorsK t : wf t → mul_aux (factors t) = t.
Proof.
case E: (is_mul t) => wf_t; last first.
  by rewrite factors_Nmul ?E // (mul_aux_single _ t) // lists_singleton.
case: t E wf_t => [o|o t|o t1 t2|ps ns|l] // _ wf_t.
rewrite mul_aux_Nsingle (lists_factors _ _ wf_t) //.
by move: wf_t; rewrite wf_mulE => /andb_True [].
Qed.

Lemma wf_bind_factors s : (∀ t, t ∈ s → wf t) → wf_factors (SMS.bind factors s).
Proof.
move=> wfs; apply/wf_factorsP => t /SMS.elem_of_bind [u [u_s t_u]].
have wfu := wf_wf_factors _ (wfs _ u_s).
by split; [apply: wf_factors_wf wfu t_u|apply: wf_factors_Nmul wfu t_u].
Qed.

Lemma wf_mul s : (∀ t, t ∈ s → wf t) → wf (mul s).
Proof. by move=> wfs; rewrite mulE; apply: wf_mul_aux; apply: wf_bind_factors.
Qed.

Lemma bind_factors_wf s : wf_factors s → SMS.bind factors s = s.
Proof.
move=> wfs; rewrite -[RHS]SMS.bind_unit; apply: SMS.bind_ext => t t_s.
by apply: factors_Nmul; apply: wf_factors_Nmul wfs t_s.
Qed.

Lemma mul1 t : wf t → mul {[+ t +]} = t.
Proof. by move=> wf_t; rewrite mulE SMS.bind_singleton factorsK. Qed.

Lemma mul_empty : mul ∅ = PTMul [] [].
Proof. by rewrite mulE SMS.bind_empty. Qed.

Lemma mul_unit_l t : mul {[+ PTMul [] []; t +]} = mul {[+ t +]}.
Proof.
rewrite !mulE SMS.bind_disj_union !SMS.bind_singleton.
by rewrite (_ : factors (PTMul [] []) = ∅) // (left_id ∅ (⊎)).
Qed.

Lemma mul_unit_r t : wf t → mul {[+ t; PTMul [] [] +]} = t.
Proof.
move=> wf_t; rewrite mulE SMS.bind_disj_union !SMS.bind_singleton.
by rewrite (_ : factors (PTMul [] []) = ∅) // (right_id ∅ (⊎)) factorsK.
Qed.

(** Powers and exponentials *)

Lemma mk_exp_neq b e : PTDH [(b, ([e], []))] ≠ b.
Proof. by move=> /(f_equal height) /=; lia. Qed.

Lemma mk_exp_inj b e1 e2 : mk_exp b e1 = mk_exp b e2 → e1 = e2.
Proof.
rewrite /mk_exp.
case: (bool_decide_reflect (e1 = PTMul [] [])) => [->|n1];
  case: (bool_decide_reflect (e2 = PTMul [] [])) => [->|n2] //.
- by move=> E; case: (mk_exp_neq b e2 (eq_sym E)).
- by move=> E; case: (mk_exp_neq b e1 E).
- by case.
Qed.

Lemma base_mk_exp b e : negb (is_exp b) → base (mk_exp b e) = b.
Proof.
rewrite /mk_exp => Nb; case: (bool_decide (e = PTMul [] [])) => //.
exact: base_expN.
Qed.

Lemma expo_mk_exp b e : negb (is_exp b) → expo (mk_exp b e) = e.
Proof.
rewrite /mk_exp => Nb.
case: (bool_decide_reflect (e = PTMul [] [])) => [->|_] //.
exact: expo_expN.
Qed.

Lemma Ngmul_mk_exp b e : negb (is_gmul b) → negb (is_gmul (mk_exp b e)).
Proof. by rewrite /mk_exp; case: (bool_decide (e = PTMul [] [])). Qed.

Lemma wf_mk_exp b e :
  negb (is_gnon_free b) → wf b → wf e → wf (mk_exp b e).
Proof.
move=> Nb wf_b wf_e; rewrite /mk_exp.
case: (bool_decide_reflect (e = PTMul [] [])) => // ne.
by apply/wf_dh_single.
Qed.

Lemma wf_base pt : wf pt → wf (base pt).
Proof. by case: (is_expP pt) => [b e ->|_ -> _] // /wf_dh_single []. Qed.

Lemma base_Nexp pt : wf pt → negb (is_exp (base pt)).
Proof.
case: (is_expP pt) => [b e ->|Nx -> _] // /wf_dh_single [_ [Nb _]].
exact: Ngnf_Nexp.
Qed.

(* There is deliberately no scalar counterpart: a scalar product in a base is
   an atom, so [is_mul (base pt) = is_mul pt] is false. *)
Lemma is_gmul_base pt : wf pt → is_gmul (base pt) = is_gmul pt.
Proof.
case: (is_expP pt) => [b e ->|_ -> _] // /wf_dh_single [_ [Nb _]] /=.
by case: (is_gmul b) (Ngnf_Ngmul _ Nb).
Qed.

Lemma wf_expo pt : wf pt → wf (expo pt).
Proof.
case: (is_expP pt) => [b e ->|_ _ ->]; last by move=> _; exact: wf_one.
by case/wf_dh_single => _ [_ []].
Qed.

Lemma base_Ngnf t : wf t → negb (is_gmul t) → negb (is_gnon_free (base t)).
Proof.
case: (is_expP t) => [b e ->|Nx -> _]; first by case/wf_dh_single => _ [].
move=> _ Ng; rewrite /is_gnon_free.
by case: (is_exp t) Nx; case: (is_gmul t) Ng.
Qed.

Lemma mk_exp_base_expo t : wf t → mk_exp (base t) (expo t) = t.
Proof.
case: (is_expP t) => [b e ->|_ -> ->].
- case/wf_dh_single => _ [_ [_ ne]] /=.
  by rewrite /mk_exp bool_decide_eq_false_2.
- by move=> _; rewrite /mk_exp bool_decide_eq_true_2.
Qed.

(** Grouping factors by base *)

Lemma of_pairsK s : (∀ t, t ∈ s → wf t) → of_pairs (to_pairs s) = s.
Proof.
move=> wfs; rewrite /of_pairs /to_pairs SMS.map_map /=.
by apply: SMS.map_id_ext => t /wfs /mk_exp_base_expo.
Qed.

Lemma to_pairsK P :
  (∀ p, p ∈ P → negb (is_exp p.1)) → to_pairs (of_pairs P) = P.
Proof.
move=> NP; rewrite /of_pairs /to_pairs SMS.map_map.
apply: SMS.map_id_ext => -[b e] /NP /= Nb.
by rewrite base_mk_exp // expo_mk_exp.
Qed.

Lemma to_list_entries m :
  (λ e, (e.1, of_lists e.2)) <$> entries m = FMap.to_list m.
Proof.
rewrite /entries -list_fmap_compose -[RHS]list_fmap_id.
by apply: list_fmap_ext => _ [k s] _ /=; rewrite of_lists_lists.
Qed.

Lemma elem_of_entries m e :
  e ∈ entries m → e.2 = lists (m !!! e.1) ∧ m !!! e.1 ≠ ∅.
Proof.
move=> /list_elem_of_fmap [[k s] [-> /FMap.elem_of_to_list [ms ne]]] /=.
by rewrite ms.
Qed.

Lemma elem_of_entries_2 m k :
  m !!! k ≠ ∅ → (k, lists (m !!! k)) ∈ entries m.
Proof.
move=> ne; apply/list_elem_of_fmap; exists (k, m !!! k); split => //.
exact/FMap.elem_of_to_list.
Qed.

Lemma keys_map_snd {A B} (f : A → B) (l : list (pre_term * A)) :
  FMap.keys ((λ e, (e.1, f e.2)) <$> l) = FMap.keys l.
Proof. by elim: l => //= -[k a] l ->. Qed.

Lemma keys_entries m : FMap.keys (entries m) = FMap.keys (FMap.to_list m).
Proof. exact: keys_map_snd. Qed.

Lemma wf_entries m : FMap.wf ([], []) (entries m).
Proof.
apply: bool_decide_pack; split.
- rewrite keys_entries FMap.keys_fmap; exact: FMap.to_list_sorted.
- apply/list.Forall_forall => e /elem_of_entries [-> ne] /lists_empty_inv.
  exact: ne.
Qed.

Lemma dh_factors_nil : dh_factors [] = ∅.
Proof. done. Qed.

Lemma dh_factors_cons e l :
  dh_factors (e :: l) = SMS.map (mk_exp e.1) (of_lists e.2) ⊎ dh_factors l.
Proof. done. Qed.

Lemma dh_factors_uncurry l :
  dh_factors l =
  of_pairs (SMS.uncurry_list ((λ e, (e.1, of_lists e.2)) <$> l)).
Proof.
elim: l => [|e l IH]; first by rewrite /of_pairs SMS.map_empty.
rewrite dh_factors_cons IH fmap_cons /of_pairs.
by rewrite [SMS.uncurry_list _]/= SMS.map_disj_union SMS.map_map.
Qed.

Lemma dh_factors_entries m : dh_factors (entries m) = of_pairs (SMS.uncurry m).
Proof. by rewrite dh_factors_uncurry to_list_entries. Qed.

Lemma elem_of_dh_factors l t :
  t ∈ dh_factors l → ∃ e x, e ∈ l ∧ x ∈ of_lists e.2 ∧ t = mk_exp e.1 x.
Proof.
elim: l => [|e l IH].
  by rewrite dh_factors_nil SMS.elem_of_count SMS.count_empty.
rewrite dh_factors_cons => /SMS.elem_of_disj_union [].
- move=> /SMS.elem_of_map [x [-> x_e]].
  by exists e, x; split; [left|].
- move=> /IH [e' [x [e'_l [x_e' ->]]]].
  by exists e', x; split; [right|].
Qed.

Lemma gfactors_dh_of m :
  (∀ b, m !!! b ≠ ∅ → negb (is_gmul b)) →
  gfactors (dh_of m) = of_pairs (SMS.uncurry m).
Proof.
move=> Nk; rewrite -dh_factors_entries /dh_of.
case E: (entries m) => [|[b [[|e [|??]] [|??]]] [|??]] //.
have [_ ne] : ([e], []) = lists (m !!! b) ∧ m !!! b ≠ ∅.
  by apply: (elem_of_entries m (b, ([e], []))); rewrite E; left.
rewrite gfactors_Ngmul; last exact: Ngmul_mk_exp (Nk _ ne).
rewrite dh_factors_cons dh_factors_nil of_lists_single SMS.map_singleton.
by rewrite (right_id ∅ (⊎)).
Qed.

Lemma wf_dh_of m :
  (∀ b, m !!! b ≠ ∅ → wf b ∧ negb (is_gnon_free b)) →
  (∀ b t, t ∈ m !!! b → wf t) →
  wf (dh_of m).
Proof.
move=> wfk wfv.
have wfe e : e ∈ entries m → wf_entry e.
  move=> /elem_of_entries [e2 /wfk [wf_b Nb]].
  have wfl t : t ∈ elements (m !!! e.1) → wf t.
    by rewrite SMS.elem_of_elements; apply: wfv.
  rewrite /wf_entry e2; apply/andb_True; split; last exact: wf_lists_lists.
  rewrite !andb_True; split; first split; first by split.
  + apply/forallb_True/list.Forall_forall => t t_in; apply: wfl.
    by rewrite elements_lists elem_of_app; left.
  + apply/forallb_True/list.Forall_forall => t t_in; apply: wfl.
    by rewrite elements_lists elem_of_app; right.
have wf_m : forallb wf_entry (entries m) && FMap.wf ([], []) (entries m).
  apply/andb_True; split; last exact: wf_entries.
  by apply/forallb_True/list.Forall_forall.
rewrite /dh_of.
case E: (entries m) wf_m wfe => [|[b [[|e [|??]] [|??]]] [|??]] wf_m wfe;
  try by rewrite wf_dhE; apply/andb_True.
move: (wfe (b, ([e], [])) ltac:(by left)).
rewrite /wf_entry; cbn [fst snd forallb].
move=> /andb_True [/andb_True [/andb_True [/andb_True [wf_b Nb]]]].
move=> /andb_True [wf_e _] _ _.
exact: wf_mk_exp.
Qed.

#[local] Lemma sms_nonempty (s : SMS.sms pre_term) : s ≠ ∅ → ∃ x, x ∈ s.
Proof.
move=> ne; destruct (elements s) as [|x xs] eqn:E.
  by case: ne; exact: SMS.elements_empty_inv.
by exists x; apply/SMS.elem_of_elements; rewrite E; left.
Qed.

Lemma curry_keys s b :
  SMS.curry (to_pairs s) !!! b ≠ ∅ → ∃ t, t ∈ s ∧ b = base t.
Proof.
move=> /sms_nonempty [v /SMS.elem_of_curry /SMS.elem_of_map [t [[-> _] t_s]]].
by exists t.
Qed.

Lemma curry_values s b v :
  v ∈ SMS.curry (to_pairs s) !!! b → ∃ t, t ∈ s ∧ b = base t ∧ v = expo t.
Proof.
move=> /SMS.elem_of_curry /SMS.elem_of_map [t [[-> ->] t_s]].
by exists t.
Qed.

Lemma gmul_auxK s : wf_gfactors s → gfactors (gmul_aux s) = s.
Proof.
move=> /wf_gfactorsP wfs.
have Nk b : SMS.curry (to_pairs s) !!! b ≠ ∅ → negb (is_gmul b).
  move=> /curry_keys [t [/wfs [wf_t Nt] ->]].
  exact: Ngnf_Ngmul (base_Ngnf _ wf_t Nt).
rewrite /gmul_aux (gfactors_dh_of _ Nk) SMS.curryK of_pairsK //.
by move=> t /wfs [].
Qed.

Lemma wf_gmul_aux s : wf_gfactors s → wf (gmul_aux s).
Proof.
move=> /wf_gfactorsP wfs; apply: wf_dh_of.
- move=> b /curry_keys [t [/wfs [wf_t Nt] ->]].
  by split; [exact: wf_base|exact: base_Ngnf].
- move=> b v /curry_values [t [/wfs [wf_t _] [_ ->]]].
  exact: wf_expo.
Qed.

(* [gmul_aux] adds the factors to the map one at a time. *)
Lemma gmul_auxE s :
  gmul_aux s =
  dh_of (foldr (λ t m, SMS.curry_add (base t) {[+ expo t +]} m)
           (foldr (λ t m, SMS.curry_add (base t) (SMS.inv {[+ expo t +]}) m)
              ∅ (elements (SMS.neg s)))
           (elements (SMS.pos s))).
Proof.
have fold (f : pre_term → SMS.sms pre_term) L (m : dhmap) :
    foldr (λ t m, SMS.curry_add (base t) (f (expo t)) m) m L =
    SMS.curry_list f ((λ t, (base t, expo t)) <$> L) m.
  by elim: L => [//|t L IH] /=; rewrite IH.
rewrite /gmul_aux (fold (λ u, SMS.inv {[+ u +]})) (fold (λ u, {[+ u +]})).
congr dh_of; symmetry.
apply: FMap.lookup_inj => k; apply: SMS.count_inj => v.
have cp u : SMS.count v {[+ u +]} = (1 * Z.b2z (bool_decide (v = u)))%Z.
  by rewrite SMS.count_singleton; lia.
have cn u :
    SMS.count v (SMS.inv {[+ u +]}) = (-1 * Z.b2z (bool_decide (v = u)))%Z.
  by rewrite SMS.count_inv SMS.count_singleton; lia.
rewrite (SMS.count_curry_list _ _ _ _ _ _ cp).
rewrite (SMS.count_curry_list _ _ _ _ _ _ cn) FMap.lookup_empty.
rewrite SMS.count_empty SMS.count_curry /to_pairs SMS.map_pos_neg.
rewrite SMS.count_make /MSet.map !MSet.count_of_list; lia.
Qed.

Lemma gfactors_PTDH l : wf (PTDH l) → gfactors (PTDH l) = dh_factors l.
Proof.
case: l => [|[b [[|e [|??]] [|??]]] [|??]] //.
case/wf_dh_single => _ [_ [_ ne]].
rewrite dh_factors_cons dh_factors_nil of_lists_single SMS.map_singleton.
by rewrite (right_id ∅ (⊎)) /mk_exp bool_decide_eq_false_2.
Qed.

Lemma entries_of_wf l : wf (PTDH l) → ∃ m, entries m = l.
Proof.
rewrite wf_dhE => /andb_True [/andb_True [/forallb_True Hl wf_l] _].
move/bool_decide_unpack: wf_l => [ss vs].
have wfA e : e ∈ l → wf_lists e.2.
  by move=> /(proj1 (list.Forall_forall _ _) Hl) /andb_True [].
(* [have] would generalize the [FMap list] instance. *)
assert (wfL : FMap.wf ∅ ((λ e, (e.1, of_lists e.2)) <$> l)).
  apply: bool_decide_pack; split.
  - by rewrite keys_map_snd.
  - apply/list.Forall_forall => _ /list_elem_of_fmap [e [-> e_l]] /= e0.
    have := proj1 (list.Forall_forall _ _) vs e e_l.
    by rewrite /= -(lists_of_lists _ (wfA _ e_l)) e0.
exists (FMap.mk _ wfL).
rewrite /entries /FMap.to_list /= -list_fmap_compose -[RHS]list_fmap_id.
apply/Forall_fmap_ext/list.Forall_forall => e e_l /=.
by rewrite (lists_of_lists _ (wfA _ e_l)) -surjective_pairing.
Qed.

Lemma gfactorsK t : wf t → gmul_aux (gfactors t) = t.
Proof.
case Eg: (is_gmul t) => wf_t; last first.
  have ne : ({[+ expo t +]} : SMS.sms pre_term) ≠ ∅.
    move=> /(f_equal (SMS.count (expo t))).
    by rewrite SMS.count_singleton SMS.count_empty bool_decide_eq_true_2.
  rewrite gfactors_Ngmul ?Eg // /gmul_aux /to_pairs SMS.map_singleton.
  rewrite SMS.curry_singleton /dh_of /entries FMap.to_list_singleton //=.
  exact: mk_exp_base_expo.
case: t Eg wf_t => // l Eg wf_l.
have [m Em] := entries_of_wf l wf_l.
have Nk p : p ∈ SMS.uncurry m → negb (is_exp p.1).
  case: p => k v /SMS.elem_of_uncurry v_k /=.
  have ne : m !!! k ≠ ∅.
    move=> e; move: v_k; rewrite e SMS.elem_of_count SMS.count_empty.
    by [].
  move: (elem_of_entries_2 m k ne); rewrite Em.
  move: wf_l; rewrite wf_dhE => /andb_True [/andb_True [/forallb_True Hl _] _].
  move=> /(proj1 (list.Forall_forall _ _) Hl).
  rewrite /wf_entry /= !andb_True => -[[[[_ Nb] _] _] _].
  exact: Ngnf_Nexp.
rewrite gfactors_PTDH // -Em dh_factors_entries /gmul_aux to_pairsK //.
rewrite SMS.uncurryK /dh_of Em.
by case: l Eg {wf_l Em Nk} => [|[b [[|e [|??]] [|??]]] [|??]].
Qed.

Lemma wf_dh_factors l : wf (PTDH l) → wf_gfactors (dh_factors l).
Proof.
rewrite wf_dhE => /andb_True [/andb_True [/forallb_True Hl _] _].
apply/wf_gfactorsP => t /elem_of_dh_factors [e [x [e_l [x_e ->]]]].
move: (proj1 (list.Forall_forall _ _) Hl e e_l).
rewrite /wf_entry !andb_True => -[[[[wf_b Nb] wf_ps] wf_ns] _].
have wf_x : wf x.
  move: x_e; rewrite /of_lists => /SMS.elem_of_make.
  rewrite !MSet.elem_of_of_list.
  case=> x_in; [move/forallb_True/list.Forall_forall: wf_ps
               |move/forallb_True/list.Forall_forall: wf_ns]; by apply.
split; [exact: wf_mk_exp|exact: Ngmul_mk_exp (Ngnf_Ngmul _ Nb)].
Qed.

(** The factors of a Diffie-Hellman pre-term, listed entry by entry. *)
Definition dh_elements
    (l : list (pre_term * (list pre_term * list pre_term))) :=
  foldr (λ e ts, (mk_exp e.1 <$> e.2.1 ++ e.2.2) ++ ts) [] l.

Lemma elem_of_dh_elements l x :
  x ∈ dh_elements l ↔ ∃ e p, e ∈ l ∧ p ∈ e.2.1 ++ e.2.2 ∧ x = mk_exp e.1 p.
Proof.
elim: l => [|e l IH] /=.
  by split=> [/elem_of_nil []|[? [? [/elem_of_nil []]]]].
rewrite elem_of_app IH list_elem_of_fmap; split.
- case=> [[p [-> p_in]]|[e' [p [e'_l [p_in ->]]]]].
  + by exists e, p; split; [left|].
  + by exists e', p; split; [right|].
- case=> [e' [p [/elem_of_cons [<-|e'_l] [p_in ->]]]].
  + by left; exists p.
  + by right; exists e', p.
Qed.

Lemma elements_dh_factors l :
  Forall (λ e, wf_entry e) l → StronglySorted lexico (FMap.keys l) →
  elements (dh_factors l) ≡ₚ dh_elements l.
Proof.
elim: l => [|[b A] l IH]; first by constructor.
move=> /Forall_cons_iff [wf_e wf_l] /StronglySorted_cons [lb sl].
move: wf_e => /andb_True [/andb_True [/andb_True [/andb_True [_ Nb] _] _] wfA].
have Nx := Ngnf_Nexp _ Nb.
have base_l t : t ∈ dh_factors l → lexico b (base t).
  move=> /elem_of_dh_factors [e [x [e_l [_ ->]]]].
  have Ne : negb (is_exp e.1).
    apply: Ngnf_Nexp.
    move: (proj1 (list.Forall_forall _ _) wf_l e e_l).
    by rewrite /wf_entry !andb_True => -[[[[_ ?] _] _] _].
  rewrite base_mk_exp //; case: e e_l {Ne} => k A' e_l /=.
  exact: FMap.lexico_keys lb e_l.
have base_b t : t ∈ SMS.map (mk_exp b) (of_lists A) → base t = b.
  by move=> /SMS.elem_of_map [x [-> _]]; rewrite base_mk_exp.
have disj t : t ∈ SMS.map (mk_exp b) (of_lists A) → t ∈ dh_factors l → False.
  move=> /base_b eb /base_l; rewrite eb.
  exact: irreflexivity.
assert (d1 : SMS.pos (SMS.map (mk_exp b) (of_lists A)) ##
              SMS.neg (dh_factors l)).
  move=> t t1 t2; apply: (disj t).
  - exact: SMS.elem_of_pos t1.
  - exact: SMS.elem_of_neg t2.
assert (d2 : SMS.neg (SMS.map (mk_exp b) (of_lists A)) ##
              SMS.pos (dh_factors l)).
  move=> t t1 t2; apply: (disj t).
  - exact: SMS.elem_of_neg t1.
  - exact: SMS.elem_of_pos t2.
rewrite dh_factors_cons (SMS.elements_disj_union _ _ d1 d2) IH //.
apply: Permutation_app_tail.
rewrite SMS.elements_map_inj; last exact: mk_exp_inj.
by rewrite elements_lists lists_of_lists.
Qed.

Lemma elements_gfactors pt :
  wf pt →
  elements (gfactors pt) ≡ₚ if pt is PTDH l then dh_elements l else [pt].
Proof.
case: pt => [o|o t|o t1 t2|ps ns|l] wf_pt;
  try by rewrite gfactors_Ngmul // SMS.elements_singleton.
rewrite gfactors_PTDH //.
move: wf_pt; rewrite wf_dhE => /andb_True [/andb_True [/forallb_True Hl]].
move=> /bool_decide_unpack [ss _] _.
exact: elements_dh_factors.
Qed.

Lemma wf_bind_gfactors s :
  (∀ t, t ∈ s → wf t) → wf_gfactors (SMS.bind gfactors s).
Proof.
move=> wfs; apply/wf_gfactorsP => t /SMS.elem_of_bind [u [u_s t_u]].
have wfu : wf_gfactors (gfactors u).
  case Eg: (is_gmul u).
    case: u Eg u_s t_u => // l _ u_s _.
    rewrite gfactors_PTDH; last exact: wfs _ u_s.
    exact: wf_dh_factors (wfs _ u_s).
  rewrite gfactors_Ngmul ?Eg //.
  by apply/wf_gfactorsP => v /SMS.elem_of_singleton ->; rewrite Eg; split;
    [exact: wfs _ u_s|].
by split; [apply: wf_gfactors_wf wfu t_u|apply: wf_gfactors_Ngmul wfu t_u].
Qed.

Lemma wf_wf_gfactors pt : wf pt → wf_gfactors (gfactors pt).
Proof.
move=> wf_pt; rewrite -[gfactors pt]SMS.bind_singleton.
by apply: wf_bind_gfactors => t /SMS.elem_of_singleton ->.
Qed.

Lemma wf_gmul s : (∀ t, t ∈ s → wf t) → wf (gmul s).
Proof. by move=> wfs; apply: wf_gmul_aux; apply: wf_bind_gfactors. Qed.

Lemma bind_gfactors_wf s : wf_gfactors s → SMS.bind gfactors s = s.
Proof.
move=> wfs; rewrite -[RHS]SMS.bind_unit; apply: SMS.bind_ext => t t_s.
by apply: gfactors_Ngmul; apply: wf_gfactors_Ngmul wfs t_s.
Qed.

Lemma gmul1 t : wf t → gmul {[+ t +]} = t.
Proof. by move=> wf_t; rewrite /gmul SMS.bind_singleton gfactorsK. Qed.

Lemma wf_exp_aux t e : wf t → negb (is_gmul t) → wf e → wf (exp_aux t e).
Proof.
move=> wf_t Nm wf_e; apply: wf_mk_exp.
- exact: base_Ngnf.
- exact: wf_base.
- apply: wf_mul => u /SMS.elem_of_disj_union.
  by case=> /SMS.elem_of_singleton -> //; exact: wf_expo.
Qed.

Lemma exp_aux_Ngmul t e :
  wf t → negb (is_gmul t) → negb (is_gmul (exp_aux t e)).
Proof.
move=> wf_t Nm; apply: Ngmul_mk_exp.
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

Lemma exp_atom b e :
  wf b → negb (is_gnon_free b) → wf e → exp b e = mk_exp b e.
Proof.
move=> wf_b Nb wf_e; rewrite exp_Ngmul //; last exact: Ngnf_Ngmul.
rewrite /exp_aux (base_expN _ (Ngnf_Nexp _ Nb)).
by rewrite (expo_expN _ (Ngnf_Nexp _ Nb)) mul_unit_l mul1.
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

Lemma foldr_Forall_entries (P : pre_term → Prop) l :
  seq.foldr (λ e (R : Type),
      (P e.1 * seq.foldr (λ t (R : Type), (P t * R)%type) unit e.2.1
       * seq.foldr (λ t (R : Type), (P t * R)%type) unit e.2.2 * R)%type)
    unit l →
  Forall (λ e, P e.1 ∧ Forall P e.2.1 ∧ Forall P e.2.2) l.
Proof.
elim: l => [|e l IH] /= H; first by constructor.
case: H => [[[He Hps] Hns] Hl]; constructor; last exact: IH.
by split; [|split; apply: foldr_Forall].
Qed.

Lemma wf_normalize pt : wf (normalize pt).
Proof.
elim: pt => //=.
- by move=> o t1 IH1 t2 IH2; rewrite andb_True; split.
- move=> ps /(foldr_Forall _ _) IHps ns /(foldr_Forall _ _) IHns.
  apply: wf_mul => t /SMS.elem_of_make.
  rewrite !MSet.elem_of_of_list -elem_of_app -fmap_app
    => /list_elem_of_fmap [u [-> u_in]].
  by move: u u_in; apply/list.Forall_forall/Forall_app.
- move=> l /(foldr_Forall_entries _ _) IHl; apply: wf_gmul.
  elim: l IHl => [|e l IH] /=.
    by move=> _ t; rewrite SMS.elem_of_count SMS.count_empty.
  move=> /Forall_cons_iff [[IHb [IHps IHns]] /IH {}IH] t.
  case/SMS.elem_of_disj_union => [|/IH //].
  move=> /SMS.elem_of_map [x [-> /SMS.elem_of_make]].
  rewrite !MSet.elem_of_of_list => x_in.
  apply: wf_exp => //.
  case: x_in => /list_elem_of_fmap [u [-> u_in]].
  + by move/list.Forall_forall: IHps; apply.
  + by move/list.Forall_forall: IHns; apply.
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
            |ps /(foldr_Forall _ _) IHps ns /(foldr_Forall _ _) IHns
            |l /(foldr_Forall_entries _ _) IHl].
- by [].
- by move=> /= wf_t; rewrite IH.
- by rewrite /= andb_True => - [/IH1 -> /IH2 ->].
- move=> wf_pt; have := wf_pt; rewrite wf_mulE /=.
  move=> /andb_True [/andb_True [/forallb_True/list.Forall_forall wfA _] _].
  have wf_in t : t ∈ ps ++ ns → wf t by move=> /wfA /andb_True [].
  rewrite !fmapE //; try (apply/list.Forall_forall => t t_in; apply: wf_in;
                           rewrite elem_of_app; by [left|right]).
  rewrite mulE bind_factors_wf; first exact: (factorsK (PTMul ps ns)).
  exact: (wf_wf_factors (PTMul ps ns)).
- move=> wf_pt /=.
  have := wf_pt; rewrite wf_dhE.
  move=> /andb_True [/andb_True [/forallb_True Hl _] _].
  set S := foldr _ _ l.
  have -> : S = dh_factors l.
    rewrite /S; elim: (l) IHl Hl {wf_pt S} => [|e l' IH] //.
    move=> /Forall_cons_iff [[IHb [IHps IHns]] /IH {}IH].
    move=> /Forall_cons_iff [wf_e /IH {}IH].
    rewrite [foldr _ _ _]/= dh_factors_cons IH.
    move: wf_e; rewrite /wf_entry !andb_True => -[[[[wf_b Nb] wf_ps] wf_ns] _].
    move/forallb_True: wf_ps => wf_ps; move/forallb_True: wf_ns => wf_ns.
    rewrite (IHb wf_b) (fmapE _ IHps wf_ps) (fmapE _ IHns wf_ns).
    congr (_ ⊎ _).
    apply: SMS.map_ext => x /SMS.elem_of_make; rewrite !MSet.elem_of_of_list.
    move=> x_in; apply: exp_atom => //.
    by case: x_in; move: (x); apply/list.Forall_forall.
  rewrite /gmul bind_gfactors_wf; last exact: wf_dh_factors.
  by rewrite -gfactors_PTDH // gfactorsK.
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
move=> wf_b; case: (is_expP b) => [c d eb|Nx -> ->]; last exact: exp_unit.
have Ng : negb (is_gmul b) by rewrite eb.
rewrite exp_atom ?mk_exp_base_expo //.
- exact: wf_base.
- exact: base_Ngnf.
- exact: wf_expo.
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
  expo (exp b e) = mul {[+ expo b; e +]}.
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
