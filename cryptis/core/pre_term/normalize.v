(** Pre-term normalization
    ======================

    This file defines a normalization function on pre-terms.  Pre-terms carry
    two algebraic structures:

    - the exponents [PTMod], rational functions with integer coefficients over
      atoms ([Frac.frac]);
    - the Diffie-Hellman group (a symbolic model of a prime-order
      elliptic-curve group), whose elements [PTDH] map bases to logarithms.

    An exponent [PTMod F] stores the numerator and the denominator of a
    rational function in the canonical form of [Frac] ([lists], [canonical]):
    each polynomial is the sorted lists of its positive and of its negative
    monomials, and each monomial the sorted list of its atoms.  Atoms are
    pre-terms other than exponents, and a lone atom stands for itself
    ([mod_aux]).  The exponents form a field, with [inv 0 = 0].

    A Diffie-Hellman pre-term [PTDH l] denotes the product, over the entries
    [(b, F)] of [l], of the powers [b ^ F]: [l] lists each base once, sorted,
    with its logarithm, a nonzero exponent.  Writing [1G := PTDH []],
    [g ^ x := PTDH [(g, x)]], [u ⋅ v] for the product of [u] and [v] and
    [u^-1] for the inverse of [u], two pre-terms have the same normal form if
    and only if they are equal according to the field laws for exponents, the
    group laws for [⋅] and the following equations:

    - [(g ^ a) ^ b = g ^ (a * b)]
    - [g ^ a ⋅ g ^ b = g ^ (a + b)]
    - [g ^ 1 = g]
    - [(u ⋅ v) ^ x = u^x ⋅ v^x]

    Bases are group atoms: neither group products nor exponentials.  A single
    base with logarithm [1] is the base itself.  An exponential ([is_exp]) is
    a single base whose logarithm has a single monomial with coefficient [1]
    as numerator; every other group element is a product ([is_gmul]) of the
    exponentials [gfactors], one for each monomial of each numerator.

    The predicate [wf : pre_term -> bool] characterizes normal forms.  We have
    the following properties:

   - [normalize_wf : wf t -> normalize t = t]
   - [wf_normalize : wf (normalize t)]
   - [normalize_idem : normalize (normalize t) = normalize t]

*)

From stdpp Require Import sorting list numbers.
From cryptis Require Import lib.
From cryptis.lib Require Import list_sort fmap mset sms poly poly_gcd frac.
From mathcomp Require Import ssreflect.
From Stdlib Require Import Lia.
From cryptis.core.pre_term Require Export base with_stdpp.

Module PreTerm.
Import base.PreTerm.

Local Abbreviation poly := (Poly.poly pre_term).
Local Abbreviation frac := (Frac.frac pre_term).

Fixpoint height (pt : pre_term) : nat :=
  let hm (ms : monos) := max_list_with (max_list_with height) ms in
  let hf (F : frac_lists) :=
    Nat.max (Nat.max (hm F.1.1) (hm F.1.2)) (Nat.max (hm F.2.1) (hm F.2.2)) in
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (height pt)
  | PT2 _ pt1 pt2 => S (Nat.max (height pt1) (height pt2))
  | PTMod F => S (hf F)
  | PTDH l => S (max_list_with (λ e, Nat.max (height e.1) (hf e.2)) l)
  end.

(** ** Recognizers *)

(* [is_exp] and [is_gmul] are exclusive: [public] recurses on the factors of a
   group product, and the only factor of an exponential is itself. *)
Definition is_exp pt :=
  if pt is PTDH [(_, (([_], []), _))] then true else false.
Definition is_mod pt := if pt is PTMod _ then true else false.
Definition is_gmul pt :=
  match pt with
  | PTDH [(_, (([_], []), _))] => false
  | PTDH _ => true
  | _ => false
  end.
Definition is_nonce pt := if pt is PT0 (O0Nonce _) then true else false.

(** [is_non_free] collects the heads that [term] represents indirectly, and is
    what [core/term/base.v] uses for [TNonFree].  [is_gnon_free] collects the
    heads a normal-form base may not have, and is what [wf] uses: an exponent
    in a base is an atom, since [exp] does not distribute over it. *)
Definition is_non_free pt := is_exp pt || is_mod pt || is_gmul pt.

Definition is_gnon_free pt := is_exp pt || is_gmul pt.

Lemma Nnf_Nexp pt : negb (is_non_free pt) → negb (is_exp pt).
Proof.
by rewrite /is_non_free; case: (is_exp pt); case: (is_mod pt);
  case: (is_gmul pt).
Qed.

Lemma Nnf_Nmod pt : negb (is_non_free pt) → negb (is_mod pt).
Proof.
by rewrite /is_non_free; case: (is_exp pt); case: (is_mod pt);
  case: (is_gmul pt).
Qed.

Lemma Nnf_Ngmul pt : negb (is_non_free pt) → negb (is_gmul pt).
Proof.
by rewrite /is_non_free; case: (is_exp pt); case: (is_mod pt);
  case: (is_gmul pt).
Qed.

Lemma Nnf_Ngnf pt : negb (is_non_free pt) → negb (is_gnon_free pt).
Proof.
by rewrite /is_non_free /is_gnon_free; case: (is_exp pt); case: (is_mod pt);
  case: (is_gmul pt).
Qed.

Lemma Ngnf_Nexp pt : negb (is_gnon_free pt) → negb (is_exp pt).
Proof. by rewrite /is_gnon_free; case: (is_exp pt); case: (is_gmul pt). Qed.

Lemma Ngnf_Ngmul pt : negb (is_gnon_free pt) → negb (is_gmul pt).
Proof. by rewrite /is_gnon_free; case: (is_exp pt); case: (is_gmul pt). Qed.

Lemma is_non_free_dh l : is_non_free (PTDH l).
Proof. by case: l => [|[b [[[|m [|??]] [|??]] d]] [|??]]. Qed.

Lemma is_exp_Ngmul pt : is_exp pt → negb (is_gmul pt).
Proof. by case: pt => // -[|[b [[[|m [|??]] [|??]] d]] [|??]]. Qed.

Lemma is_gmul_Nexp pt : is_gmul pt → negb (is_exp pt).
Proof. by case: pt => // -[|[b [[[|m [|??]] [|??]] d]] [|??]]. Qed.

Lemma is_exp_Nmod pt : is_exp pt → negb (is_mod pt).
Proof. by case: pt. Qed.

Lemma is_mod_Ngmul pt : is_mod pt → negb (is_gmul pt).
Proof. by case: pt. Qed.

(** ** Exponents

    A polynomial is stored as the lists of its positive and of its negative
    monomials ([poly_lists_of]), and a fraction as the lists of its numerator
    and of its denominator ([lists]).  These lists are [canonical]. *)

Definition poly_lists_of (p : poly) : poly_lists :=
  (MSet.car <$> elements (SMS.pos (Poly.car p)),
   MSet.car <$> elements (SMS.neg (Poly.car p))).

Definition poly_of_lists (A : poly_lists) : poly :=
  Poly.mk (SMS.make (MSet.of_list (MSet.of_list <$> A.1))
                    (MSet.of_list (MSet.of_list <$> A.2))).

Definition lists (r : frac) : frac_lists :=
  (poly_lists_of (Frac.num r), poly_lists_of (Frac.den r)).

Definition of_lists (F : frac_lists) : frac :=
  Frac.make (poly_of_lists F.1) (poly_of_lists F.2).

Definition canonical (F : frac_lists) : bool :=
  bool_decide (lists (of_lists F) = F).

Definition one_lists : frac_lists := (([[]], []), ([[]], [])).
Definition zero_lists : frac_lists := (([], []), ([[]], [])).

Definition one := PTMod one_lists.

(** A lone atom [x] stands for itself rather than for [x / 1]. *)
Definition lone_atom (F : frac_lists) : option pre_term :=
  if F is (([[x]], []), ([[]], [])) then Some x else None.

Definition lone (F : frac_lists) : bool :=
  if lone_atom F is Some _ then true else false.

Definition mod_of_lists (F : frac_lists) : pre_term :=
  if lone_atom F is Some x then x else PTMod F.

Definition mod_aux (r : frac) : pre_term := mod_of_lists (lists r).

Definition frac_of pt : frac :=
  if pt is PTMod F then of_lists F else Frac.of_poly (Poly.var pt).

(** [all_atoms P F]: every atom of [F] satisfies [P]. *)
Definition all_atoms (P : pre_term → bool) (F : frac_lists) : bool :=
  forallb (forallb P) F.1.1 && forallb (forallb P) F.1.2 &&
  forallb (forallb P) F.2.1 && forallb (forallb P) F.2.2.

Definition map_lists (f : pre_term → pre_term) (F : frac_lists) : frac_lists :=
  ((map (map f) F.1.1, map (map f) F.1.2),
   (map (map f) F.2.1, map (map f) F.2.2)).

(** [modf r] evaluates a fraction whose atoms may be exponents. *)
Definition modf (r : frac) : pre_term := mod_aux (Frac.bind frac_of r).

(** ** Diffie-Hellman terms

    A group element is a finite map from bases to logarithms ([dh_map]).
    [gmul] adds the maps of a signed multiset of group elements, and [exp]
    multiplies every logarithm; [dh_of] turns a map back into a pre-term. *)

Definition dhmap := FMap.fmap pre_term frac Frac.zero.

Definition mk_exp b (r : frac) : pre_term :=
  if bool_decide (r = Frac.one) then b else PTDH [(b, lists r)].

Definition entries (m : dhmap) : list entry :=
  (λ p, (p.1, lists p.2)) <$> FMap.to_list m.

Definition dh_of (m : dhmap) : pre_term :=
  if FMap.to_list m is [(b, r)] then mk_exp b r else PTDH (entries m).

Definition of_entries (l : list entry) : dhmap :=
  foldr (λ e m, <[e.1 := of_lists e.2]> m) ∅ l.

Definition dh_map pt : dhmap :=
  if pt is PTDH l then of_entries l else {[pt := Frac.one]}.

Definition dh_add (m1 m2 : dhmap) : dhmap :=
  FMap.cast (left_id Frac.zero Frac.add Frac.zero) (FMap.merge Frac.add m1 m2).

Definition dh_opp (m : dhmap) : dhmap :=
  FMap.cast Frac.opp_zero (FMap.map Frac.opp m).

Definition dh_scale (r : frac) (m : dhmap) : dhmap :=
  FMap.cast (Frac.mul_zero_l r) (FMap.map (λ f, Frac.mul f r) m).

Definition dh_sum (s : SMS.sms pre_term) : dhmap :=
  foldr (λ t m, dh_add (dh_map t) m)
    (foldr (λ t m, dh_add (dh_opp (dh_map t)) m) ∅ (elements (SMS.neg s)))
    (elements (SMS.pos s)).

Definition gmul (s : SMS.sms pre_term) : pre_term := dh_of (dh_sum s).

Definition exp_frac b (r : frac) : pre_term := dh_of (dh_scale r (dh_map b)).

Definition exp b e : pre_term := exp_frac b (frac_of e).

(** The factors of a logarithm [p / q] are the fractions [n / q] for the
    monomials [n] of [p], each normalized to a positive numerator. *)
Definition exp_factor b (q : poly) (n : MSet.mset pre_term) :
    SMS.sms pre_term :=
  let r := Frac.make (Poly.mono n) q in
  if Poly.first_neg (Frac.num r) then SMS.inv {[+ mk_exp b (Frac.opp r) +]}
  else {[+ mk_exp b r +]}.

Definition dh_factors (m : dhmap) : SMS.sms pre_term :=
  foldr (λ p s, SMS.bind (exp_factor p.1 (Frac.den p.2))
                         (Poly.car (Frac.num p.2)) ⊎ s)
    ∅ (FMap.to_list m).

Definition gfactors pt : SMS.sms pre_term :=
  if is_exp pt then {[+ pt +]}
  else if pt is PTDH _ then dh_factors (dh_map pt) else {[+ pt +]}.

Definition base pt :=
  if pt is PTDH [(b, (([_], []), _))] then b else pt.

Definition expo pt :=
  if pt is PTDH [(_, (([m], []), d))] then mod_of_lists (([m], []), d) else one.

Fixpoint normalize pt :=
  match pt with
  | PT0 o => PT0 o
  | PT1 o t => PT1 o (normalize t)
  | PT2 o t1 t2 => PT2 o (normalize t1) (normalize t2)
  | PTMod F => modf (of_lists (map_lists normalize F))
  | PTDH l =>
    gmul (foldr (λ e s,
      {[+ exp_frac (normalize e.1)
            (Frac.bind frac_of (of_lists (map_lists normalize e.2))) +]}
      ⊎ s) ∅ l)
  end.

Definition trivial_dh (l : list entry) :=
  if l is [(_, F)] then bool_decide (F = one_lists) else false.

Fixpoint wf (pt : pre_term) : bool :=
  match pt with
  | PT0 _ => true
  | PT1 _ pt => wf pt
  | PT2 _ pt1 pt2 => wf pt1 && wf pt2
  | PTMod F =>
    all_atoms (λ x, wf x && negb (is_mod x)) F && canonical F && negb (lone F)
  | PTDH l =>
    forallb (λ e, wf e.1 && negb (is_gnon_free e.1)
                  && all_atoms (λ x, wf x && negb (is_mod x)) e.2
                  && canonical e.2) l
    && FMap.wf zero_lists l && negb (trivial_dh l)
  end.


(** ** Lists *)

Lemma poly_of_lists_of p : poly_of_lists (poly_lists_of p) = p.
Proof.
case: p => s; rewrite /poly_of_lists /poly_lists_of /=; congr Poly.mk.
rewrite -!list_fmap_compose.
assert (E : ∀ X : MSet.mset (MSet.mset pre_term),
  MSet.of_list ((MSet.of_list ∘ MSet.car) <$> elements X) = X).
  move=> X; rewrite -[X in MSet.of_list _ = X]MSet.of_list_elements.
  congr MSet.of_list; rewrite -[RHS]list_fmap_id.
  by apply: list_fmap_ext => i m _ /=; apply: MSet.of_list_elements.
by rewrite !E SMS.make_pos_neg.
Qed.

Lemma of_lists_lists r : of_lists (lists r) = r.
Proof. by rewrite /of_lists /lists /= !poly_of_lists_of Frac.make_num_den. Qed.

Lemma canonical_lists r : canonical (lists r).
Proof. by rewrite /canonical of_lists_lists bool_decide_eq_true_2. Qed.

Lemma lists_of_lists F : canonical F → lists (of_lists F) = F.
Proof. exact: bool_decide_unpack. Qed.

Lemma lists_inj r1 r2 : lists r1 = lists r2 → r1 = r2.
Proof. by move=> e; rewrite -(of_lists_lists r1) e of_lists_lists. Qed.

Lemma poly_lists_mono m : poly_lists_of (Poly.mono m) = ([MSet.car m], []).
Proof.
rewrite /poly_lists_of Poly.car_mono SMS.pos_singleton SMS.neg_singleton.
by rewrite MSet.elements_singleton MSet.elements_empty.
Qed.

Lemma poly_lists_zero : poly_lists_of Poly.zero = ([], []).
Proof.
rewrite /poly_lists_of Poly.car_zero SMS.pos_empty SMS.neg_empty.
by rewrite MSet.elements_empty.
Qed.

Lemma lists_var x :
  lists (Frac.of_poly (Poly.var x)) = (([[x]], []), ([[]], [])).
Proof.
rewrite /lists Frac.num_of_poly Frac.den_of_poly Poly.varE Poly.oneE.
by rewrite !poly_lists_mono MSet.car_singleton MSet.car_empty.
Qed.

Lemma lists_one : lists Frac.one = one_lists.
Proof.
rewrite /lists Frac.num_one Frac.den_one Poly.oneE.
by rewrite !poly_lists_mono MSet.car_empty.
Qed.

Lemma lists_zero : lists Frac.zero = zero_lists.
Proof.
rewrite /lists Frac.num_zero Frac.den_zero Poly.oneE.
by rewrite poly_lists_mono poly_lists_zero MSet.car_empty.
Qed.

Lemma of_lists_var x :
  of_lists (([[x]], []), ([[]], [])) = Frac.of_poly (Poly.var x).
Proof. by rewrite -lists_var of_lists_lists. Qed.

Lemma lone_atom_Some F x :
  lone_atom F = Some x ↔ F = (([[x]], []), ([[]], [])).
Proof.
split; last by move=> ->.
rewrite /lone_atom; repeat case_match; congruence.
Qed.

Lemma lone_atom_None F : lone_atom F = None → mod_of_lists F = PTMod F.
Proof. by rewrite /mod_of_lists => ->. Qed.

Lemma lone_lists_var x : lone_atom (lists (Frac.of_poly (Poly.var x))) = Some x.
Proof. by rewrite lists_var. Qed.

(** ** Exponents *)

(** [atoms_all P r]: every atom of [r] satisfies [P]. *)
Definition atoms_all (P : pre_term → Prop) (r : frac) : Prop :=
  ∀ m x, m ∈ Poly.car (Frac.num r) ∨ m ∈ Poly.car (Frac.den r) → x ∈ m → P x.

Lemma all_atoms_lists (P : pre_term → bool) r :
  all_atoms P (lists r) ↔ atoms_all P r.
Proof.
have M (s : SMS.sms (MSet.mset pre_term)) :
    forallb (forallb P) (MSet.car <$> elements (SMS.pos s)) &&
    forallb (forallb P) (MSet.car <$> elements (SMS.neg s)) ↔
    ∀ m x, m ∈ s → x ∈ m → P x.
  rewrite andb_True !forallb_True !Forall_fmap !list.Forall_forall.
  split.
  - move=> [hp hn] m x /SMS.elem_of_pos_neg [mp|mn] xm.
    + have := hp m (proj2 (MSet.elem_of_elements _ _) mp).
      by move=> /forallb_True/list.Forall_forall; apply.
    + have := hn m (proj2 (MSet.elem_of_elements _ _) mn).
      by move=> /forallb_True/list.Forall_forall; apply.
  - move=> h; split=> m /MSet.elem_of_elements mX /=;
      apply/forallb_True/list.Forall_forall => x xm.
    + by apply: (h m x) => //; apply/SMS.elem_of_pos_neg; left.
    + by apply: (h m x) => //; apply/SMS.elem_of_pos_neg; right.
rewrite /all_atoms /lists /poly_lists_of /=.
rewrite -andb_assoc !andb_True -!(andb_True (forallb _ _)).
rewrite (M (Poly.car (Frac.num r))) (M (Poly.car (Frac.den r))) /atoms_all.
naive_solver.
Qed.

Lemma frac_of_Nmod pt :
  negb (is_mod pt) → frac_of pt = Frac.of_poly (Poly.var pt).
Proof. by case: pt. Qed.

Lemma car_num_var x :
  Poly.car (Frac.num (Frac.of_poly (Poly.var x))) = {[+ {[+ x +]} +]}.
Proof. by rewrite Frac.num_of_poly Poly.varE Poly.car_mono. Qed.

Lemma car_den_of_poly p :
  Poly.car (Frac.den (Frac.of_poly p)) = {[+ ∅ +]}.
Proof. by rewrite Frac.den_of_poly Poly.oneE Poly.car_mono. Qed.

Lemma atoms_all_var (P : pre_term → Prop) x :
  P x → atoms_all P (Frac.of_poly (Poly.var x)).
Proof.
move=> Px m y; rewrite car_num_var car_den_of_poly.
move=> [/SMS.elem_of_singleton ->|/SMS.elem_of_singleton ->].
- by move=> /MSet.elem_of_singleton ->.
- by move=> ym; case: (MSet.not_elem_of_empty y).
Qed.

Lemma frac_of_mod_aux r :
  atoms_all (λ x, negb (is_mod x)) r → frac_of (mod_aux r) = r.
Proof.
rewrite /mod_aux /mod_of_lists => h.
case E: (lone_atom (lists r)) => [x|]; last by rewrite /= of_lists_lists.
move/lone_atom_Some: E => E.
have Er : r = Frac.of_poly (Poly.var x).
  by apply: lists_inj; rewrite lists_var.
subst r; apply: frac_of_Nmod; apply: (h {[+ x +]} x).
- by left; rewrite car_num_var; apply/SMS.elem_of_singleton.
- exact/MSet.elem_of_singleton.
Qed.


(** *** Atoms of fractions *)

Definition frac_vars (r : frac) : list pre_term :=
  Poly.vars (Frac.num r) ++ Poly.vars (Frac.den r).

Lemma atoms_all_vars (P : pre_term → Prop) r :
  atoms_all P r ↔ ∀ x, x ∈ frac_vars r → P x.
Proof.
rewrite /atoms_all /frac_vars; split.
- move=> h x /elem_of_app
    [/Poly.elem_of_vars [m [mr xm]]|/Poly.elem_of_vars [m [mr xm]]];
    apply: (h m x) => //; by [left|right].
- move=> h m x [mr|mr] xm; apply: h; apply/elem_of_app;
    [left|right]; apply/Poly.elem_of_vars; by exists m.
Qed.

Lemma over_frac_vars_sub vs r :
  (∀ x, x ∈ frac_vars r → x ∈ vs) → Frac.over vs r.
Proof.
move=> sub; split; apply: PolyGcd.over_mono (PolyGcd.over_vars _) => x xv;
  apply: sub; apply/elem_of_app; by [left|right].
Qed.

Lemma atoms_all_over (P : pre_term → Prop) vs r :
  Frac.over vs r → (∀ x, x ∈ vs → P x) → atoms_all P r.
Proof. move=> o h m x mr xm; apply: h; exact: Frac.over_elem o mr xm. Qed.

Lemma atoms_all_op2 (P : pre_term → Prop) (op : frac → frac → frac) r1 r2 :
  (∀ vs f g, Frac.over vs f → Frac.over vs g → Frac.over vs (op f g)) →
  atoms_all P r1 → atoms_all P r2 → atoms_all P (op r1 r2).
Proof.
move=> hop /atoms_all_vars h1 /atoms_all_vars h2.
apply: (atoms_all_over _ (frac_vars r1 ++ frac_vars r2)).
- by apply: hop; apply: over_frac_vars_sub => x xv; apply/elem_of_app;
    [left|right].
- by move=> x /elem_of_app [/h1|/h2].
Qed.

Lemma atoms_all_op1 (P : pre_term → Prop) (op : frac → frac) r :
  (∀ vs f, Frac.over vs f → Frac.over vs (op f)) →
  atoms_all P r → atoms_all P (op r).
Proof.
move=> hop /atoms_all_vars h; apply: (atoms_all_over _ (frac_vars r)) => //.
by apply: hop; apply: over_frac_vars_sub.
Qed.

Lemma atoms_all_add P r1 r2 :
  atoms_all P r1 → atoms_all P r2 → atoms_all P (Frac.add r1 r2).
Proof. exact: atoms_all_op2 Frac.over_add. Qed.

Lemma atoms_all_mul P r1 r2 :
  atoms_all P r1 → atoms_all P r2 → atoms_all P (Frac.mul r1 r2).
Proof. exact: atoms_all_op2 Frac.over_mul. Qed.

Lemma atoms_all_sub P r1 r2 :
  atoms_all P r1 → atoms_all P r2 → atoms_all P (Frac.sub r1 r2).
Proof. exact: atoms_all_op2 Frac.over_sub. Qed.

Lemma atoms_all_div P r1 r2 :
  atoms_all P r1 → atoms_all P r2 → atoms_all P (Frac.div r1 r2).
Proof. exact: atoms_all_op2 Frac.over_div. Qed.

Lemma atoms_all_opp P r : atoms_all P r → atoms_all P (Frac.opp r).
Proof. exact: atoms_all_op1 Frac.over_opp. Qed.

Lemma atoms_all_inv P r : atoms_all P r → atoms_all P (Frac.inv r).
Proof. exact: atoms_all_op1 Frac.over_inv. Qed.

Lemma atoms_all_zero P : atoms_all P Frac.zero.
Proof.
apply: (atoms_all_over _ []); first exact: Frac.over_zero.
by move=> x /elem_of_nil.
Qed.

Lemma atoms_all_one P : atoms_all P Frac.one.
Proof.
apply: (atoms_all_over _ []); first exact: Frac.over_one.
by move=> x /elem_of_nil.
Qed.

Lemma atoms_all_fsum P l :
  Forall (atoms_all P) l → atoms_all P (Frac.fsum l).
Proof.
elim=> [|r l' hr _ IH]; rewrite ?Frac.fsum_nil ?Frac.fsum_cons;
  [exact: atoms_all_zero|exact: atoms_all_add].
Qed.

Lemma atoms_all_fprod P l :
  Forall (atoms_all P) l → atoms_all P (Frac.fprod l).
Proof.
elim=> [|r l' hr _ IH]; rewrite ?Frac.fprod_nil ?Frac.fprod_cons;
  [exact: atoms_all_one|exact: atoms_all_mul].
Qed.

Lemma atoms_all_bind P (φ : pre_term → frac) r :
  (∀ x, x ∈ frac_vars r → atoms_all P (φ x)) → atoms_all P (Frac.bind φ r).
Proof.
move=> h; set vs := frac_vars r ≫= (λ x, frac_vars (φ x)).
apply: (atoms_all_over _ vs).
- apply: Frac.over_bind => m x mr xm.
  have xr : x ∈ frac_vars r.
    rewrite /frac_vars elem_of_app; case: mr => mr; [left|right];
      apply/Poly.elem_of_vars; by exists m.
  apply: over_frac_vars_sub => y yv.
  by apply/list_elem_of_bind; exists x.
- move=> y /list_elem_of_bind [x [yx xr]].
  exact: (proj1 (atoms_all_vars _ _) (h x xr)).
Qed.


Lemma atoms_all_impl (P Q : pre_term → Prop) r :
  (∀ x, P x → Q x) → atoms_all P r → atoms_all Q r.
Proof. by move=> PQ h m x mr xm; apply: PQ; apply: h mr xm. Qed.

(** *** Atoms of lists *)

Lemma map_fmapE {A B} (f : A → B) (l : list A) : map f l = f <$> l.
Proof. by elim: l => //= x l ->. Qed.

Definition in_lists (F : frac_lists) (x : pre_term) : Prop :=
  ∃ m, (m ∈ F.1.1 ∨ m ∈ F.1.2 ∨ m ∈ F.2.1 ∨ m ∈ F.2.2) ∧ x ∈ m.

Lemma frac_all_in (T : pre_term → Prop) F :
  frac_all T F → ∀ x, in_lists F x → T x.
Proof.
case: F => [[ps ns] [qs rs]] [[Hps Hns] [Hqs Hrs]] x [m [mF xm]] /=.
have M ms : monos_all T ms → m ∈ ms → T x.
  move=> /monos_all_Forall /list.Forall_forall h /h /list.Forall_forall.
  by apply.
by case: mF => [/(M _ Hps)|[/(M _ Hns)|[/(M _ Hqs)|/(M _ Hrs)]]].
Qed.

Lemma all_atoms_in (P : pre_term → bool) F :
  all_atoms P F ↔ ∀ x, in_lists F x → P x.
Proof.
have M ms : forallb (forallb P) ms ↔ ∀ m x, m ∈ ms → x ∈ m → P x.
  rewrite forallb_True list.Forall_forall; split.
  - by move=> h m x /h /forallb_True /list.Forall_forall; apply.
  - by move=> h m mms; apply/forallb_True/list.Forall_forall => x; apply: h.
rewrite /all_atoms !andb_True !M /in_lists; split.
- by move=> [[[h1 h2] h3] h4] x [m [[|[|[|]]] xm]];
    [apply: h1|apply: h2|apply: h3|apply: h4].
- move=> h; split; [split; [split|]|] => m x mF xm; apply: h; exists m;
    split=> //; naive_solver.
Qed.

Lemma in_lists_map (f : pre_term → pre_term) F x :
  in_lists (map_lists f F) x ↔ ∃ y, in_lists F y ∧ x = f y.
Proof.
have M (ms : monos) m :
    m ∈ map (map f) ms ↔ ∃ m', m' ∈ ms ∧ m = map f m'.
  by rewrite map_fmapE list_elem_of_fmap; naive_solver.
rewrite /in_lists /map_lists /=; split.
- move=> [m [mF xm]].
  have [m' [m'F Em]] : ∃ m', (m' ∈ F.1.1 ∨ m' ∈ F.1.2 ∨ m' ∈ F.2.1 ∨
                             m' ∈ F.2.2) ∧ m = map f m'.
    by case: mF => [/M|[/M|[/M|/M]]]; naive_solver.
  subst m; move: xm; rewrite map_fmapE list_elem_of_fmap => -[y [-> ym']].
  by exists y; split=> //; exists m'.
- move=> [y [[m' [m'F ym']] ->]]; exists (map f m'); split.
  + by case: m'F => [h|[h|[h|h]]]; [left|right; left|right; right; left|
      right; right; right]; apply/M; exists m'.
  + by rewrite map_fmapE; apply: list_elem_of_fmap_2.
Qed.

Lemma map_lists_id (f : pre_term → pre_term) F :
  (∀ x, in_lists F x → f x = x) → map_lists f F = F.
Proof.
case: F => [[ps ns] [qs rs]] /= h.
have M ms : (∀ m x, m ∈ ms → x ∈ m → f x = x) → map (map f) ms = ms.
  move=> hm; rewrite -[RHS]list_fmap_id map_fmapE.
  apply: list_fmap_ext => i m him /=.
  have mms := list_elem_of_lookup_2 _ _ _ him.
  rewrite -[RHS]list_fmap_id map_fmapE; apply: list_fmap_ext => j x hjx.
  exact: hm mms (list_elem_of_lookup_2 _ _ _ hjx).
rewrite /map_lists /= !M //; move=> m x mF xm; apply: h; exists m; split=> //=;
  naive_solver.
Qed.

Lemma over_of_atoms vs (p : poly) :
  (∀ m x, m ∈ Poly.car p → x ∈ m → x ∈ vs) → PolyGcd.over vs p.
Proof.
move=> h y yn; case: (decide (Poly.deg y p = 0)) => // nd; exfalso.
have np : p ≠ Poly.zero by move=> e; apply: nd; rewrite e PolyGcd.deg_zero.
have [m [cm em]] := PolyGcd.deg_witness y p np.
apply: yn; apply: (h m); first exact/Poly.coeff_neq0_elem.
apply/MSet.elem_of_count; lia.
Qed.

Lemma atoms_all_of_lists (P : pre_term → Prop) F :
  (∀ x, in_lists F x → P x) → atoms_all P (of_lists F).
Proof.
move=> h; set vs := mjoin (F.1.1 ++ F.1.2 ++ F.2.1 ++ F.2.2).
have hvs : ∀ x, in_lists F x → x ∈ vs.
  move=> x [m [mF xm]]; apply/list_elem_of_join; exists m; split=> //.
  by rewrite !elem_of_app.
have P_lists (A : poly_lists) :
    (∀ m x, m ∈ A.1 ∨ m ∈ A.2 → x ∈ m → x ∈ vs) →
    PolyGcd.over vs (poly_of_lists A).
  move=> hA; apply: over_of_atoms => m x /= /SMS.elem_of_make.
  case=> /MSet.elem_of_of_list /list_elem_of_fmap [l [-> lA]]
    /MSet.elem_of_of_list xl; apply: (hA l x) => //; by [left|right].
apply: (atoms_all_over _ vs).
- apply: Frac.over_make; apply: P_lists => m x mA xm; apply: hvs;
    exists m; split=> //; naive_solver.
- move=> x /list_elem_of_join [m [xm mF]].
  apply: h; exists m; split=> //; rewrite !elem_of_app in mF; naive_solver.
Qed.


(** ** Normal forms of exponents *)

Lemma wf_modE F :
  wf (PTMod F) =
  all_atoms (λ x, wf x && negb (is_mod x)) F && canonical F && negb (lone F).
Proof. done. Qed.

Lemma wf_mod_aux r :
  atoms_all (λ x, wf x && negb (is_mod x)) r → wf (mod_aux r).
Proof.
move=> h; rewrite /mod_aux /mod_of_lists.
case E: (lone_atom (lists r)) => [x|].
- move/lone_atom_Some: E => E.
  have Er : r = Frac.of_poly (Poly.var x).
    by apply: lists_inj; rewrite lists_var.
  subst r.
  have /andb_True [] // : Is_true (wf x && negb (is_mod x)).
  apply: (h {[+ x +]} x); last exact/MSet.elem_of_singleton.
  by left; rewrite car_num_var; apply/SMS.elem_of_singleton.
- rewrite wf_modE /lone E.
  apply/andb_True; split; last done; apply/andb_True; split.
  + exact: (proj2 (all_atoms_lists (λ x, wf x && negb (is_mod x)) r) h).
  + exact: canonical_lists.
Qed.

Lemma mod_aux_frac_of pt : wf pt → mod_aux (frac_of pt) = pt.
Proof.
case: pt => [o|o t|o t1 t2|F|l] /=; try by rewrite /mod_aux lists_var.
move=> /andb_True [/andb_True [_ cF] nl].
rewrite /mod_aux (lists_of_lists _ cF) /mod_of_lists.
by move: nl; rewrite /lone; case: (lone_atom F).
Qed.

Lemma frac_of_atoms pt :
  wf pt → atoms_all (λ x, wf x && negb (is_mod x)) (frac_of pt).
Proof.
case: pt => [o|o t|o t1 t2|F|l] /= wpt;
  try by apply: atoms_all_var; apply/andb_True.
move: wpt => /andb_True [/andb_True [aF cF] _].
apply: (proj1 (all_atoms_lists (λ x, wf x && negb (is_mod x)) _)).
by rewrite (lists_of_lists _ cF).
Qed.

Lemma frac_of_mod_aux_wf r :
  atoms_all (λ x, wf x && negb (is_mod x)) r → frac_of (mod_aux r) = r.
Proof.
move=> h; apply: frac_of_mod_aux; apply: atoms_all_impl h.
by move=> x /andb_True [].
Qed.

Lemma bind_frac_of_id r :
  atoms_all (λ x, negb (is_mod x)) r → Frac.bind frac_of r = r.
Proof.
move=> h.
have E : ∀ m x, m ∈ Poly.car (Frac.num r) ∨ m ∈ Poly.car (Frac.den r) →
    x ∈ m → frac_of x = Frac.of_poly (Poly.var x).
  move=> m x mr xm; exact: frac_of_Nmod (h m x mr xm).
by rewrite (Frac.bind_ext _ _ _ E) Frac.bind_var_map Frac.map_id.
Qed.

Lemma wf_modf r :
  (∀ x, x ∈ frac_vars r → wf x) → wf (modf r).
Proof.
move=> h; apply wf_mod_aux; apply: atoms_all_bind => x xr.
exact: frac_of_atoms (h x xr).
Qed.


(** ** Diffie-Hellman maps *)

Section DHMaps.

Add Ring frac_ring : (Frac.frac_ring_theory (T := pre_term)).

Lemma lookup_dh_add m1 m2 k :
  dh_add m1 m2 !!! k = Frac.add (m1 !!! k) (m2 !!! k).
Proof. by rewrite /dh_add FMap.lookup_cast FMap.lookup_merge. Qed.

Lemma lookup_dh_opp m k : dh_opp m !!! k = Frac.opp (m !!! k).
Proof. rewrite /dh_opp FMap.lookup_cast; exact: FMap.lookup_map. Qed.

Lemma lookup_dh_scale r m k : dh_scale r m !!! k = Frac.mul (m !!! k) r.
Proof.
rewrite /dh_scale FMap.lookup_cast.
exact: (FMap.lookup_map (λ f, Frac.mul f r)).
Qed.

Lemma lookup_dh_sum s k :
  dh_sum s !!! k =
  Frac.sub (Frac.fsum ((λ t, dh_map t !!! k) <$> elements (SMS.pos s)))
           (Frac.fsum ((λ t, dh_map t !!! k) <$> elements (SMS.neg s))).
Proof.
rewrite /dh_sum Frac.subE.
have N : ∀ l, foldr (λ t m, dh_add (dh_opp (dh_map t)) m) ∅ l !!! k =
              Frac.opp (Frac.fsum ((λ t, dh_map t !!! k) <$> l)).
  elim=> [|t l IH] /=.
    by rewrite FMap.lookup_empty Frac.fsum_nil Frac.opp_zero.
  rewrite lookup_dh_add lookup_dh_opp IH Frac.fsum_cons.
  by move: (dh_map t !!! k) (Frac.fsum _) => a b; ring.
elim: (elements (SMS.pos s)) => [|t l IH] /=.
  by rewrite N Frac.fsum_nil (left_id Frac.zero Frac.add).
rewrite lookup_dh_add IH Frac.fsum_cons.
by move: (dh_map t !!! k) (Frac.fsum ((λ t, _) <$> l)) (Frac.opp _) => a b c;
  ring.
Qed.

Lemma lookup_to_list (m : dhmap) k :
  m !!! k = FMap.lookup_list Frac.zero k (FMap.to_list m).
Proof. by rewrite FMap.lookupE FMap.to_listE. Qed.

Lemma lookup_of_entries l k :
  of_entries l !!! k = of_lists (FMap.lookup_list zero_lists k l).
Proof.
elim: l => [|[b F] l IH] /=.
  by rewrite FMap.lookup_empty -lists_zero of_lists_lists.
by rewrite FMap.lookup_insert IH; case: bool_decide.
Qed.

Lemma lookup_list_entries m k :
  FMap.lookup_list zero_lists k (entries m) = lists (m !!! k).
Proof.
rewrite /entries lookup_to_list; elim: (FMap.to_list m) => [|[b r] l IH] /=.
  by rewrite lists_zero.
by rewrite IH; case: bool_decide.
Qed.

Lemma elem_of_entries m k F :
  (k, F) ∈ entries m ↔ F = lists (m !!! k) ∧ m !!! k ≠ Frac.zero.
Proof.
rewrite /entries list_elem_of_fmap; split.
- by move=> [[b r] [[-> ->] /FMap.elem_of_to_list [<- nr]]].
- move=> [-> nr]; exists (k, m !!! k).
  by split=> //; apply/FMap.elem_of_to_list.
Qed.

Lemma wf_entries m : FMap.wf zero_lists (entries m).
Proof.
apply bool_decide_pack; split.
- rewrite FMap.keys_fmap /entries -list_fmap_compose.
  exact: FMap.to_list_sorted.
- apply/list.Forall_forall => -[k F] /elem_of_entries [-> nr] /= e.
  by apply: nr; rewrite -(of_lists_lists (m !!! k)) e -lists_zero
    of_lists_lists.
Qed.

(** The keys of a well-formed map are bases, and its logarithms have
    normal atoms. *)
Definition wf_dh (m : dhmap) : Prop :=
  ∀ k, m !!! k ≠ Frac.zero →
    wf k ∧ negb (is_gnon_free k) ∧
    atoms_all (λ x, wf x && negb (is_mod x)) (m !!! k).

Lemma wf_dh_atoms m k :
  wf_dh m → atoms_all (λ x, wf x && negb (is_mod x)) (m !!! k).
Proof.
move=> wm; case: (decide (m !!! k = Frac.zero)) => [->|nz].
  exact: atoms_all_zero.
by case: (wm k nz) => _ [].
Qed.

Lemma wf_dhE l :
  wf (PTDH l) =
  forallb (λ e, wf e.1 && negb (is_gnon_free e.1)
                && all_atoms (λ x, wf x && negb (is_mod x)) e.2
                && canonical e.2) l
  && FMap.wf zero_lists l && negb (trivial_dh l).
Proof. done. Qed.

Lemma wf_dh_entries m : wf_dh m →
  forallb (λ e, wf e.1 && negb (is_gnon_free e.1)
                && all_atoms (λ x, wf x && negb (is_mod x)) e.2
                && canonical e.2) (entries m).
Proof.
move=> wm; apply/forallb_True/list.Forall_forall => -[k F].
move=> /elem_of_entries [-> nr] /=; have [wk [gk ak]] := wm k nr.
apply/andb_True; split; last exact: canonical_lists.
apply/andb_True; split.
  by apply/andb_True.
exact: (proj2 (all_atoms_lists _ _) ak).
Qed.

Lemma is_gnon_free_dh l : is_gnon_free (PTDH l) = true.
Proof. by case: l => [|[b [[[|m [|??]] [|??]] d]] [|??]]. Qed.

Lemma dh_map_Ngnf b : negb (is_gnon_free b) → dh_map b = {[b := Frac.one]}.
Proof. by case: b => // l; rewrite is_gnon_free_dh. Qed.

Lemma wf_dh_of m : wf_dh m → wf (dh_of m).
Proof.
move=> wm; rewrite /dh_of.
case E: (FMap.to_list m) => [|[b r] [|e l]].
- by rewrite /entries E.
- have /FMap.elem_of_to_list [mb nr] : (b, r) ∈ FMap.to_list m.
    by rewrite E; left.
  have [wb [gb ab]] := wm b ltac:(by rewrite mb).
  rewrite mb in ab; rewrite /mk_exp.
  case: bool_decide_reflect => [_|n1]; first done.
  rewrite wf_dhE; apply/andb_True; split; last first.
    rewrite /trivial_dh bool_decide_eq_false_2 //.
    by move=> /(f_equal of_lists); rewrite of_lists_lists -lists_one
      of_lists_lists.
  apply/andb_True; split.
  + apply/andb_True; split; last done.
    apply/andb_True; split; last exact: canonical_lists.
    apply/andb_True; split; first by apply/andb_True.
    exact: (proj2 (all_atoms_lists _ _) ab).
  + apply bool_decide_pack; split; first by repeat constructor.
    apply/Forall_singleton => /= e0; apply: nr.
    by rewrite -(of_lists_lists r) e0 -lists_zero of_lists_lists.
- rewrite wf_dhE; apply/andb_True; split.
    by apply/andb_True; split; [exact: wf_dh_entries|exact: wf_entries].
  by rewrite /entries E.
Qed.

Lemma dh_map_dh_of m : wf_dh m → dh_map (dh_of m) = m.
Proof.
move=> wm; rewrite /dh_of.
have Hent : of_entries (entries m) = m.
  apply/FMap.fmap_eq => k.
  by rewrite lookup_of_entries lookup_list_entries of_lists_lists.
case E: (FMap.to_list m) => [|[b r] [|e l]]; try exact: Hent.
have /FMap.elem_of_to_list [mb nr] : (b, r) ∈ FMap.to_list m.
  by rewrite E; left.
have [wb [gb ab]] := wm b ltac:(by rewrite mb).
apply/FMap.fmap_eq => k; rewrite [RHS]lookup_to_list E /=.
rewrite /mk_exp; case: bool_decide_reflect => [r1|n1].
- rewrite (dh_map_Ngnf _ gb) FMap.lookup_singleton r1.
  by case: bool_decide.
- by rewrite /= FMap.lookup_insert of_lists_lists FMap.lookup_empty.
Qed.

Lemma lookup_list_canonical (l : list entry) k :
  forallb (λ e, wf e.1 && negb (is_gnon_free e.1)
                && all_atoms (λ x, wf x && negb (is_mod x)) e.2
                && canonical e.2) l →
  canonical (FMap.lookup_list zero_lists k l).
Proof.
elim: l => [|[b F] l IH] /=.
  by move=> _; have := canonical_lists Frac.zero; rewrite lists_zero.
move=> /andb_True [/andb_True [_ cF] /IH hl].
by case: bool_decide.
Qed.

Lemma lookup_list_elem (l : list entry) k :
  FMap.lookup_list zero_lists k l ≠ zero_lists →
  (k, FMap.lookup_list zero_lists k l) ∈ l.
Proof.
elim: l => [|[b F] l IH] //=.
case: (bool_decide_reflect (k = b)) => [->|_]; first by left.
by move=> /IH h; right.
Qed.

Lemma entries_of_entries l : wf (PTDH l) → entries (of_entries l) = l.
Proof.
rewrite wf_dhE => /andb_True [/andb_True [hl wl] _].
apply: (FMap.lookup_list_inj zero_lists); [exact: wf_entries|exact: wl|] => k.
rewrite lookup_list_entries lookup_of_entries lists_of_lists //.
exact: lookup_list_canonical.
Qed.

Lemma dh_of_dh_map pt : wf pt → dh_of (dh_map pt) = pt.
Proof.
case: pt => [o|o t|o t1 t2|F|l] wpt;
  try by rewrite /= /dh_of FMap.to_list_singleton ?/mk_exp
    ?bool_decide_eq_true_2 //; apply: Frac.one_neq0.
have Hen := entries_of_entries l wpt.
move: wpt; rewrite wf_dhE => /andb_True [_ ntriv].
rewrite /= /dh_of; case E: (FMap.to_list (of_entries l)) => [|[b r] [|e l']];
  try by rewrite Hen.
move: Hen; rewrite /entries E /= => Hl; subst l.
rewrite /mk_exp bool_decide_eq_false_2 //.
move=> r1; move: ntriv.
by rewrite r1 lists_one /trivial_dh bool_decide_eq_true_2.
Qed.

Lemma wf_dh_map pt : wf pt → wf_dh (dh_map pt).
Proof.
case: pt => [o|o t|o t1 t2|F|l] wpt k;
  try (rewrite /= FMap.lookup_singleton;
       case: (bool_decide_reflect (k = _)) => [->|_] //= _;
       by split=> //; split; [|exact: atoms_all_one]).
have [hl _] : Is_true (forallb (λ e, wf e.1 && negb (is_gnon_free e.1)
                && all_atoms (λ x, wf x && negb (is_mod x)) e.2
                && canonical e.2) l) ∧ True.
  by move: wpt; rewrite wf_dhE => /andb_True [/andb_True []].
rewrite /= lookup_of_entries => nz.
have nF : FMap.lookup_list zero_lists k l ≠ zero_lists.
  by move=> e; apply: nz; rewrite e -lists_zero of_lists_lists.
have /(lookup_list_elem _ _) kl := nF.
move: hl => /forallb_True /list.Forall_forall /(_ _ kl) /=.
move=> /andb_True [/andb_True [/andb_True [wk gk] ak] ck].
split=> //; split=> //.
by apply/all_atoms_lists; rewrite lists_of_lists.
Qed.

Lemma wf_dh_empty : wf_dh ∅.
Proof. by move=> k; rewrite FMap.lookup_empty. Qed.

Lemma wf_dh_add m1 m2 : wf_dh m1 → wf_dh m2 → wf_dh (dh_add m1 m2).
Proof.
move=> w1 w2 k; rewrite lookup_dh_add => nz.
have [n1|n2] : m1 !!! k ≠ Frac.zero ∨ m2 !!! k ≠ Frac.zero.
  case: (decide (m1 !!! k = Frac.zero)) => [e1|]; last by left.
  right=> e2; apply: nz; rewrite e1 e2; exact: (left_id Frac.zero Frac.add).
- have [wk [gk _]] := w1 k n1; split=> //; split=> //.
  by apply: atoms_all_add; apply: wf_dh_atoms.
- have [wk [gk _]] := w2 k n2; split=> //; split=> //.
  by apply: atoms_all_add; apply: wf_dh_atoms.
Qed.

Lemma wf_dh_opp m : wf_dh m → wf_dh (dh_opp m).
Proof.
move=> w k; rewrite lookup_dh_opp => nz.
have n : m !!! k ≠ Frac.zero by move=> e; apply: nz; rewrite e Frac.opp_zero.
have [wk [gk ak]] := w k n; split=> //; split=> //.
exact: atoms_all_opp.
Qed.

Lemma wf_dh_scale r m :
  atoms_all (λ x, wf x && negb (is_mod x)) r → wf_dh m → wf_dh (dh_scale r m).
Proof.
move=> ar w k; rewrite lookup_dh_scale => nz.
have n : m !!! k ≠ Frac.zero by move=> e; apply: nz; rewrite e Frac.mul_zero_l.
have [wk [gk ak]] := w k n; split=> //; split=> //.
exact: atoms_all_mul.
Qed.

Lemma wf_dh_sum s : (∀ t, t ∈ s → wf t) → wf_dh (dh_sum s).
Proof.
move=> h; rewrite /dh_sum.
have hp : ∀ t, t ∈ elements (SMS.pos s) → wf t.
  by move=> t /MSet.elem_of_elements tp; apply: h; apply: SMS.elem_of_pos.
have hn : ∀ t, t ∈ elements (SMS.neg s) → wf t.
  by move=> t /MSet.elem_of_elements tn; apply: h; apply: SMS.elem_of_neg.
elim: (elements (SMS.pos s)) hp => [_|t l IH hp] /=; last first.
  apply: wf_dh_add; first by apply: wf_dh_map; apply: hp; left.
  by apply: IH => t' t'l; apply: hp; right.
elim: (elements (SMS.neg s)) hn => [_|t l IH hn] /=; first exact: wf_dh_empty.
apply: wf_dh_add; first by apply: wf_dh_opp; apply: wf_dh_map; apply: hn; left.
by apply: IH => t' t'l; apply: hn; right.
Qed.

Lemma wf_gmul s : (∀ t, t ∈ s → wf t) → wf (gmul s).
Proof. by move=> h; apply wf_dh_of; apply: wf_dh_sum. Qed.

Lemma wf_exp_frac b r :
  wf b → atoms_all (λ x, wf x && negb (is_mod x)) r → wf (exp_frac b r).
Proof.
by move=> wb ar; apply wf_dh_of; apply: wf_dh_scale => //; apply: wf_dh_map.
Qed.

Lemma wf_exp b e : wf b → wf e → wf (exp b e).
Proof. by move=> wb we; apply wf_exp_frac => //; apply: frac_of_atoms. Qed.

Lemma dh_map_mk_exp b r :
  negb (is_gnon_free b) → r ≠ Frac.zero → dh_map (mk_exp b r) = {[b := r]}.
Proof.
move=> gb nr; rewrite /mk_exp; case: bool_decide_reflect => [->|n1].
  exact: dh_map_Ngnf.
apply/FMap.fmap_eq => k.
by rewrite /= FMap.lookup_insert of_lists_lists FMap.lookup_empty
  FMap.lookup_singleton.
Qed.

Lemma dh_scale_singleton b r :
  dh_scale r {[b := Frac.one]} = {[b := r]}.
Proof.
apply/FMap.fmap_eq => k; rewrite lookup_dh_scale !FMap.lookup_singleton.
case: bool_decide; [exact: (left_id Frac.one Frac.mul)|exact: Frac.mul_zero_l].
Qed.

Lemma dh_of_singleton b r :
  r ≠ Frac.zero → dh_of {[b := r]} = mk_exp b r.
Proof. by move=> nr; rewrite /dh_of FMap.to_list_singleton. Qed.

Lemma exp_frac_atom b r :
  negb (is_gnon_free b) → r ≠ Frac.zero → exp_frac b r = mk_exp b r.
Proof.
move=> gb nr.
by rewrite /exp_frac (dh_map_Ngnf _ gb) dh_scale_singleton dh_of_singleton.
Qed.

(** ** Normalization *)

Lemma frac_vars_in_lists F x : x ∈ frac_vars (of_lists F) → in_lists F x.
Proof.
have := atoms_all_of_lists (in_lists F) F (λ x hx, hx).
by move=> /atoms_all_vars; apply.
Qed.

Lemma atoms_bind_normalize F :
  (∀ y, in_lists F y → wf (normalize y)) →
  atoms_all (λ x, wf x && negb (is_mod x))
    (Frac.bind frac_of (of_lists (map_lists normalize F))).
Proof.
move=> h; apply: atoms_all_bind => x /frac_vars_in_lists.
move=> /in_lists_map [y [yF ->]]; exact: frac_of_atoms (h y yF).
Qed.

Lemma elem_of_foldr_singletons (f : entry → pre_term) l t :
  t ∈ (foldr (λ e s, {[+ f e +]} ⊎ s) ∅ l : SMS.sms pre_term) →
  ∃ e, e ∈ l ∧ t = f e.
Proof.
elim: l => [|e l IH] /=.
  by move=> /SMS.elem_of_count; rewrite SMS.count_empty.
move=> /SMS.elem_of_disj_union [/SMS.elem_of_singleton ->|/IH [e' [e'l ->]]].
  by exists e; split=> //; left.
by exists e'; split=> //; right.
Qed.

Lemma foldr_singletons (f : entry → pre_term) l :
  (foldr (λ e s, {[+ f e +]} ⊎ s) ∅ l : SMS.sms pre_term) =
  SMS.make (MSet.of_list (f <$> l)) ∅.
Proof.
elim: l => [|e l IH] /=; first by rewrite MSet.of_list_nil.
by rewrite IH MSet.of_list_cons SMS.make_singleton_l.
Qed.

Lemma wf_normalize pt : wf (normalize pt).
Proof.
elim: pt => [o|o t IH|o t1 IH1 t2 IH2|F IH|l IH] /=.
- done.
- exact: IH.
- by apply/andb_True.
- apply wf_modf => x /frac_vars_in_lists /in_lists_map [y [yF ->]].
  exact: frac_all_in IH y yF.
- apply wf_gmul => t /elem_of_foldr_singletons [[b F] [eb ->]] /=.
  have [wb [HF]] :=
    proj1 (list.Forall_forall _ _) (entries_all_Forall _ _ IH) _ eb.
  apply wf_exp_frac => //; apply: atoms_bind_normalize => y yF.
  exact: frac_all_in HF y yF.
Qed.

Lemma normalize_lists_wf F :
  frac_all (λ x, wf x → normalize x = x) F →
  all_atoms (λ x, wf x && negb (is_mod x)) F →
  Frac.bind frac_of (of_lists (map_lists normalize F)) = of_lists F.
Proof.
move=> IH aF.
have hF : ∀ x, in_lists F x → wf x ∧ negb (is_mod x).
  by move=> x xF; apply/andb_True; apply: (proj1 (all_atoms_in _ _) aF x xF).
have Hid : ∀ x, in_lists F x → normalize x = x.
  by move=> x xF; apply: (frac_all_in _ _ IH x xF); case: (hF x xF).
rewrite (map_lists_id _ _ Hid); apply: bind_frac_of_id.
by apply: atoms_all_of_lists => x xF; case: (hF x xF).
Qed.

Lemma fsum_singletons (l : list entry) k :
  StronglySorted lexico (FMap.keys l) →
  Frac.fsum ((λ e, if bool_decide (k = e.1) then of_lists e.2
                   else Frac.zero) <$> l) =
  of_lists (FMap.lookup_list zero_lists k l).
Proof.
elim: l => [|[b F] l IH] /=.
  by move=> _; rewrite Frac.fsum_nil -lists_zero of_lists_lists.
move=> /StronglySorted_cons [lb sl]; rewrite Frac.fsum_cons.
case: (bool_decide_reflect (k = b)) => [->|nk]; last first.
  by rewrite (left_id Frac.zero Frac.add) IH.
have -> : Frac.fsum ((λ e, if bool_decide (b = e.1) then of_lists e.2
                           else Frac.zero) <$> l) = Frac.zero.
  move: lb; elim: (l) => [|[b' F'] l' IHl] /=; first by rewrite Frac.fsum_nil.
  move=> /Forall_cons_iff [bb' lb]; rewrite Frac.fsum_cons.
  rewrite IHl // bool_decide_eq_false_2; last first.
    by move=> e; move: bb'; rewrite /= -e; apply: irreflexivity.
  exact: (left_id Frac.zero Frac.add).
by move: (of_lists F) => a; ring.
Qed.

Lemma normalize_entries (l : list entry) :
  forallb (λ e, wf e.1 && negb (is_gnon_free e.1)
                && all_atoms (λ x, wf x && negb (is_mod x)) e.2
                && canonical e.2) l →
  Forall (λ e, (wf e.1 → normalize e.1 = e.1) ∧
               inhabited (frac_all (λ x, wf x → normalize x = x) e.2)) l →
  (foldr (λ e s, {[+ exp_frac (normalize e.1)
            (Frac.bind frac_of (of_lists (map_lists normalize e.2))) +]}
            ⊎ s) ∅ l : SMS.sms pre_term) =
  foldr (λ e s, {[+ exp_frac e.1 (of_lists e.2) +]} ⊎ s) ∅ l.
Proof.
elim: l => [//|[b F] l IHl] /=.
move=> /andb_True [/andb_True [/andb_True [/andb_True [wb _] aF] _] hl].
move=> /Forall_cons_iff [[nb [HF]] Hl] /=.
by rewrite (nb wb) (normalize_lists_wf F HF aF) (IHl hl Hl).
Qed.

Lemma normalize_wf pt : wf pt → normalize pt = pt.
Proof.
elim: pt => [o|o t IH|o t1 IH1 t2 IH2|F IH|l IH] /=.
- done.
- by move=> /IH ->.
- by move=> /andb_True [/IH1 -> /IH2 ->].
- move=> wF; move: (wF) => /andb_True [/andb_True [aF cF] nl].
  rewrite /modf (normalize_lists_wf F IH aF).
  rewrite /mod_aux (lists_of_lists _ cF) /mod_of_lists.
  by move: nl; rewrite /lone; case: (lone_atom F).
- move=> wl; move: (wl) => /andb_True [/andb_True [hl wfl] _].
  have Hl := entries_all_Forall _ _ IH.
  rewrite (normalize_entries l hl Hl).
  set f := λ e : entry, exp_frac e.1 (of_lists e.2).
  rewrite -[RHS](dh_of_dh_map (PTDH l) wl) /gmul; congr dh_of.
  apply/FMap.fmap_eq => k; rewrite lookup_dh_sum foldr_singletons.
  rewrite SMS.pos_make_empty_r SMS.neg_make_empty_r /= lookup_of_entries.
  have [sl _] := bool_decide_unpack _ wfl.
  transitivity (Frac.fsum ((λ e : entry, if bool_decide (k = e.1)
                             then of_lists e.2 else Frac.zero) <$> l));
    last exact: fsum_singletons.
  rewrite MSet.elements_empty /= Frac.fsum_nil Frac.subE Frac.opp_zero.
  assert (E1 : Frac.fsum ((λ t, dh_map t !!! k) <$> elements
                 (MSet.of_list
                    ((λ e : entry, exp_frac e.1 (of_lists e.2)) <$> l)))
               = Frac.fsum ((λ t, dh_map t !!! k) <$>
                   ((λ e : entry, exp_frac e.1 (of_lists e.2)) <$> l))).
    by apply: Frac.fsum_perm; apply: fmap_Permutation;
      exact: MSet.elements_of_list.
  rewrite E1 -list_fmap_compose.
  assert (E2 : ((λ t, dh_map t !!! k) ∘
                 (λ e : entry, exp_frac e.1 (of_lists e.2))) <$> l =
               (λ e : entry, if bool_decide (k = e.1) then of_lists e.2
                             else Frac.zero) <$> l).
    apply: list_fmap_ext => i [b F] hi.
    have eb := list_elem_of_lookup_2 _ _ _ hi.
    have := proj1 (list.Forall_forall _ _) (proj1 (forallb_True _ _) hl) _ eb.
    move=> /= /andb_True [/andb_True [/andb_True [_ gb] _] cF].
    have [_ /list.Forall_forall nz] := bool_decide_unpack _ wfl.
    have nF := nz _ eb; rewrite /= in nF.
    have nr : of_lists F ≠ Frac.zero.
      by move=> e; apply: nF; rewrite -(lists_of_lists _ cF) e lists_zero.
    rewrite /= (exp_frac_atom _ _ gb nr) (dh_map_mk_exp _ _ gb nr).
    exact: FMap.lookup_singleton.
  rewrite E2; by move: (Frac.fsum _) => a; ring.
Qed.

Lemma normalize_idem pt : normalize (normalize pt) = normalize pt.
Proof. exact: normalize_wf (wf_normalize pt). Qed.

(** ** Group factors *)

Lemma lookup_dh_sum_ssum s k :
  dh_sum s !!! k = Frac.ssum (λ t, dh_map t !!! k) s.
Proof. by rewrite lookup_dh_sum Frac.ssumE. Qed.

Lemma lookup_dh_map_mk_exp b r k :
  negb (is_gnon_free b) → r ≠ Frac.zero →
  dh_map (mk_exp b r) !!! k = if bool_decide (k = b) then r else Frac.zero.
Proof. by move=> gb nr; rewrite dh_map_mk_exp // FMap.lookup_singleton. Qed.

Lemma ssum_exp_factor b q n k :
  negb (is_gnon_free b) → q ≠ Poly.zero →
  Frac.ssum (λ t, dh_map t !!! k) (exp_factor b q n) =
  if bool_decide (k = b) then Frac.make (Poly.mono n) q else Frac.zero.
Proof.
move=> gb nq; rewrite /exp_factor.
have nr : Frac.make (Poly.mono n) q ≠ Frac.zero.
  exact: Frac.make_neq0 (PolyGcd.mono_neq0 n) nq.
case: (Poly.first_neg _).
- have nr' : Frac.opp (Frac.make (Poly.mono n) q) ≠ Frac.zero.
    move=> e; apply: nr.
    by rewrite -(Frac.opp_opp (Frac.make _ _)) e Frac.opp_zero.
  rewrite Frac.ssum_inv Frac.ssum_singleton (lookup_dh_map_mk_exp _ _ _ gb nr').
  by case: bool_decide; rewrite ?Frac.opp_opp ?Frac.opp_zero.
- by rewrite Frac.ssum_singleton (lookup_dh_map_mk_exp _ _ _ gb nr).
Qed.

Lemma ssum_of_poly_mono (p : poly) :
  Frac.ssum (λ n, Frac.of_poly (Poly.mono n)) (Poly.car p) = Frac.of_poly p.
Proof.
elim/(Poly.poly_ind (T := pre_term)): p => [|m p IH|m p IH].
- by rewrite Poly.car_zero Frac.ssum_empty Frac.zeroE.
- rewrite Poly.car_add Poly.car_mono Frac.ssum_disj_union.
  rewrite Frac.ssum_singleton IH.
  by rewrite -Frac.of_poly_add.
- rewrite Poly.car_add Poly.car_opp Poly.car_mono Frac.ssum_disj_union.
  rewrite Frac.ssum_inv Frac.ssum_singleton.
  by rewrite IH -Frac.of_poly_opp -Frac.of_poly_add.
Qed.

Lemma ssum_make_mono (p q : poly) : q ≠ Poly.zero →
  Frac.ssum (λ n, Frac.make (Poly.mono n) q) (Poly.car p) = Frac.make p q.
Proof.
move=> nq.
have E : ∀ n, n ∈ Poly.car p → Frac.make (Poly.mono n) q =
  Frac.mul (Frac.of_poly (Poly.mono n)) (Frac.inv (Frac.of_poly q)).
  by move=> n _; rewrite Frac.make_div Frac.divE.
by rewrite (Frac.ssum_ext _ _ _ E) Frac.ssum_mul_r ssum_of_poly_mono
  [RHS]Frac.make_div Frac.divE.
Qed.

Lemma ssum_foldr (g : pre_term → frac) (X : pre_term * frac → SMS.sms pre_term)
    (l : list (pre_term * frac)) :
  Frac.ssum g (foldr (λ p s, X p ⊎ s) ∅ l) =
  Frac.fsum ((λ p, Frac.ssum g (X p)) <$> l).
Proof.
elim: l => [|p l IH] /=; first by rewrite Frac.ssum_empty Frac.fsum_nil.
by rewrite Frac.ssum_disj_union IH Frac.fsum_cons.
Qed.

Lemma fsum_to_list (m : dhmap) k :
  Frac.fsum ((λ p, if bool_decide (k = p.1) then p.2 else Frac.zero)
               <$> FMap.to_list m) = m !!! k.
Proof.
rewrite lookup_to_list; have := FMap.to_list_sorted m.
elim: (FMap.to_list m) => [|[b r] l IH] /=; first by rewrite Frac.fsum_nil.
move=> /StronglySorted_cons [lb sl]; rewrite Frac.fsum_cons.
case: (bool_decide_reflect (k = b)) => [->|nk]; last first.
  by rewrite (left_id Frac.zero Frac.add) IH.
have -> : Frac.fsum ((λ p, if bool_decide (b = p.1) then p.2 else Frac.zero)
                     <$> l) = Frac.zero.
  move: lb; elim: (l) => [|[b' r'] l' IHl] /=; first by rewrite Frac.fsum_nil.
  move=> /Forall_cons_iff [bb' lb]; rewrite Frac.fsum_cons.
  rewrite IHl // bool_decide_eq_false_2; last first.
    by move=> e; move: bb'; rewrite /= -e; apply: irreflexivity.
  exact: (left_id Frac.zero Frac.add).
by move: r => a; ring.
Qed.

Lemma ssum_const_zero (s : SMS.sms (MSet.mset pre_term)) :
  Frac.ssum (λ _ : MSet.mset pre_term, (Frac.zero : frac)) s = Frac.zero.
Proof.
elim/(SMS.sms_ind (T := MSet.mset pre_term)): s => [|x s IH|x s IH].
- exact: Frac.ssum_empty.
- rewrite Frac.ssum_disj_union Frac.ssum_singleton IH; ring.
- rewrite Frac.ssum_disj_union Frac.ssum_inv Frac.ssum_singleton IH; ring.
Qed.

Lemma dh_sum_dh_factors m : wf_dh m → dh_sum (dh_factors m) = m.
Proof.
move=> wm; apply/FMap.fmap_eq => k.
rewrite lookup_dh_sum_ssum /dh_factors ssum_foldr -[RHS]fsum_to_list.
congr Frac.fsum; apply: list_fmap_ext => i [b r] hi /=.
have /FMap.elem_of_to_list [mb nr] := list_elem_of_lookup_2 _ _ _ hi.
have [_ [gb _]] := wm b ltac:(by rewrite mb).
have E : ∀ n, n ∈ Poly.car (Frac.num r) →
    Frac.ssum (λ t, dh_map t !!! k) (exp_factor b (Frac.den r) n) =
    if bool_decide (k = b) then Frac.make (Poly.mono n) (Frac.den r)
    else Frac.zero.
  by move=> n _; apply: ssum_exp_factor => //; exact: Frac.den_neq0.
rewrite Frac.ssum_bind (Frac.ssum_ext _ _ _ E).
case: bool_decide => /=; last exact: ssum_const_zero.
by rewrite ssum_make_mono ?Frac.make_num_den //; exact: Frac.den_neq0.
Qed.

Lemma dh_sum_singleton t : dh_sum {[+ t +]} = dh_map t.
Proof.
by apply/FMap.fmap_eq => k; rewrite lookup_dh_sum_ssum Frac.ssum_singleton.
Qed.

Lemma dh_sum_gfactors t : wf t → dh_sum (gfactors t) = dh_map t.
Proof.
move=> wt; rewrite /gfactors.
case: (is_exp t); first exact: dh_sum_singleton.
case: t wt => [o|o t|o t1 t2|F|l] wt; try exact: dh_sum_singleton.
exact: dh_sum_dh_factors (wf_dh_map _ wt).
Qed.

Lemma gfactorsK t : wf t → gmul (gfactors t) = t.
Proof. by move=> wt; rewrite /gmul dh_sum_gfactors // dh_of_dh_map. Qed.

Lemma wf_mk_exp b r :
  wf b → negb (is_gnon_free b) → r ≠ Frac.zero →
  atoms_all (λ x, wf x && negb (is_mod x)) r → wf (mk_exp b r).
Proof.
move=> wb gb nr ar.
have wm : wf_dh {[b := r]}.
  move=> k; rewrite FMap.lookup_singleton.
  by case: bool_decide_reflect => [->|_] // _; split=> //; split.
by have := wf_dh_of _ wm; rewrite dh_of_singleton.
Qed.

Lemma mk_exp_Ngmul b r n :
  negb (is_gnon_free b) → Frac.num r = Poly.mono n →
  negb (is_gmul (mk_exp b r)).
Proof.
move=> gb nr; rewrite /mk_exp; case: bool_decide => //.
  exact: Ngnf_Ngmul.
by rewrite /lists nr poly_lists_mono.
Qed.

Lemma is_exp_mk_exp b r n :
  r ≠ Frac.one → Frac.num r = Poly.mono n → is_exp (mk_exp b r).
Proof.
move=> n1 nr; rewrite /mk_exp bool_decide_eq_false_2 //.
by rewrite /lists nr poly_lists_mono.
Qed.

Lemma elem_of_inv_singleton (x y : pre_term) :
  x ∈ SMS.inv ({[+ y +]} : SMS.sms pre_term) → x = y.
Proof.
rewrite SMS.elem_of_count SMS.count_inv SMS.count_singleton.
by case: bool_decide_reflect => [//|_] h; exfalso; apply: h.
Qed.

(** Each factor is [mk_exp b r] for a fraction [r] with a monomial
    numerator. *)
Lemma elem_of_exp_factor b q n x :
  q ≠ Poly.zero → x ∈ exp_factor b q n →
  ∃ r n', x = mk_exp b r ∧ Frac.num r = Poly.mono n' ∧
          (r = Frac.make (Poly.mono n) q ∨
           r = Frac.opp (Frac.make (Poly.mono n) q)).
Proof.
move=> nq; rewrite /exp_factor.
have [n' [_ E]] := Frac.num_make_mono n q nq.
case F: (Poly.first_neg _) => xe.
- have -> : x = mk_exp b (Frac.opp (Frac.make (Poly.mono n) q)).
    exact: elem_of_inv_singleton xe.
  exists (Frac.opp (Frac.make (Poly.mono n) q)), n'; split=> //; split; last
    by right.
  rewrite Frac.num_opp.
  case: E F => ->; first by rewrite Poly.first_neg_mono.
  by rewrite Poly.opp_opp.
- move/SMS.elem_of_singleton: xe => ->.
  exists (Frac.make (Poly.mono n) q), n'; split=> //; split; last by left.
  by case: E F => -> //; rewrite Poly.first_neg_opp_mono.
Qed.

Lemma elem_of_dh_factors m x :
  x ∈ dh_factors m →
  ∃ b r n, (b, r) ∈ FMap.to_list m ∧ n ∈ Poly.car (Frac.num r) ∧
           x ∈ exp_factor b (Frac.den r) n.
Proof.
rewrite /dh_factors; elim: (FMap.to_list m) => [|[b r] l IH] /=.
  by move=> /SMS.elem_of_count; rewrite SMS.count_empty.
move=> /SMS.elem_of_disj_union [/SMS.elem_of_bind [n [nr xn]]|].
  by exists b, r, n; split=> //; left.
by move=> /IH [b' [r' [n [? [? ?]]]]]; exists b', r', n; split=> //; right.
Qed.

Lemma atoms_all_make_mono P r n :
  n ∈ Poly.car (Frac.num r) → atoms_all P r →
  atoms_all P (Frac.make (Poly.mono n) (Frac.den r)).
Proof.
move=> nr /atoms_all_vars ar; apply: (atoms_all_over _ (frac_vars r)) => //.
apply: Frac.over_make.
- apply: over_of_atoms => m x; rewrite Poly.car_mono.
  move=> /SMS.elem_of_singleton -> xn.
  by apply/elem_of_app; left; apply/Poly.elem_of_vars; exists n.
- apply: PolyGcd.over_mono (PolyGcd.over_vars _) => x xv.
  by apply/elem_of_app; right.
Qed.

Lemma gfactors_Ngmul pt : negb (is_gmul pt) → gfactors pt = {[+ pt +]}.
Proof.
by rewrite /gfactors; case: pt => // -[|[b [[[|m [|??]] [|??]] d]] [|??]].
Qed.

Lemma gfactors_elem t x :
  wf t → x ∈ gfactors t → wf x ∧ negb (is_gmul x).
Proof.
move=> wt; rewrite /gfactors.
case E: (is_exp t).
  move=> /SMS.elem_of_singleton ->; split=> //.
  by apply: is_exp_Ngmul; rewrite E.
case: t wt E => [o|o t|o t1 t2|F|l] wt E;
  try by move=> /SMS.elem_of_singleton ->.
move=> /elem_of_dh_factors [b [r [n [br [nr xe]]]]].
have /FMap.elem_of_to_list [mb r0] := br.
have [wb [gb ar]] := wf_dh_map _ wt b ltac:(by rewrite mb).
rewrite mb in ar.
have nq := Frac.den_neq0 r.
have [r' [n' [-> [Er' Hr']]]] := elem_of_exp_factor b (Frac.den r) n x nq xe.
have nr0 : Frac.make (Poly.mono n) (Frac.den r) ≠ Frac.zero.
  exact: Frac.make_neq0 (PolyGcd.mono_neq0 n) nq.
have ar0 := atoms_all_make_mono _ _ _ nr ar.
split; last exact: mk_exp_Ngmul gb Er'.
case: Hr' => ->.
- exact: wf_mk_exp.
- apply: wf_mk_exp => //; last exact: atoms_all_opp.
  move=> e; apply: nr0.
  by rewrite -(Frac.opp_opp (Frac.make _ _)) e Frac.opp_zero.
Qed.

Variant is_exp_spec pt : bool → Prop :=
| IsExp b m d of pt = PTDH [(b, (([m], []), d))] : is_exp_spec pt true
| NotExp of base pt = pt & expo pt = one : is_exp_spec pt false.

Lemma is_expP pt : is_exp_spec pt (is_exp pt).
Proof.
case: pt => [o|o t|o t1 t2|F|l]; try by constructor.
case: l => [|[b [[ps ns] d]] l]; first by constructor.
case: ps => [|m [|??]]; try by constructor.
case: ns => [|??]; last by constructor.
case: l => [|??]; last by constructor.
by econstructor.
Qed.

Lemma base_expN pt : negb (is_exp pt) → base pt = pt.
Proof. by case: is_expP. Qed.

Lemma expo_expN pt : negb (is_exp pt) → expo pt = one.
Proof. by case: is_expP. Qed.

Lemma base_mk_exp b r n :
  r ≠ Frac.one → Frac.num r = Poly.mono n → base (mk_exp b r) = b.
Proof.
by move=> n1 nr; rewrite /mk_exp bool_decide_eq_false_2 // /lists nr
  poly_lists_mono.
Qed.

Lemma expo_mk_exp b r n :
  r ≠ Frac.one → Frac.num r = Poly.mono n → expo (mk_exp b r) = mod_aux r.
Proof.
by move=> n1 nr; rewrite /mk_exp bool_decide_eq_false_2 // /mod_aux /lists nr
  poly_lists_mono.
Qed.

Lemma wf_one : wf one.
Proof.
rewrite /one wf_modE; apply/andb_True; split; last done.
apply/andb_True; split; first done.
rewrite -lists_one; exact: canonical_lists.
Qed.

Lemma wf_exp_entry b F :
  wf (PTDH [(b, F)]) →
  wf b ∧ negb (is_gnon_free b) ∧
  all_atoms (λ x, wf x && negb (is_mod x)) F ∧ canonical F.
Proof.
rewrite wf_dhE.
move=> /andb_True [/andb_True [/forallb_True/list.Forall_forall H _] _].
have := H (b, F) ltac:(by left).
by move=> /andb_True [/andb_True [/andb_True [? ?] ?] ?].
Qed.

Lemma wf_base pt : wf pt → wf (base pt).
Proof.
case: (is_expP pt) => [b m d ->|-> _ //].
by move=> /wf_exp_entry [wb _].
Qed.

Lemma wf_expo pt : wf pt → wf (expo pt).
Proof.
case: (is_expP pt) => [b m d -> /wf_exp_entry [_ [_ [aF cF]]]|_ -> _].
- change (wf (mod_of_lists (([m], []), d))).
  have E := lists_of_lists _ cF.
  rewrite -E; apply: wf_mod_aux; apply/all_atoms_lists.
  by rewrite E.
- exact: wf_one.
Qed.

Lemma dh_map_gmul s : (∀ t, t ∈ s → wf t) → dh_map (gmul s) = dh_sum s.
Proof. by move=> h; apply: dh_map_dh_of; apply: wf_dh_sum. Qed.

Lemma dh_map_exp_frac b r :
  wf b → atoms_all (λ x, wf x && negb (is_mod x)) r →
  dh_map (exp_frac b r) = dh_scale r (dh_map b).
Proof.
by move=> wb ar; apply: dh_map_dh_of; apply: wf_dh_scale => //;
  apply: wf_dh_map.
Qed.

Lemma dh_map_exp b e :
  wf b → wf e → dh_map (exp b e) = dh_scale (frac_of e) (dh_map b).
Proof. by move=> wb we; apply: dh_map_exp_frac => //; apply: frac_of_atoms. Qed.

Lemma dh_map_inj t1 t2 : wf t1 → wf t2 → dh_map t1 = dh_map t2 → t1 = t2.
Proof. by move=> w1 w2 e; rewrite -(dh_of_dh_map _ w1) e dh_of_dh_map. Qed.

(** ** Laurent logarithms

    A logarithm is Laurent when its denominator is a monomial.  Splitting such
    a logarithm into its monomials ([lfactors]) is additive ([lfactors_add]),
    so [gfactors] is a homomorphism on group elements whose logarithms are
    Laurent ([gfactors_gmul]).  It is not one in general: [g^(1/(x+1))] and
    [g^(x/(x+1))] multiply to [g]. *)

Add Ring poly_ring_L : (Poly.poly_ring_theory (T := pre_term)).

Definition lfrac (r : frac) : Prop := ∃ Q, Frac.den r = Poly.mono Q.

Definition llogs pt : Prop := ∀ k, lfrac (dh_map pt !!! k).

Definition lfactors b (r : frac) : SMS.sms pre_term :=
  SMS.bind (exp_factor b (Frac.den r)) (Poly.car (Frac.num r)).

Definition lsplit b (Q : MSet.mset pre_term) (p : poly) : SMS.sms pre_term :=
  SMS.bind (exp_factor b (Poly.mono Q)) (Poly.car p).

Lemma lfactorsE b r Q :
  Frac.den r = Poly.mono Q → lfactors b r = lsplit b Q (Frac.num r).
Proof. by rewrite /lfactors /lsplit => ->. Qed.

Lemma exp_factor_scale b K Q n :
  exp_factor b (Poly.mono (K ⊎ Q)) (K ⊎ n) = exp_factor b (Poly.mono Q) n.
Proof.
have E : Frac.make (Poly.mono (K ⊎ n)) (Poly.mono (K ⊎ Q)) =
         Frac.make (Poly.mono n) (Poly.mono Q).
  apply: Frac.make_eq; try exact: PolyGcd.mono_neq0.
  rewrite !Poly.mul_mono; congr Poly.mono; apply: MSet.count_inj => x.
  rewrite !MSet.count_disj_union; lia.
by rewrite /exp_factor E.
Qed.

Lemma lsplit_scale b K Q p :
  lsplit b (K ⊎ Q) (Poly.mul (Poly.mono K) p) = lsplit b Q p.
Proof.
rewrite /lsplit Poly.car_mul_mono SMS.bind_map.
by apply: SMS.bind_ext => n _; exact: exp_factor_scale.
Qed.

Lemma lsplit_scale_r b K Q p :
  lsplit b (Q ⊎ K) (Poly.mul (Poly.mono K) p) = lsplit b Q p.
Proof.
have -> : Q ⊎ K = K ⊎ Q.
  by apply: MSet.count_inj => x; rewrite !MSet.count_disj_union; lia.
exact: lsplit_scale.
Qed.

Lemma lsplit_add b Q p1 p2 :
  lsplit b Q (Poly.add p1 p2) = lsplit b Q p1 ⊎ lsplit b Q p2.
Proof. by rewrite /lsplit Poly.car_add SMS.bind_disj_union. Qed.

Lemma mono_neq_opp (Q : MSet.mset pre_term) :
  Poly.mono Q ≠ Poly.opp (Poly.mono Q).
Proof.
move=> e; have := Poly.first_neg_mono Q.
by rewrite {1}e Poly.first_neg_opp_mono.
Qed.

(** Reducing [P / Q] for a monomial [Q] cancels a monomial [K]. *)
Lemma make_mono_den (P : poly) Q :
  ∃ Q' K, Frac.den (Frac.make P (Poly.mono Q)) = Poly.mono Q' ∧
          Q = K ⊎ Q' ∧
          P = Poly.mul (Poly.mono K) (Frac.num (Frac.make P (Poly.mono Q))).
Proof.
have nq := PolyGcd.mono_neq0 Q.
have [e1 e2] := Frac.make_cancel P (Poly.mono Q) nq.
have [g [EP EQ]] := Poly.cancel_spec P (Poly.mono Q).
rewrite -e1 in EP; rewrite -e2 in EQ.
move: (Frac.make P (Poly.mono Q)) EP EQ => r EP EQ.
have [Q' [_ hd]] := PolyGcd.dvd_mono (Frac.den r) Q
  ltac:(by exists g; rewrite EQ (comm Poly.mul)).
have {}hd : Frac.den r = Poly.mono Q'.
  case: hd => // e; have := Frac.den_first_neg r.
  by rewrite e Poly.first_neg_opp_mono.
have [K [_ hg]] := PolyGcd.dvd_mono g Q ltac:(by exists (Frac.den r)).
exists Q', K; split=> //.
case: hg => eg; rewrite eg in EP EQ.
- rewrite hd Poly.mul_mono in EQ.
  by split=> //; apply: Poly.mono_pm_inj; left.
- exfalso.
  have E : Poly.mono Q = Poly.opp (Poly.mono (K ⊎ Q')).
    by rewrite EQ hd -Poly.mul_mono; ring.
  have EQ' := Poly.mono_pm_inj Q (K ⊎ Q') (or_intror E).
  by apply: (mono_neq_opp Q); rewrite {1}E EQ'.
Qed.

Lemma lfactors_make b P Q :
  lfrac (Frac.make P (Poly.mono Q)) ∧
  lfactors b (Frac.make P (Poly.mono Q)) = lsplit b Q P.
Proof.
have [Q' [K [hd [EQ hP]]]] := make_mono_den P Q.
subst Q; split; first by exists Q'.
by rewrite (lfactorsE _ _ _ hd) [in RHS]hP lsplit_scale.
Qed.

Lemma lfrac_zero : lfrac Frac.zero.
Proof. by exists ∅; rewrite Frac.den_zero Poly.oneE. Qed.

Lemma lfrac_one : lfrac Frac.one.
Proof. by exists ∅; rewrite Frac.den_one Poly.oneE. Qed.

Lemma lfrac_opp r : lfrac r → lfrac (Frac.opp r).
Proof. by case=> Q e; exists Q; rewrite Frac.den_opp. Qed.

Lemma lfactors_zero b : lfactors b Frac.zero = ∅.
Proof. by rewrite /lfactors Frac.num_zero Poly.car_zero SMS.bind_empty. Qed.

Lemma lfactors_opp b r : lfactors b (Frac.opp r) = SMS.inv (lfactors b r).
Proof.
by rewrite /lfactors Frac.num_opp Frac.den_opp Poly.car_opp SMS.bind_inv.
Qed.

Lemma lfactors_add b r1 r2 : lfrac r1 → lfrac r2 →
  lfrac (Frac.add r1 r2) ∧
  lfactors b (Frac.add r1 r2) = lfactors b r1 ⊎ lfactors b r2.
Proof.
move=> [Q1 e1] [Q2 e2].
rewrite Frac.addE e1 e2 Poly.mul_mono.
have [L E] := lfactors_make b
  (Poly.add (Poly.mul (Frac.num r1) (Poly.mono Q2))
            (Poly.mul (Frac.num r2) (Poly.mono Q1))) (Q1 ⊎ Q2).
split=> //; rewrite E lsplit_add (lfactorsE _ _ _ e1) (lfactorsE _ _ _ e2).
rewrite (comm Poly.mul (Frac.num r1)) (comm Poly.mul (Frac.num r2)).
by rewrite lsplit_scale_r lsplit_scale.
Qed.

Lemma lfrac_mul r1 r2 : lfrac r1 → lfrac r2 → lfrac (Frac.mul r1 r2).
Proof.
move=> [Q1 e1] [Q2 e2]; rewrite Frac.mulE e1 e2 Poly.mul_mono.
have [Q' [_ [hd _]]] :=
  make_mono_den (Poly.mul (Frac.num r1) (Frac.num r2)) (Q1 ⊎ Q2).
by exists Q'.
Qed.

Lemma base_lfactors b r y :
  negb (is_gnon_free b) → y ∈ lfactors b r → base y = b.
Proof.
move=> gb /SMS.elem_of_bind [n [_ yn]].
have [r' [n' [-> [nr' _]]]] :=
  elem_of_exp_factor b (Frac.den r) n y (Frac.den_neq0 r) yn.
case: (decide (r' = Frac.one)) => [->|n1]; last exact: base_mk_exp n1 nr'.
by rewrite /mk_exp bool_decide_eq_true_2 // base_expN //; exact: Ngnf_Nexp.
Qed.

Lemma count_lfactors_ne b r z :
  negb (is_gnon_free b) → base z ≠ b → SMS.count z (lfactors b r) = 0%Z.
Proof.
move=> gb nz; case: (decide (z ∈ lfactors b r)).
  by move=> /(base_lfactors _ _ _ gb).
move=> h.
by move: h; rewrite SMS.elem_of_count; lia.
Qed.

(** Only the logarithm at the base of [z] counts toward [z]. *)
Lemma count_dh_factors m z :
  wf_dh m →
  SMS.count z (dh_factors m) = SMS.count z (lfactors (base z) (m !!! base z)).
Proof.
move=> wm; rewrite lookup_to_list.
have K : ∀ k r, (k, r) ∈ FMap.to_list m → negb (is_gnon_free k).
  move=> k r /FMap.elem_of_to_list [mk nr].
  by have [_ [gk _]] := wm k ltac:(by rewrite mk).
have S := FMap.to_list_sorted m.
rewrite /dh_factors.
change (foldr _ ∅ (FMap.to_list m)) with
  (foldr (λ p s, lfactors p.1 p.2 ⊎ s) ∅ (FMap.to_list m)).
elim: (FMap.to_list m) K S => [|[k r] l IH] K /=.
  by rewrite SMS.count_empty lfactors_zero SMS.count_empty.
move=> /StronglySorted_cons [lk sl].
have Kk : negb (is_gnon_free k) by apply: (K k r); left.
have Kl : ∀ k' r', (k', r') ∈ l → negb (is_gnon_free k').
  by move=> k' r' h; apply: (K k' r'); right.
rewrite SMS.count_disj_union.
case: (bool_decide_reflect (base z = k)) => [ek|nk].
- have -> : SMS.count z (foldr (λ p s, lfactors p.1 p.2 ⊎ s) ∅ l) = 0%Z.
    move: lk Kl; elim: (l) => [|[k' r'] l' IHl] /=.
      by move=> _ _; rewrite SMS.count_empty.
    move=> /Forall_cons_iff [kk' lk'] Kl'.
    have Kl'' : ∀ k0 r0, (k0, r0) ∈ l' → negb (is_gnon_free k0).
      by move=> k0 r0 h0; apply: (Kl' k0 r0); right.
    have nz : base z ≠ k'.
      by move=> e; move: kk'; rewrite -e ek; apply: irreflexivity.
    rewrite SMS.count_disj_union (IHl lk' Kl'').
    by rewrite (count_lfactors_ne _ _ _ (Kl' k' r' ltac:(by left)) nz).
  by rewrite ek; lia.
- by rewrite count_lfactors_ne // (IH Kl sl); lia.
Qed.

Lemma dh_factors_opp m :
  wf_dh m → dh_factors (dh_opp m) = SMS.inv (dh_factors m).
Proof.
move=> w; have w' := wf_dh_opp _ w; apply: SMS.count_inj => z.
rewrite SMS.count_inv !count_dh_factors // lookup_dh_opp lfactors_opp.
by rewrite SMS.count_inv.
Qed.

Lemma count_bind_make z (f : pre_term → SMS.sms pre_term) X Y :
  SMS.count z (SMS.bind f (SMS.make X Y)) =
  (SMS.count z (SMS.bind f (SMS.make X ∅)) -
   SMS.count z (SMS.bind f (SMS.make Y ∅)))%Z.
Proof.
rewrite !SMS.bind_make !SMS.count_make !MSet.bind_empty.
rewrite !MSet.count_disj_union !MSet.count_empty; lia.
Qed.

Lemma lfactors_fsum z (X : MSet.mset pre_term) :
  (∀ x, x ∈ X → wf x ∧ llogs x) →
  lfrac (Frac.fsum ((λ t, dh_map t !!! base z) <$> elements X)) ∧
  SMS.count z (lfactors (base z)
    (Frac.fsum ((λ t, dh_map t !!! base z) <$> elements X))) =
  SMS.count z (SMS.bind (λ x, dh_factors (dh_map x)) (SMS.make X ∅)).
Proof.
elim/(MSet.mset_ind (T := pre_term)): X => [|x X IH] h.
  rewrite MSet.elements_empty fmap_nil Frac.fsum_nil lfactors_zero.
  rewrite (_ : SMS.make ∅ ∅ = ∅) // SMS.bind_empty.
  by split; first exact: lfrac_zero.
have [wx lx] : wf x ∧ llogs x.
  apply: h; apply/MSet.elem_of_disj_union; left.
  exact/MSet.elem_of_singleton.
have [lX eX] : _ ∧ _ := IH (λ y hy, h y (proj2 (MSet.elem_of_disj_union _ _ _)
                                         (or_intror hy))).
rewrite Frac.fsum_disj_union MSet.elements_singleton fmap_cons fmap_nil.
rewrite Frac.fsum_cons Frac.fsum_nil.
rewrite (_ : Frac.add (Frac.add (dh_map x !!! base z) Frac.zero) _ =
             Frac.add (dh_map x !!! base z)
               (Frac.fsum ((λ t, dh_map t !!! base z) <$> elements X)));
  last by ring.
have [L E] := lfactors_add (base z) _ _ (lx (base z)) lX.
split=> //; rewrite E SMS.bind_make_singleton_l !SMS.count_disj_union eX.
by rewrite count_dh_factors //; exact: wf_dh_map.
Qed.

Lemma dh_factors_sum s :
  (∀ x, x ∈ s → wf x ∧ llogs x) →
  dh_factors (dh_sum s) = SMS.bind (λ x, dh_factors (dh_map x)) s.
Proof.
move=> h; have ws : wf_dh (dh_sum s) by apply: wf_dh_sum => x /h [].
apply: SMS.count_inj => z.
rewrite count_dh_factors // lookup_dh_sum_ssum Frac.ssumE.
transitivity (SMS.count z (SMS.bind (λ x, dh_factors (dh_map x))
                             (SMS.make (SMS.pos s) (SMS.neg s))));
  last by rewrite SMS.make_pos_neg.
have hp : ∀ x, x ∈ SMS.pos s → wf x ∧ llogs x.
  by move=> x hx; apply: h; exact: SMS.elem_of_pos hx.
have hn : ∀ x, x ∈ SMS.neg s → wf x ∧ llogs x.
  by move=> x hx; apply: h; exact: SMS.elem_of_neg hx.
have [lp ep] := lfactors_fsum z (SMS.pos s) hp.
have [ln en] := lfactors_fsum z (SMS.neg s) hn.
rewrite Frac.subE count_bind_make.
have [_ ->] := lfactors_add (base z) _ _ lp (lfrac_opp _ ln).
by rewrite SMS.count_disj_union lfactors_opp SMS.count_inv ep en; lia.
Qed.

Lemma lfactors_mk_exp b r n :
  negb (is_gnon_free b) → r ≠ Frac.zero → Frac.num r = Poly.mono n →
  lfactors b r = {[+ mk_exp b r +]}.
Proof.
move=> gb nr er.
rewrite /lfactors er Poly.car_mono SMS.bind_singleton /exp_factor.
by rewrite -er Frac.make_num_den er Poly.first_neg_mono.
Qed.

Lemma dh_factors_singleton b r :
  r ≠ Frac.zero → dh_factors {[b := r]} = lfactors b r.
Proof.
move=> nr; rewrite /dh_factors FMap.to_list_singleton //=.
by rewrite (right_id ∅ (⊎)).
Qed.

Lemma dh_factors_atom b :
  negb (is_gnon_free b) → dh_factors {[b := Frac.one]} = {[+ b +]}.
Proof.
move=> gb; have n1 : (Frac.one : frac) ≠ Frac.zero by apply: Frac.one_neq0.
have e1 : Frac.num (Frac.one : frac) = Poly.mono ∅.
  by rewrite Frac.num_one Poly.oneE.
rewrite (dh_factors_singleton _ _ n1) (lfactors_mk_exp _ _ _ gb n1 e1).
by rewrite /mk_exp bool_decide_eq_true_2.
Qed.

Lemma poly_of_lists_mono m :
  poly_of_lists ([m], []) = Poly.mono (MSet.of_list m).
Proof.
apply: Poly.car_inj; rewrite Poly.car_mono /poly_of_lists /=.
by rewrite MSet.of_list_cons MSet.of_list_nil (right_id ∅ (⊎)).
Qed.

Lemma gfactors_dh t : wf t → gfactors t = dh_factors (dh_map t).
Proof.
move=> wt; case E: (is_exp t); last first.
  rewrite /gfactors E; case: t wt E => [o|o t|o t1 t2|F|l] wt E //;
    by rewrite dh_factors_atom.
case: (is_expP t) E wt => [b m d -> _ wt|//].
have [wb [gb [aF cF]]] := wf_exp_entry _ _ wt.
set F := (([m], []), d) in wt aF cF *.
have lr : lists (of_lists F) = F := lists_of_lists _ cF.
set r := of_lists F in lr *.
have n1 : r ≠ Frac.one.
  move=> e; move: wt; rewrite wf_dhE => /andb_True [_].
  by rewrite /trivial_dh -lr e lists_one bool_decide_eq_true_2.
have er : Frac.num r = Poly.mono (MSet.of_list m).
  have e1 : poly_lists_of (Frac.num r) = ([m], []).
    by move: lr => /(f_equal fst).
  by rewrite -(poly_of_lists_of (Frac.num r)) e1 poly_of_lists_mono.
have nr : r ≠ Frac.zero.
  move=> e; move: er; rewrite e Frac.num_zero => e'.
  exact: (PolyGcd.mono_neq0 _ (eq_sym e')).
have Et : PTDH [(b, F)] = mk_exp b r.
  by rewrite /mk_exp bool_decide_eq_false_2 // lr.
have -> : gfactors (PTDH [(b, F)]) = {[+ PTDH [(b, F)] +]} by [].
rewrite Et (dh_map_mk_exp _ _ gb nr) (dh_factors_singleton _ _ nr).
by rewrite (lfactors_mk_exp _ _ _ gb nr er).
Qed.

Lemma gfactors_gmul s :
  (∀ x, x ∈ s → wf x ∧ llogs x) → gfactors (gmul s) = SMS.bind gfactors s.
Proof.
move=> h; have W : ∀ x, x ∈ s → wf x by move=> x /h [].
rewrite (gfactors_dh _ (wf_gmul _ W)) (dh_map_gmul _ W) (dh_factors_sum _ h).
by apply: SMS.bind_ext => x /W wx; rewrite gfactors_dh.
Qed.

Lemma dh_sum_inv_singleton t :
  dh_sum (SMS.inv {[+ t +]}) = dh_opp (dh_map t).
Proof.
apply/FMap.fmap_eq => k.
by rewrite lookup_dh_sum_ssum lookup_dh_opp Frac.ssum_inv Frac.ssum_singleton.
Qed.

Lemma gfactors_ginv t :
  wf t → gfactors (gmul (SMS.inv {[+ t +]})) = SMS.inv (gfactors t).
Proof.
move=> wt.
have W : ∀ x, x ∈ SMS.inv ({[+ t +]} : SMS.sms pre_term) → wf x.
  by move=> x /elem_of_inv_singleton ->.
rewrite (gfactors_dh _ (wf_gmul _ W)) (dh_map_gmul _ W) dh_sum_inv_singleton.
rewrite dh_factors_opp ?gfactors_dh //; exact: wf_dh_map.
Qed.

End DHMaps.

End PreTerm.
