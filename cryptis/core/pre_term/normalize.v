(** Pre-term normalization
    ======================

    This file defines a normalization function on pre-terms.  Pre-terms carry
    two algebraic structures:

    - the exponents [PTMod], rational functions with integer coefficients over
      atoms ([Frac.frac]);
    - the Diffie-Hellman group (a symbolic model of a prime-order
      elliptic-curve group), whose elements [PTDH] map bases to logarithms.

    An exponent [PTMod F] stores the numerator and the denominator of a
    rational function in the canonical form of [Frac] ([frac_lists_of],
    [canonical]): each polynomial is the sorted lists of its positive and of its
    negative monomials, and each monomial the sorted list of its atoms.  Atoms
    are pre-terms other than exponents, and a lone atom stands for itself
    ([mod_of_frac]).  The exponents form a field, with [inv 0 = 0].

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

    [core/term/presentation.v] proves this characterization for terms
    ([term_equiv_iff]).

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
Definition is_dh pt := if pt is PTDH _ then true else false.

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
    and of its denominator ([frac_lists_of]).  These lists are [canonical]. *)

Definition poly_lists_of (p : poly) : poly_lists :=
  (MSet.car <$> elements (SMS.pos (Poly.car p)),
   MSet.car <$> elements (SMS.neg (Poly.car p))).

Definition poly_of_lists (A : poly_lists) : poly :=
  Poly.mk (SMS.make (MSet.of_list (MSet.of_list <$> A.1))
                    (MSet.of_list (MSet.of_list <$> A.2))).

Definition frac_lists_of (r : frac) : frac_lists :=
  (poly_lists_of (Frac.num r), poly_lists_of (Frac.den r)).

Definition frac_of_lists (F : frac_lists) : frac :=
  Frac.make (poly_of_lists F.1) (poly_of_lists F.2).

Definition canonical (F : frac_lists) : bool :=
  bool_decide (frac_lists_of (frac_of_lists F) = F).

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

Definition mod_of_frac (r : frac) : pre_term := mod_of_lists (frac_lists_of r).

Definition frac_of pt : frac :=
  if pt is PTMod F then frac_of_lists F else Frac.of_poly (Poly.var pt).

(** The atoms of a pre-term are the variables of its fraction. *)
Definition atoms pt : list pre_term := Frac.vars (frac_of pt).

(** [all_atoms P F]: every atom of [F] satisfies [P]. *)
Definition all_atoms (P : pre_term → bool) (F : frac_lists) : bool :=
  forallb (forallb P) F.1.1 && forallb (forallb P) F.1.2 &&
  forallb (forallb P) F.2.1 && forallb (forallb P) F.2.2.

Definition map_lists (f : pre_term → pre_term) (F : frac_lists) : frac_lists :=
  ((map (map f) F.1.1, map (map f) F.1.2),
   (map (map f) F.2.1, map (map f) F.2.2)).

(** [mod_subst r] evaluates a fraction whose atoms may be exponents. *)
Definition mod_subst (r : frac) : pre_term := mod_of_frac (Frac.bind frac_of r).

(** ** Diffie-Hellman terms

    A group element is a finite map from bases to logarithms ([dh_map]).
    [gmul] adds the maps of a signed multiset of group elements, and [exp]
    multiplies every logarithm; [dh_of] turns a map back into a pre-term. *)

Definition dhmap := FMap.fmap pre_term frac Frac.zero.

Definition mk_exp b (r : frac) : pre_term :=
  if bool_decide (r = Frac.one) then b else PTDH [(b, frac_lists_of r)].

Definition entries (m : dhmap) : list entry :=
  (λ p, (p.1, frac_lists_of p.2)) <$> FMap.to_list m.

Definition dh_of (m : dhmap) : pre_term :=
  if FMap.to_list m is [(b, r)] then mk_exp b r else PTDH (entries m).

Definition of_entries (l : list entry) : dhmap :=
  foldr (λ e m, <[e.1 := frac_of_lists e.2]> m) ∅ l.

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
  | PTMod F => mod_subst (frac_of_lists (map_lists normalize F))
  | PTDH l =>
    gmul (foldr (λ e s,
      {[+ exp_frac (normalize e.1)
            (Frac.bind frac_of (frac_of_lists (map_lists normalize e.2))) +]}
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

Lemma frac_of_listsK r : frac_of_lists (frac_lists_of r) = r.
Proof. by rewrite /frac_of_lists /frac_lists_of /= !poly_of_lists_of
  Frac.make_num_den. Qed.

Lemma canonical_frac_lists_of r : canonical (frac_lists_of r).
Proof. by rewrite /canonical frac_of_listsK bool_decide_eq_true_2. Qed.

Lemma frac_lists_ofK F : canonical F → frac_lists_of (frac_of_lists F) = F.
Proof. exact: bool_decide_unpack. Qed.

Lemma frac_lists_of_inj r1 r2 : frac_lists_of r1 = frac_lists_of r2 → r1 = r2.
Proof. by move=> e; rewrite -(frac_of_listsK r1) e frac_of_listsK. Qed.

Lemma poly_lists_mono m : poly_lists_of (Poly.mono m) = ([MSet.car m], []).
Proof.
rewrite /poly_lists_of Poly.car_mono SMS.pos_singleton SMS.neg_singleton.
by rewrite MSet.elements_singleton MSet.elements_empty.
Qed.

Lemma poly_lists_one : poly_lists_of Poly.one = ([[]], []).
Proof. by rewrite Poly.oneE poly_lists_mono MSet.car_empty. Qed.

Lemma poly_lists_one_inv (q : poly) :
  poly_lists_of q = ([[]], []) → q = Poly.one.
Proof.
move=> e; rewrite -(poly_of_lists_of q) e -(poly_of_lists_of Poly.one).
by rewrite poly_lists_one.
Qed.

Lemma poly_lists_zero : poly_lists_of Poly.zero = ([], []).
Proof.
rewrite /poly_lists_of Poly.car_zero SMS.pos_empty SMS.neg_empty.
by rewrite MSet.elements_empty.
Qed.

Lemma frac_lists_of_var x :
  frac_lists_of (Frac.of_poly (Poly.var x)) = (([[x]], []), ([[]], [])).
Proof.
rewrite /frac_lists_of Frac.num_of_poly Frac.den_of_poly Poly.varE Poly.oneE.
by rewrite !poly_lists_mono MSet.car_singleton MSet.car_empty.
Qed.

Lemma frac_lists_of_one : frac_lists_of Frac.one = one_lists.
Proof.
rewrite /frac_lists_of Frac.num_one Frac.den_one Poly.oneE.
by rewrite !poly_lists_mono MSet.car_empty.
Qed.

Lemma frac_of_one : frac_of one = Frac.one.
Proof. by rewrite /one /frac_of -frac_lists_of_one frac_of_listsK. Qed.

Lemma frac_lists_of_zero : frac_lists_of Frac.zero = zero_lists.
Proof.
rewrite /frac_lists_of Frac.num_zero Frac.den_zero Poly.oneE.
by rewrite poly_lists_mono poly_lists_zero MSet.car_empty.
Qed.

Lemma lone_atom_Some F x :
  lone_atom F = Some x ↔ F = (([[x]], []), ([[]], [])).
Proof.
split; last by move=> ->.
rewrite /lone_atom; repeat case_match; congruence.
Qed.

(** ** Exponents *)

Lemma all_atoms_frac_lists_of (P : pre_term → bool) r :
  all_atoms P (frac_lists_of r) ↔ Frac.all_vars P r.
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
rewrite /all_atoms /frac_lists_of /poly_lists_of /=.
rewrite -andb_assoc !andb_True -!(andb_True (forallb _ _)).
rewrite (M (Poly.car (Frac.num r))) (M (Poly.car (Frac.den r))) /Frac.all_vars.
naive_solver.
Qed.

Lemma frac_of_Nmod pt :
  negb (is_mod pt) → frac_of pt = Frac.of_poly (Poly.var pt).
Proof. by case: pt. Qed.

Lemma frac_of_mod_of_frac r :
  Frac.all_vars (λ x, negb (is_mod x)) r → frac_of (mod_of_frac r) = r.
Proof.
rewrite /mod_of_frac /mod_of_lists => h.
case E: (lone_atom (frac_lists_of r)) => [x|];
  last by rewrite /= frac_of_listsK.
move/lone_atom_Some: E => E.
have Er : r = Frac.of_poly (Poly.var x).
  by apply: frac_lists_of_inj; rewrite frac_lists_of_var.
subst r; apply: frac_of_Nmod; apply: (h {[+ x +]} x).
- by left; rewrite Frac.car_num_var; apply/SMS.elem_of_singleton.
- exact/MSet.elem_of_singleton.
Qed.


(** *** Atoms of fractions *)


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

Lemma all_vars_frac_of_lists (P : pre_term → Prop) F :
  (∀ x, in_lists F x → P x) → Frac.all_vars P (frac_of_lists F).
Proof.
move=> h; set vs := mjoin (F.1.1 ++ F.1.2 ++ F.2.1 ++ F.2.2).
have hvs : ∀ x, in_lists F x → x ∈ vs.
  move=> x [m [mF xm]]; apply/list_elem_of_join; exists m; split=> //.
  by rewrite !elem_of_app.
have P_lists (A : poly_lists) :
    (∀ m x, m ∈ A.1 ∨ m ∈ A.2 → x ∈ m → x ∈ vs) →
    PolyGcd.over vs (poly_of_lists A).
  move=> hA; apply: PolyGcd.over_intro => m x /= /SMS.elem_of_make.
  case=> /MSet.elem_of_of_list /list_elem_of_fmap [l [-> lA]]
    /MSet.elem_of_of_list xl; apply: (hA l x) => //; by [left|right].
apply: (Frac.all_vars_over _ vs).
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

Lemma wf_mod_of_frac r :
  Frac.all_vars (λ x, wf x && negb (is_mod x)) r → wf (mod_of_frac r).
Proof.
move=> h; rewrite /mod_of_frac /mod_of_lists.
case E: (lone_atom (frac_lists_of r)) => [x|].
- move/lone_atom_Some: E => E.
  have Er : r = Frac.of_poly (Poly.var x).
    by apply: frac_lists_of_inj; rewrite frac_lists_of_var.
  subst r.
  have /andb_True [] // : Is_true (wf x && negb (is_mod x)).
  apply: (h {[+ x +]} x); last exact/MSet.elem_of_singleton.
  by left; rewrite Frac.car_num_var; apply/SMS.elem_of_singleton.
- rewrite wf_modE /lone E.
  apply/andb_True; split; last done; apply/andb_True; split.
  + exact: (proj2 (all_atoms_frac_lists_of (λ x, wf x && negb (is_mod x)) r) h).
  + exact: canonical_frac_lists_of.
Qed.

Lemma mod_of_frac_frac_of pt : wf pt → mod_of_frac (frac_of pt) = pt.
Proof.
case: pt => [o|o t|o t1 t2|F|l] /=; try
  by rewrite /mod_of_frac frac_lists_of_var.
move=> /andb_True [/andb_True [_ cF] nl].
rewrite /mod_of_frac (frac_lists_ofK _ cF) /mod_of_lists.
by move: nl; rewrite /lone; case: (lone_atom F).
Qed.

Lemma frac_of_atoms pt :
  wf pt → Frac.all_vars (λ x, wf x && negb (is_mod x)) (frac_of pt).
Proof.
case: pt => [o|o t|o t1 t2|F|l] /= wpt;
  try by apply: Frac.all_vars_var; apply/andb_True.
move: wpt => /andb_True [/andb_True [aF cF] _].
apply: (proj1 (all_atoms_frac_lists_of (λ x, wf x && negb (is_mod x)) _)).
by rewrite (frac_lists_ofK _ cF).
Qed.

Lemma frac_of_mod_of_frac_wf r :
  Frac.all_vars (λ x, wf x && negb (is_mod x)) r → frac_of (mod_of_frac r) = r.
Proof.
move=> h; apply: frac_of_mod_of_frac; apply: Frac.all_vars_impl h.
by move=> x /andb_True [].
Qed.

Lemma bind_frac_of_id r :
  Frac.all_vars (λ x, negb (is_mod x)) r → Frac.bind frac_of r = r.
Proof.
move=> h.
have E : ∀ m x, m ∈ Poly.car (Frac.num r) ∨ m ∈ Poly.car (Frac.den r) →
    x ∈ m → frac_of x = Frac.of_poly (Poly.var x).
  move=> m x mr xm; exact: frac_of_Nmod (h m x mr xm).
by rewrite (Frac.bind_ext _ _ _ E) Frac.bind_var_map Frac.map_id.
Qed.

Lemma wf_mod_subst r :
  (∀ x, x ∈ Frac.vars r → wf x) → wf (mod_subst r).
Proof.
move=> h; apply wf_mod_of_frac; apply: Frac.all_vars_bind => x xr.
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
  of_entries l !!! k = frac_of_lists (FMap.lookup_list zero_lists k l).
Proof.
elim: l => [|[b F] l IH] /=.
  by rewrite FMap.lookup_empty -frac_lists_of_zero frac_of_listsK.
by rewrite FMap.lookup_insert IH; case: bool_decide.
Qed.

Lemma lookup_list_entries m k :
  FMap.lookup_list zero_lists k (entries m) = frac_lists_of (m !!! k).
Proof.
rewrite /entries lookup_to_list; elim: (FMap.to_list m) => [|[b r] l IH] /=.
  by rewrite frac_lists_of_zero.
by rewrite IH; case: bool_decide.
Qed.

Lemma elem_of_entries m k F :
  (k, F) ∈ entries m ↔ F = frac_lists_of (m !!! k) ∧ m !!! k ≠ Frac.zero.
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
  by apply: nr; rewrite -(frac_of_listsK (m !!! k)) e -frac_lists_of_zero
    frac_of_listsK.
Qed.

(** The keys of a well-formed map are bases, and its logarithms have
    normal atoms. *)
Definition wf_dh (m : dhmap) : Prop :=
  ∀ k, m !!! k ≠ Frac.zero →
    wf k ∧ negb (is_gnon_free k) ∧
    Frac.all_vars (λ x, wf x && negb (is_mod x)) (m !!! k).

Lemma wf_dh_atoms m k :
  wf_dh m → Frac.all_vars (λ x, wf x && negb (is_mod x)) (m !!! k).
Proof.
move=> wm; case: (decide (m !!! k = Frac.zero)) => [->|nz].
  exact: Frac.all_vars_zero.
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
apply/andb_True; split; last exact: canonical_frac_lists_of.
apply/andb_True; split.
  by apply/andb_True.
exact: (proj2 (all_atoms_frac_lists_of _ _) ak).
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
    by move=> /(f_equal frac_of_lists);
      rewrite frac_of_listsK -frac_lists_of_one
      frac_of_listsK.
  apply/andb_True; split.
  + apply/andb_True; split; last done.
    apply/andb_True; split; last exact: canonical_frac_lists_of.
    apply/andb_True; split; first by apply/andb_True.
    exact: (proj2 (all_atoms_frac_lists_of _ _) ab).
  + apply bool_decide_pack; split; first by repeat constructor.
    apply/Forall_singleton => /= e0; apply: nr.
    by rewrite -(frac_of_listsK r) e0 -frac_lists_of_zero frac_of_listsK.
- rewrite wf_dhE; apply/andb_True; split.
    by apply/andb_True; split; [exact: wf_dh_entries|exact: wf_entries].
  by rewrite /entries E.
Qed.

Lemma dh_map_dh_of m : wf_dh m → dh_map (dh_of m) = m.
Proof.
move=> wm; rewrite /dh_of.
have Hent : of_entries (entries m) = m.
  apply/FMap.fmap_eq => k.
  by rewrite lookup_of_entries lookup_list_entries frac_of_listsK.
case E: (FMap.to_list m) => [|[b r] [|e l]]; try exact: Hent.
have /FMap.elem_of_to_list [mb nr] : (b, r) ∈ FMap.to_list m.
  by rewrite E; left.
have [wb [gb ab]] := wm b ltac:(by rewrite mb).
apply/FMap.fmap_eq => k; rewrite [RHS]lookup_to_list E /=.
rewrite /mk_exp; case: bool_decide_reflect => [r1|n1].
- rewrite (dh_map_Ngnf _ gb) FMap.lookup_singleton r1.
  by case: bool_decide.
- by rewrite /= FMap.lookup_insert frac_of_listsK FMap.lookup_empty.
Qed.

Lemma lookup_list_canonical (l : list entry) k :
  forallb (λ e, wf e.1 && negb (is_gnon_free e.1)
                && all_atoms (λ x, wf x && negb (is_mod x)) e.2
                && canonical e.2) l →
  canonical (FMap.lookup_list zero_lists k l).
Proof.
elim: l => [|[b F] l IH] /=.
  by move=> _; have := canonical_frac_lists_of Frac.zero;
    rewrite frac_lists_of_zero.
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
rewrite lookup_list_entries lookup_of_entries frac_lists_ofK //.
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
by rewrite r1 frac_lists_of_one /trivial_dh bool_decide_eq_true_2.
Qed.

Lemma wf_dh_map pt : wf pt → wf_dh (dh_map pt).
Proof.
case: pt => [o|o t|o t1 t2|F|l] wpt k;
  try (rewrite /= FMap.lookup_singleton;
       case: (bool_decide_reflect (k = _)) => [->|_] //= _;
       by split=> //; split; [|exact: Frac.all_vars_one]).
have [hl _] : Is_true (forallb (λ e, wf e.1 && negb (is_gnon_free e.1)
                && all_atoms (λ x, wf x && negb (is_mod x)) e.2
                && canonical e.2) l) ∧ True.
  by move: wpt; rewrite wf_dhE => /andb_True [/andb_True []].
rewrite /= lookup_of_entries => nz.
have nF : FMap.lookup_list zero_lists k l ≠ zero_lists.
  by move=> e; apply: nz; rewrite e -frac_lists_of_zero frac_of_listsK.
have /(lookup_list_elem _ _) kl := nF.
move: hl => /forallb_True /list.Forall_forall /(_ _ kl) /=.
move=> /andb_True [/andb_True [/andb_True [wk gk] ak] ck].
split=> //; split=> //.
by apply/all_atoms_frac_lists_of; rewrite frac_lists_ofK.
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
  by apply: Frac.all_vars_add; apply: wf_dh_atoms.
- have [wk [gk _]] := w2 k n2; split=> //; split=> //.
  by apply: Frac.all_vars_add; apply: wf_dh_atoms.
Qed.

Lemma wf_dh_opp m : wf_dh m → wf_dh (dh_opp m).
Proof.
move=> w k; rewrite lookup_dh_opp => nz.
have n : m !!! k ≠ Frac.zero by move=> e; apply: nz; rewrite e Frac.opp_zero.
have [wk [gk ak]] := w k n; split=> //; split=> //.
exact: Frac.all_vars_opp.
Qed.

Lemma wf_dh_scale r m :
  Frac.all_vars (λ x, wf x && negb (is_mod x)) r → wf_dh m →
    wf_dh (dh_scale r m).
Proof.
move=> ar w k; rewrite lookup_dh_scale => nz.
have n : m !!! k ≠ Frac.zero by move=> e; apply: nz; rewrite e Frac.mul_zero_l.
have [wk [gk ak]] := w k n; split=> //; split=> //.
exact: Frac.all_vars_mul.
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
  wf b → Frac.all_vars (λ x, wf x && negb (is_mod x)) r → wf (exp_frac b r).
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
by rewrite /= FMap.lookup_insert frac_of_listsK FMap.lookup_empty
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

Lemma vars_in_lists F x : x ∈ Frac.vars (frac_of_lists F) → in_lists F x.
Proof.
have := all_vars_frac_of_lists (in_lists F) F (λ x hx, hx).
by move=> /Frac.all_vars_iff; apply.
Qed.

Lemma in_lists_frac_lists_of r y :
  in_lists (frac_lists_of r) y ↔ y ∈ Frac.vars r.
Proof.
split.
  2: by rewrite -{1}(frac_of_listsK r) => /vars_in_lists.
case=> m [hm ym]; rewrite /Frac.vars elem_of_app !Poly.elem_of_vars.
have E (p : Poly.poly pre_term) :
    m ∈ (poly_lists_of p).1 ∨ m ∈ (poly_lists_of p).2 →
    ∃ n, n ∈ Poly.car p ∧ y ∈ n.
  rewrite /poly_lists_of /=.
  case=> /list_elem_of_fmap [n [em /MSet.elem_of_elements nn]]; exists n.
  - by split; [exact: SMS.elem_of_pos|move: ym; rewrite em].
  - by split; [exact: SMS.elem_of_neg|move: ym; rewrite em].
by case: hm => [h|[h|[h|h]]]; [left|left|right|right]; apply: E; tauto.
Qed.

Lemma atoms_bind_normalize F :
  (∀ y, in_lists F y → wf (normalize y)) →
  Frac.all_vars (λ x, wf x && negb (is_mod x))
    (Frac.bind frac_of (frac_of_lists (map_lists normalize F))).
Proof.
move=> h; apply: Frac.all_vars_bind => x /vars_in_lists.
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
- apply wf_mod_subst => x /vars_in_lists /in_lists_map [y [yF ->]].
  exact: frac_all_in IH y yF.
- apply wf_gmul => t /elem_of_foldr_singletons [[b F] [eb ->]] /=.
  have [wb [HF]] :=
    proj1 (list.Forall_forall _ _) (entries_all_Forall IH) _ eb.
  apply wf_exp_frac => //; apply: atoms_bind_normalize => y yF.
  exact: frac_all_in HF y yF.
Qed.

Lemma normalize_lists_wf F :
  frac_all (λ x, wf x → normalize x = x) F →
  all_atoms (λ x, wf x && negb (is_mod x)) F →
  Frac.bind frac_of (frac_of_lists (map_lists normalize F)) = frac_of_lists F.
Proof.
move=> IH aF.
have hF : ∀ x, in_lists F x → wf x ∧ negb (is_mod x).
  by move=> x xF; apply/andb_True; apply: (proj1 (all_atoms_in _ _) aF x xF).
have Hid : ∀ x, in_lists F x → normalize x = x.
  by move=> x xF; apply: (frac_all_in _ _ IH x xF); case: (hF x xF).
rewrite (map_lists_id _ _ Hid); apply: bind_frac_of_id.
by apply: all_vars_frac_of_lists => x xF; case: (hF x xF).
Qed.

Lemma fsum_singletons (l : list entry) k :
  StronglySorted lexico (FMap.keys l) →
  Frac.fsum ((λ e, if bool_decide (k = e.1) then frac_of_lists e.2
                   else Frac.zero) <$> l) =
  frac_of_lists (FMap.lookup_list zero_lists k l).
Proof.
elim: l => [|[b F] l IH] /=.
  by move=> _; rewrite Frac.fsum_nil -frac_lists_of_zero frac_of_listsK.
move=> /StronglySorted_cons [lb sl]; rewrite Frac.fsum_cons.
case: (bool_decide_reflect (k = b)) => [->|nk]; last first.
  by rewrite (left_id Frac.zero Frac.add) IH.
have -> : Frac.fsum ((λ e, if bool_decide (b = e.1) then frac_of_lists e.2
                           else Frac.zero) <$> l) = Frac.zero.
  move: lb; elim: (l) => [|[b' F'] l' IHl] /=; first by rewrite Frac.fsum_nil.
  move=> /Forall_cons_iff [bb' lb]; rewrite Frac.fsum_cons.
  rewrite IHl // bool_decide_eq_false_2; last first.
    by move=> e; move: bb'; rewrite /= -e; apply: irreflexivity.
  exact: (left_id Frac.zero Frac.add).
by move: (frac_of_lists F) => a; ring.
Qed.

Lemma normalize_entries (l : list entry) :
  forallb (λ e, wf e.1 && negb (is_gnon_free e.1)
                && all_atoms (λ x, wf x && negb (is_mod x)) e.2
                && canonical e.2) l →
  Forall (λ e, (wf e.1 → normalize e.1 = e.1) ∧
               inhabited (frac_all (λ x, wf x → normalize x = x) e.2)) l →
  (foldr (λ e s, {[+ exp_frac (normalize e.1)
            (Frac.bind frac_of (frac_of_lists (map_lists normalize e.2))) +]}
            ⊎ s) ∅ l : SMS.sms pre_term) =
  foldr (λ e s, {[+ exp_frac e.1 (frac_of_lists e.2) +]} ⊎ s) ∅ l.
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
  rewrite /mod_subst (normalize_lists_wf F IH aF).
  rewrite /mod_of_frac (frac_lists_ofK _ cF) /mod_of_lists.
  by move: nl; rewrite /lone; case: (lone_atom F).
- move=> wl; move: (wl) => /andb_True [/andb_True [hl wfl] _].
  have Hl := entries_all_Forall IH.
  rewrite (normalize_entries l hl Hl).
  set f := λ e : entry, exp_frac e.1 (frac_of_lists e.2).
  rewrite -[RHS](dh_of_dh_map (PTDH l) wl) /gmul; congr dh_of.
  apply/FMap.fmap_eq => k; rewrite lookup_dh_sum foldr_singletons.
  rewrite SMS.pos_make_empty_r SMS.neg_make_empty_r /= lookup_of_entries.
  have [sl _] := bool_decide_unpack _ wfl.
  transitivity (Frac.fsum ((λ e : entry, if bool_decide (k = e.1)
                             then frac_of_lists e.2 else Frac.zero) <$> l));
    last exact: fsum_singletons.
  rewrite MSet.elements_empty /= Frac.fsum_nil Frac.subE Frac.opp_zero.
  assert (E1 : Frac.fsum ((λ t, dh_map t !!! k) <$> elements
                 (MSet.of_list
                    ((λ e : entry, exp_frac e.1 (frac_of_lists e.2)) <$> l)))
               = Frac.fsum ((λ t, dh_map t !!! k) <$>
                   ((λ e : entry, exp_frac e.1 (frac_of_lists e.2)) <$> l))).
    by apply: Frac.fsum_perm; apply: fmap_Permutation;
      exact: MSet.elements_of_list.
  rewrite E1 -list_fmap_compose.
  assert (E2 : ((λ t, dh_map t !!! k) ∘
                 (λ e : entry, exp_frac e.1 (frac_of_lists e.2))) <$> l =
               (λ e : entry, if bool_decide (k = e.1) then frac_of_lists e.2
                             else Frac.zero) <$> l).
    apply: list_fmap_ext => i [b F] hi.
    have eb := list_elem_of_lookup_2 _ _ _ hi.
    have := proj1 (list.Forall_forall _ _) (proj1 (forallb_True _ _) hl) _ eb.
    move=> /= /andb_True [/andb_True [/andb_True [_ gb] _] cF].
    have [_ /list.Forall_forall nz] := bool_decide_unpack _ wfl.
    have nF := nz _ eb; rewrite /= in nF.
    have nr : frac_of_lists F ≠ Frac.zero.
      by move=> e; apply: nF;
        rewrite -(frac_lists_ofK _ cF) e frac_lists_of_zero.
    rewrite /= (exp_frac_atom _ _ gb nr) (dh_map_mk_exp _ _ gb nr).
    exact: FMap.lookup_singleton.
  rewrite E2; by move: (Frac.fsum _) => a; ring.
Qed.

Lemma normalize_idem pt : normalize (normalize pt) = normalize pt.
Proof. exact: normalize_wf (wf_normalize pt). Qed.

End DHMaps.

End PreTerm.
