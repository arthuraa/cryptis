(** Pre-term normalization
    ======================

    A pre-term is read as an exponent ([frac_of], a rational function over
    atoms) or as a Diffie-Hellman group element ([dh_map], a map from bases
    to logarithms); every head that a reading does not interpret is an atom,
    or a base.  [mod_of_frac] and [dh_of] write canonical values back as
    pre-terms, and [normalize] evaluates each operation on the readings of
    its normalized arguments and writes the result back.  A lone atom is
    written as itself and a base with logarithm [1] as the base, so that the
    normal form of an atom does not depend on the reading that produced it.

    The exponents are rational functions with integer coefficients over
    atoms ([Frac.frac]), a field with [inv 0 = 0]; the Diffie-Hellman group (a
    symbolic model of a prime-order elliptic-curve group) is the free module
    over them on the bases.  Writing [1G], [g ^ x], [u ⋅ v] and [u^-1] for its
    operations, two pre-terms have the same normal form if and only if they
    are equal according to the field laws for exponents, the group laws for
    [⋅] and the following equations ([normalize_equiv] in
    [core/term/presentation.v]):

    - [(g ^ a) ^ b = g ^ (a * b)]
    - [g ^ a ⋅ g ^ b = g ^ (a + b)]
    - [g ^ 1 = g]
    - [(u ⋅ v) ^ x = u^x ⋅ v^x]

    Normal forms are the pre-terms that [normalize] fixes ([wf]).  Their
    atoms satisfy [wf_atom], their fractions [wf_frac] and their
    Diffie-Hellman maps [wf_dh].  We have the following properties:

   - [normalize_wf : wf t -> normalize t = t]
   - [wf_normalize : wf (normalize t)]
   - [normalize_idem : normalize (normalize t) = normalize t]

*)

From stdpp Require Import sorting list numbers.
From cryptis Require Import lib.
From cryptis.lib Require Import list_sort fmap mset sms poly poly_gcd frac.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith Lia Ring.
From cryptis.core.pre_term Require Export base with_stdpp.

Module PreTerm.
Import base.PreTerm.

Local Abbreviation poly := (Poly.poly pre_term).
Local Abbreviation frac := (Frac.frac pre_term).

Fixpoint height (pt : pre_term) : nat :=
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (height pt)
  | PT2 _ pt1 pt2 => S (Nat.max (height pt1) (height pt2))
  end.

(** ** Readings *)

Implicit Types (t u : pre_term).

Definition dhmap := FMap.fmap pre_term frac Frac.zero.

Definition is_mod t : bool :=
  match t with
  | PT0 O0Zero | PT0 O0One | PT1 O1Opp _ | PT1 O1Inv _
  | PT2 O2Add _ _ | PT2 O2Mul _ _ => true
  | _ => false
  end.

Definition is_dh t : bool :=
  match t with
  | PT0 O0GOne | PT1 O1GInv _ | PT2 O2GMul _ _ | PT2 O2Exp _ _ => true
  | _ => false
  end.

Fixpoint frac_of t : frac :=
  match t with
  | PT0 O0Zero => Frac.zero
  | PT0 O0One => Frac.one
  | PT1 O1Opp t1 => Frac.opp (frac_of t1)
  | PT1 O1Inv t1 => Frac.inv (frac_of t1)
  | PT2 O2Add t1 t2 => Frac.add (frac_of t1) (frac_of t2)
  | PT2 O2Mul t1 t2 => Frac.mul (frac_of t1) (frac_of t2)
  | _ => Frac.var t
  end.

Definition dh_add (m1 m2 : dhmap) : dhmap :=
  FMap.cast (left_id Frac.zero Frac.add Frac.zero) (FMap.merge Frac.add m1 m2).

Definition dh_opp (m : dhmap) : dhmap :=
  FMap.cast Frac.opp_zero (FMap.map Frac.opp m).

Definition dh_scale (r : frac) (m : dhmap) : dhmap :=
  FMap.cast (Frac.mul_zero_l r) (FMap.map (λ f, Frac.mul f r) m).

Fixpoint dh_map t : dhmap :=
  match t with
  | PT0 O0GOne => ∅
  | PT1 O1GInv t1 => dh_opp (dh_map t1)
  | PT2 O2GMul t1 t2 => dh_add (dh_map t1) (dh_map t2)
  | PT2 O2Exp t1 t2 => dh_scale (frac_of t2) (dh_map t1)
  | _ => {[t := Frac.one]}
  end.

(** ** Writing values back *)

Fixpoint fold_tree_ne (op : pre_term → pre_term → pre_term) t
    (l : list pre_term) : pre_term :=
  if l is u :: l then op t (fold_tree_ne op u l) else t.

Definition fold_tree (op : pre_term → pre_term → pre_term) (unit : pre_term)
    (l : list pre_term) : pre_term :=
  if l is t :: l then fold_tree_ne op t l else unit.

Definition encode_mono (M : MSet.mset pre_term) : pre_term :=
  fold_tree (PT2 O2Mul) (PT0 O0One) (elements M).

Definition encode_sum (Ms : list (MSet.mset pre_term)) : pre_term :=
  fold_tree (PT2 O2Add) (PT0 O0Zero) (encode_mono <$> Ms).

Definition encode_signed (P N : list (MSet.mset pre_term)) : pre_term :=
  match N, P with
  | [], _ => encode_sum P
  | _, [] => PT1 O1Opp (encode_sum N)
  | _, _ => PT2 O2Add (encode_sum P) (PT1 O1Opp (encode_sum N))
  end.

Definition encode_poly (p : Poly.poly pre_term) : pre_term :=
  encode_signed (elements (SMS.pos (Poly.car p)))
    (elements (SMS.neg (Poly.car p))).

Definition mod_of_frac (r : frac) : pre_term :=
  if bool_decide (Frac.den r = Poly.one) then encode_poly (Frac.num r)
  else PT2 O2Mul (encode_poly (Frac.num r))
         (PT1 O1Inv (encode_poly (Frac.den r))).

(** A base with logarithm [1] is the base itself, so that a power of an atom
    to the [1] has the normal form of the atom. *)
Definition mk_exp b (r : frac) : pre_term :=
  if bool_decide (r = Frac.one) then b else PT2 O2Exp b (mod_of_frac r).

Definition dh_of (m : dhmap) : pre_term :=
  fold_tree (PT2 O2GMul) (PT0 O0GOne)
    ((λ e, mk_exp e.1 e.2) <$> FMap.to_list m).

(** ** Normalization *)

Fixpoint normalize t : pre_term :=
  match t with
  | PT0 O0Zero => mod_of_frac Frac.zero
  | PT0 O0One => mod_of_frac Frac.one
  | PT0 O0GOne => dh_of ∅
  | PT0 o => PT0 o
  | PT1 O1Opp t1 => mod_of_frac (Frac.opp (frac_of (normalize t1)))
  | PT1 O1Inv t1 => mod_of_frac (Frac.inv (frac_of (normalize t1)))
  | PT1 O1GInv t1 => dh_of (dh_opp (dh_map (normalize t1)))
  | PT1 o t1 => PT1 o (normalize t1)
  | PT2 O2Add t1 t2 =>
    mod_of_frac
      (Frac.add (frac_of (normalize t1)) (frac_of (normalize t2)))
  | PT2 O2Mul t1 t2 =>
    mod_of_frac
      (Frac.mul (frac_of (normalize t1)) (frac_of (normalize t2)))
  | PT2 O2GMul t1 t2 =>
    dh_of (dh_add (dh_map (normalize t1)) (dh_map (normalize t2)))
  | PT2 O2Exp t1 t2 =>
    dh_of (dh_scale (frac_of (normalize t2)) (dh_map (normalize t1)))
  | PT2 o t1 t2 => PT2 o (normalize t1) (normalize t2)
  end.

(** Each equation below holds by computation; rewriting with them keeps
    [simpl] away from [mod_of_frac], [dh_of] and [∅]. *)

Lemma normalize_zero : normalize (PT0 O0Zero) = mod_of_frac Frac.zero.
Proof. by []. Qed.

Lemma normalize_one : normalize (PT0 O0One) = mod_of_frac Frac.one.
Proof. by []. Qed.

Lemma normalize_opp t :
  normalize (PT1 O1Opp t) = mod_of_frac (Frac.opp (frac_of (normalize t))).
Proof. by []. Qed.

Lemma normalize_inv t :
  normalize (PT1 O1Inv t) = mod_of_frac (Frac.inv (frac_of (normalize t))).
Proof. by []. Qed.

Lemma normalize_add t1 t2 :
  normalize (PT2 O2Add t1 t2) =
  mod_of_frac
    (Frac.add (frac_of (normalize t1)) (frac_of (normalize t2))).
Proof. by []. Qed.

Lemma normalize_mul t1 t2 :
  normalize (PT2 O2Mul t1 t2) =
  mod_of_frac
    (Frac.mul (frac_of (normalize t1)) (frac_of (normalize t2))).
Proof. by []. Qed.

Lemma normalize_ginv t :
  normalize (PT1 O1GInv t) = dh_of (dh_opp (dh_map (normalize t))).
Proof. by []. Qed.

Lemma normalize_gmul t1 t2 :
  normalize (PT2 O2GMul t1 t2) =
  dh_of (dh_add (dh_map (normalize t1)) (dh_map (normalize t2))).
Proof. by []. Qed.

Lemma normalize_exp t1 t2 :
  normalize (PT2 O2Exp t1 t2) =
  dh_of (dh_scale (frac_of (normalize t2)) (dh_map (normalize t1))).
Proof. by []. Qed.

(** ** Round trips *)

Section RoundTrips.

Add Ring flat_frac_ring : (Frac.frac_ring_theory (T := pre_term)).

Implicit Types (r : frac) (m : dhmap) (p : Poly.poly pre_term).

#[local] Lemma frac_of_atom t : is_mod t = false → frac_of t = Frac.var t.
Proof. by case: t => [[]|[] ?|[] ? ?]. Qed.

Lemma dh_map_base t : is_dh t = false → dh_map t = {[t := Frac.one]}.
Proof. by case: t => [[]|[] ?|[] ? ?]. Qed.

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

Lemma lookup_dh_add_neq0 m1 m2 k : dh_add m1 m2 !!! k ≠ Frac.zero →
  m1 !!! k ≠ Frac.zero ∨ m2 !!! k ≠ Frac.zero.
Proof.
rewrite lookup_dh_add.
case: (decide (m1 !!! k = Frac.zero)) => [->|]; last by left.
by move=> nz; right=> e2; apply: nz; rewrite e2; ring.
Qed.

Lemma vars_num r x : x ∈ Poly.vars (Frac.num r) → x ∈ Frac.vars r.
Proof. by move=> h; rewrite /Frac.vars elem_of_app; left. Qed.

Lemma vars_den r x : x ∈ Poly.vars (Frac.den r) → x ∈ Frac.vars r.
Proof. by move=> h; rewrite /Frac.vars elem_of_app; right. Qed.

Lemma frac_of_fold_mul l :
  frac_of (fold_tree (PT2 O2Mul) (PT0 O0One) l) =
  Frac.fprod (frac_of <$> l).
Proof.
case: l => [|t l] /=; first by rewrite Frac.fprod_nil.
elim: l t => [|u l IH] t /=.
  by rewrite Frac.fprod_cons Frac.fprod_nil; ring.
by rewrite IH !Frac.fprod_cons.
Qed.

Lemma frac_of_fold_add l :
  frac_of (fold_tree (PT2 O2Add) (PT0 O0Zero) l) =
  Frac.fsum (frac_of <$> l).
Proof.
case: l => [|t l] /=; first by rewrite Frac.fsum_nil.
elim: l t => [|u l IH] t /=.
  by rewrite Frac.fsum_cons Frac.fsum_nil; ring.
by rewrite IH !Frac.fsum_cons.
Qed.

Lemma dh_map_fold l k :
  dh_map (fold_tree (PT2 O2GMul) (PT0 O0GOne) l) !!! k =
  Frac.fsum ((λ t, dh_map t !!! k) <$> l).
Proof.
case: l => [|t l] /=; first by rewrite FMap.lookup_empty Frac.fsum_nil.
elim: l t => [|u l IH] t /=.
  by rewrite Frac.fsum_cons Frac.fsum_nil; ring.
by rewrite lookup_dh_add IH !Frac.fsum_cons.
Qed.

Definition mono_frac (M : MSet.mset pre_term) : frac :=
  Frac.fprod (Frac.var <$> elements M).

Lemma frac_of_encode_mono M :
  (∀ x, x ∈ elements M → is_mod x = false) →
  frac_of (encode_mono M) = mono_frac M.
Proof.
move=> h; rewrite /encode_mono frac_of_fold_mul /mono_frac; congr Frac.fprod.
apply: list_fmap_ext => i x ix.
by apply: frac_of_atom; apply: h; apply: list_elem_of_lookup_2 ix.
Qed.

Lemma frac_of_encode_sum Ms :
  (∀ M x, M ∈ Ms → x ∈ elements M → is_mod x = false) →
  frac_of (encode_sum Ms) = Frac.fsum (mono_frac <$> Ms).
Proof.
move=> h; rewrite /encode_sum frac_of_fold_add -list_fmap_compose.
congr Frac.fsum; apply: list_fmap_ext => i M iM /=.
by apply: frac_of_encode_mono => x; apply: h;
  apply: list_elem_of_lookup_2 iM.
Qed.

Lemma frac_of_encode_signed P N :
  (∀ M x, M ∈ P → x ∈ elements M → is_mod x = false) →
  (∀ M x, M ∈ N → x ∈ elements M → is_mod x = false) →
  frac_of (encode_signed P N) =
  Frac.add (Frac.fsum (mono_frac <$> P))
    (Frac.opp (Frac.fsum (mono_frac <$> N))).
Proof.
move=> hP hN.
have eP := frac_of_encode_sum P hP; have eN := frac_of_encode_sum N hN.
case: N hN eN => [|n N] hN eN.
  by rewrite /encode_signed eP Frac.fsum_nil; ring.
case: P hP eP => [|m P] hP eP.
  rewrite -[frac_of _]/(Frac.opp (frac_of (encode_sum (n :: N)))).
  by rewrite eN Frac.fsum_nil; ring.
rewrite -[frac_of _]/(Frac.add (frac_of (encode_sum (m :: P)))
                          (Frac.opp (frac_of (encode_sum (n :: N))))).
by rewrite eP eN.
Qed.

Lemma fsum_mono_frac (X : MSet.mset (MSet.mset pre_term)) :
  Frac.fsum (mono_frac <$> elements X) = Frac.msum Frac.var X.
Proof.
rewrite Frac.msumE; congr Frac.fsum.
by apply: list_fmap_ext => i M _; rewrite Frac.mono_valE.
Qed.

Lemma frac_of_encode_poly p :
  (∀ x, x ∈ Poly.vars p → is_mod x = false) →
  frac_of (encode_poly p) = Frac.of_poly p.
Proof.
move=> h.
have hX (X : MSet.mset (MSet.mset pre_term)) :
    (∀ M, M ∈ X → M ∈ Poly.car p) →
    ∀ M x, M ∈ elements X → x ∈ elements M → is_mod x = false.
  move=> hX' M x MX xM; apply: h; apply/Poly.elem_of_vars; exists M.
  split; first by apply: hX'; apply/MSet.elem_of_elements.
  exact/MSet.elem_of_elements.
rewrite /encode_poly frac_of_encode_signed; first last.
- by apply: hX => M MX; right.
- by apply: hX => M MX; left.
rewrite !fsum_mono_frac -Frac.subE -Frac.evalE.
rewrite (Frac.eval_ext _ (λ x, Frac.of_poly (Poly.var (id x)))); last first.
  by move=> *; rewrite Frac.varE.
by rewrite Frac.eval_var_map Poly.map_id_ext.
Qed.

#[local] Lemma frac_of_mod_of_frac_atoms r :
  (∀ x, x ∈ Frac.vars r → is_mod x = false) →
  frac_of (mod_of_frac r) = r.
Proof.
move=> h.
have hn := frac_of_encode_poly (Frac.num r) (λ x xv, h x (vars_num _ _ xv)).
have hd := frac_of_encode_poly (Frac.den r) (λ x xv, h x (vars_den _ _ xv)).
rewrite /mod_of_frac; case: bool_decide_reflect => [e|_].
  rewrite hn; apply: Frac.num_den_inj.
    exact: Frac.num_of_poly.
  by rewrite Frac.den_of_poly e.
rewrite /= hn hd -Frac.divE -Frac.make_div; exact: Frac.make_num_den.
Qed.

Lemma fsum_lookup_list (l : list (pre_term * frac)) k :
  StronglySorted lexico (FMap.keys l) →
  Frac.fsum ((λ e, if bool_decide (k = e.1) then e.2 else Frac.zero) <$> l) =
  FMap.lookup_list Frac.zero k l.
Proof.
elim: l => [|[b v] l IH] /= sl; first by rewrite Frac.fsum_nil.
have [sl' bl] : StronglySorted lexico (FMap.keys l) ∧
    Forall (lexico b) (FMap.keys l) := StronglySorted_inv sl.
rewrite Frac.fsum_cons IH //; case: bool_decide_reflect => [->|_].
  by rewrite FMap.lookup_list_lexico //; ring.
by ring.
Qed.

#[local] Lemma dh_map_dh_of_atoms m :
  (∀ k, m !!! k ≠ Frac.zero → is_dh k = false) →
  (∀ k x, x ∈ Frac.vars (m !!! k) → is_mod x = false) →
  dh_map (dh_of m) = m.
Proof.
move=> hk hv; apply/FMap.fmap_eq => k.
rewrite /dh_of dh_map_fold -list_fmap_compose.
have E : ∀ e, e ∈ FMap.to_list m →
    ((λ t, dh_map t !!! k) ∘ (λ e, mk_exp e.1 e.2)) e =
    if bool_decide (k = e.1) then e.2 else Frac.zero.
  move=> [b v] /FMap.elem_of_to_list [bv nv] /=.
  have gb : is_dh b = false by apply: hk; rewrite bv.
  rewrite /mk_exp /=; case: bool_decide_reflect => [->|_].
    by rewrite dh_map_base // FMap.lookup_singleton.
  rewrite /= lookup_dh_scale dh_map_base // FMap.lookup_singleton.
  rewrite frac_of_mod_of_frac_atoms; last by rewrite -bv; apply: hv.
  by case: bool_decide; ring.
rewrite (list_fmap_ext _ _ _
  (λ i e ie, E e (list_elem_of_lookup_2 _ _ _ ie))).
rewrite fsum_lookup_list ?FMap.lookupE ?FMap.to_listE //.
by rewrite FMap.keys_fmap -FMap.to_listE; exact: FMap.to_list_sorted.
Qed.

Lemma mod_of_frac_var a : mod_of_frac (Frac.var a) = a.
Proof.
rewrite /mod_of_frac Frac.varE Frac.den_of_poly bool_decide_true //.
rewrite /encode_poly Frac.num_of_poly.
have -> : Poly.car (Poly.var a) = {[+ {[+ a +]} +]}.
  by rewrite -(Frac.car_num_var a) Frac.num_of_poly.
rewrite SMS.pos_singleton SMS.neg_singleton MSet.elements_singleton.
by rewrite MSet.elements_empty /= /encode_sum /= /encode_mono
  MSet.elements_singleton.
Qed.

Lemma dh_of_single k : dh_of {[k := Frac.one]} = k.
Proof.
rewrite /dh_of FMap.to_list_singleton; last exact: Frac.one_neq0.
by rewrite /= /mk_exp bool_decide_true.
Qed.

End RoundTrips.

(** ** Normal forms

    [fall P t] says that the atoms at the leaves of the field structure of
    [t] satisfy [P]; [gall Pb Pe t] says the same of the bases at the leaves
    of its group structure, and [Pe] of the atoms of its exponents. *)

Fixpoint fall (P : pre_term → Prop) t : Prop :=
  match t with
  | PT0 O0Zero | PT0 O0One => True
  | PT1 O1Opp t1 | PT1 O1Inv t1 => fall P t1
  | PT2 O2Add t1 t2 | PT2 O2Mul t1 t2 => fall P t1 ∧ fall P t2
  | _ => P t
  end.

Fixpoint gall (Pb Pe : pre_term → Prop) t : Prop :=
  match t with
  | PT0 O0GOne => True
  | PT1 O1GInv t1 => gall Pb Pe t1
  | PT2 O2GMul t1 t2 => gall Pb Pe t1 ∧ gall Pb Pe t2
  | PT2 O2Exp t1 t2 => gall Pb Pe t1 ∧ fall Pe t2
  | _ => Pb t
  end.

#[local] Definition fixed_atom a := normalize a = a ∧ is_mod a = false.
#[local] Definition fixed_base b := normalize b = b ∧ is_dh b = false.

Section NormalForms.

Add Ring flat_frac_ring' : (Frac.frac_ring_theory (T := pre_term)).

Implicit Types (r : frac) (m : dhmap) (P Pb Pe : pre_term → Prop).

Lemma mod_not_dh t : is_mod t = true → is_dh t = false.
Proof. by case: t => [[]|[] ?|[] ? ?]. Qed.

Lemma dh_not_mod t : is_dh t = true → is_mod t = false.
Proof. by case: t => [[]|[] ?|[] ? ?]. Qed.

Lemma dh_map_gone : dh_map (PT0 O0GOne) = ∅.
Proof. by []. Qed.

Lemma dh_map_ginv t : dh_map (PT1 O1GInv t) = dh_opp (dh_map t).
Proof. by []. Qed.

Lemma dh_map_gmul2 t1 t2 :
  dh_map (PT2 O2GMul t1 t2) = dh_add (dh_map t1) (dh_map t2).
Proof. by []. Qed.

Lemma dh_map_exp2 t1 t2 :
  dh_map (PT2 O2Exp t1 t2) = dh_scale (frac_of t2) (dh_map t1).
Proof. by []. Qed.

Lemma normalize_gone : normalize (PT0 O0GOne) = dh_of ∅.
Proof. by []. Qed.

Lemma fall_leaf P t : is_mod t = false → fall P t = P t.
Proof. by case: t => [[]|[] ?|[] ? ?]. Qed.

Lemma gall_leaf Pb Pe t : is_dh t = false → gall Pb Pe t = Pb t.
Proof. by case: t => [[]|[] ?|[] ? ?]. Qed.

Lemma vars_var a x : x ∈ Frac.vars (Frac.var a) ↔ x = a.
Proof.
rewrite /Frac.vars elem_of_app !Poly.elem_of_vars Frac.varE.
rewrite Frac.car_den_of_poly.
rewrite Frac.car_num_var; split.
- case=> [] [M [MS xM]]; move/SMS.elem_of_singleton: MS xM => ->.
    by move/MSet.elem_of_singleton.
  by move=> xe; case: (MSet.not_elem_of_empty _ xe).
- by move=> ->; left; exists {[+ a +]}; rewrite SMS.elem_of_singleton
    MSet.elem_of_singleton.
Qed.

Lemma vars_one_zero (r : frac) x :
  r = Frac.one ∨ r = Frac.zero → x ∉ Frac.vars r.
Proof. by case=> ->; [exact: Frac.vars_one|exact: Frac.vars_zero]. Qed.

Lemma fall_vars P t : fall P t → Frac.all_vars P (frac_of t).
Proof.
elim: t => [o|o t IH|o t1 IH1 t2 IH2].
- case: o => [n|a| | |] /=; try by move=> ?; apply: Frac.all_vars_var.
  + by move=> _; apply: Frac.all_vars_zero.
  + by move=> _; apply: Frac.all_vars_one.
- case: o => [kt| | | |] /=; try by move=> ?; apply: Frac.all_vars_var.
  + by move=> /IH; apply: Frac.all_vars_opp.
  + by move=> /IH; apply: Frac.all_vars_inv.
- case: o => [| | | | |] /=; try by move=> ?; apply: Frac.all_vars_var.
  + by move=> [/IH1 h1 /IH2 h2]; apply: Frac.all_vars_add.
  + by move=> [/IH1 h1 /IH2 h2]; apply: Frac.all_vars_mul.
Qed.

Lemma gall_ok_leaf Pb Pe t : is_dh t = false → Pb t →
  (∀ k, dh_map t !!! k ≠ Frac.zero → Pb k) ∧
  (∀ k, Frac.all_vars Pe (dh_map t !!! k)).
Proof.
move=> gt pt; rewrite dh_map_base //.
split=> k; rewrite FMap.lookup_singleton.
  by case: bool_decide_reflect => [->|].
by case: bool_decide; [apply: Frac.all_vars_one|apply: Frac.all_vars_zero].
Qed.

Lemma gall_ok Pb Pe t : gall Pb Pe t →
  (∀ k, dh_map t !!! k ≠ Frac.zero → Pb k) ∧
  (∀ k, Frac.all_vars Pe (dh_map t !!! k)).
Proof.
elim: t => [o|o t IH|o t1 IH1 t2 IH2].
- case: o => [n|a| | |]; try by move=> h; apply: gall_ok_leaf.
  move=> _; rewrite dh_map_gone; split=> k; rewrite FMap.lookup_empty //.
  exact: Frac.all_vars_zero.
- case: o => [kt| | | |]; try by move=> h; apply: gall_ok_leaf.
  move=> /IH [k1 v1]; split=> k; rewrite dh_map_ginv lookup_dh_opp.
    by move=> nk; apply: k1 => e; apply: nk; rewrite e Frac.opp_zero.
  exact: Frac.all_vars_opp.
- case: o => [| | | | |]; try by move=> h; apply: gall_ok_leaf.
  + move=> [/IH1 [k1 v1] /IH2 [k2 v2]]; split=> k; rewrite dh_map_gmul2.
      by case/lookup_dh_add_neq0; [apply: k1|apply: k2].
    rewrite lookup_dh_add; exact: Frac.all_vars_add.
  + move=> [/IH1 [k1 v1] fe]; split=> k; rewrite dh_map_exp2 lookup_dh_scale.
      by move=> nk; apply: k1 => z; apply: nk; rewrite z Frac.mul_zero_l.
    by apply: Frac.all_vars_mul => //; apply: fall_vars.
Qed.

#[local] Lemma normalize_frac_of s :
  fall fixed_atom s → frac_of (normalize s) = frac_of s.
Proof.
have R : ∀ r, Frac.all_vars fixed_atom r → frac_of (mod_of_frac r) = r.
  move=> r /Frac.all_vars_iff h; apply: frac_of_mod_of_frac_atoms => x /h [] //.
elim: s => [o|o s IH|o s1 IH1 s2 IH2].
- case: o => [n|a| | |]; try by move=> [h _]; rewrite h.
  + by move=> _; rewrite normalize_zero R //; apply: Frac.all_vars_zero.
  + by move=> _; rewrite normalize_one R //; apply: Frac.all_vars_one.
- case: o => [kt| | | |]; try by move=> [h _]; rewrite h.
  + move=> h; rewrite normalize_opp (IH h) R //; apply: Frac.all_vars_opp.
    exact: fall_vars.
  + move=> h; rewrite normalize_inv (IH h) R //; apply: Frac.all_vars_inv.
    exact: fall_vars.
- case: o => [| | | | |]; try by move=> [h _]; rewrite h.
  + move=> [h1 h2]; rewrite normalize_add (IH1 h1) (IH2 h2) R //.
    by apply: Frac.all_vars_add; apply: fall_vars.
  + move=> [h1 h2]; rewrite normalize_mul (IH1 h1) (IH2 h2) R //.
    by apply: Frac.all_vars_mul; apply: fall_vars.
Qed.

#[local] Lemma normalize_mod s : is_mod s = true → fall fixed_atom s →
  normalize s = mod_of_frac (frac_of s).
Proof.
case: s => [[]|[] s1|[] s1 s2] //= _.
- by move=> h; rewrite normalize_frac_of.
- by move=> h; rewrite normalize_frac_of.
- by move=> [h1 h2]; rewrite !normalize_frac_of.
- by move=> [h1 h2]; rewrite !normalize_frac_of.
Qed.

#[local] Lemma normalize_dh_map s :
  gall fixed_base fixed_atom s → dh_map (normalize s) = dh_map s.
Proof.
have R : ∀ m,
    (∀ k, m !!! k ≠ Frac.zero → fixed_base k) →
    (∀ k, Frac.all_vars fixed_atom (m !!! k)) →
    dh_map (dh_of m) = m.
  move=> m hk hv; apply: dh_map_dh_of_atoms.
    by move=> k /hk [].
  by move=> k x /(proj1 (Frac.all_vars_iff _ _) (hv k)) [].
elim: s => [o|o s IH|o s1 IH1 s2 IH2].
- case: o => [n|a| | |]; try by move=> [h _]; rewrite h.
  move=> _; rewrite normalize_gone dh_map_gone R //.
  + by move=> k; rewrite FMap.lookup_empty.
  + by move=> k; rewrite FMap.lookup_empty; exact: Frac.all_vars_zero.
- case: o => [kt| | | |]; try by move=> [h _]; rewrite h.
  move=> h; rewrite normalize_ginv dh_map_ginv (IH h).
  have [k1 v1] := gall_ok _ _ s h.
  apply: R => k; rewrite lookup_dh_opp.
    by move=> nk; apply: k1 => e; apply: nk; rewrite e Frac.opp_zero.
  exact: Frac.all_vars_opp.
- case: o => [| | | | |]; try by move=> [h _]; rewrite h.
  + move=> [h1 h2]; rewrite normalize_gmul dh_map_gmul2 (IH1 h1) (IH2 h2).
    have [k1 v1] := gall_ok _ _ _ h1; have [k2 v2] := gall_ok _ _ _ h2.
    apply: R => k; first by case/lookup_dh_add_neq0; [apply: k1|apply: k2].
    rewrite lookup_dh_add; exact: Frac.all_vars_add.
  + move=> [h1 h2].
    rewrite normalize_exp dh_map_exp2 (IH1 h1) (normalize_frac_of _ h2).
    have [k1 v1] := gall_ok _ _ _ h1.
    apply: R => k; rewrite lookup_dh_scale.
      by move=> nk; apply: k1 => z; apply: nk; rewrite z Frac.mul_zero_l.
    by apply: Frac.all_vars_mul => //; apply: fall_vars.
Qed.

#[local] Lemma normalize_dh s : is_dh s = true → gall fixed_base fixed_atom s →
  normalize s = dh_of (dh_map s).
Proof.
case: s => [[]|[] s1|[] s1 s2] //= _.
- by move=> h; rewrite normalize_dh_map.
- by move=> [h1 h2]; rewrite !normalize_dh_map.
- by move=> [h1 h2]; rewrite normalize_dh_map // normalize_frac_of.
Qed.

Lemma fall_fold_tree o u P l : o = O2Add ∨ o = O2Mul → fall P u →
  (∀ x, x ∈ l → fall P x) → fall P (fold_tree (PT2 o) u l).
Proof.
move=> ho hu; case: l => [|t l] //= hl.
elim: l t hl => [|t' l IH] t hl /=; first exact: hl (list_elem_of_here _ _).
have IH' := IH t' (λ x xl, hl x (list_elem_of_further _ _ _ xl)).
move: IH'; case: ho => -> /= IH'; split=> //;
  by apply: hl; apply: list_elem_of_here.
Qed.

Lemma fall_encode_poly P p :
  (∀ x, x ∈ Poly.vars p → P x ∧ is_mod x = false) → fall P (encode_poly p).
Proof.
move=> h.
have hM : ∀ M, M ∈ Poly.car p → fall P (encode_mono M).
  move=> M Mp; apply: fall_fold_tree; [by right|done|].
  move=> x /MSet.elem_of_elements xM.
  have [px fx] : P x ∧ is_mod x = false.
    by apply: h; apply/Poly.elem_of_vars; exists M.
  by rewrite fall_leaf.
have hS : ∀ Ms, (∀ M, M ∈ Ms → M ∈ Poly.car p) → fall P (encode_sum Ms).
  move=> Ms hMs; apply: fall_fold_tree; [by left|done|] => t.
  by move=> /list_elem_of_fmap [M [-> /hMs /hM]].
have hP : fall P (encode_sum (elements (SMS.pos (Poly.car p)))).
  by apply: hS => M /MSet.elem_of_elements MP; left.
have hN : fall P (encode_sum (elements (SMS.neg (Poly.car p)))).
  by apply: hS => M /MSet.elem_of_elements MN; right.
rewrite /encode_poly; move: hP hN.
case: (elements (SMS.neg _)) => [|n N];
  by case: (elements (SMS.pos _)) => [|m M] //=.
Qed.

Lemma fall_mod_of_frac P r :
  (∀ x, x ∈ Frac.vars r → P x ∧ is_mod x = false) →
  fall P (mod_of_frac r).
Proof.
move=> h.
have hn := fall_encode_poly P (Frac.num r) (λ x xv, h x (vars_num _ _ xv)).
have hd := fall_encode_poly P (Frac.den r) (λ x xv, h x (vars_den _ _ xv)).
by rewrite /mod_of_frac; case: bool_decide.
Qed.

Lemma gall_dh_of Pb Pe m :
  (∀ k, m !!! k ≠ Frac.zero → Pb k ∧ is_dh k = false) →
  (∀ k x, x ∈ Frac.vars (m !!! k) → Pe x ∧ is_mod x = false) →
  gall Pb Pe (dh_of m).
Proof.
move=> hk hv.
have hf : ∀ e, e ∈ FMap.to_list m → gall Pb Pe (mk_exp e.1 e.2).
  move=> [b v] /FMap.elem_of_to_list [bv nv].
  have [pb gb] := hk b ltac:(by rewrite bv).
  rewrite /mk_exp /=; case: bool_decide; first by rewrite gall_leaf.
  split; first by rewrite gall_leaf.
  by apply: fall_mod_of_frac => x; rewrite -bv; apply: hv.
rewrite /dh_of; case: (FMap.to_list m) hf => [|e l] //= hf.
elim: l e hf => [|e' l IH] e hf /=; first exact: hf (list_elem_of_here _ _).
split; first exact: hf (list_elem_of_here _ _).
by apply: IH => e'' he''; apply: hf; apply: list_elem_of_further.
Qed.

#[local] Lemma normalize_mod_of_frac r :
  (∀ x, x ∈ Frac.vars r → fixed_atom x) →
  normalize (mod_of_frac r) = mod_of_frac r.
Proof.
move=> h.
have hf : ∀ x, x ∈ Frac.vars r → is_mod x = false by move=> x /h [].
have fe : fall fixed_atom (mod_of_frac r).
  by apply: fall_mod_of_frac => x xr; split; [apply: h|apply: hf].
case E: (is_mod (mod_of_frac r)).
  by rewrite normalize_mod // frac_of_mod_of_frac_atoms.
have er : r = Frac.var (mod_of_frac r).
  by rewrite -{1}(frac_of_mod_of_frac_atoms r hf) frac_of_atom.
have : mod_of_frac r ∈ Frac.vars r by rewrite {2}er; apply/vars_var.
by move=> /h [].
Qed.

#[local] Lemma normalize_dh_of m :
  (∀ k, m !!! k ≠ Frac.zero → fixed_base k) →
  (∀ k x, x ∈ Frac.vars (m !!! k) → fixed_atom x) →
  normalize (dh_of m) = dh_of m.
Proof.
move=> hk hv.
have hkg : ∀ k, m !!! k ≠ Frac.zero → is_dh k = false by move=> k /hk [].
have hvf : ∀ k x, x ∈ Frac.vars (m !!! k) → is_mod x = false.
  by move=> k x /hv [].
have ge : gall fixed_base fixed_atom (dh_of m).
  apply: gall_dh_of => [k nk|k x xv]; split.
  - exact: hk.
  - exact: hkg.
  - exact: hv xv.
  - exact: hvf xv.
case E: (is_dh (dh_of m)).
  by rewrite normalize_dh // dh_map_dh_of_atoms.
have em : m = {[dh_of m := Frac.one]}.
  by rewrite -{1}(dh_map_dh_of_atoms m hkg hvf) dh_map_base.
have : m !!! dh_of m ≠ Frac.zero.
  rewrite [X in X !!! _]em FMap.lookup_singleton bool_decide_true //.
  exact: Frac.one_neq0.
by move=> /hk [].
Qed.

End NormalForms.

(* Idempotence needs an invariant on the leaves of the readings, since the
   subterms of a normal form need not be normal forms; [wf] replaces it once
   [normalize_idem] holds. *)
Module Internal.
Section Canon.

Add Ring flat_frac_ring_canon : (Frac.frac_ring_theory (T := pre_term)).

Implicit Types (r : frac) (m : dhmap).

(** [canon] characterizes normal forms: free nodes over normal forms, and
    encodings of values whose atoms and bases are normal forms. *)
Inductive canon : pre_term → Prop :=
| canon_free0 o :
  is_mod (PT0 o) = false → is_dh (PT0 o) = false → canon (PT0 o)
| canon_free1 o t :
  is_mod (PT1 o t) = false → is_dh (PT1 o t) = false →
  canon t → canon (PT1 o t)
| canon_free2 o t1 t2 :
  is_mod (PT2 o t1 t2) = false → is_dh (PT2 o t1 t2) = false →
  canon t1 → canon t2 → canon (PT2 o t1 t2)
| canon_frac r :
  (∀ x, x ∈ Frac.vars r → canon x) →
  (∀ x, x ∈ Frac.vars r → is_mod x = false) →
  canon (mod_of_frac r)
| canon_dh m :
  (∀ k, m !!! k ≠ Frac.zero → canon k) →
  (∀ k, m !!! k ≠ Frac.zero → is_dh k = false) →
  (∀ k x, x ∈ Frac.vars (m !!! k) → canon x) →
  (∀ k x, x ∈ Frac.vars (m !!! k) → is_mod x = false) →
  canon (dh_of m).

Definition nf_props n : Prop :=
  normalize n = n ∧
  mod_of_frac (frac_of n) = n ∧
  dh_of (dh_map n) = n ∧
  (∀ x, x ∈ Frac.vars (frac_of n) → canon x ∧ is_mod x = false) ∧
  (∀ k, dh_map n !!! k ≠ Frac.zero → canon k ∧ is_dh k = false) ∧
  (∀ k x, x ∈ Frac.vars (dh_map n !!! k) → canon x ∧ is_mod x = false).

Lemma nf_props_atom n : canon n → is_mod n = false → is_dh n = false →
  normalize n = n → nf_props n.
Proof.
move=> cn fn gn nn; rewrite /nf_props frac_of_atom // dh_map_base //.
rewrite mod_of_frac_var dh_of_single.
split=> //; split=> //; split=> //; split.
  by move=> x /vars_var ->.
split=> k; rewrite FMap.lookup_singleton.
  by case: bool_decide_reflect => [->|].
move=> x xv; exfalso; move: xv; apply: vars_one_zero.
by case: bool_decide; [left|right].
Qed.

Lemma canon_props n : canon n → nf_props n.
Proof.
elim=> {n}.
- move=> o fo go; apply: nf_props_atom => //; first exact: canon_free0.
  by case: o fo go.
- move=> o t fo go ct IH; apply: nf_props_atom => //.
    exact: canon_free1.
  by case: o fo go => //= *; rewrite (proj1 IH).
- move=> o t1 t2 fo go c1 IH1 c2 IH2; apply: nf_props_atom => //.
    exact: canon_free2.
  by case: o fo go => //= *; rewrite (proj1 IH1) (proj1 IH2).
- move=> r cr IH fr.
  have pr := frac_of_mod_of_frac_atoms r fr.
  have nr : normalize (mod_of_frac r) = mod_of_frac r.
    apply: normalize_mod_of_frac => x xr.
    by split; [exact: (proj1 (IH x xr))|exact: fr].
  case E: (is_mod (mod_of_frac r)).
    rewrite /nf_props pr dh_map_base ?mod_not_dh // dh_of_single.
    split=> //; split=> //; split=> //; split.
      by move=> x xr; split; [apply: cr|apply: fr].
    split=> k; rewrite FMap.lookup_singleton.
      case: bool_decide_reflect => [->|] // _.
      split; last exact: mod_not_dh.
      exact: canon_frac.
    move=> x xv; exfalso; move: xv; apply: vars_one_zero.
    by case: bool_decide; [left|right].
  have er : r = Frac.var (mod_of_frac r) by rewrite -{1}pr frac_of_atom.
  by apply: IH; rewrite {2}er; apply/vars_var.
- move=> m ck IHk gk cv IHv fv.
  have pm := dh_map_dh_of_atoms m gk fv.
  have nm : normalize (dh_of m) = dh_of m.
    apply: normalize_dh_of => [k nk|k x xv]; split.
    + exact: (proj1 (IHk k nk)).
    + exact: gk.
    + exact: (proj1 (IHv k x xv)).
    + exact: fv xv.
  case E: (is_dh (dh_of m)).
    rewrite /nf_props pm frac_of_atom ?dh_not_mod // mod_of_frac_var.
    split=> //; split=> //; split=> //; split.
      move=> x /vars_var ->; split; last exact: dh_not_mod.
      exact: canon_dh.
    by split=> [k nk|k x xv]; split;
      [apply: ck|apply: gk|apply: cv xv|apply: fv xv].
  have em : m = {[dh_of m := Frac.one]}.
    by rewrite -{1}pm dh_map_base.
  apply: IHk.
  rewrite [X in X !!! _]em FMap.lookup_singleton bool_decide_true //.
  exact: Frac.one_neq0.
Qed.

Lemma canon_normalize t : canon (normalize t).
Proof.
have frac_case : ∀ r,
    (∀ x, x ∈ Frac.vars r → canon x ∧ is_mod x = false) →
    canon (mod_of_frac r).
  by move=> r h; apply: canon_frac => x /h [].
have av : ∀ n, canon n →
    Frac.all_vars (λ x, canon x ∧ is_mod x = false) (frac_of n).
  by move=> n /canon_props [_ [_ [_ [h _]]]]; apply/Frac.all_vars_iff.
have dh_case : ∀ m,
    (∀ k, m !!! k ≠ Frac.zero → canon k ∧ is_dh k = false) →
    (∀ k, Frac.all_vars (λ x, canon x ∧ is_mod x = false) (m !!! k)) →
    canon (dh_of m).
  move=> m hk hv; apply: canon_dh => [k /hk []|k /hk []|k x|k x] //.
  - by move=> /(proj1 (Frac.all_vars_iff _ _) (hv k)) [].
  - by move=> /(proj1 (Frac.all_vars_iff _ _) (hv k)) [].
have dk : ∀ n, canon n → ∀ k,
    dh_map n !!! k ≠ Frac.zero → canon k ∧ is_dh k = false.
  by move=> n /canon_props [_ [_ [_ [_ [h _]]]]].
have dv : ∀ n, canon n → ∀ k,
    Frac.all_vars (λ x, canon x ∧ is_mod x = false) (dh_map n !!! k).
  move=> n /canon_props [_ [_ [_ [_ [_ h]]]]] k; apply/Frac.all_vars_iff.
  exact: h k.
elim: t => [o|o t IH|o t1 IH1 t2 IH2].
- case: o => [n|a| | |]; try by apply: canon_free0.
  + by apply: frac_case => x xv; case: (Frac.vars_zero x xv).
  + by apply: frac_case => x xv; case: (Frac.vars_one x xv).
  + rewrite normalize_gone; apply: dh_case => k; rewrite FMap.lookup_empty //.
    exact: Frac.all_vars_zero.
- case: o => [kt| | | |] /=; try by apply: canon_free1.
  + apply: frac_case; apply/Frac.all_vars_iff; apply: Frac.all_vars_opp.
    exact: av.
  + apply: frac_case; apply/Frac.all_vars_iff; apply: Frac.all_vars_inv.
    exact: av.
  + apply: dh_case => k; rewrite lookup_dh_opp.
      by move=> nk; apply: (dk _ IH) => e; apply: nk; rewrite e Frac.opp_zero.
    by apply: Frac.all_vars_opp; apply: dv.
- case: o => [| | | | |] /=; try by apply: canon_free2.
  + apply: frac_case; apply/Frac.all_vars_iff.
    by apply: Frac.all_vars_add; apply: av.
  + apply: frac_case; apply/Frac.all_vars_iff.
    by apply: Frac.all_vars_mul; apply: av.
  + apply: dh_case => k.
      by case/lookup_dh_add_neq0; [apply: (dk _ IH1)|apply: (dk _ IH2)].
    by rewrite lookup_dh_add; apply: Frac.all_vars_add; apply: dv.
  + apply: dh_case => k; rewrite lookup_dh_scale.
      move=> nk; apply: (dk _ IH1) => z; apply: nk.
      by rewrite z Frac.mul_zero_l.
    by apply: Frac.all_vars_mul; [apply: dv|apply: av].
Qed.

End Canon.
End Internal.
Import Internal.

Theorem normalize_idem t : normalize (normalize t) = normalize t.
Proof. exact: (proj1 (canon_props _ (canon_normalize t))). Qed.


(** ** Recognizers *)

Definition is_mono_poly (p : poly) : bool :=
  match elements (SMS.pos (Poly.car p)), elements (SMS.neg (Poly.car p)) with
  | [_], [] => true
  | _, _ => false
  end.

(* [is_exp] and [is_gmul] are exclusive: [public] recurses on the factors of a
   group product, and the only factor of an exponential is itself. *)
Definition is_exp pt :=
  if pt is PT2 O2Exp _ e then is_mono_poly (Frac.num (frac_of e)) else false.
Definition is_gmul pt := is_dh pt && negb (is_exp pt).
Definition is_nonce pt := if pt is PT0 (O0Nonce _) then true else false.

(** [is_non_free] recognizes the heads that [term] represents indirectly
    ([TNonFree] in [core/term/base.v]). *)
Definition is_non_free pt := is_mod pt || is_dh pt.

Lemma is_dh_exp_gmul pt : is_dh pt = is_exp pt || is_gmul pt.
Proof.
by rewrite /is_gmul; case: pt => [[]|[] ?|[] ? ?] //=; case: is_mono_poly.
Qed.

Lemma Ndh_Nexp pt : negb (is_dh pt) → negb (is_exp pt).
Proof. by case: pt => [[]|[] ?|[] ? ?]. Qed.

Lemma Ndh_Ngmul pt : negb (is_dh pt) → negb (is_gmul pt).
Proof. by rewrite /is_gmul; case: (is_dh pt). Qed.

Lemma is_exp_Ngmul pt : is_exp pt → negb (is_gmul pt).
Proof. by rewrite /is_gmul; case: (is_exp pt); case: (is_dh pt). Qed.

Lemma is_gmul_Nexp pt : is_gmul pt → negb (is_exp pt).
Proof. by rewrite /is_gmul; case: (is_exp pt); case: (is_dh pt). Qed.

Lemma is_exp_Nmod pt : is_exp pt → negb (is_mod pt).
Proof. by case: pt => [[]|[] ?|[] ? ?]. Qed.

Lemma is_mod_Ngmul pt : is_mod pt → negb (is_gmul pt).
Proof. by case: pt => [[]|[] ?|[] ? ?]. Qed.

Lemma Is_true_negb b : negb b ↔ b = false.
Proof. by case: b. Qed.

(** ** Derived operations *)

Definition one := PT0 O0One.

(** The atoms of a pre-term are the variables of its fraction. *)
Definition atoms pt : list pre_term := Frac.vars (frac_of pt).

(** [mod_subst r] evaluates a fraction whose atoms may be exponents. *)
Definition mod_subst (r : frac) : pre_term := mod_of_frac (Frac.bind frac_of r).

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
  foldr (λ p acc, SMS.bind (exp_factor p.1 (Frac.den p.2))
                           (Poly.car (Frac.num p.2)) ⊎ acc)
    ∅ (FMap.to_list m).

Definition gfactors pt : SMS.sms pre_term :=
  if is_exp pt then {[+ pt +]}
  else if is_dh pt then dh_factors (dh_map pt) else {[+ pt +]}.

Definition base pt :=
  if is_exp pt then (if pt is PT2 _ b _ then b else pt) else pt.

Definition expo pt :=
  if is_exp pt then (if pt is PT2 _ _ e then e else one) else one.

(** [wf] recognizes the normal forms. *)
Definition wf pt : bool := bool_decide (normalize pt = pt).

(** The atoms of normal forms are normal forms that are not field
    operations. *)
Definition wf_atom x : bool := wf x && negb (is_mod x).

Definition wf_frac (r : frac) : Prop := Frac.all_vars wf_atom r.

Section API.

Add Ring frac_ring_api : (Frac.frac_ring_theory (T := pre_term)).

Implicit Types (r : frac) (m : dhmap) (s : SMS.sms pre_term).

Lemma wfP pt : wf pt ↔ normalize pt = pt.
Proof. exact: bool_decide_spec. Qed.

#[local] Lemma wf_canon pt : wf pt ↔ canon pt.
Proof.
rewrite wfP; split=> [<-|/canon_props [//]]; exact: canon_normalize.
Qed.

Lemma normalize_wf pt : wf pt → normalize pt = pt.
Proof. by move=> /wfP. Qed.

Lemma wf_normalize pt : wf (normalize pt).
Proof. by apply/wfP; exact: normalize_idem. Qed.

Lemma wf_free0 o :
  is_mod (PT0 o) = false → is_dh (PT0 o) = false → wf (PT0 o).
Proof. by case: o => // *; apply/wfP. Qed.

Lemma wf_free1 o t :
  is_mod (PT1 o t) = false → is_dh (PT1 o t) = false → wf (PT1 o t) ↔ wf t.
Proof.
rewrite !wfP.
by case: o => [kt| | | |] //= _ _; split=> [[]|->].
Qed.

Lemma wf_free2 o t1 t2 :
  is_mod (PT2 o t1 t2) = false → is_dh (PT2 o t1 t2) = false →
  wf (PT2 o t1 t2) ↔ wf t1 ∧ wf t2.
Proof.
rewrite !wfP.
by case: o => //= _ _; split=> [[-> ->]|[-> ->]].
Qed.

#[local] Lemma canon_wf_atoms r :
  wf_frac r →
  ∀ x, x ∈ Frac.vars r → canon x ∧ is_mod x = false.
Proof.
move=> /Frac.all_vars_iff h x /h /andb_True [/wf_canon cx /Is_true_negb fx].
by split.
Qed.

Lemma frac_of_Nmod pt : negb (is_mod pt) → frac_of pt = Frac.var pt.
Proof. by move=> /Is_true_negb; exact: frac_of_atom. Qed.

Lemma frac_of_mod_of_frac r : wf_frac r → frac_of (mod_of_frac r) = r.
Proof.
move=> /Frac.all_vars_iff h; apply: frac_of_mod_of_frac_atoms => x /h.
by move=> /andb_True [_ /Is_true_negb].
Qed.

Lemma wf_mod_of_frac r :
  wf_frac r → wf (mod_of_frac r).
Proof.
move=> /canon_wf_atoms h; apply/wf_canon; apply: canon_frac => x /h [] //.
Qed.

Lemma mod_of_frac_frac_of pt : wf pt → mod_of_frac (frac_of pt) = pt.
Proof. by move=> /wf_canon /canon_props [_ []]. Qed.

Lemma frac_of_atoms pt :
  wf pt → wf_frac (frac_of pt).
Proof.
move=> /wf_canon /canon_props [_ [_ [_ [h _]]]]; apply/Frac.all_vars_iff.
move=> x /h [cx fx]; apply/andb_True; split; first exact/wf_canon.
exact/Is_true_negb.
Qed.

Lemma frac_of_one : frac_of one = Frac.one.
Proof. by []. Qed.

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

Lemma lookup_to_list m k :
  m !!! k = FMap.lookup_list Frac.zero k (FMap.to_list m).
Proof. by rewrite FMap.lookupE FMap.to_listE. Qed.

(** The keys of a well-formed map are bases, and its logarithms have
    normal atoms. *)
Definition wf_dh m : Prop :=
  ∀ k, m !!! k ≠ Frac.zero →
    wf k ∧ negb (is_dh k) ∧
    wf_frac (m !!! k).

Lemma wf_dh_atoms m k :
  wf_dh m → wf_frac (m !!! k).
Proof.
move=> w; case: (decide (m !!! k = Frac.zero)) => [->|nk].
  exact: Frac.all_vars_zero.
by have [_ [_ h]] := w k nk.
Qed.

#[local] Lemma wf_dh_canon m : wf_dh m →
  (∀ k, m !!! k ≠ Frac.zero → canon k ∧ is_dh k = false) ∧
  (∀ k x, x ∈ Frac.vars (m !!! k) → canon x ∧ is_mod x = false).
Proof.
move=> w; split.
  move=> k nk; have [/wf_canon ck [gk _]] := w k nk.
  by split=> //; move: gk => /Is_true_negb.
by move=> k x; apply: canon_wf_atoms; apply: wf_dh_atoms.
Qed.

Lemma dh_map_Ndh b : negb (is_dh b) → dh_map b = {[b := Frac.one]}.
Proof. by move=> /Is_true_negb; exact: dh_map_base. Qed.

Lemma wf_dh_of m : wf_dh m → wf (dh_of m).
Proof.
move=> /wf_dh_canon [hk hv]; apply/wf_canon.
apply: canon_dh => [k /hk []|k /hk []|k x /hv []|k x /hv []] //.
Qed.

Lemma dh_map_dh_of m : wf_dh m → dh_map (dh_of m) = m.
Proof.
move=> /wf_dh_canon [hk hv]; apply: dh_map_dh_of_atoms.
  by move=> k /hk [].
by move=> k x /hv [].
Qed.

Lemma dh_of_dh_map pt : wf pt → dh_of (dh_map pt) = pt.
Proof. by move=> /wf_canon /canon_props [_ [_ []]]. Qed.

Lemma wf_dh_map pt : wf pt → wf_dh (dh_map pt).
Proof.
move=> /wf_canon /canon_props [_ [_ [_ [_ [hk hv]]]]] k nk.
have [ck gk] := hk k nk; split; first exact/wf_canon.
split; first by apply/Is_true_negb.
apply/Frac.all_vars_iff => x /hv [cx fx]; apply/andb_True.
by split; [exact/wf_canon|exact/Is_true_negb].
Qed.

Lemma wf_dh_empty : wf_dh ∅.
Proof. by move=> k; rewrite FMap.lookup_empty. Qed.

Lemma wf_dh_add m1 m2 : wf_dh m1 → wf_dh m2 → wf_dh (dh_add m1 m2).
Proof.
move=> w1 w2 k nz; rewrite lookup_dh_add.
have A : wf_frac (Frac.add (m1 !!! k) (m2 !!! k)).
  by apply: Frac.all_vars_add; apply: wf_dh_atoms.
by case/lookup_dh_add_neq0: nz => [/w1|/w2] [wk [gk _]].
Qed.

Lemma wf_dh_opp m : wf_dh m → wf_dh (dh_opp m).
Proof.
move=> w k; rewrite lookup_dh_opp => nz.
have n : m !!! k ≠ Frac.zero by move=> e; apply: nz; rewrite e Frac.opp_zero.
have [wk [gk ak]] := w k n; split=> //; split=> //.
exact: Frac.all_vars_opp.
Qed.

Lemma wf_dh_scale r m :
  wf_frac r → wf_dh m →
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
  wf b → wf_frac r → wf (exp_frac b r).
Proof.
by move=> wb ar; apply wf_dh_of; apply: wf_dh_scale => //; apply: wf_dh_map.
Qed.

Lemma wf_exp b e : wf b → wf e → wf (exp b e).
Proof. by move=> wb we; apply wf_exp_frac => //; apply: frac_of_atoms. Qed.

Lemma dh_map_mk_exp b r :
  negb (is_dh b) → wf_frac r →
  r ≠ Frac.zero → dh_map (mk_exp b r) = {[b := r]}.
Proof.
move=> gb ar nr; rewrite /mk_exp; case: bool_decide_reflect => [->|n1].
  exact: dh_map_Ndh.
apply/FMap.fmap_eq => k.
rewrite dh_map_exp2 lookup_dh_scale (dh_map_Ndh _ gb) frac_of_mod_of_frac //.
rewrite !FMap.lookup_singleton.
by case: bool_decide;
  [exact: (left_id Frac.one Frac.mul)|exact: Frac.mul_zero_l].
Qed.

Lemma dh_of_singleton b r :
  r ≠ Frac.zero → dh_of {[b := r]} = mk_exp b r.
Proof. by move=> nr; rewrite /dh_of FMap.to_list_singleton. Qed.

Lemma mod_of_frac_zero : mod_of_frac Frac.zero = PT0 O0Zero.
Proof.
rewrite /mod_of_frac Frac.den_zero bool_decide_true // Frac.num_zero.
by rewrite /encode_poly Poly.car_zero SMS.pos_empty SMS.neg_empty
  MSet.elements_empty.
Qed.

Lemma mod_of_frac_one : mod_of_frac Frac.one = PT0 O0One.
Proof.
rewrite /mod_of_frac Frac.den_one bool_decide_true // Frac.num_one.
rewrite /encode_poly Poly.oneE Poly.car_mono.
rewrite SMS.pos_singleton SMS.neg_singleton.
rewrite MSet.elements_singleton MSet.elements_empty /=.
by rewrite /encode_sum /= /encode_mono MSet.elements_empty.
Qed.

Lemma dh_of_empty : dh_of ∅ = PT0 O0GOne.
Proof. by rewrite /dh_of FMap.to_listE. Qed.

Lemma is_mono_polyP p : is_mono_poly p ↔ ∃ n, p = Poly.mono n.
Proof.
rewrite /is_mono_poly; split; last first.
  move=> [n ->]; rewrite Poly.car_mono SMS.pos_singleton SMS.neg_singleton.
  by rewrite MSet.elements_singleton MSet.elements_empty.
destruct (elements (SMS.pos (Poly.car p))) as [|n [|? ?]] eqn:EP;
  destruct (elements (SMS.neg (Poly.car p))) as [|? ?] eqn:EN; try done.
move=> _; exists n; apply: Poly.car_inj; rewrite Poly.car_mono.
apply: SMS.sms_eq.
  rewrite SMS.pos_singleton -(MSet.of_list_elements (SMS.pos _)) EP.
  by rewrite MSet.of_list_cons MSet.of_list_nil (right_id ∅ (⊎)).
by rewrite SMS.neg_singleton (MSet.elements_empty_inv _ EN).
Qed.

(** An encoded fraction whose head is not a field operation is a lone
    atom. *)
Lemma mod_of_frac_Nmod r : is_mod (mod_of_frac r) = false →
  ∃ a, r = Frac.of_poly (Poly.var a) ∧ mod_of_frac r = a.
Proof.
rewrite /mod_of_frac; case: bool_decide_reflect => [d1|//].
rewrite /encode_poly /encode_signed.
destruct (elements (SMS.neg (Poly.car (Frac.num r)))) as [|n N] eqn:EN;
  last by destruct (elements (SMS.pos (Poly.car (Frac.num r)))).
rewrite /encode_sum.
destruct (elements (SMS.pos (Poly.car (Frac.num r)))) as [|M [|M' Ms]] eqn:EP;
  rewrite //= /encode_mono.
destruct (elements M) as [|a [|a' l]] eqn:EM => //= _.
exists a; split=> //.
apply: Frac.num_den_inj; rewrite ?Frac.num_of_poly ?Frac.den_of_poly //.
apply: Poly.car_inj; rewrite Poly.varE Poly.car_mono; apply: SMS.sms_eq.
  rewrite SMS.pos_singleton -(MSet.of_list_elements (SMS.pos _)) EP.
  rewrite MSet.of_list_cons MSet.of_list_nil (right_id ∅ (⊎)).
  rewrite -(MSet.of_list_elements M) EM.
  by rewrite MSet.of_list_cons MSet.of_list_nil (right_id ∅ (⊎)).
by rewrite SMS.neg_singleton (MSet.elements_empty_inv _ EN).
Qed.

(** A normal map written as a power is a single entry. *)
Lemma dh_of_exp_shape m b e : wf_dh m → dh_of m = PT2 O2Exp b e →
  m = {[b := frac_of e]} ∧ frac_of e ≠ Frac.one ∧ frac_of e ≠ Frac.zero ∧
  e = mod_of_frac (frac_of e).
Proof.
move=> wm; rewrite /dh_of.
have hl : ∀ k v, (k, v) ∈ FMap.to_list m → m !!! k = v ∧ v ≠ Frac.zero.
  by move=> k v /FMap.elem_of_to_list.
case E: (FMap.to_list m) hl => [|[k v] [|kv l]] //= hl.
have [mk nv] := hl k v (list_elem_of_here _ _).
have [_ [gk av]] := wm k ltac:(by rewrite mk).
rewrite mk in av.
rewrite /mk_exp; case: bool_decide_reflect => [v1|n1] ek.
  by move: gk; rewrite ek.
case: ek => <- <-; rewrite frac_of_mod_of_frac //.
split=> //; apply/FMap.fmap_eq => k'.
by rewrite lookup_to_list E FMap.lookup_singleton /=; case: bool_decide.
Qed.

Lemma wf_exp_parts pt b e : wf pt → pt = PT2 O2Exp b e →
  dh_map pt = {[b := frac_of e]} ∧ frac_of e ≠ Frac.one ∧
  frac_of e ≠ Frac.zero ∧ e = mod_of_frac (frac_of e) ∧
  wf b ∧ negb (is_dh b) ∧
  wf_frac (frac_of e).
Proof.
move=> wpt ept; have wm := wf_dh_map _ wpt.
have [em [n1 [n0 ee]]] :=
  dh_of_exp_shape _ _ _ wm (eq_trans (dh_of_dh_map _ wpt) ept).
have [wb [gb ab]] :
  wf b ∧ negb (is_dh b) ∧
  wf_frac (dh_map pt !!! b).
  by apply: wm; rewrite em FMap.lookup_singleton bool_decide_true.
by rewrite em FMap.lookup_singleton bool_decide_true // in ab.
Qed.

End API.

End PreTerm.
