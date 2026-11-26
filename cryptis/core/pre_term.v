From mathcomp Require Import ssreflect.
From stdpp Require Import list_numbers.
From cryptis.lib Require Import list_sort fmap mset sms poly poly_gcd frac.
From cryptis.core.pre_term Require Export base with_stdpp normalize.

(* [base.v] holds the datatype definitions, class instances and the lemmas about
   the comparison function; [normalize.v] holds the normalization machinery and
   the exponentiation laws.  We reassemble the pieces into a single [PreTerm]
   module here, so that clients can keep referring to [PreTerm.foo]. *)
Module PreTerm.
Include base.PreTerm.
Include normalize.PreTerm.

Local Abbreviation poly := (Poly.poly pre_term).

(* A polynomial is as large as its monomials plus one per [+] between them, so
   that a Laurent monomial keeps its size and a unit part [p] with at least two
   monomials outweighs the monomials it multiplies.  A Diffie-Hellman pre-term
   is at least as large as the product of its factors [b ^ (n / q)]
   ([gfactors]); the factors are measured before [n / q] is reduced, so the
   size can be computed structurally.  The measures are parameterized by the
   size of atoms so that [tsize] unfolds to them. *)
Section Sizes.

Variable size : pre_term → nat.

Definition wsize_with (m : list pre_term) := sum_list_with size m.

Definition psize_with (A : poly_lists) :=
  sum_list_with wsize_with A.1 + sum_list_with wsize_with A.2 +
  (length A.1 + length A.2 - 1).

Definition esize_with (m : list pre_term) (d : poly_lists) :=
  match m, d with
  | [x], ([[]], []) => size x
  | _, _ => S (wsize_with m + psize_with d)
  end.

Definition fsize_with (b : pre_term) (m : list pre_term) (d : poly_lists) :=
  match m, d with
  | [], ([[]], []) => size b
  | _, _ => S (size b + esize_with m d)
  end.

Definition dh_size_with (l : list entry) :=
  sum_list_with (λ e,
    sum_list_with (λ m, fsize_with e.1 m e.2.2) e.2.1.1 +
    sum_list_with (λ m, fsize_with e.1 m e.2.2) e.2.1.2) l.

End Sizes.

Fixpoint tsize (pt : pre_term) : nat :=
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (tsize pt)
  | PT2 _ t1 t2 => S (tsize t1 + tsize t2)
  | PTMod F => S (psize_with tsize F.1 + psize_with tsize F.2)
  | PTDH [(b, (([m], []), d))] => S (tsize b + esize_with tsize m d)
  | PTDH l => S (dh_size_with tsize l)
  end.

Abbreviation wsize := (wsize_with tsize).
Abbreviation psize := (psize_with tsize).
Abbreviation esize := (esize_with tsize).
Abbreviation fsize := (fsize_with tsize).
Abbreviation dh_size := (dh_size_with tsize).

Lemma tsize_mod F : tsize (PTMod F) = S (psize F.1 + psize F.2).
Proof. by []. Qed.

Lemma tsize_dh_exp b m d :
  tsize (PTDH [(b, (([m], []), d))]) = S (tsize b + esize m d).
Proof. by []. Qed.

Lemma tsize_dh l : negb (is_exp (PTDH l)) → tsize (PTDH l) = S (dh_size l).
Proof. by case: l => [|[b [[[|m [|??]] [|??]] d]] [|??]]. Qed.

Lemma esizeE m d : esize m d = tsize (mod_of_lists (([m], []), d)).
Proof.
have -> : esize m d = if lone_atom (([m], []), d) is Some x then tsize x
                      else S (wsize m + psize d).
  by case: m => [|x [|y m]] //; case: d => [[|[|??] [|??]] [|??]].
have dflt : tsize (PTMod (([m], []), d)) = S (wsize m + psize d).
  by rewrite tsize_mod /psize_with /=; lia.
by rewrite /mod_of_lists; case: lone_atom.
Qed.

Lemma esize_cases m d :
  esize m d = S (wsize m + psize d) ∨
  ∃ x, m = [x] ∧ d = ([[]], []) ∧ esize m d = tsize x.
Proof.
rewrite /esize_with; case: m => [|x [|??]]; try by left.
case: d => [[|[|??] [|??]] [|??]]; try by left.
by right; exists x.
Qed.

Lemma fsize_cases b m d :
  fsize b m d = S (tsize b + esize m d) ∨
  m = [] ∧ d = ([[]], []) ∧ fsize b m d = tsize b.
Proof.
rewrite /fsize_with; case: m => [|??]; last by left.
case: d => [[|[|??] [|??]] [|??]]; try by left.
by right.
Qed.

Lemma psize_mono_lists m : psize ([m], []) = wsize m.
Proof. rewrite /psize_with /=; lia. Qed.

Lemma tsize_mod_of_lists F : tsize (mod_of_lists F) ≤ tsize (PTMod F).
Proof.
rewrite /mod_of_lists; case E: (lone_atom F) => [x|] //.
rewrite (proj1 (lone_atom_Some _ _) E) tsize_mod /psize_with /= /wsize_with /=.
lia.
Qed.

Lemma tsize_exp pt :
  is_exp pt → tsize pt = S (tsize (base pt) + tsize (expo pt)).
Proof. by case: is_expP => // b m d -> _; rewrite tsize_dh_exp esizeE. Qed.

Lemma tsize_mk_exp b r n :
  r ≠ Frac.one → Frac.num r = Poly.mono n →
  tsize (mk_exp b r) = S (tsize b + tsize (mod_aux r)).
Proof.
move=> n1 nr; rewrite /mk_exp bool_decide_eq_false_2 //.
by rewrite /mod_aux /lists nr poly_lists_mono tsize_dh_exp esizeE.
Qed.

(** *** Factor sizes *)

Lemma wsize_disj_union (m n : MSet.mset pre_term) :
  wsize (MSet.car (m ⊎ n)) = wsize (MSet.car m) + wsize (MSet.car n).
Proof.
rewrite /wsize_with -sum_list_with_app; apply: sum_list_with_Permutation.
exact: MSet.elements_disj_union.
Qed.

Lemma wsize_subseteq (m n : MSet.mset pre_term) :
  m ⊆ n → wsize (MSet.car m) ≤ wsize (MSet.car n).
Proof.
move=> /MSet.subseteq_count mn.
have -> : n = m ⊎ (n ∖ m).
  apply: MSet.count_inj => x.
  by rewrite MSet.count_disj_union MSet.count_difference; have := mn x; lia.
rewrite wsize_disj_union; lia.
Qed.

Lemma pos_map_inj {A B : Type}
    `{EqDecision A, Lexico A, !StrictOrder (@lexico A _),
      !TrichotomyT (@lexico A _)}
    `{EqDecision B, Lexico B, !StrictOrder (@lexico B _),
      !TrichotomyT (@lexico B _)}
    (f : A → B) (s : SMS.sms A) :
  (∀ a b, f a = f b → a = b) →
  SMS.pos (SMS.map f s) = MSet.map f (SMS.pos s) ∧
  SMS.neg (SMS.map f s) = MSet.map f (SMS.neg s).
Proof.
move=> finj; have d := MSet.map_disjoint f _ _ finj (SMS.pos_neg_disj s).
rewrite SMS.map_pos_neg SMS.pos_make SMS.neg_make.
rewrite MSet.difference_disjoint_l // MSet.difference_disjoint_l //.
by move=> y h1 h2; exact: d y h2 h1.
Qed.

Lemma sum_map_mono h (X : MSet.mset (MSet.mset pre_term)) :
  sum_list_with wsize (MSet.car <$> elements X) ≤
  sum_list_with wsize (MSet.car <$> elements (MSet.map (λ m, h ⊎ m) X)) ∧
  length (MSet.car <$> elements X) =
  length (MSet.car <$> elements (MSet.map (λ m, h ⊎ m) X)).
Proof.
have P : MSet.car <$> elements (MSet.map (λ m, h ⊎ m) X) ≡ₚ
         MSet.car <$> ((λ m, h ⊎ m) <$> elements X).
  by apply: fmap_Permutation; exact: MSet.elements_map_perm.
rewrite (sum_list_with_Permutation _ _ _ P) (Permutation_length P) !length_fmap.
have E (a : list pre_term) l :
  sum_list_with wsize (a :: l) = wsize a + sum_list_with wsize l by [].
split=> //; elim: (elements X) => [|m ms IH] //.
rewrite !fmap_cons !E wsize_disj_union; lia.
Qed.

Lemma psize_mul_mono h (q : poly) :
  psize (poly_lists_of q) ≤ psize (poly_lists_of (Poly.mono h * q)%P).
Proof.
have finj : ∀ a b, h ⊎ a = h ⊎ b → a = b.
  move=> a b e; apply: MSet.count_inj => x.
  by have := f_equal (MSet.count x) e; rewrite !MSet.count_disj_union; lia.
have [ep en] := pos_map_inj (λ m, h ⊎ m) (Poly.car q) finj.
have E : Poly.car (Poly.mono h * q)%P = SMS.map (λ m, h ⊎ m) (Poly.car q).
  exact: Poly.car_mul_mono.
rewrite /psize_with /poly_lists_of E ep en; cbn [fst snd].
have [s1 l1] := sum_map_mono h (SMS.pos (Poly.car q)).
have [s2 l2] := sum_map_mono h (SMS.neg (Poly.car q)).
lia.
Qed.

Lemma sum_map_monoE h (X : MSet.mset (MSet.mset pre_term)) :
  sum_list_with wsize (MSet.car <$> elements (MSet.map (λ m, h ⊎ m) X)) =
  sum_list_with wsize (MSet.car <$> elements X) +
  length (elements X) * wsize (MSet.car h).
Proof.
have P : MSet.car <$> elements (MSet.map (λ m, h ⊎ m) X) ≡ₚ
         MSet.car <$> ((λ m, h ⊎ m) <$> elements X).
  by apply: fmap_Permutation; exact: MSet.elements_map_perm.
rewrite (sum_list_with_Permutation _ _ _ P).
have E (a : list pre_term) l :
  sum_list_with wsize (a :: l) = wsize a + sum_list_with wsize l by [].
elim: (elements X) => [|m ms IH] //.
rewrite !fmap_cons !E wsize_disj_union IH /=; lia.
Qed.

Definition nentries (q : poly) : nat :=
  length (elements (SMS.pos (Poly.car q))) +
  length (elements (SMS.neg (Poly.car q))).

Lemma psize_mul_monoE h (q : poly) :
  psize (poly_lists_of (Poly.mono h * q)%P) =
  psize (poly_lists_of q) + nentries q * wsize (MSet.car h).
Proof.
have finj : ∀ a b, h ⊎ a = h ⊎ b → a = b.
  move=> a b e; apply: MSet.count_inj => x.
  by have := f_equal (MSet.count x) e; rewrite !MSet.count_disj_union; lia.
have [ep en] := pos_map_inj (λ m, h ⊎ m) (Poly.car q) finj.
have E : Poly.car (Poly.mono h * q)%P = SMS.map (λ m, h ⊎ m) (Poly.car q).
  exact: Poly.car_mul_mono.
rewrite /psize_with /poly_lists_of /nentries E ep en; cbn [fst snd].
rewrite !sum_map_monoE.
have [_ l1] := sum_map_mono h (SMS.pos (Poly.car q)).
have [_ l2] := sum_map_mono h (SMS.neg (Poly.car q)).
rewrite -l1 -l2 !length_fmap; lia.
Qed.

Lemma nentries_pos q : q ≠ Poly.zero → 0 < nentries q.
Proof.
move=> nq; rewrite /nentries.
case E1: (elements (SMS.pos (Poly.car q))) => [|x l]; last by rewrite /=; lia.
case E2: (elements (SMS.neg (Poly.car q))) => [|y l]; last by rewrite /=; lia.
exfalso; apply: nq; apply: Poly.car_inj; rewrite Poly.car_zero.
apply: SMS.elements_empty_inv.
by rewrite SMS.elements_pos_neg E1 E2.
Qed.

Lemma psize_opp (q : poly) :
  psize (poly_lists_of (- q)%P) = psize (poly_lists_of q).
Proof.
rewrite /psize_with /poly_lists_of.
rewrite Poly.car_opp.
rewrite SMS.pos_inv SMS.neg_inv; cbn [fst snd]; lia.
Qed.

Lemma make_one (p : poly) : Frac.make p Poly.one = Frac.of_poly p.
Proof. exact: Frac.of_poly_make. Qed.

Lemma poly_lists_one : poly_lists_of Poly.one = ([[]], []).
Proof. by rewrite Poly.oneE poly_lists_mono MSet.car_empty. Qed.

Lemma poly_lists_one_inv (q : poly) :
  poly_lists_of q = ([[]], []) → q = Poly.one.
Proof.
move=> e; rewrite -(poly_of_lists_of q) e -(poly_of_lists_of Poly.one).
by rewrite poly_lists_one.
Qed.

(** The factor [b ^ (n / q)] of a logarithm is at most as large as [n / q]
    before reduction. *)
Lemma tsize_exp_factor b (q : poly) n x :
  q ≠ Poly.zero → x ∈ exp_factor b q n →
  tsize x ≤ fsize b (MSet.car n) (poly_lists_of q).
Proof.
move=> nq xe.
have [r' [n' [-> [Er' Hr']]]] := elem_of_exp_factor b q n x nq xe.
set r := Frac.make (Poly.mono n) q in Hr'.
have [e1 e2] := Frac.make_cancel (Poly.mono n) q nq.
have den_r' : Frac.den r' = Frac.den r.
  by case: Hr' => ->; rewrite ?Frac.den_opp.
have num_r' : Poly.mono n' = Frac.num r ∨ Poly.mono n' = (- Frac.num r)%P.
  by rewrite -Er'; case: Hr' => ->; [left|right; rewrite Frac.num_opp].
have [G [EG Eq]] := Poly.cancel_spec (Poly.mono n) q.
rewrite -e1 -e2 -/r in EG Eq.
have nn : n' ⊆ n.
  have : PolyGcd.dvd (Frac.num r) (Poly.mono n).
    by exists G; rewrite {1}EG; exact: (comm Poly.mul).
  move=> /PolyGcd.dvd_mono [n'' [sub E'']].
  suff -> : n' = n'' by [].
  apply: Poly.mono_pm_inj.
  by case: num_r' E'' => -> [] ->; rewrite ?Poly.opp_opp; tauto.
have qq : psize (poly_lists_of (Frac.den r')) ≤ psize (poly_lists_of q).
  have : PolyGcd.dvd G (Poly.mono n) by exists (Frac.num r).
  move=> /PolyGcd.dvd_mono [h [_ [EGh|EGh]]]; rewrite den_r' Eq EGh.
    exact: psize_mul_mono.
  by rewrite Poly.mul_opp_l psize_opp; exact: psize_mul_mono.
have neg_mono m : Poly.mono n' ≠ (- Poly.mono m)%P.
  move=> /(f_equal (Poly.coeff n')).
  rewrite Poly.coeff_opp !Poly.coeff_mono bool_decide_eq_true_2 //.
  by case: bool_decide.
case: (decide (r' = Frac.one)) => [->|n1].
  rewrite /mk_exp bool_decide_eq_true_2 //.
  by case: (fsize_cases b (MSet.car n) (poly_lists_of q)) => [->|[_ [_ ->]]];
    lia.
rewrite (tsize_mk_exp _ _ _ n1 Er').
case: (fsize_cases b (MSet.car n) (poly_lists_of q)) => [->|[en [eq _]]];
  last first.
  (* [n / q] is [1 / 1]: its factor is [b] itself. *)
  have n0 : n = ∅ by apply: MSet.car_inj; rewrite en MSet.car_empty.
  have rE : r = Frac.one.
    by rewrite /r n0 (poly_lists_one_inv _ eq) -Poly.oneE make_one -Frac.oneE.
  case: Hr' => E1; first by case: n1; rewrite E1 rE.
  by case: (neg_mono ∅); rewrite -Er' E1 rE Frac.num_opp Frac.num_one Poly.oneE.
suff : tsize (mod_aux r') ≤ esize (MSet.car n) (poly_lists_of q) by lia.
case: (esize_cases (MSet.car n) (poly_lists_of q)) => [->|[y [en [eq ->]]]].
  apply: Nat.le_trans (tsize_mod_of_lists _) _.
  rewrite /lists Er' poly_lists_mono tsize_mod; cbn [fst snd].
  rewrite psize_mono_lists; have := wsize_subseteq _ _ nn; lia.
(* [n / q] is a lone atom [y]: already reduced. *)
have ny : n = {[+ y +]}.
  by apply: MSet.car_inj; rewrite en MSet.car_singleton.
have rE : r = Frac.of_poly (Poly.var y).
  by rewrite /r ny (poly_lists_one_inv _ eq) make_one Poly.varE.
case: Hr' => E1; first by rewrite E1 rE /mod_aux lists_var.
by case: (neg_mono {[+ y +]});
  rewrite -Er' E1 rE Frac.num_opp Frac.num_of_poly Poly.varE.
Qed.

Lemma tsize_gfactors_lt pt x :
  wf pt → is_gmul pt → x ∈ gfactors pt → tsize x < tsize pt.
Proof.
case: pt => // l wl gl.
have nx := is_gmul_Nexp _ gl.
rewrite /gfactors; case E: (is_exp (PTDH l)) nx => // _.
move=> /elem_of_dh_factors [b [r [n [br [nr xe]]]]].
have := tsize_exp_factor b (Frac.den r) n x (Frac.den_neq0 r) xe.
rewrite tsize_dh; last by rewrite E.
suff : fsize b (MSet.car n) (poly_lists_of (Frac.den r)) ≤ dh_size l by lia.
have bl : (b, lists r) ∈ l.
  rewrite -(entries_of_entries l wl); apply/list_elem_of_fmap.
  by exists (b, r).
have := sum_list_with_in _ (λ e : entry,
  sum_list_with (λ m, fsize e.1 m e.2.2) e.2.1.1 +
  sum_list_with (λ m, fsize e.1 m e.2.2) e.2.1.2) _ bl.
cbn [fst snd lists]; rewrite /dh_size_with.
set g := λ m, fsize b m (poly_lists_of (Frac.den r)).
move: nr => /SMS.elem_of_pos_neg [] np.
- have := sum_list_with_in (MSet.car n) g (poly_lists_of (Frac.num r)).1
    (list_elem_of_fmap_2 MSet.car _ _ np).
  rewrite /g; lia.
- have := sum_list_with_in (MSet.car n) g (poly_lists_of (Frac.num r)).2
    (list_elem_of_fmap_2 MSet.car _ _ np).
  rewrite /g; lia.
Qed.

Lemma tsize_gfactors_le pt x : wf pt → x ∈ gfactors pt → tsize x ≤ tsize pt.
Proof.
move=> wpt xp; case G: (is_gmul pt).
  by apply: Nat.lt_le_incl; apply: tsize_gfactors_lt => //; rewrite G.
rewrite gfactors_Ngmul in xp; last by rewrite G.
by move/SMS.elem_of_singleton: xp => ->.
Qed.

(** ** Scalars

    [mul s] and [sum s] multiply and add up the scalars of a signed multiset
    through their fractions ([frac_of_mul], [frac_of_sum]).  [factors pt]
    lists the atoms of the monomial content of the numerator of [frac_of pt]
    (positively) and of its denominator (negatively), with their unit parts
    when these are not [1], so that [mul (factors pt) = pt] ([factorsK]).
    On an atom [x], [count x pt] is the [x]-adic valuation of [pt]
    ([count_vx]). *)

Definition mul (s : SMS.sms pre_term) : pre_term :=
  mod_aux (Frac.sprod frac_of s).

Definition sum (s : SMS.sms pre_term) : pre_term :=
  mod_aux (Frac.ssum frac_of s).

Definition units (p : poly) : MSet.mset pre_term :=
  if bool_decide (PolyGcd.unit_part p = Poly.one) then ∅
  else {[+ mod_aux (Frac.of_poly (PolyGcd.unit_part p)) +]}.

Definition factors pt : SMS.sms pre_term :=
  SMS.make
    (PolyGcd.content (Frac.num (frac_of pt)) ⊎ units (Frac.num (frac_of pt)))
    (PolyGcd.content (Frac.den (frac_of pt)) ⊎ units (Frac.den (frac_of pt))).

Definition count x pt : Z := SMS.count x (factors pt).

Lemma atoms_all_fprod_frac_of P (l : list pre_term) :
  (∀ x, x ∈ l → atoms_all P (frac_of x)) →
  atoms_all P (Frac.fprod (frac_of <$> l)).
Proof.
move=> h; apply: atoms_all_fprod; apply/Forall_fmap/list.Forall_forall.
by move=> x /h.
Qed.

Lemma atoms_all_fsum_frac_of P (l : list pre_term) :
  (∀ x, x ∈ l → atoms_all P (frac_of x)) →
  atoms_all P (Frac.fsum (frac_of <$> l)).
Proof.
move=> h; apply: atoms_all_fsum; apply/Forall_fmap/list.Forall_forall.
by move=> x /h.
Qed.

Lemma atoms_all_sprod P s :
  (∀ x, x ∈ s → atoms_all P (frac_of x)) →
  atoms_all P (Frac.sprod frac_of s).
Proof.
move=> h; rewrite Frac.sprodE; apply: atoms_all_div;
  apply: atoms_all_fprod_frac_of => x /MSet.elem_of_elements hx; apply: h.
- exact: SMS.elem_of_pos hx.
- exact: SMS.elem_of_neg hx.
Qed.

Lemma atoms_all_ssum P s :
  (∀ x, x ∈ s → atoms_all P (frac_of x)) →
  atoms_all P (Frac.ssum frac_of s).
Proof.
move=> h; rewrite Frac.ssumE; apply: atoms_all_sub;
  apply: atoms_all_fsum_frac_of => x /MSet.elem_of_elements hx; apply: h.
- exact: SMS.elem_of_pos hx.
- exact: SMS.elem_of_neg hx.
Qed.

Lemma wf_mul s : (∀ x, x ∈ s → wf x) → wf (mul s).
Proof.
move=> h; apply: wf_mod_aux.
by apply: atoms_all_sprod => x /h; exact: frac_of_atoms.
Qed.

Lemma wf_sum s : (∀ x, x ∈ s → wf x) → wf (sum s).
Proof.
move=> h; apply: wf_mod_aux.
by apply: atoms_all_ssum => x /h; exact: frac_of_atoms.
Qed.

Lemma frac_of_mul s :
  (∀ x, x ∈ s → wf x) → frac_of (mul s) = Frac.sprod frac_of s.
Proof.
move=> h; apply: frac_of_mod_aux_wf.
by apply: atoms_all_sprod => x /h; exact: frac_of_atoms.
Qed.

Lemma frac_of_sum s :
  (∀ x, x ∈ s → wf x) → frac_of (sum s) = Frac.ssum frac_of s.
Proof.
move=> h; apply: frac_of_mod_aux_wf.
by apply: atoms_all_ssum => x /h; exact: frac_of_atoms.
Qed.

Lemma elem_of_content x (p : poly) :
  x ∈ PolyGcd.content p → ∃ m, m ∈ Poly.car p ∧ x ∈ m.
Proof.
case: (decide (p = Poly.zero)) => [->|np].
  by rewrite PolyGcd.content_zero => h; case: (MSet.not_elem_of_empty _ h).
move=> xc; destruct (elements (Poly.car p)) as [|m ms] eqn:E.
  by case: np; apply: Poly.car_inj; rewrite Poly.car_zero;
    exact: SMS.elements_empty_inv.
have mp : m ∈ Poly.car p by rewrite -SMS.elem_of_elements E; left.
by exists m; split=> //; apply: MSet.elem_of_subseteq xc;
  exact: PolyGcd.content_sub.
Qed.

Lemma elem_of_unit_part x (p : poly) m :
  m ∈ Poly.car (PolyGcd.unit_part p) → x ∈ m →
  ∃ m', m' ∈ Poly.car p ∧ x ∈ m'.
Proof.
rewrite PolyGcd.unit_partE PolyGcd.car_unmono.
move=> /SMS.elem_of_map [m' [-> mp]] /MSet.elem_of_difference h.
by exists m'; split=> //; apply/MSet.elem_of_count; lia.
Qed.

Lemma units_mod (p : poly) y : y ∈ units p → is_mod y.
Proof.
rewrite /units; case: bool_decide_reflect => [_|nu].
  by move=> h; case: (MSet.not_elem_of_empty _ h).
move=> /MSet.elem_of_singleton ->; rewrite /mod_aux /mod_of_lists.
case E: (lone_atom (lists (Frac.of_poly (PolyGcd.unit_part p)))) => [z|] //.
exfalso.
have Er : Frac.of_poly (PolyGcd.unit_part p) = Frac.of_poly (Poly.var z).
  by apply: lists_inj; rewrite lists_var; apply/lone_atom_Some.
have := PolyGcd.content_unit_part p.
rewrite (Frac.of_poly_inj _ _ Er) Poly.varE PolyGcd.content_mono.
move=> /(f_equal (MSet.count z)); rewrite MSet.count_singleton MSet.count_empty.
by rewrite bool_decide_eq_true_2.
Qed.

Lemma atoms_all_of_poly P (p : poly) :
  (∀ m x, m ∈ Poly.car p → x ∈ m → P x) → atoms_all P (Frac.of_poly p).
Proof.
move=> h m x; rewrite Frac.num_of_poly Frac.den_of_poly Poly.oneE Poly.car_mono.
case=> [mp|/SMS.elem_of_singleton ->]; first exact: h.
by move=> e; case: (MSet.not_elem_of_empty _ e).
Qed.

Lemma frac_of_units (p : poly) y :
  (∀ m x, m ∈ Poly.car p → x ∈ m → negb (is_mod x)) →
  y ∈ units p → frac_of y = Frac.of_poly (PolyGcd.unit_part p).
Proof.
move=> h; rewrite /units; case: bool_decide_reflect => [_|_].
  by move=> e; case: (MSet.not_elem_of_empty _ e).
move=> /MSet.elem_of_singleton ->; apply: frac_of_mod_aux.
apply: atoms_all_of_poly => m x mu xm.
have [m' [m'p xm']] := elem_of_unit_part x p m mu xm.
exact: h m'p xm'.
Qed.

Lemma wf_units (p : poly) y :
  (∀ m x, m ∈ Poly.car p → x ∈ m → wf x && negb (is_mod x)) →
  y ∈ units p → wf y.
Proof.
move=> h; rewrite /units; case: bool_decide_reflect => [_|_].
  by move=> e; case: (MSet.not_elem_of_empty _ e).
move=> /MSet.elem_of_singleton ->; apply: wf_mod_aux.
apply: atoms_all_of_poly => m x mu xm.
have [m' [m'p xm']] := elem_of_unit_part x p m mu xm.
exact: h m'p xm'.
Qed.

Lemma wf_factors pt y : wf pt → y ∈ factors pt → wf y.
Proof.
move=> wpt; have A := frac_of_atoms pt wpt.
have hn : ∀ m x, m ∈ Poly.car (Frac.num (frac_of pt)) → x ∈ m →
    wf x && negb (is_mod x).
  by move=> m x mr xm; apply: (A m x) => //; left.
have hd : ∀ m x, m ∈ Poly.car (Frac.den (frac_of pt)) → x ∈ m →
    wf x && negb (is_mod x).
  by move=> m x mr xm; apply: (A m x) => //; right.
rewrite /factors => /SMS.elem_of_make [] /MSet.elem_of_disj_union [].
- move=> /elem_of_content [m [mr xm]].
  by have /andb_True [] := hn m y mr xm.
- exact: wf_units hn.
- move=> /elem_of_content [m [mr xm]].
  by have /andb_True [] := hd m y mr xm.
- exact: wf_units hd.
Qed.

Lemma factors_atom pt : negb (is_mod pt) → factors pt = {[+ pt +]}.
Proof.
move=> npt.
rewrite /factors (frac_of_Nmod _ npt) Frac.num_of_poly Frac.den_of_poly.
rewrite Poly.varE Poly.oneE !PolyGcd.content_mono /units.
rewrite !PolyGcd.unit_part_mono bool_decide_eq_true_2 //.
by rewrite !(right_id ∅ (⊎)) -SMS.singleton_make.
Qed.

Lemma count_vx x pt : negb (is_mod x) → count x pt = Frac.vx x (frac_of pt).
Proof.
move=> nx.
have U p : MSet.count x (units p) = 0.
  apply/MSet.not_elem_of_count => /units_mod.
  by case: (is_mod x) nx.
rewrite /count /factors SMS.count_make !MSet.count_disj_union !U Frac.vxE.
lia.
Qed.

Lemma frac_of_var pt : negb (is_mod pt) → frac_of pt = Frac.var pt.
Proof. by rewrite Frac.varE; exact: frac_of_Nmod. Qed.

Lemma fprod_frac_of_var (l : list pre_term) :
  (∀ x, x ∈ l → negb (is_mod x)) →
  Frac.fprod (frac_of <$> l) = Frac.fprod (Frac.var <$> l).
Proof.
elim: l => [|x l IH] h; first by [].
have hl : ∀ y, y ∈ l → negb (is_mod y) by move=> y yl; apply: h; right.
rewrite !fmap_cons !Frac.fprod_cons (IH hl) frac_of_var //.
by apply: h; left.
Qed.

Lemma frac_of_unit_part (p : poly) :
  (∀ m x, m ∈ Poly.car p → x ∈ m → negb (is_mod x)) →
  frac_of (mod_aux (Frac.of_poly (PolyGcd.unit_part p))) =
  Frac.of_poly (PolyGcd.unit_part p).
Proof.
move=> h; apply: frac_of_mod_aux; apply: atoms_all_of_poly => m x mu xm.
have [m' [m'p xm']] := elem_of_unit_part x p m mu xm.
exact: h m'p xm'.
Qed.

Lemma fprod_units (p : poly) :
  (∀ m x, m ∈ Poly.car p → x ∈ m → negb (is_mod x)) →
  Frac.fprod (frac_of <$> elements (units p)) =
  Frac.of_poly (PolyGcd.unit_part p).
Proof.
move=> h; rewrite /units; case: bool_decide_reflect => [->|nu].
  by rewrite MSet.elements_empty fmap_nil Frac.fprod_nil Frac.oneE.
rewrite MSet.elements_singleton fmap_cons fmap_nil.
rewrite Frac.fprod_cons Frac.fprod_nil frac_of_unit_part //.
by rewrite (comm Frac.mul) (left_id Frac.one Frac.mul).
Qed.

Lemma fprod_content_units (p : poly) :
  (∀ m x, m ∈ Poly.car p → x ∈ m → negb (is_mod x)) →
  Frac.fprod (frac_of <$> elements (PolyGcd.content p ⊎ units p)) =
  Frac.of_poly p.
Proof.
move=> h.
have C : ∀ x, x ∈ elements (PolyGcd.content p) → negb (is_mod x).
  move=> x /MSet.elem_of_elements /elem_of_content [m [mp xm]].
  exact: h mp xm.
rewrite Frac.fprod_disj_union fprod_units // (fprod_frac_of_var _ C).
by rewrite Frac.fprod_var -Frac.of_poly_mul PolyGcd.content_unitK.
Qed.

Lemma frac_of_units_neq0 (p : poly) y :
  (∀ m x, m ∈ Poly.car p → x ∈ m → negb (is_mod x)) → p ≠ Poly.zero →
  y ∈ PolyGcd.content p ⊎ units p → frac_of y ≠ Frac.zero.
Proof.
move=> h np /MSet.elem_of_disj_union [].
- move=> /elem_of_content [m [mp xm]]; rewrite frac_of_var; last exact: h mp xm.
  exact: Frac.var_neq0.
- move=> yu; rewrite (frac_of_units p y h yu) Frac.zeroE => /Frac.of_poly_inj.
  exact: PolyGcd.unit_part_neq0.
Qed.

Lemma factorsK pt : wf pt → mul (factors pt) = pt.
Proof.
move=> wpt; have A := frac_of_atoms pt wpt.
have hn : ∀ m x, m ∈ Poly.car (Frac.num (frac_of pt)) → x ∈ m →
    negb (is_mod x).
  by move=> m x mr xm; have /andb_True [] := A m x (or_introl mr) xm.
have hd : ∀ m x, m ∈ Poly.car (Frac.den (frac_of pt)) → x ∈ m →
    negb (is_mod x).
  by move=> m x mr xm; have /andb_True [] := A m x (or_intror mr) xm.
have S : ∀ x, x ∈ PolyGcd.content (Frac.num (frac_of pt)) ⊎
                  units (Frac.num (frac_of pt)) →
              x ∈ PolyGcd.content (Frac.den (frac_of pt)) ⊎
                  units (Frac.den (frac_of pt)) →
              frac_of x ≠ Frac.zero.
  move=> x _; apply: frac_of_units_neq0 hd _; exact: Frac.den_neq0.
rewrite /mul /factors (Frac.sprod_make _ _ _ S) !fprod_content_units //.
by rewrite -Frac.make_div Frac.make_num_den mod_aux_frac_of.
Qed.

Lemma units_mono X : units (Poly.mono X) = ∅.
Proof. by rewrite /units PolyGcd.unit_part_mono bool_decide_eq_true_2. Qed.

Lemma factors_mul_atoms s :
  (∀ x, x ∈ s → wf x ∧ negb (is_mod x)) → factors (mul s) = s.
Proof.
move=> h.
have W : ∀ x, x ∈ s → wf x by move=> x /h [].
have E : Frac.sprod frac_of s = Frac.sprod Frac.var s.
  by apply: Frac.sprod_ext => x /h [_ nx]; exact: frac_of_var.
have [en ed] := Frac.sprod_var_canon s.
rewrite /factors (frac_of_mul _ W) E en ed !PolyGcd.content_mono !units_mono.
by rewrite !(right_id ∅ (⊎)) SMS.make_pos_neg.
Qed.

(** The atoms of a pre-term are the variables of its fraction. *)
Definition atoms pt : list pre_term := frac_vars (frac_of pt).

Lemma elem_of_atoms x pt :
  x ∈ atoms pt ↔
  ∃ m, (m ∈ Poly.car (Frac.num (frac_of pt)) ∨
        m ∈ Poly.car (Frac.den (frac_of pt))) ∧ x ∈ m.
Proof.
rewrite /atoms /frac_vars elem_of_app !Poly.elem_of_vars.
split.
- by case=> -[m [mp xm]]; exists m; split=> //; [left|right].
- by case=> m [[mp|mp] xm]; [left|right]; exists m.
Qed.

Lemma atoms_wf pt x : wf pt → x ∈ atoms pt → wf x ∧ negb (is_mod x).
Proof.
move=> wpt /elem_of_atoms [m [mp xm]].
by have /andb_True := frac_of_atoms pt wpt m x mp xm.
Qed.

Lemma atoms_atom pt x : negb (is_mod pt) → x ∈ atoms pt ↔ x = pt.
Proof.
move=> npt; rewrite elem_of_atoms (frac_of_Nmod _ npt).
rewrite car_num_var car_den_of_poly; split.
- case=> m [[/SMS.elem_of_singleton ->|/SMS.elem_of_singleton ->]].
    by move/MSet.elem_of_singleton.
  by move=> e; case: (MSet.not_elem_of_empty _ e).
- move=> ->; exists {[+ pt +]}; split.
    by left; apply/SMS.elem_of_singleton.
  exact/MSet.elem_of_singleton.
Qed.

(** ** Laurent monomials

    A fraction is a Laurent monomial ([mfrac]) when its numerator and its
    denominator are monomials; a pre-term is [laurent] when its factors are
    atoms, which happens exactly when its fraction is a Laurent monomial
    ([laurent_mfrac]). *)

Section Laurent.

Add Ring poly_ring_M : (Poly.poly_ring_theory (T := pre_term)).

Definition mfrac (r : Frac.frac pre_term) : Prop :=
  ∃ n Q, Frac.num r = Poly.mono n ∧ Frac.den r = Poly.mono Q.

Definition laurent pt : Prop := ∀ x, x ∈ factors pt → negb (is_mod x).

Lemma mfrac_neq0 r : mfrac r → r ≠ Frac.zero.
Proof.
case=> n [Q [en _]] e; move: en; rewrite e Frac.num_zero => e'.
exact: (PolyGcd.mono_neq0 _ (eq_sym e')).
Qed.

Lemma mfrac_lfrac r : mfrac r → lfrac r.
Proof. by case=> n [Q [_ eQ]]; exists Q. Qed.

Lemma mfrac_make_mono n Q : mfrac (Frac.make (Poly.mono n) (Poly.mono Q)).
Proof.
have [Q' [K [hd [_ hP]]]] := make_mono_den (Poly.mono n) Q.
move: (Frac.make _ _) hd hP => r hd hP.
have [n' [_ hn]] := PolyGcd.dvd_mono (Frac.num r) n
  ltac:(by exists (Poly.mono K); rewrite hP (comm Poly.mul)).
exists n', Q'; split=> //.
case: hn => // e; exfalso; rewrite e in hP.
have E : Poly.mono n = Poly.opp (Poly.mono (K ⊎ n')).
  by rewrite hP -Poly.mul_mono; ring.
have En := Poly.mono_pm_inj n (K ⊎ n') (or_intror E).
by apply: (mono_neq_opp n); rewrite {1}E En.
Qed.

Lemma mfrac_one : mfrac Frac.one.
Proof. by exists ∅, ∅; rewrite Frac.num_one Frac.den_one Poly.oneE. Qed.

Lemma mfrac_var x : mfrac (Frac.var x).
Proof.
exists {[+ x +]}, ∅.
by rewrite Frac.varE Frac.num_of_poly Frac.den_of_poly Poly.varE Poly.oneE.
Qed.

Lemma mfrac_mul r1 r2 : mfrac r1 → mfrac r2 → mfrac (Frac.mul r1 r2).
Proof.
move=> [n1 [Q1 [e1 f1]]] [n2 [Q2 [e2 f2]]].
by rewrite Frac.mulE e1 f1 e2 f2 !Poly.mul_mono; exact: mfrac_make_mono.
Qed.

Lemma mfrac_inv r : mfrac r → mfrac (Frac.inv r).
Proof.
move=> [n [Q [e f]]].
rewrite -(Frac.make_num_den r) e f Frac.inv_make; first exact: mfrac_make_mono.
exact: PolyGcd.mono_neq0.
Qed.

Lemma mfrac_sprod_var s : mfrac (Frac.sprod Frac.var s).
Proof.
by have [en ed] := Frac.sprod_var_canon s; exists (SMS.pos s), (SMS.neg s).
Qed.

(** A fraction has a monic numerator ([mnum]) when its numerator is a
    monomial; products keep such numerators ([mnum_mul]). *)
Definition mnum (r : Frac.frac pre_term) : Prop :=
  ∃ n, Frac.num r = Poly.mono n.

Lemma mfrac_mnum r : mfrac r → mnum r.
Proof. by case=> n [Q [en _]]; exists n. Qed.

Lemma mnum_neq0 r : mnum r → r ≠ Frac.zero.
Proof.
case=> n en e; move: en; rewrite e Frac.num_zero => e'.
exact: (PolyGcd.mono_neq0 _ (eq_sym e')).
Qed.

Lemma mnum_mul r1 r2 : mnum r1 → mnum r2 → mnum (Frac.mul r1 r2).
Proof. by move=> [n1 e1] [n2 e2]; exact: (Frac.num_mul_mono _ _ _ _ e1 e2). Qed.

Lemma laurent_mfrac pt : wf pt → laurent pt ↔ mfrac (frac_of pt).
Proof.
move=> wpt; split.
- move=> L; rewrite -(factorsK _ wpt).
  rewrite (frac_of_mul _ (λ x hx, wf_factors _ _ wpt hx)).
  have E : Frac.sprod frac_of (factors pt) = Frac.sprod Frac.var (factors pt).
    by apply: Frac.sprod_ext => x /L; exact: frac_of_var.
  rewrite E; exact: mfrac_sprod_var.
- move=> [n [Q [en eQ]]] x; rewrite /factors en eQ !PolyGcd.content_mono.
  rewrite !units_mono !(right_id ∅ (⊎)) => /SMS.elem_of_make hx.
  have A := frac_of_atoms pt wpt.
  have nn : n ∈ Poly.car (Frac.num (frac_of pt)).
    by rewrite en Poly.car_mono; apply/SMS.elem_of_singleton.
  have nQ : Q ∈ Poly.car (Frac.den (frac_of pt)).
    by rewrite eQ Poly.car_mono; apply/SMS.elem_of_singleton.
  case: hx => hx.
  + by have /andb_True [] := A n x (or_introl nn) hx.
  + by have /andb_True [] := A Q x (or_intror nQ) hx.
Qed.

End Laurent.

(** ** Powers of non-products

    A non-product is a power of a base that is neither a power nor a product;
    raising it to a Laurent monomial yields another such power. *)

Lemma frac_of_one : frac_of one = Frac.one.
Proof. by rewrite /one /frac_of -lists_one of_lists_lists. Qed.

Lemma base_Ngnf pt :
  wf pt → negb (is_gmul pt) → negb (is_gnon_free (base pt)).
Proof.
move=> wpt Ng; case E: (is_exp pt).
  case: (is_expP pt) E wpt => [b m d -> _ /wf_exp_entry [_ [gb _]] //|//].
rewrite base_expN ?E // /is_gnon_free E.
by move: Ng; case: (is_gmul pt).
Qed.

Lemma frac_of_exp_entry b m d :
  wf (PTDH [(b, (([m], []), d))]) →
  frac_of (mod_of_lists (([m], []), d)) = of_lists (([m], []), d) ∧
  Frac.num (of_lists (([m], []), d)) = Poly.mono (MSet.of_list m).
Proof.
move=> /wf_exp_entry [_ [_ [aF cF]]].
have lr := lists_of_lists _ cF.
split.
- rewrite -{1}lr; apply: frac_of_mod_aux.
  apply: (atoms_all_impl (λ x, wf x && negb (is_mod x))).
    by move=> x /andb_True [].
  by apply/all_atoms_lists; rewrite lr.
- have e1 : poly_lists_of (Frac.num (of_lists (([m], []), d))) = ([m], []).
    by move: lr => /(f_equal fst).
  by rewrite -(poly_of_lists_of (Frac.num _)) e1 poly_of_lists_mono.
Qed.

Lemma mnum_expo pt : wf pt → negb (is_gmul pt) → mnum (frac_of (expo pt)).
Proof.
move=> wpt Ng; case E: (is_exp pt); last first.
  have nE : negb (is_exp pt) by rewrite E.
  rewrite (expo_expN _ nE) frac_of_one; exists ∅.
  by rewrite Frac.num_one Poly.oneE.
case: (is_expP pt) E wpt => [b m d -> _ wpt|//].
have [E1 E2] := frac_of_exp_entry _ _ _ wpt.
by rewrite [expo _]/= E1; exists (MSet.of_list m).
Qed.

Lemma dh_map_Ngmul pt :
  wf pt → negb (is_gmul pt) → dh_map pt = {[base pt := frac_of (expo pt)]}.
Proof.
move=> wpt Ng; case E: (is_exp pt); last first.
  have nE : negb (is_exp pt) by rewrite E.
  rewrite (base_expN _ nE) (expo_expN _ nE) frac_of_one dh_map_Ngnf //.
  by rewrite /is_gnon_free E; move: Ng; case: (is_gmul pt).
case: (is_expP pt) E wpt => [b m d -> _ wpt|//].
have [E1 _] := frac_of_exp_entry _ _ _ wpt.
rewrite [base _]/= [expo _]/= E1.
change (dh_map (PTDH [(b, (([m], []), d))])) with
  (of_entries [(b, (([m], []), d))]).
apply/FMap.fmap_eq => k; rewrite lookup_of_entries.
rewrite FMap.lookup_singleton [FMap.lookup_list _ _ _]/=.
case: bool_decide => //.
by rewrite -lists_zero of_lists_lists.
Qed.

Lemma exp_frac_Ngmul b r :
  wf b → negb (is_gmul b) → Frac.mul (frac_of (expo b)) r ≠ Frac.zero →
  exp_frac b r = mk_exp (base b) (Frac.mul (frac_of (expo b)) r).
Proof.
move=> wb Nb nr.
rewrite /exp_frac (dh_map_Ngmul _ wb Nb).
have -> : dh_scale r {[base b := frac_of (expo b)]} =
          {[base b := Frac.mul (frac_of (expo b)) r]}.
  apply/FMap.fmap_eq => k; rewrite lookup_dh_scale !FMap.lookup_singleton.
  by case: bool_decide => //; rewrite Frac.mul_zero_l.
exact: dh_of_singleton.
Qed.

Lemma mk_exp_mnum b r :
  negb (is_gnon_free b) → mnum r →
  negb (is_gmul (mk_exp b r)) ∧ base (mk_exp b r) = b ∧
  expo (mk_exp b r) = mod_aux r.
Proof.
move=> gb [n en]; split; first exact: (mk_exp_Ngmul _ _ _ gb en).
case: (decide (r = Frac.one)) => [->|n1].
- have nb := Ngnf_Nexp _ gb.
  rewrite /mk_exp bool_decide_eq_true_2 // (base_expN _ nb) (expo_expN _ nb).
  by rewrite /mod_aux lists_one.
- by rewrite (base_mk_exp _ _ _ n1 en) (expo_mk_exp _ _ _ n1 en).
Qed.

Lemma exp_factor_mono b n Q :
  exp_factor b (Poly.mono Q) n =
  {[+ mk_exp b (Frac.make (Poly.mono n) (Poly.mono Q)) +]}.
Proof.
have [n' [Q' [en _]]] := mfrac_make_mono n Q.
by rewrite /exp_factor; cbv zeta; rewrite en Poly.first_neg_mono.
Qed.

(** The group factors of an element with Laurent logarithms are powers whose
    exponents are Laurent monomials. *)
Lemma gfactors_llogs pt u :
  wf pt → llogs pt → u ∈ gfactors pt →
  wf u ∧ llogs u ∧ mfrac (frac_of (expo u)).
Proof.
move=> wpt L; rewrite (gfactors_dh _ wpt).
move=> /elem_of_dh_factors [b [r [n [br [nr ue]]]]].
have /FMap.elem_of_to_list [mb r0] := br.
have [wb [gb ar]] := wf_dh_map _ wpt b ltac:(by rewrite mb).
rewrite mb in ar.
have [Q eQ] := L b; rewrite mb in eQ.
have ar' : atoms_all (λ x, wf x && negb (is_mod x))
             (Frac.make (Poly.mono n) (Poly.mono Q)).
  by rewrite -eQ; apply: atoms_all_make_mono nr ar.
move: ue; rewrite eQ exp_factor_mono => /SMS.elem_of_singleton ->.
have mr := mfrac_make_mono n Q.
have nr' := mfrac_neq0 _ mr.
split; first exact: wf_mk_exp.
split.
- move=> k; rewrite (dh_map_mk_exp _ _ gb nr') FMap.lookup_singleton.
  by case: bool_decide; [exact: mfrac_lfrac|exact: lfrac_zero].
- have [_ [_ ->]] := mk_exp_mnum _ _ gb (mfrac_mnum _ mr).
  by rewrite frac_of_mod_aux_wf.
Qed.

(** ** Sizes of powers *)

Lemma tsize_pos pt : 0 < tsize pt.
Proof.
case: pt => [o|o t|o t1 t2|F|l]; try by rewrite /=; lia.
case E: (is_exp (PTDH l)).
- have xE : is_exp (PTDH l) by rewrite E.
  rewrite (tsize_exp _ xE); lia.
- have nE : negb (is_exp (PTDH l)) by rewrite E.
  rewrite (tsize_dh _ nE); lia.
Qed.

Lemma psize_ge_l (A : poly_lists) m : m ∈ A.1 → wsize m ≤ psize A.
Proof.
by move=> h; rewrite /psize_with; have := sum_list_with_in _ wsize _ h; lia.
Qed.

Lemma psize_ge_r (A : poly_lists) m : m ∈ A.2 → wsize m ≤ psize A.
Proof.
by move=> h; rewrite /psize_with; have := sum_list_with_in _ wsize _ h; lia.
Qed.

Lemma psize_ge (q : poly) n :
  n ∈ Poly.car q → wsize (MSet.car n) ≤ psize (poly_lists_of q).
Proof.
move=> /SMS.elem_of_pos_neg [] h.
- by apply: psize_ge_l; exact: list_elem_of_fmap_2 h.
- by apply: psize_ge_r; exact: list_elem_of_fmap_2 h.
Qed.

Lemma tsize_mod_aux_le r :
  tsize (mod_aux r) ≤
  S (psize (poly_lists_of (Frac.num r)) + psize (poly_lists_of (Frac.den r))).
Proof. exact: (tsize_mod_of_lists (lists r)). Qed.

Lemma tsize_mk_exp_le b r n :
  Frac.num r = Poly.mono n →
  tsize (mk_exp b r) ≤ S (tsize b + tsize (mod_aux r)).
Proof.
move=> en; case: (decide (r = Frac.one)) => [->|n1].
  by rewrite /mk_exp bool_decide_eq_true_2 //; lia.
rewrite (tsize_mk_exp _ _ _ n1 en); lia.
Qed.

Lemma factors_mono_num pt M :
  Frac.num (frac_of pt) = Poly.mono M →
  factors pt =
  SMS.make M (PolyGcd.content (Frac.den (frac_of pt)) ⊎
              units (Frac.den (frac_of pt))).
Proof.
move=> e; rewrite /factors e PolyGcd.content_mono units_mono.
by rewrite (right_id ∅ (⊎)).
Qed.

Lemma tsize_in_lists F x : in_lists F x → tsize x < tsize (PTMod F).
Proof.
case=> m [hm xm]; rewrite tsize_mod.
have hx : tsize x ≤ wsize m := sum_list_with_in x tsize m xm.
case: hm => [h|[h|[h|h]]].
- by have := psize_ge_l F.1 m h; lia.
- by have := psize_ge_r F.1 m h; lia.
- by have := psize_ge_l F.2 m h; lia.
- by have := psize_ge_r F.2 m h; lia.
Qed.

Lemma tsize_atoms_lt pt x : is_mod pt → x ∈ atoms pt → tsize x < tsize pt.
Proof.
case: pt => // F _ h; apply: tsize_in_lists.
exact: frac_vars_in_lists h.
Qed.

Lemma factors_atoms pt x : x ∈ factors pt → negb (is_mod x) → x ∈ atoms pt.
Proof.
rewrite /factors => /SMS.elem_of_make [] /MSet.elem_of_disj_union [] h nx.
- have [m [mp xm]] := elem_of_content _ _ h.
  by apply/elem_of_atoms; exists m; split=> //; left.
- by move: (units_mod _ _ h); case: (is_mod x) nx.
- have [m [mp xm]] := elem_of_content _ _ h.
  by apply/elem_of_atoms; exists m; split=> //; right.
- by move: (units_mod _ _ h); case: (is_mod x) nx.
Qed.

Lemma psize_pos_nonunit (U : poly) :
  U ≠ Poly.zero → U ≠ Poly.one → Poly.first_neg U = false →
  0 < psize (poly_lists_of U).
Proof.
move=> nU nU1 fU.
have np := nentries_pos _ nU.
have elE (X : MSet.mset (MSet.mset pre_term)) n :
    elements X = [n] → X = {[+ n +]}.
  by move=> e; apply: MSet.car_inj; rewrite MSet.car_singleton; exact: e.
have elN (X : MSet.mset (MSet.mset pre_term)) : elements X = [] → X = ∅.
  by move=> e; apply: MSet.car_inj; rewrite MSet.car_empty; exact: e.
have w0 (n : MSet.mset pre_term) : wsize (MSet.car n) = 0 → n = ∅.
  case E: (MSet.car n) => [|y l] /=.
    by move=> _; apply: MSet.car_inj; rewrite MSet.car_empty.
  by have := tsize_pos y; lia.
move: np; rewrite /nentries /psize_with /poly_lists_of; cbn [fst snd].
rewrite !length_fmap.
case E1: (elements (SMS.pos (Poly.car U))) => [|a1 [|a1' l1]];
case E2: (elements (SMS.neg (Poly.car U))) => [|a2 [|a2' l2]] /=; try lia.
- move=> _; case: (decide (wsize (MSet.car a2) = 0)) => [w|w]; last lia.
  exfalso; move: fU.
  have -> : U = Poly.opp Poly.one.
    apply: Poly.coeff_inj => z.
    rewrite Poly.coeff_opp Poly.oneE Poly.coeff_mono !Poly.coeffE SMS.countE.
    rewrite (elE _ _ E2) (elN _ E1) (w0 _ w) MSet.count_empty.
    by rewrite MSet.count_singleton; case: bool_decide.
  by rewrite Poly.oneE Poly.first_neg_opp_mono.
- move=> _; case: (decide (wsize (MSet.car a1) = 0)) => [w|w]; last lia.
  exfalso; apply: nU1; apply: Poly.car_inj.
  rewrite -(SMS.make_pos_neg (Poly.car U)) (elE _ _ E1) (elN _ E2) (w0 _ w).
  by rewrite Poly.oneE Poly.car_mono -SMS.singleton_make.
Qed.

End PreTerm.

Export PreTerm.Exports.
