(** Sizes of pre-terms

    [tsize] is the measure of the well-founded inductions on terms: every
    subterm, factor, group factor and stripped exponent of a pre-term is
    smaller than it. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list_numbers.
From cryptis.lib Require Import list_sort fmap mset sms poly poly_gcd frac.
From cryptis.core.pre_term Require Import base with_stdpp normalize gfactors.

Module PreTerm.
Import base.PreTerm normalize.PreTerm gfactors.PreTerm.

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

Definition mono_size_with (m : list pre_term) := sum_list_with size m.

Definition poly_size_with (A : poly_lists) :=
  sum_list_with mono_size_with A.1 + sum_list_with mono_size_with A.2 +
  (length A.1 + length A.2 - 1).

Definition expo_size_with (m : list pre_term) (d : poly_lists) :=
  match m, d with
  | [x], ([[]], []) => size x
  | _, _ => S (mono_size_with m + poly_size_with d)
  end.

Definition factor_size_with (b : pre_term) (m : list pre_term) (d : poly_lists)
  :=
  match m, d with
  | [], ([[]], []) => size b
  | _, _ => S (size b + expo_size_with m d)
  end.

Definition dh_size_with (l : list entry) :=
  sum_list_with (λ e,
    sum_list_with (λ m, factor_size_with e.1 m e.2.2) e.2.1.1 +
    sum_list_with (λ m, factor_size_with e.1 m e.2.2) e.2.1.2) l.

End Sizes.

Fixpoint tsize (pt : pre_term) : nat :=
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (tsize pt)
  | PT2 _ t1 t2 => S (tsize t1 + tsize t2)
  | PTMod F => S (poly_size_with tsize F.1 + poly_size_with tsize F.2)
  | PTDH [(b, (([m], []), d))] => S (tsize b + expo_size_with tsize m d)
  | PTDH l => S (dh_size_with tsize l)
  end.

Abbreviation mono_size := (mono_size_with tsize).
Abbreviation poly_size := (poly_size_with tsize).
Abbreviation expo_size := (expo_size_with tsize).
Abbreviation factor_size := (factor_size_with tsize).
Abbreviation dh_size := (dh_size_with tsize).

Lemma tsize_mod F : tsize (PTMod F) = S (poly_size F.1 + poly_size F.2).
Proof. by []. Qed.

Lemma tsize_dh_exp b m d :
  tsize (PTDH [(b, (([m], []), d))]) = S (tsize b + expo_size m d).
Proof. by []. Qed.

Lemma tsize_dh l : negb (is_exp (PTDH l)) → tsize (PTDH l) = S (dh_size l).
Proof. by case: l => [|[b [[[|m [|??]] [|??]] d]] [|??]]. Qed.

Lemma expo_sizeE m d : expo_size m d = tsize (mod_of_lists (([m], []), d)).
Proof.
have -> : expo_size m d = if lone_atom (([m], []), d) is Some x then tsize x
                      else S (mono_size m + poly_size d).
  by case: m => [|x [|y m]] //; case: d => [[|[|??] [|??]] [|??]].
have dflt : tsize (PTMod (([m], []), d)) = S (mono_size m + poly_size d).
  by rewrite tsize_mod /poly_size_with /=; lia.
by rewrite /mod_of_lists; case: lone_atom.
Qed.

Lemma expo_size_cases m d :
  expo_size m d = S (mono_size m + poly_size d) ∨
  ∃ x, m = [x] ∧ d = ([[]], []) ∧ expo_size m d = tsize x.
Proof.
rewrite /expo_size_with; case: m => [|x [|??]]; try by left.
case: d => [[|[|??] [|??]] [|??]]; try by left.
by right; exists x.
Qed.

Lemma factor_size_cases b m d :
  factor_size b m d = S (tsize b + expo_size m d) ∨
  m = [] ∧ d = ([[]], []) ∧ factor_size b m d = tsize b.
Proof.
rewrite /factor_size_with; case: m => [|??]; last by left.
case: d => [[|[|??] [|??]] [|??]]; try by left.
by right.
Qed.

Lemma poly_size_mono_lists m : poly_size ([m], []) = mono_size m.
Proof. rewrite /poly_size_with /=; lia. Qed.

Lemma poly_size_one : poly_size (poly_lists_of Poly.one) = 0.
Proof.
by rewrite Poly.oneE poly_lists_mono poly_size_mono_lists
  MSet.car_empty.
Qed.

Lemma poly_size_monoE X :
  poly_size (poly_lists_of (Poly.mono X)) =
  mono_size (MSet.car X).
Proof. by rewrite poly_lists_mono poly_size_mono_lists. Qed.

Lemma tsize_mod_of_lists F : tsize (mod_of_lists F) ≤ tsize (PTMod F).
Proof.
rewrite /mod_of_lists; case E: (lone_atom F) => [x|] //.
rewrite (proj1 (lone_atom_Some _ _) E) tsize_mod /poly_size_with /=
  /mono_size_with /=.
lia.
Qed.

Lemma tsize_exp pt :
  is_exp pt → tsize pt = S (tsize (base pt) + tsize (expo pt)).
Proof. by case: is_expP => // b m d -> _; rewrite tsize_dh_exp expo_sizeE. Qed.

Lemma tsize_mk_exp b r n :
  r ≠ Frac.one → Frac.num r = Poly.mono n →
  tsize (mk_exp b r) = S (tsize b + tsize (mod_of_frac r)).
Proof.
move=> n1 nr; rewrite /mk_exp bool_decide_eq_false_2 //.
by rewrite /mod_of_frac /frac_lists_of nr poly_lists_mono tsize_dh_exp
  expo_sizeE.
Qed.

(** *** Factor sizes *)

Lemma mono_size_disj_union (m n : MSet.mset pre_term) :
  mono_size (MSet.car (m ⊎ n)) =
    mono_size (MSet.car m) + mono_size (MSet.car n).
Proof.
rewrite /mono_size_with -sum_list_with_app; apply: sum_list_with_Permutation.
exact: MSet.elements_disj_union.
Qed.

Lemma mono_size_subseteq (m n : MSet.mset pre_term) :
  m ⊆ n → mono_size (MSet.car m) ≤ mono_size (MSet.car n).
Proof.
move=> /MSet.subseteq_count mn.
have -> : n = m ⊎ (n ∖ m).
  apply: MSet.count_inj => x.
  by rewrite MSet.count_disj_union MSet.count_difference; have := mn x; lia.
rewrite mono_size_disj_union; lia.
Qed.

Lemma sum_map_mono h (X : MSet.mset (MSet.mset pre_term)) :
  sum_list_with mono_size (MSet.car <$> elements X) ≤
  sum_list_with mono_size (MSet.car <$> elements (MSet.map (λ m, h ⊎ m) X)) ∧
  length (MSet.car <$> elements X) =
  length (MSet.car <$> elements (MSet.map (λ m, h ⊎ m) X)).
Proof.
have P : MSet.car <$> elements (MSet.map (λ m, h ⊎ m) X) ≡ₚ
         MSet.car <$> ((λ m, h ⊎ m) <$> elements X).
  by apply: fmap_Permutation; exact: MSet.elements_map_perm.
rewrite (sum_list_with_Permutation _ _ _ P) (Permutation_length P) !length_fmap.
have E (a : list pre_term) l :
  sum_list_with mono_size (a :: l) =
    mono_size a + sum_list_with mono_size l by [].
split=> //; elim: (elements X) => [|m ms IH] //.
rewrite !fmap_cons !E mono_size_disj_union; lia.
Qed.

Lemma poly_size_mul_mono h (q : poly) :
  poly_size (poly_lists_of q) ≤ poly_size (poly_lists_of (Poly.mono h * q)%P).
Proof.
have finj : ∀ a b, h ⊎ a = h ⊎ b → a = b.
  move=> a b e; apply: MSet.count_inj => x.
  by have := f_equal (MSet.count x) e; rewrite !MSet.count_disj_union; lia.
have [ep en] := SMS.pos_map_inj (λ m, h ⊎ m) (Poly.car q) finj.
have E : Poly.car (Poly.mono h * q)%P = SMS.map (λ m, h ⊎ m) (Poly.car q).
  exact: Poly.car_mul_mono.
rewrite /poly_size_with /poly_lists_of E ep en; cbn [fst snd].
have [s1 l1] := sum_map_mono h (SMS.pos (Poly.car q)).
have [s2 l2] := sum_map_mono h (SMS.neg (Poly.car q)).
lia.
Qed.

Lemma sum_map_monoE h (X : MSet.mset (MSet.mset pre_term)) :
  sum_list_with mono_size (MSet.car <$> elements (MSet.map (λ m, h ⊎ m) X)) =
  sum_list_with mono_size (MSet.car <$> elements X) +
  length (elements X) * mono_size (MSet.car h).
Proof.
have P : MSet.car <$> elements (MSet.map (λ m, h ⊎ m) X) ≡ₚ
         MSet.car <$> ((λ m, h ⊎ m) <$> elements X).
  by apply: fmap_Permutation; exact: MSet.elements_map_perm.
rewrite (sum_list_with_Permutation _ _ _ P).
have E (a : list pre_term) l :
  sum_list_with mono_size (a :: l) =
    mono_size a + sum_list_with mono_size l by [].
elim: (elements X) => [|m ms IH] //.
rewrite !fmap_cons !E mono_size_disj_union IH /=; lia.
Qed.

Definition poly_length (q : poly) : nat :=
  length (elements (SMS.pos (Poly.car q))) +
  length (elements (SMS.neg (Poly.car q))).

Lemma poly_size_mul_monoE h (q : poly) :
  poly_size (poly_lists_of (Poly.mono h * q)%P) =
  poly_size (poly_lists_of q) + poly_length q * mono_size (MSet.car h).
Proof.
have finj : ∀ a b, h ⊎ a = h ⊎ b → a = b.
  move=> a b e; apply: MSet.count_inj => x.
  by have := f_equal (MSet.count x) e; rewrite !MSet.count_disj_union; lia.
have [ep en] := SMS.pos_map_inj (λ m, h ⊎ m) (Poly.car q) finj.
have E : Poly.car (Poly.mono h * q)%P = SMS.map (λ m, h ⊎ m) (Poly.car q).
  exact: Poly.car_mul_mono.
rewrite /poly_size_with /poly_lists_of /poly_length E ep en; cbn [fst snd].
rewrite !sum_map_monoE.
have [_ l1] := sum_map_mono h (SMS.pos (Poly.car q)).
have [_ l2] := sum_map_mono h (SMS.neg (Poly.car q)).
rewrite -l1 -l2 !length_fmap; lia.
Qed.

Lemma poly_length_pos q : q ≠ Poly.zero → 0 < poly_length q.
Proof.
move=> nq; rewrite /poly_length.
case E1: (elements (SMS.pos (Poly.car q))) => [|x l]; last by rewrite /=; lia.
case E2: (elements (SMS.neg (Poly.car q))) => [|y l]; last by rewrite /=; lia.
exfalso; apply: nq; apply: Poly.car_inj; rewrite Poly.car_zero.
apply: SMS.elements_empty_inv.
by rewrite SMS.elements_pos_neg E1 E2.
Qed.

Lemma poly_size_opp (q : poly) :
  poly_size (poly_lists_of (- q)%P) = poly_size (poly_lists_of q).
Proof.
rewrite /poly_size_with /poly_lists_of.
rewrite Poly.car_opp.
rewrite SMS.pos_inv SMS.neg_inv; cbn [fst snd]; lia.
Qed.

(** The factor [b ^ (n / q)] of a logarithm is at most as large as [n / q]
    before reduction. *)
Lemma tsize_exp_factor b (q : poly) n x :
  q ≠ Poly.zero → x ∈ exp_factor b q n →
  tsize x ≤ factor_size b (MSet.car n) (poly_lists_of q).
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
have qq : poly_size (poly_lists_of (Frac.den r')) ≤ poly_size (poly_lists_of q).
  have : PolyGcd.dvd G (Poly.mono n) by exists (Frac.num r).
  move=> /PolyGcd.dvd_mono [h [_ [EGh|EGh]]]; rewrite den_r' Eq EGh.
    exact: poly_size_mul_mono.
  by rewrite Poly.mul_opp_l poly_size_opp; exact: poly_size_mul_mono.
have neg_mono m : Poly.mono n' ≠ (- Poly.mono m)%P.
  move=> /(f_equal (Poly.coeff n')).
  rewrite Poly.coeff_opp !Poly.coeff_mono bool_decide_eq_true_2 //.
  by case: bool_decide.
case: (decide (r' = Frac.one)) => [->|n1].
  rewrite /mk_exp bool_decide_eq_true_2 //.
  by case: (factor_size_cases b (MSet.car n) (poly_lists_of q))
    => [->|[_ [_ ->]]];
    lia.
rewrite (tsize_mk_exp _ _ _ n1 Er').
case: (factor_size_cases b (MSet.car n) (poly_lists_of q)) => [->|[en [eq _]]];
  last first.
  (* [n / q] is [1 / 1]: its factor is [b] itself. *)
  have n0 : n = ∅ by apply: MSet.car_inj; rewrite en MSet.car_empty.
  have rE : r = Frac.one.
    by rewrite /r n0 (poly_lists_one_inv _ eq) -Poly.oneE Frac.of_poly_make
      -Frac.oneE.
  case: Hr' => E1; first by case: n1; rewrite E1 rE.
  by case: (neg_mono ∅); rewrite -Er' E1 rE Frac.num_opp Frac.num_one Poly.oneE.
suff : tsize (mod_of_frac r') ≤ expo_size (MSet.car n) (poly_lists_of q) by lia.
case: (expo_size_cases (MSet.car n) (poly_lists_of q)) => [->|[y [en [eq ->]]]].
  apply: Nat.le_trans (tsize_mod_of_lists _) _.
  rewrite /frac_lists_of Er' poly_lists_mono tsize_mod; cbn [fst snd].
  rewrite poly_size_mono_lists; have := mono_size_subseteq _ _ nn; lia.
(* [n / q] is a lone atom [y]: already reduced. *)
have ny : n = {[+ y +]}.
  by apply: MSet.car_inj; rewrite en MSet.car_singleton.
have rE : r = Frac.of_poly (Poly.var y).
  by rewrite /r ny (poly_lists_one_inv _ eq) Frac.of_poly_make Poly.varE.
case: Hr' => E1; first by rewrite E1 rE /mod_of_frac frac_lists_of_var.
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
suff : factor_size b (MSet.car n) (poly_lists_of (Frac.den r)) ≤ dh_size l
  by lia.
have bl : (b, frac_lists_of r) ∈ l.
  rewrite -(entries_of_entries l wl); apply/list_elem_of_fmap.
  by exists (b, r).
have := sum_list_with_in _ (λ e : entry,
  sum_list_with (λ m, factor_size e.1 m e.2.2) e.2.1.1 +
  sum_list_with (λ m, factor_size e.1 m e.2.2) e.2.1.2) _ bl.
cbn [fst snd frac_lists_of]; rewrite /dh_size_with.
set g := λ m, factor_size b m (poly_lists_of (Frac.den r)).
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

Lemma poly_size_ge_l (A : poly_lists) m : m ∈ A.1 → mono_size m ≤ poly_size A.
Proof.
by move=> h; rewrite /poly_size_with;
  have := sum_list_with_in _ mono_size _ h; lia.
Qed.

Lemma poly_size_ge_r (A : poly_lists) m : m ∈ A.2 → mono_size m ≤ poly_size A.
Proof.
by move=> h; rewrite /poly_size_with;
  have := sum_list_with_in _ mono_size _ h; lia.
Qed.

Lemma poly_size_ge (q : poly) n :
  n ∈ Poly.car q → mono_size (MSet.car n) ≤ poly_size (poly_lists_of q).
Proof.
move=> /SMS.elem_of_pos_neg [] h.
- by apply: poly_size_ge_l; exact: list_elem_of_fmap_2 h.
- by apply: poly_size_ge_r; exact: list_elem_of_fmap_2 h.
Qed.

Lemma tsize_mod_of_frac_le r :
  tsize (mod_of_frac r) ≤
  S
    (poly_size (poly_lists_of (Frac.num r)) + poly_size
      (poly_lists_of (Frac.den r))).
Proof. exact: (tsize_mod_of_lists (frac_lists_of r)). Qed.

Lemma tsize_mk_exp_le b r n :
  Frac.num r = Poly.mono n →
  tsize (mk_exp b r) ≤ S (tsize b + tsize (mod_of_frac r)).
Proof.
move=> en; case: (decide (r = Frac.one)) => [->|n1].
  by rewrite /mk_exp bool_decide_eq_true_2 //; lia.
rewrite (tsize_mk_exp _ _ _ n1 en); lia.
Qed.

Lemma tsize_in_lists F x : in_lists F x → tsize x < tsize (PTMod F).
Proof.
case=> m [hm xm]; rewrite tsize_mod.
have hx : tsize x ≤ mono_size m := sum_list_with_in x tsize m xm.
case: hm => [h|[h|[h|h]]].
- by have := poly_size_ge_l F.1 m h; lia.
- by have := poly_size_ge_r F.1 m h; lia.
- by have := poly_size_ge_l F.2 m h; lia.
- by have := poly_size_ge_r F.2 m h; lia.
Qed.

Lemma tsize_atoms_lt pt x : is_mod pt → x ∈ atoms pt → tsize x < tsize pt.
Proof.
case: pt => // F _ h; apply: tsize_in_lists.
exact: vars_in_lists h.
Qed.

Lemma poly_size_pos_nonunit (U : poly) :
  U ≠ Poly.zero → U ≠ Poly.one → Poly.first_neg U = false →
  0 < poly_size (poly_lists_of U).
Proof.
move=> nU nU1 fU.
have np := poly_length_pos _ nU.
have elE (X : MSet.mset (MSet.mset pre_term)) n :
    elements X = [n] → X = {[+ n +]}.
  by move=> e; apply: MSet.car_inj; rewrite MSet.car_singleton; exact: e.
have elN (X : MSet.mset (MSet.mset pre_term)) : elements X = [] → X = ∅.
  by move=> e; apply: MSet.car_inj; rewrite MSet.car_empty; exact: e.
have w0 (n : MSet.mset pre_term) : mono_size (MSet.car n) = 0 → n = ∅.
  case E: (MSet.car n) => [|y l] /=.
    by move=> _; apply: MSet.car_inj; rewrite MSet.car_empty.
  by have := tsize_pos y; lia.
move: np; rewrite /poly_length /poly_size_with /poly_lists_of; cbn [fst snd].
rewrite !length_fmap.
case E1: (elements (SMS.pos (Poly.car U))) => [|a1 [|a1' l1]];
case E2: (elements (SMS.neg (Poly.car U))) => [|a2 [|a2' l2]] /=; try lia.
- move=> _; case: (decide (mono_size (MSet.car a2) = 0)) => [w|w]; last lia.
  exfalso; move: fU.
  have -> : U = Poly.opp Poly.one.
    apply: Poly.coeff_inj => z.
    rewrite Poly.coeff_opp Poly.oneE Poly.coeff_mono !Poly.coeffE SMS.countE.
    rewrite (elE _ _ E2) (elN _ E1) (w0 _ w) MSet.count_empty.
    by rewrite MSet.count_singleton; case: bool_decide.
  by rewrite Poly.oneE Poly.first_neg_opp_mono.
- move=> _; case: (decide (mono_size (MSet.car a1) = 0)) => [w|w]; last lia.
  exfalso; apply: nU1; apply: Poly.car_inj.
  rewrite -(SMS.make_pos_neg (Poly.car U)) (elE _ _ E1) (elN _ E2) (w0 _ w).
  by rewrite Poly.oneE Poly.car_mono -SMS.singleton_make.
Qed.

End PreTerm.
