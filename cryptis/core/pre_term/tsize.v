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
Local Abbreviation frac := (Frac.frac pre_term).

Definition poly_lists := (list (list pre_term) * list (list pre_term))%type.

Definition poly_lists_of (p : poly) : poly_lists :=
  (MSet.car <$> elements (SMS.pos (Poly.car p)),
   MSet.car <$> elements (SMS.neg (Poly.car p))).

Definition lone_expo (m : list pre_term) (d : poly_lists) : option pre_term :=
  match m, d with
  | [x], ([[]], []) => Some x
  | _, _ => None
  end.

Definition unit_expo (m : list pre_term) (d : poly_lists) : bool :=
  match m, d with
  | [], ([[]], []) => true
  | _, _ => false
  end.

(* A polynomial is as large as its monomials plus one per [+] between them, so
   that a Laurent monomial keeps its size and a unit part [p] with at least two
   monomials outweighs the monomials it multiplies.  A Diffie-Hellman pre-term
   is at least as large as the product of its factors [b ^ (n / q)]
   ([gfactors]); the factors are measured before [n / q] is reduced.  Field and
   group products are measured through their readings rather than their trees,
   because the tree of [2 * x] is no larger than that of [2]; the leaves of a
   reading are lower than the pre-term, so [tsize] recurses on [height]. *)
Section Sizes.

Variable size : pre_term → nat.

Definition mono_size_with (m : list pre_term) := sum_list_with size m.

Definition poly_size_with (A : poly_lists) :=
  sum_list_with mono_size_with A.1 + sum_list_with mono_size_with A.2 +
  (length A.1 + length A.2 - 1).

Definition expo_size_with (m : list pre_term) (d : poly_lists) :=
  if lone_expo m d is Some x then size x
  else S (mono_size_with m + poly_size_with d).

Definition factor_size_with (b : pre_term) (m : list pre_term) (d : poly_lists)
  :=
  if unit_expo m d then size b else S (size b + expo_size_with m d).

Definition entry_size_with (b : pre_term) (r : frac) :=
  sum_list_with (λ m, factor_size_with b m (poly_lists_of (Frac.den r)))
    (poly_lists_of (Frac.num r)).1 +
  sum_list_with (λ m, factor_size_with b m (poly_lists_of (Frac.den r)))
    (poly_lists_of (Frac.num r)).2.

Definition dh_size_with (m : dhmap) :=
  sum_list_with (λ e, entry_size_with e.1 e.2) (FMap.to_list m).

Definition tsize_body (pt : pre_term) : nat :=
  if is_mod pt then
    S (poly_size_with (poly_lists_of (Frac.num (frac_of pt))) +
       poly_size_with (poly_lists_of (Frac.den (frac_of pt))))
  else if is_exp pt then S (size (base pt) + size (expo pt))
  else if is_dh pt then S (dh_size_with (dh_map pt))
  else
    match pt with
    | PT0 _ => 1
    | PT1 _ t => S (size t)
    | PT2 _ t1 t2 => S (size t1 + size t2)
    end.

End Sizes.

Fixpoint tsize_rec (n : nat) (pt : pre_term) : nat :=
  if n is S n then tsize_body (tsize_rec n) pt else 0.

Definition tsize (pt : pre_term) : nat := tsize_rec (height pt) pt.

Abbreviation mono_size := (mono_size_with tsize).
Abbreviation poly_size := (poly_size_with tsize).
Abbreviation expo_size := (expo_size_with tsize).
Abbreviation factor_size := (factor_size_with tsize).
Abbreviation dh_size := (dh_size_with tsize).

(** ** Unfolding *)

Lemma height_gt0 pt : 0 < height pt.
Proof. by case: pt => [?|? ?|? ? ?] /=; lia. Qed.

Lemma fall_lower P t : (∀ x, height x ≤ height t → P x) → fall P t.
Proof.
elim: t => [o|o t IH|o t1 IH1 t2 IH2] h.
- by case: o h => [n|a| | |] h //=; apply: h.
- case: o h => [kt| | | |] h /=; try by apply: h.
  + by apply: IH => x hx; apply: h => /=; lia.
  + by apply: IH => x hx; apply: h => /=; lia.
- case: o h => [| | | | |] h /=; try by apply: h.
  + by split; [apply: IH1|apply: IH2] => x hx; apply: h => /=; lia.
  + by split; [apply: IH1|apply: IH2] => x hx; apply: h => /=; lia.
Qed.

Lemma gall_lower Pb Pe t :
  (∀ x, height x ≤ height t → Pb x) → (∀ x, height x ≤ height t → Pe x) →
  gall Pb Pe t.
Proof.
elim: t => [o|o t IH|o t1 IH1 t2 IH2] hb he.
- by case: o hb he => [n|a| | |] hb he //=; apply: hb.
- case: o hb he => [kt| | | |] hb he /=; try by apply: hb.
  by apply: IH => x hx; [apply: hb|apply: he] => /=; lia.
- case: o hb he => [| | | | |] hb he /=; try by apply: hb.
  + by split; [apply: IH1|apply: IH2] => x hx; [apply: hb|apply: he|
      apply: hb|apply: he] => /=; lia.
  + split; first by apply: IH1 => x hx; [apply: hb|apply: he] => /=; lia.
    by apply: fall_lower => x hx; apply: he => /=; lia.
Qed.

Lemma fall_height t : is_mod t → fall (λ x, height x < height t) t.
Proof.
case: t => [o|o t|o t1 t2]; case: o => //= *; try split;
  apply: fall_lower => x /=; lia.
Qed.

Lemma gall_height t :
  is_dh t → gall (λ x, height x < height t) (λ x, height x < height t) t.
Proof.
case: t => [o|o t|o t1 t2]; case: o => //= *.
- by apply: gall_lower => x /=; lia.
- by split; apply: gall_lower => x /=; lia.
- split; first by apply: gall_lower => x /=; lia.
  by apply: fall_lower => x /=; lia.
Qed.

Lemma sum_list_with_ext {A} (f g : A → nat) l :
  (∀ x, x ∈ l → f x = g x) → sum_list_with f l = sum_list_with g l.
Proof.
elim: l => [|x l IH] //= h.
rewrite h; last by constructor.
by rewrite IH // => y yl; apply: h; constructor.
Qed.

Lemma elem_of_poly_lists (q : poly) l :
  l ∈ (poly_lists_of q).1 ∨ l ∈ (poly_lists_of q).2 →
  ∃ n, n ∈ Poly.car q ∧ l = MSet.car n.
Proof.
case=> /list_elem_of_fmap [n [-> /MSet.elem_of_elements nq]]; exists n;
  split=> //; apply/SMS.elem_of_pos_neg; by [left|right].
Qed.

Lemma poly_size_with_ext f g (q : poly) :
  (∀ n x, n ∈ Poly.car q → x ∈ n → f x = g x) →
  poly_size_with f (poly_lists_of q) = poly_size_with g (poly_lists_of q).
Proof.
move=> h; rewrite /poly_size_with /mono_size_with.
have E : ∀ l, l ∈ (poly_lists_of q).1 ∨ l ∈ (poly_lists_of q).2 →
    sum_list_with f l = sum_list_with g l.
  move=> l /elem_of_poly_lists [n [nq ->]].
  by apply: sum_list_with_ext => x xn; apply: (h n).
rewrite (sum_list_with_ext _ (sum_list_with g) (poly_lists_of q).1);
  last by move=> l lq; apply: E; left.
rewrite (sum_list_with_ext _ (sum_list_with g) (poly_lists_of q).2) //.
by move=> l lq; apply: E; right.
Qed.

Lemma lone_expoP m d x : lone_expo m d = Some x ↔ m = [x] ∧ d = ([[]], []).
Proof.
split; last by case=> -> ->.
by case: m => [|y [|? ?]] //; case: d => [[|[|? ?] [|? ?]] [|? ?]] //= [->].
Qed.

Lemma unit_expoP m d : unit_expo m d ↔ m = [] ∧ d = ([[]], []).
Proof.
split; last by case=> -> ->.
by case: m => [|? ?] //; case: d => [[|[|? ?] [|? ?]] [|? ?]].
Qed.

Lemma expo_size_with_ext f g m d :
  (∀ x, x ∈ m → f x = g x) → poly_size_with f d = poly_size_with g d →
  expo_size_with f m d = expo_size_with g m d.
Proof.
move=> hm hd; rewrite /expo_size_with /mono_size_with.
case E: (lone_expo m d) => [x|].
  by apply: hm; have [-> _] := proj1 (lone_expoP _ _ _) E; constructor.
by rewrite (sum_list_with_ext f g m hm) hd.
Qed.

Lemma factor_size_with_ext f g b m d :
  f b = g b → (∀ x, x ∈ m → f x = g x) →
  poly_size_with f d = poly_size_with g d →
  factor_size_with f b m d = factor_size_with g b m d.
Proof.
move=> hb hm hd.
by rewrite /factor_size_with hb (expo_size_with_ext f g m d hm hd).
Qed.

Lemma dh_size_with_ext f g m :
  (∀ k, m !!! k ≠ Frac.zero → f k = g k) →
  (∀ k, Frac.all_vars (λ x, f x = g x) (m !!! k)) →
  dh_size_with f m = dh_size_with g m.
Proof.
move=> hk hv; rewrite /dh_size_with.
apply: sum_list_with_ext => -[k v] /FMap.elem_of_to_list [mk nv].
have fk : f k = g k by apply: hk; rewrite mk.
have A := hv k; rewrite mk in A.
have hd : poly_size_with f (poly_lists_of (Frac.den v)) =
          poly_size_with g (poly_lists_of (Frac.den v)).
  by apply: poly_size_with_ext => n x nd xn; apply: (A n x) => //; right.
have F : ∀ l, l ∈ (poly_lists_of (Frac.num v)).1 ∨
              l ∈ (poly_lists_of (Frac.num v)).2 →
    factor_size_with f k l (poly_lists_of (Frac.den v)) =
    factor_size_with g k l (poly_lists_of (Frac.den v)).
  move=> l /elem_of_poly_lists [n [nv' ->]].
  by apply: factor_size_with_ext => // x xn; apply: (A n x) => //; left.
rewrite /entry_size_with [(k, v).1]/= [(k, v).2]/=.
by congr (_ + _); apply: sum_list_with_ext => l lv; apply: F; [left|right].
Qed.

Lemma tsize_body_ext f g pt :
  (∀ x, height x < height pt → f x = g x) → tsize_body f pt = tsize_body g pt.
Proof.
move=> h; rewrite /tsize_body.
case M: (is_mod pt).
  have /fall_vars A := fall_height pt ltac:(by rewrite M).
  have A' : ∀ n x, n ∈ Poly.car (Frac.num (frac_of pt)) ∨
                   n ∈ Poly.car (Frac.den (frac_of pt)) → x ∈ n → f x = g x.
    by move=> n x nr xn; apply: h; apply: (A n x nr xn).
  rewrite (poly_size_with_ext f g (Frac.num _));
    last by move=> n x nr; apply: A'; left.
  rewrite (poly_size_with_ext f g (Frac.den _)) //.
  by move=> n x nr; apply: A'; right.
case X: (is_exp pt).
  rewrite /base /expo X.
  case: pt h M X => [o|o t|o t1 t2] h //= _ _.
  have h1 : f t1 = g t1 by apply: h => /=; lia.
  have h2 : f t2 = g t2 by apply: h => /=; lia.
  by rewrite h1 h2.
case D: (is_dh pt).
  have [K V] := gall_ok _ _ _ (gall_height pt ltac:(by rewrite D)).
  rewrite (dh_size_with_ext f g) //.
  - by move=> k /K; apply: h.
  - by move=> k; apply: Frac.all_vars_impl (V k) => x; apply: h.
case: pt h {M X D} => [o|o t|o t1 t2] h //=.
- by rewrite h //=; lia.
- have h1 : f t1 = g t1 by apply: h => /=; lia.
  have h2 : f t2 = g t2 by apply: h => /=; lia.
  by rewrite h1 h2.
Qed.

Lemma tsize_rec_irrel n1 n2 pt :
  height pt ≤ n1 → height pt ≤ n2 → tsize_rec n1 pt = tsize_rec n2 pt.
Proof.
elim: n1 n2 pt => [|n1 IH] [|n2] pt h1 h2; try by have := height_gt0 pt; lia.
apply: tsize_body_ext => x hx; apply: IH; lia.
Qed.

Lemma tsize_unfold pt : tsize pt = tsize_body tsize pt.
Proof.
rewrite {1}/tsize; case E: (height pt) => [|n].
  by have := height_gt0 pt; lia.
apply: tsize_body_ext => x hx; apply: tsize_rec_irrel; lia.
Qed.

Lemma tsize_free pt : is_non_free pt = false →
  tsize pt =
    match pt with
    | PT0 _ => 1
    | PT1 _ t => S (tsize t)
    | PT2 _ t1 t2 => S (tsize t1 + tsize t2)
    end.
Proof. by rewrite is_non_freeE tsize_unfold; case: pt => [[]|[] ?|[] ? ?]. Qed.

Lemma tsize_mod pt : is_mod pt →
  tsize pt = S (poly_size (poly_lists_of (Frac.num (frac_of pt))) +
                poly_size (poly_lists_of (Frac.den (frac_of pt)))).
Proof. by rewrite tsize_unfold /tsize_body; case: (is_mod pt). Qed.

Lemma tsize_exp pt :
  is_exp pt → tsize pt = S (tsize (base pt) + tsize (expo pt)).
Proof.
move=> xe; have /Is_true_negb M := is_exp_Nmod _ xe.
rewrite tsize_unfold /tsize_body M.
by case: (is_exp pt) xe.
Qed.

Lemma tsize_gmul pt :
  is_dh pt → negb (is_exp pt) → tsize pt = S (dh_size (dh_map pt)).
Proof.
move=> /Is_true_true_1 D /Is_true_negb X.
by rewrite tsize_unfold /tsize_body (dh_not_mod _ D) X D.
Qed.

Lemma tsize_pos pt : 0 < tsize pt.
Proof.
rewrite tsize_unfold /tsize_body.
case: (is_mod pt) => /=; first lia.
case: (is_exp pt) => /=; first lia.
case: (is_dh pt) => /=; first lia.
by case: pt => * /=; lia.
Qed.

(** ** Polynomial sizes *)

Lemma poly_lists_mono m : poly_lists_of (Poly.mono m) = ([MSet.car m], []).
Proof.
rewrite /poly_lists_of Poly.car_mono SMS.pos_singleton SMS.neg_singleton.
by rewrite MSet.elements_singleton MSet.elements_empty.
Qed.

Lemma poly_lists_one_inv (q : poly) :
  poly_lists_of q = ([[]], []) → q = Poly.one.
Proof.
rewrite /poly_lists_of => -[].
destruct (elements (SMS.pos (Poly.car q))) as [|n [|? ?]] eqn:EP => //= -[en].
destruct (elements (SMS.neg (Poly.car q))) eqn:EN => // _.
apply: Poly.car_inj; rewrite Poly.oneE Poly.car_mono; apply: SMS.sms_eq.
- rewrite SMS.pos_singleton -(MSet.of_list_elements (SMS.pos _)) EP.
  have -> : n = ∅ by apply: MSet.car_inj; rewrite en MSet.car_empty.
  by rewrite MSet.of_list_cons MSet.of_list_nil (right_id ∅ (⊎)).
- by rewrite SMS.neg_singleton (MSet.elements_empty_inv _ EN).
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

Lemma expo_size_cases m d :
  expo_size m d = S (mono_size m + poly_size d) ∨
  ∃ x, m = [x] ∧ d = ([[]], []) ∧ expo_size m d = tsize x.
Proof.
rewrite /expo_size_with; case E: (lone_expo m d) => [x|]; last by left.
by right; exists x; have [-> ->] := proj1 (lone_expoP _ _ _) E.
Qed.

Lemma factor_size_cases b m d :
  factor_size b m d = S (tsize b + expo_size m d) ∨
  m = [] ∧ d = ([[]], []) ∧ factor_size b m d = tsize b.
Proof.
rewrite /factor_size_with; case E: (unit_expo m d); last by left.
by right; have [-> ->] := proj1 (unit_expoP m d) ltac:(by rewrite E).
Qed.

(** ** Sizes of encodings *)

Lemma tsize_mod_of_frac_le r :
  Frac.all_vars (λ x, negb (is_mod x)) r →
  tsize (mod_of_frac r) ≤
  S
    (poly_size (poly_lists_of (Frac.num r)) + poly_size
      (poly_lists_of (Frac.den r))).
Proof.
move=> ar; case M: (is_mod (mod_of_frac r)).
  by rewrite (tsize_mod (mod_of_frac r) ltac:(by rewrite M))
    (frac_of_mod_of_frac _ ar).
have [a [-> ->]] := mod_of_frac_Nmod _ M.
rewrite Frac.num_of_poly Frac.den_of_poly Poly.varE poly_size_monoE.
rewrite poly_size_one MSet.car_singleton /mono_size_with /=; lia.
Qed.

Lemma tsize_mk_exp b r n :
  r ≠ Frac.one → Frac.all_vars (λ x, negb (is_mod x)) r →
  Frac.num r = Poly.mono n →
  tsize (mk_exp b r) = S (tsize b + tsize (mod_of_frac r)).
Proof.
move=> n1 ar nr.
have xe : is_exp (mk_exp b r).
  by rewrite (is_exp_mk_exp _ _ n1 ar) nr is_mono_poly_mono.
by rewrite (tsize_exp _ xe) (base_mk_exp _ _ _ n1 ar nr)
  (expo_mk_exp _ _ _ n1 ar nr).
Qed.

Lemma tsize_mk_exp_le b r n :
  Frac.all_vars (λ x, negb (is_mod x)) r → Frac.num r = Poly.mono n →
  tsize (mk_exp b r) ≤ S (tsize b + tsize (mod_of_frac r)).
Proof.
move=> ar en; case: (decide (r = Frac.one)) => [->|n1].
  by rewrite /mk_exp bool_decide_eq_true_2 //; lia.
rewrite (tsize_mk_exp _ _ _ n1 ar en); lia.
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
  q ≠ Poly.zero →
  Frac.all_vars (λ y, negb (is_mod y)) (Frac.make (Poly.mono n) q) →
  x ∈ exp_factor b q n →
  tsize x ≤ factor_size b (MSet.car n) (poly_lists_of q).
Proof.
move=> nq ar xe.
have [r' [n' [-> [Er' Hr']]]] := elem_of_exp_factor b q n x nq xe.
set r := Frac.make (Poly.mono n) q in Hr' ar.
have ar' : Frac.all_vars (λ y, negb (is_mod y)) r'.
  by case: Hr' => ->; last exact: Frac.all_vars_opp.
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
rewrite (tsize_mk_exp _ _ _ n1 ar' Er').
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
  apply: Nat.le_trans (tsize_mod_of_frac_le _ ar') _.
  rewrite Er' poly_size_monoE; have := mono_size_subseteq _ _ nn; lia.
(* [n / q] is a lone atom [y]: already reduced. *)
have ny : n = {[+ y +]}.
  by apply: MSet.car_inj; rewrite en MSet.car_singleton.
have rE : r = Frac.of_poly (Poly.var y).
  by rewrite /r ny (poly_lists_one_inv _ eq) Frac.of_poly_make Poly.varE.
case: Hr' => E1; first by rewrite E1 rE mod_of_frac_var.
by case: (neg_mono {[+ y +]});
  rewrite -Er' E1 rE Frac.num_opp Frac.num_of_poly Poly.varE.
Qed.

Lemma tsize_gfactors_lt pt x :
  wf pt → is_gmul pt → x ∈ gfactors pt → tsize x < tsize pt.
Proof.
move=> wpt /andb_True [D X]; rewrite (gfactors_dh _ wpt) (tsize_gmul _ D X).
move=> /elem_of_dh_factors [b [r [n [br [nr xe]]]]].
have /FMap.elem_of_to_list [mb r0] := br.
have [_ [_ ar]] := wf_dh_map _ wpt b ltac:(by rewrite mb).
rewrite mb in ar.
have := tsize_exp_factor b (Frac.den r) n x (Frac.den_neq0 r)
  (all_vars_make_mono_Nmod _ _ nr ar) xe.
have : entry_size_with tsize b r ≤ dh_size (dh_map pt).
  exact: (sum_list_with_in (b, r) (λ e, entry_size_with tsize e.1 e.2) _ br).
rewrite /entry_size_with.
set g := λ m, factor_size b m (poly_lists_of (Frac.den r)).
move: nr => /SMS.elem_of_pos_neg [] /MSet.elem_of_elements np.
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

(** ** Sizes of atoms *)

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

Lemma tsize_atoms_lt pt x : is_mod pt → x ∈ atoms pt → tsize x < tsize pt.
Proof.
move=> M; rewrite /atoms /Frac.vars (tsize_mod _ M) elem_of_app.
case=> /Poly.elem_of_vars [m [mr xm]].
- have : tsize x ≤ mono_size (MSet.car m) := sum_list_with_in _ _ _ xm.
  have := poly_size_ge _ _ mr; lia.
- have : tsize x ≤ mono_size (MSet.car m) := sum_list_with_in _ _ _ xm.
  have := poly_size_ge _ _ mr; lia.
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
