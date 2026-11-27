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

(* A polynomial is as large as its monomials plus one per [+] between them, so
   that a Laurent monomial keeps its size and a unit part [p] with at least two
   monomials outweighs the monomials it multiplies.  A Diffie-Hellman pre-term
   is larger than each of its factors [b ^ (n / q)] ([gfactors]), measured
   before [n / q] is reduced.  Field and group products are measured through
   their readings rather than their trees, because the tree of [2 * x] is no
   larger than that of [2]; the leaves of a reading are lower than the
   pre-term, so [tsize] recurses on [height]. *)
Section Sizes.

Variable size : pre_term → nat.

Definition mono_size_with (n : MSet.mset pre_term) :=
  sum_list_with size (elements n).

Definition poly_size_with (p : poly) :=
  sum_list_with mono_size_with (elements (SMS.pos (Poly.car p))) +
  sum_list_with mono_size_with (elements (SMS.neg (Poly.car p))) +
  (length (elements (SMS.pos (Poly.car p))) +
   length (elements (SMS.neg (Poly.car p))) - 1).

Definition factor_size_with b (n : MSet.mset pre_term) (q : poly) :=
  S (size b + S (mono_size_with n + poly_size_with q)).

Definition entry_size_with b (r : frac) :=
  sum_list_with (λ n, factor_size_with b n (Frac.den r))
    (elements (SMS.pos (Poly.car (Frac.num r)))) +
  sum_list_with (λ n, factor_size_with b n (Frac.den r))
    (elements (SMS.neg (Poly.car (Frac.num r)))).

Definition dh_size_with (m : dhmap) :=
  sum_list_with (λ e, entry_size_with e.1 e.2) (FMap.to_list m).

Definition tsize_body (pt : pre_term) : nat :=
  if is_mod pt then
    S (poly_size_with (Frac.num (frac_of pt)) +
       poly_size_with (Frac.den (frac_of pt)))
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

Lemma mono_size_with_ext f g (n : MSet.mset pre_term) :
  (∀ x, x ∈ n → f x = g x) → mono_size_with f n = mono_size_with g n.
Proof.
move=> h; rewrite /mono_size_with.
by apply: sum_list_with_ext => x /MSet.elem_of_elements; apply: h.
Qed.

Lemma poly_size_with_ext f g (q : poly) :
  (∀ n x, n ∈ Poly.car q → x ∈ n → f x = g x) →
  poly_size_with f q = poly_size_with g q.
Proof.
move=> h; rewrite /poly_size_with.
have E : ∀ X : MSet.mset (MSet.mset pre_term),
    (∀ n, n ∈ X → n ∈ Poly.car q) →
    sum_list_with (mono_size_with f) (elements X) =
    sum_list_with (mono_size_with g) (elements X).
  move=> X hX; apply: sum_list_with_ext => n /MSet.elem_of_elements nX.
  by apply: mono_size_with_ext => x; apply: h; apply: hX.
rewrite E; last by move=> n nq; apply/SMS.elem_of_pos_neg; left.
by rewrite E // => n nq; apply/SMS.elem_of_pos_neg; right.
Qed.

Lemma factor_size_with_ext f g b n q :
  f b = g b → (∀ x, x ∈ n → f x = g x) →
  poly_size_with f q = poly_size_with g q →
  factor_size_with f b n q = factor_size_with g b n q.
Proof.
move=> hb hn hq.
by rewrite /factor_size_with hb hq (mono_size_with_ext f g n hn).
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
have hd : poly_size_with f (Frac.den v) = poly_size_with g (Frac.den v).
  by apply: poly_size_with_ext => n x nd xn; apply: (A n x) => //; right.
have F : ∀ X : MSet.mset (MSet.mset pre_term),
    (∀ n, n ∈ X → n ∈ Poly.car (Frac.num v)) →
    sum_list_with (λ n, factor_size_with f k n (Frac.den v)) (elements X) =
    sum_list_with (λ n, factor_size_with g k n (Frac.den v)) (elements X).
  move=> X hX; apply: sum_list_with_ext => n /MSet.elem_of_elements nX.
  apply: factor_size_with_ext => // x xn.
  by apply: (A n x) => //; left; apply: hX.
rewrite /entry_size_with [(k, v).1]/= [(k, v).2]/= F; last first.
  by move=> n nq; apply/SMS.elem_of_pos_neg; left.
by rewrite F // => n nq; apply/SMS.elem_of_pos_neg; right.
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
Proof. by rewrite tsize_unfold; case: pt => [[]|[] ?|[] ? ?]. Qed.

Lemma tsize_mod pt : is_mod pt →
  tsize pt = S (poly_size (Frac.num (frac_of pt)) +
                poly_size (Frac.den (frac_of pt))).
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

Lemma mono_size_singleton x : mono_size {[+ x +]} = tsize x.
Proof. by rewrite /mono_size_with MSet.elements_singleton /=; lia. Qed.

Lemma mono_size_disj_union (m n : MSet.mset pre_term) :
  mono_size (m ⊎ n) = mono_size m + mono_size n.
Proof.
rewrite /mono_size_with -sum_list_with_app; apply: sum_list_with_Permutation.
exact: MSet.elements_disj_union.
Qed.

Lemma mono_size_subseteq (m n : MSet.mset pre_term) :
  m ⊆ n → mono_size m ≤ mono_size n.
Proof.
move=> /MSet.subseteq_count mn.
have -> : n = m ⊎ (n ∖ m).
  apply: MSet.count_inj => x.
  by rewrite MSet.count_disj_union MSet.count_difference; have := mn x; lia.
rewrite mono_size_disj_union; lia.
Qed.

Lemma poly_size_monoE X : poly_size (Poly.mono X) = mono_size X.
Proof.
rewrite /poly_size_with Poly.car_mono SMS.pos_singleton SMS.neg_singleton.
by rewrite MSet.elements_singleton MSet.elements_empty /=; lia.
Qed.

Lemma poly_size_one : poly_size Poly.one = 0.
Proof.
by rewrite Poly.oneE poly_size_monoE /mono_size_with MSet.elements_empty.
Qed.

Lemma poly_size_ge (q : poly) n :
  n ∈ Poly.car q → mono_size n ≤ poly_size q.
Proof.
rewrite /poly_size_with => /SMS.elem_of_pos_neg [] /MSet.elem_of_elements h.
- set P := sum_list_with _ (elements (SMS.pos _)).
  have : mono_size n ≤ P := sum_list_with_in _ _ _ h.
  lia.
- set N := sum_list_with _ (elements (SMS.neg _)).
  have : mono_size n ≤ N := sum_list_with_in _ _ _ h.
  lia.
Qed.

Lemma sum_map_mono h (X : MSet.mset (MSet.mset pre_term)) :
  sum_list_with mono_size (elements X) ≤
  sum_list_with mono_size (elements (MSet.map (λ m, h ⊎ m) X)) ∧
  length (elements X) = length (elements (MSet.map (λ m, h ⊎ m) X)).
Proof.
have P : elements (MSet.map (λ m, h ⊎ m) X) ≡ₚ (λ m, h ⊎ m) <$> elements X.
  exact: MSet.elements_map_perm.
rewrite (sum_list_with_Permutation _ _ _ P) (Permutation_length P) length_fmap.
have E (a : MSet.mset pre_term) l :
  sum_list_with mono_size (a :: l) =
    mono_size a + sum_list_with mono_size l by [].
split=> //; elim: (elements X) => [|m ms IH] //.
rewrite fmap_cons !E mono_size_disj_union; lia.
Qed.

Lemma sum_map_monoE h (X : MSet.mset (MSet.mset pre_term)) :
  sum_list_with mono_size (elements (MSet.map (λ m, h ⊎ m) X)) =
  sum_list_with mono_size (elements X) + length (elements X) * mono_size h.
Proof.
have P : elements (MSet.map (λ m, h ⊎ m) X) ≡ₚ (λ m, h ⊎ m) <$> elements X.
  exact: MSet.elements_map_perm.
rewrite (sum_list_with_Permutation _ _ _ P).
have E (a : MSet.mset pre_term) l :
  sum_list_with mono_size (a :: l) =
    mono_size a + sum_list_with mono_size l by [].
elim: (elements X) => [|m ms IH] //.
rewrite fmap_cons !E mono_size_disj_union IH /=; lia.
Qed.

Lemma poly_size_mul_mono h (q : poly) :
  poly_size q ≤ poly_size (Poly.mono h * q)%P.
Proof.
have finj : ∀ a b, h ⊎ a = h ⊎ b → a = b.
  move=> a b e; apply: MSet.count_inj => x.
  by have := f_equal (MSet.count x) e; rewrite !MSet.count_disj_union; lia.
have [ep en] := SMS.pos_map_inj (λ m, h ⊎ m) (Poly.car q) finj.
rewrite /poly_size_with Poly.car_mul_mono ep en.
have [s1 l1] := sum_map_mono h (SMS.pos (Poly.car q)).
have [s2 l2] := sum_map_mono h (SMS.neg (Poly.car q)).
lia.
Qed.

Definition poly_length (q : poly) : nat :=
  length (elements (SMS.pos (Poly.car q))) +
  length (elements (SMS.neg (Poly.car q))).

Lemma poly_size_mul_monoE h (q : poly) :
  poly_size (Poly.mono h * q)%P = poly_size q + poly_length q * mono_size h.
Proof.
have finj : ∀ a b, h ⊎ a = h ⊎ b → a = b.
  move=> a b e; apply: MSet.count_inj => x.
  by have := f_equal (MSet.count x) e; rewrite !MSet.count_disj_union; lia.
have [ep en] := SMS.pos_map_inj (λ m, h ⊎ m) (Poly.car q) finj.
rewrite /poly_size_with /poly_length Poly.car_mul_mono ep en !sum_map_monoE.
have [_ l1] := sum_map_mono h (SMS.pos (Poly.car q)).
have [_ l2] := sum_map_mono h (SMS.neg (Poly.car q)).
rewrite -l1 -l2; lia.
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

Lemma poly_size_opp (q : poly) : poly_size (- q)%P = poly_size q.
Proof.
by rewrite /poly_size_with Poly.car_opp SMS.pos_inv SMS.neg_inv; lia.
Qed.

Lemma poly_size_pos_nonunit (U : poly) :
  U ≠ Poly.zero → U ≠ Poly.one → Poly.first_neg U = false →
  0 < poly_size U.
Proof.
move=> nU nU1 fU.
have np := poly_length_pos _ nU.
have elE (X : MSet.mset (MSet.mset pre_term)) n :
    elements X = [n] → X = {[+ n +]}.
  by move=> e; apply: MSet.car_inj; rewrite MSet.car_singleton; exact: e.
have elN (X : MSet.mset (MSet.mset pre_term)) : elements X = [] → X = ∅.
  by move=> e; apply: MSet.car_inj; rewrite MSet.car_empty; exact: e.
have w0 (n : MSet.mset pre_term) : mono_size n = 0 → n = ∅.
  rewrite /mono_size_with; case E: (elements n) => [|y l] /=.
    by move=> _; apply: MSet.car_inj; rewrite MSet.car_empty; exact: E.
  by have := tsize_pos y; lia.
move: np; rewrite /poly_length /poly_size_with.
case E1: (elements (SMS.pos (Poly.car U))) => [|a1 [|a1' l1]];
case E2: (elements (SMS.neg (Poly.car U))) => [|a2 [|a2' l2]] /=; try lia.
- move=> _; case: (decide (mono_size a2 = 0)) => [w|w]; last lia.
  exfalso; move: fU.
  have -> : U = Poly.opp Poly.one.
    apply: Poly.coeff_inj => z.
    rewrite Poly.coeff_opp Poly.oneE Poly.coeff_mono !Poly.coeffE SMS.countE.
    rewrite (elE _ _ E2) (elN _ E1) (w0 _ w) MSet.count_empty.
    by rewrite MSet.count_singleton; case: bool_decide.
  by rewrite Poly.oneE Poly.first_neg_opp_mono.
- move=> _; case: (decide (mono_size a1 = 0)) => [w|w]; last lia.
  exfalso; apply: nU1; apply: Poly.car_inj.
  rewrite -(SMS.make_pos_neg (Poly.car U)) (elE _ _ E1) (elN _ E2) (w0 _ w).
  by rewrite Poly.oneE Poly.car_mono -SMS.singleton_make.
Qed.

(** ** Sizes of encodings *)

Lemma tsize_mod_of_frac_le r :
  wf_frac r →
  tsize (mod_of_frac r) ≤ S (poly_size (Frac.num r) + poly_size (Frac.den r)).
Proof.
move=> ar; case M: (is_mod (mod_of_frac r)).
  by rewrite (tsize_mod (mod_of_frac r) ltac:(by rewrite M))
    (frac_of_mod_of_frac _ ar).
have [a [-> ->]] := mod_of_frac_Nmod _ M.
rewrite Frac.num_of_poly Frac.den_of_poly Poly.varE poly_size_monoE.
rewrite poly_size_one mono_size_singleton; lia.
Qed.

Lemma tsize_mk_exp b r n :
  r ≠ Frac.one → wf_frac r → Frac.num r = Poly.mono n →
  tsize (mk_exp b r) = S (tsize b + tsize (mod_of_frac r)).
Proof.
move=> n1 ar nr.
have xe : is_exp (mk_exp b r).
  by rewrite (is_exp_mk_exp _ _ n1 ar) nr is_mono_poly_mono.
by rewrite (tsize_exp _ xe) (base_mk_exp _ _ _ n1 ar nr)
  (expo_mk_exp _ _ _ n1 ar nr).
Qed.

Lemma tsize_mk_exp_le b r n :
  wf_frac r → Frac.num r = Poly.mono n →
  tsize (mk_exp b r) ≤ S (tsize b + tsize (mod_of_frac r)).
Proof.
move=> ar en; case: (decide (r = Frac.one)) => [->|n1].
  by rewrite /mk_exp bool_decide_eq_true_2 //; lia.
rewrite (tsize_mk_exp _ _ _ n1 ar en); lia.
Qed.

(** ** Sizes of factors *)

(** The factor [b ^ (n / q)] of a logarithm is at most as large as [n / q]
    before reduction. *)
Lemma tsize_exp_factor b (q : poly) n x :
  q ≠ Poly.zero → wf_frac (Frac.make (Poly.mono n) q) →
  x ∈ exp_factor b q n → tsize x ≤ factor_size b n q.
Proof.
move=> nq ar xe.
have [r' [n' [-> [Er' Hr']]]] := elem_of_exp_factor b q n x nq xe.
set r := Frac.make (Poly.mono n) q in Hr' ar.
have ar' : wf_frac r' by case: Hr' => ->; last exact: Frac.all_vars_opp.
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
have qq : poly_size (Frac.den r') ≤ poly_size q.
  have : PolyGcd.dvd G (Poly.mono n) by exists (Frac.num r).
  move=> /PolyGcd.dvd_mono [h [_ [EGh|EGh]]]; rewrite den_r' Eq EGh.
    exact: poly_size_mul_mono.
  by rewrite Poly.mul_opp_l poly_size_opp; exact: poly_size_mul_mono.
have := tsize_mk_exp_le b r' n' ar' Er'.
have := tsize_mod_of_frac_le r' ar'.
rewrite Er' poly_size_monoE.
have := mono_size_subseteq _ _ nn.
rewrite /factor_size_with; lia.
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
  (Frac.all_vars_make_mono _ _ _ nr ar) xe.
have : entry_size_with tsize b r ≤ dh_size (dh_map pt).
  exact: (sum_list_with_in (b, r) (λ e, entry_size_with tsize e.1 e.2) _ br).
rewrite /entry_size_with.
move: nr => /SMS.elem_of_pos_neg [] /MSet.elem_of_elements np.
- set P := sum_list_with _ (elements (SMS.pos _)).
  have : factor_size b n (Frac.den r) ≤ P := sum_list_with_in _ _ _ np.
  lia.
- set N := sum_list_with _ (elements (SMS.neg _)).
  have : factor_size b n (Frac.den r) ≤ N := sum_list_with_in _ _ _ np.
  lia.
Qed.

Lemma tsize_gfactors_le pt x : wf pt → x ∈ gfactors pt → tsize x ≤ tsize pt.
Proof.
move=> wpt xp; case G: (is_gmul pt).
  by apply: Nat.lt_le_incl; apply: tsize_gfactors_lt => //; rewrite G.
rewrite gfactors_Ngmul in xp; last by rewrite G.
by move/SMS.elem_of_singleton: xp => ->.
Qed.

Lemma tsize_atoms_lt pt x : is_mod pt → x ∈ atoms pt → tsize x < tsize pt.
Proof.
move=> M; rewrite /atoms /Frac.vars (tsize_mod _ M) elem_of_app.
case=> /Poly.elem_of_vars [m [mr /MSet.elem_of_elements xm]].
- have : tsize x ≤ mono_size m := sum_list_with_in _ _ _ xm.
  have := poly_size_ge _ _ mr; lia.
- have : tsize x ≤ mono_size m := sum_list_with_in _ _ _ xm.
  have := poly_size_ge _ _ mr; lia.
Qed.

End PreTerm.
