(** Group factors of pre-terms

    Every group element is the product of its group factors ([gfactorsK]): an
    exponential is its own factor, and a product has one power [b ^ (n / q)]
    for each monomial [n] of the numerator of each logarithm [p / q]
    ([exp_factor], [dh_factors]).  When every logarithm has a monomial
    denominator ([mono_den_logs]), [gfactors] is a homomorphism
    ([gfactors_gmul]).  The last section describes powers of non-products:
    their base, exponent and logarithms ([dh_map_Ngmul], [exp_frac_Ngmul]). *)

From stdpp Require Import sorting list numbers.
From cryptis Require Import lib.
From cryptis.lib Require Import list_sort fmap mset sms poly poly_gcd frac.
From mathcomp Require Import ssreflect.
From Stdlib Require Import Lia.
From cryptis.core.pre_term Require Import base with_stdpp normalize.

Module PreTerm.
Import base.PreTerm normalize.PreTerm.

Local Abbreviation poly := (Poly.poly pre_term).
Local Abbreviation frac := (Frac.frac pre_term).

Section GFactors.

Add Ring frac_ring_G : (Frac.frac_ring_theory (T := pre_term)).

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
  Frac.all_vars (λ x, wf x && negb (is_mod x)) r → wf (mk_exp b r).
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
by rewrite /frac_lists_of nr poly_lists_mono.
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
have ar0 := Frac.all_vars_make_mono _ _ _ nr ar.
split; last exact: mk_exp_Ngmul gb Er'.
case: Hr' => ->.
- exact: wf_mk_exp.
- apply: wf_mk_exp => //; last exact: Frac.all_vars_opp.
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
by move=> n1 nr; rewrite /mk_exp bool_decide_eq_false_2 // /frac_lists_of nr
  poly_lists_mono.
Qed.

Lemma expo_mk_exp b r n :
  r ≠ Frac.one → Frac.num r = Poly.mono n → expo (mk_exp b r) = mod_of_frac r.
Proof.
by move=> n1 nr; rewrite /mk_exp bool_decide_eq_false_2 // /mod_of_frac
  /frac_lists_of nr
  poly_lists_mono.
Qed.

Lemma wf_one : wf one.
Proof.
rewrite /one wf_modE; apply/andb_True; split; last done.
apply/andb_True; split; first done.
rewrite -frac_lists_of_one; exact: canonical_frac_lists_of.
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
  have E := frac_lists_ofK _ cF.
  rewrite -E; apply: wf_mod_of_frac; apply/all_atoms_frac_lists_of.
  by rewrite E.
- exact: wf_one.
Qed.

Lemma dh_map_gmul s : (∀ t, t ∈ s → wf t) → dh_map (gmul s) = dh_sum s.
Proof. by move=> h; apply: dh_map_dh_of; apply: wf_dh_sum. Qed.

Lemma dh_map_exp_frac b r :
  wf b → Frac.all_vars (λ x, wf x && negb (is_mod x)) r →
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
    a logarithm into its monomials ([entry_factors]) is additive
    ([entry_factors_add]), so [gfactors] is a homomorphism on group elements
    whose logarithms are Laurent ([gfactors_gmul]).  It is not one in general:
    [g^(1/(x+1))] and [g^(x/(x+1))] multiply to [g]. *)

Add Ring poly_ring_L : (Poly.poly_ring_theory (T := pre_term)).

Definition mono_den_logs pt : Prop := ∀ k, Frac.mono_den (dh_map pt !!! k).

Definition entry_factors b (r : frac) : SMS.sms pre_term :=
  SMS.bind (exp_factor b (Frac.den r)) (Poly.car (Frac.num r)).

Definition mono_den_factors b (Q : MSet.mset pre_term) (p : poly) :
  SMS.sms pre_term :=
  SMS.bind (exp_factor b (Poly.mono Q)) (Poly.car p).

Lemma entry_factorsE b r Q :
  Frac.den r = Poly.mono Q → entry_factors b r =
    mono_den_factors b Q (Frac.num r).
Proof. by rewrite /entry_factors /mono_den_factors => ->. Qed.

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

Lemma mono_den_factors_scale b K Q p :
  mono_den_factors b (K ⊎ Q) (Poly.mul (Poly.mono K) p) =
    mono_den_factors b Q p.
Proof.
rewrite /mono_den_factors Poly.car_mul_mono SMS.bind_map.
by apply: SMS.bind_ext => n _; exact: exp_factor_scale.
Qed.

Lemma mono_den_factors_scale_r b K Q p :
  mono_den_factors b (Q ⊎ K) (Poly.mul (Poly.mono K) p) =
    mono_den_factors b Q p.
Proof.
have -> : Q ⊎ K = K ⊎ Q.
  by apply: MSet.count_inj => x; rewrite !MSet.count_disj_union; lia.
exact: mono_den_factors_scale.
Qed.

Lemma mono_den_factors_add b Q p1 p2 :
  mono_den_factors b Q (Poly.add p1 p2) =
    mono_den_factors b Q p1 ⊎ mono_den_factors b Q p2.
Proof. by rewrite /mono_den_factors Poly.car_add SMS.bind_disj_union. Qed.

Lemma entry_factors_make b P Q :
  Frac.mono_den (Frac.make P (Poly.mono Q)) ∧
  entry_factors b (Frac.make P (Poly.mono Q)) = mono_den_factors b Q P.
Proof.
have [Q' [K [hd [EQ hP]]]] := Frac.make_mono_den P Q.
subst Q; split; first by exists Q'.
by rewrite (entry_factorsE _ _ _ hd) [in RHS]hP mono_den_factors_scale.
Qed.

Lemma entry_factors_zero b : entry_factors b Frac.zero = ∅.
Proof. by rewrite /entry_factors Frac.num_zero Poly.car_zero SMS.bind_empty.
  Qed.

Lemma entry_factors_opp b r :
  entry_factors b (Frac.opp r) = SMS.inv (entry_factors b r).
Proof.
by rewrite /entry_factors Frac.num_opp Frac.den_opp Poly.car_opp SMS.bind_inv.
Qed.

Lemma entry_factors_add b r1 r2 : Frac.mono_den r1 → Frac.mono_den r2 →
  Frac.mono_den (Frac.add r1 r2) ∧
  entry_factors b (Frac.add r1 r2) = entry_factors b r1 ⊎ entry_factors b r2.
Proof.
move=> [Q1 e1] [Q2 e2].
rewrite Frac.addE e1 e2 Poly.mul_mono.
have [L E] := entry_factors_make b
  (Poly.add (Poly.mul (Frac.num r1) (Poly.mono Q2))
            (Poly.mul (Frac.num r2) (Poly.mono Q1))) (Q1 ⊎ Q2).
split=> //; rewrite E mono_den_factors_add (entry_factorsE _ _ _ e1)
  (entry_factorsE _ _ _ e2).
rewrite (comm Poly.mul (Frac.num r1)) (comm Poly.mul (Frac.num r2)).
by rewrite mono_den_factors_scale_r mono_den_factors_scale.
Qed.

Lemma base_entry_factors b r y :
  negb (is_gnon_free b) → y ∈ entry_factors b r → base y = b.
Proof.
move=> gb /SMS.elem_of_bind [n [_ yn]].
have [r' [n' [-> [nr' _]]]] :=
  elem_of_exp_factor b (Frac.den r) n y (Frac.den_neq0 r) yn.
case: (decide (r' = Frac.one)) => [->|n1]; last exact: base_mk_exp n1 nr'.
by rewrite /mk_exp bool_decide_eq_true_2 // base_expN //; exact: Ngnf_Nexp.
Qed.

Lemma count_entry_factors_ne b r z :
  negb (is_gnon_free b) → base z ≠ b → SMS.count z (entry_factors b r) = 0%Z.
Proof.
move=> gb nz; case: (decide (z ∈ entry_factors b r)).
  by move=> /(base_entry_factors _ _ _ gb).
move=> h.
by move: h; rewrite SMS.elem_of_count; lia.
Qed.

(** Only the logarithm at the base of [z] counts toward [z]. *)
Lemma count_dh_factors m z :
  wf_dh m →
  SMS.count z (dh_factors m) =
    SMS.count z (entry_factors (base z) (m !!! base z)).
Proof.
move=> wm; rewrite lookup_to_list.
have K : ∀ k r, (k, r) ∈ FMap.to_list m → negb (is_gnon_free k).
  move=> k r /FMap.elem_of_to_list [mk nr].
  by have [_ [gk _]] := wm k ltac:(by rewrite mk).
have S := FMap.to_list_sorted m.
rewrite /dh_factors.
change (foldr _ ∅ (FMap.to_list m)) with
  (foldr (λ p s, entry_factors p.1 p.2 ⊎ s) ∅ (FMap.to_list m)).
elim: (FMap.to_list m) K S => [|[k r] l IH] K /=.
  by rewrite SMS.count_empty entry_factors_zero SMS.count_empty.
move=> /StronglySorted_cons [lk sl].
have Kk : negb (is_gnon_free k) by apply: (K k r); left.
have Kl : ∀ k' r', (k', r') ∈ l → negb (is_gnon_free k').
  by move=> k' r' h; apply: (K k' r'); right.
rewrite SMS.count_disj_union.
case: (bool_decide_reflect (base z = k)) => [ek|nk].
- have -> : SMS.count z (foldr (λ p s, entry_factors p.1 p.2 ⊎ s) ∅ l) = 0%Z.
    move: lk Kl; elim: (l) => [|[k' r'] l' IHl] /=.
      by move=> _ _; rewrite SMS.count_empty.
    move=> /Forall_cons_iff [kk' lk'] Kl'.
    have Kl'' : ∀ k0 r0, (k0, r0) ∈ l' → negb (is_gnon_free k0).
      by move=> k0 r0 h0; apply: (Kl' k0 r0); right.
    have nz : base z ≠ k'.
      by move=> e; move: kk'; rewrite -e ek; apply: irreflexivity.
    rewrite SMS.count_disj_union (IHl lk' Kl'').
    by rewrite (count_entry_factors_ne _ _ _ (Kl' k' r' ltac:(by left)) nz).
  by rewrite ek; lia.
- by rewrite count_entry_factors_ne // (IH Kl sl); lia.
Qed.

Lemma dh_factors_opp m :
  wf_dh m → dh_factors (dh_opp m) = SMS.inv (dh_factors m).
Proof.
move=> w; have w' := wf_dh_opp _ w; apply: SMS.count_inj => z.
rewrite SMS.count_inv !count_dh_factors // lookup_dh_opp entry_factors_opp.
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

Lemma entry_factors_fsum z (X : MSet.mset pre_term) :
  (∀ x, x ∈ X → wf x ∧ mono_den_logs x) →
  Frac.mono_den (Frac.fsum ((λ t, dh_map t !!! base z) <$> elements X)) ∧
  SMS.count z (entry_factors (base z)
    (Frac.fsum ((λ t, dh_map t !!! base z) <$> elements X))) =
  SMS.count z (SMS.bind (λ x, dh_factors (dh_map x)) (SMS.make X ∅)).
Proof.
elim/(MSet.mset_ind (T := pre_term)): X => [|x X IH] h.
  rewrite MSet.elements_empty fmap_nil Frac.fsum_nil entry_factors_zero.
  rewrite (_ : SMS.make ∅ ∅ = ∅) // SMS.bind_empty.
  by split; first exact: Frac.mono_den_zero.
have [wx lx] : wf x ∧ mono_den_logs x.
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
have [L E] := entry_factors_add (base z) _ _ (lx (base z)) lX.
split=> //; rewrite E SMS.bind_make_singleton_l !SMS.count_disj_union eX.
by rewrite count_dh_factors //; exact: wf_dh_map.
Qed.

Lemma dh_factors_sum s :
  (∀ x, x ∈ s → wf x ∧ mono_den_logs x) →
  dh_factors (dh_sum s) = SMS.bind (λ x, dh_factors (dh_map x)) s.
Proof.
move=> h; have ws : wf_dh (dh_sum s) by apply: wf_dh_sum => x /h [].
apply: SMS.count_inj => z.
rewrite count_dh_factors // lookup_dh_sum_ssum Frac.ssumE.
transitivity (SMS.count z (SMS.bind (λ x, dh_factors (dh_map x))
                             (SMS.make (SMS.pos s) (SMS.neg s))));
  last by rewrite SMS.make_pos_neg.
have hp : ∀ x, x ∈ SMS.pos s → wf x ∧ mono_den_logs x.
  by move=> x hx; apply: h; exact: SMS.elem_of_pos hx.
have hn : ∀ x, x ∈ SMS.neg s → wf x ∧ mono_den_logs x.
  by move=> x hx; apply: h; exact: SMS.elem_of_neg hx.
have [lp ep] := entry_factors_fsum z (SMS.pos s) hp.
have [ln en] := entry_factors_fsum z (SMS.neg s) hn.
rewrite Frac.subE count_bind_make.
have [_ ->] := entry_factors_add (base z) _ _ lp (Frac.mono_den_opp _ ln).
by rewrite SMS.count_disj_union entry_factors_opp SMS.count_inv ep en; lia.
Qed.

Lemma entry_factors_mk_exp b r n :
  negb (is_gnon_free b) → r ≠ Frac.zero → Frac.num r = Poly.mono n →
  entry_factors b r = {[+ mk_exp b r +]}.
Proof.
move=> gb nr er.
rewrite /entry_factors er Poly.car_mono SMS.bind_singleton /exp_factor.
by rewrite -er Frac.make_num_den er Poly.first_neg_mono.
Qed.

Lemma dh_factors_singleton b r :
  r ≠ Frac.zero → dh_factors {[b := r]} = entry_factors b r.
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
rewrite (dh_factors_singleton _ _ n1) (entry_factors_mk_exp _ _ _ gb n1 e1).
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
have lr : frac_lists_of (frac_of_lists F) = F := frac_lists_ofK _ cF.
set r := frac_of_lists F in lr *.
have n1 : r ≠ Frac.one.
  move=> e; move: wt; rewrite wf_dhE => /andb_True [_].
  by rewrite /trivial_dh -lr e frac_lists_of_one bool_decide_eq_true_2.
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
by rewrite (entry_factors_mk_exp _ _ _ gb nr er).
Qed.

Lemma gfactors_gmul s :
  (∀ x, x ∈ s → wf x ∧ mono_den_logs x) → gfactors (gmul s) =
    SMS.bind gfactors s.
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

Lemma dh_sum_pair (t1 t2 : pre_term) :
  dh_sum {[+ t1; t2 +]} =
  dh_add (dh_map t1) (dh_map t2).
Proof.
apply/FMap.fmap_eq => k.
by rewrite lookup_dh_sum_ssum Frac.ssum_disj_union
  !Frac.ssum_singleton lookup_dh_add.
Qed.

Lemma gmul_empty : gmul ∅ = PTDH [].
Proof.
rewrite /gmul; have -> : dh_sum ∅ = ∅.
  apply/FMap.fmap_eq => k.
  by rewrite lookup_dh_sum_ssum Frac.ssum_empty FMap.lookup_empty.
by rewrite /dh_of /entries FMap.to_listE.
Qed.

Lemma gfactors_dh_vars pt u :
  wf pt → u ∈ gfactors pt →
  ∃ b r, dh_map pt !!! b ≠ Frac.zero ∧
         dh_map u = {[b := r]} ∧ r ≠ Frac.zero ∧
         ∀ y, y ∈ Frac.vars r →
              y ∈ Frac.vars (dh_map pt !!! b).
Proof.
move=> wpt; rewrite (gfactors_dh _ wpt).
move=> /elem_of_dh_factors [b [r [n [br [nr ue]]]]].
have /FMap.elem_of_to_list [mb r0] := br.
have [wb [gb ar]] := wf_dh_map _ wpt b ltac:(by rewrite mb).
have nq := Frac.den_neq0 r.
have [r' [n' [-> [Er' Hr']]]] :=
  elem_of_exp_factor b (Frac.den r) n u nq ue.
have nr' : r' ≠ Frac.zero.
  move=> e; move: Er'; rewrite e Frac.num_zero => e'.
  exact: (PolyGcd.mono_neq0 _ (eq_sym e')).
exists b, r'; rewrite mb; split=> //; split.
  exact: dh_map_mk_exp.
split=> // y.
have P : Frac.all_vars (λ y, y ∈ Frac.vars r) r.
  exact/Frac.all_vars_iff.
have H : Frac.all_vars (λ y, y ∈ Frac.vars r) r'.
  have M := Frac.all_vars_make_mono _ _ _ nr P.
  by case: Hr' => ->; [exact: M|exact: Frac.all_vars_opp].
by move: H => /Frac.all_vars_iff; apply.
Qed.

(** ** Powers of non-products

    A non-product is a power of a base that is neither a power nor a product;
    raising it to a Laurent monomial yields another such power. *)

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
  frac_of (mod_of_lists (([m], []), d)) = frac_of_lists (([m], []), d) ∧
  Frac.num (frac_of_lists (([m], []), d)) = Poly.mono (MSet.of_list m).
Proof.
move=> /wf_exp_entry [_ [_ [aF cF]]].
have lr := frac_lists_ofK _ cF.
split.
- rewrite -{1}lr; apply: frac_of_mod_of_frac.
  apply: (Frac.all_vars_impl (λ x, wf x && negb (is_mod x))).
    by move=> x /andb_True [].
  by apply/all_atoms_frac_lists_of; rewrite lr.
- have e1 : poly_lists_of (Frac.num (frac_of_lists (([m], []), d))) = ([m], []).
    by move: lr => /(f_equal fst).
  by rewrite -(poly_of_lists_of (Frac.num _)) e1 poly_of_lists_mono.
Qed.

Lemma mono_num_expo pt :
  wf pt → negb (is_gmul pt) → Frac.mono_num (frac_of (expo pt)).
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
by rewrite -frac_lists_of_zero frac_of_listsK.
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

Lemma mk_exp_mono_num b r :
  negb (is_gnon_free b) → Frac.mono_num r →
  negb (is_gmul (mk_exp b r)) ∧ base (mk_exp b r) = b ∧
  expo (mk_exp b r) = mod_of_frac r.
Proof.
move=> gb [n en]; split; first exact: (mk_exp_Ngmul _ _ _ gb en).
case: (decide (r = Frac.one)) => [->|n1].
- have nb := Ngnf_Nexp _ gb.
  rewrite /mk_exp bool_decide_eq_true_2 // (base_expN _ nb) (expo_expN _ nb).
  by rewrite /mod_of_frac frac_lists_of_one.
- by rewrite (base_mk_exp _ _ _ n1 en) (expo_mk_exp _ _ _ n1 en).
Qed.

Lemma exp_factor_mono b n Q :
  exp_factor b (Poly.mono Q) n =
  {[+ mk_exp b (Frac.make (Poly.mono n) (Poly.mono Q)) +]}.
Proof.
have [n' [Q' [en _]]] := Frac.laurent_make_mono n Q.
by rewrite /exp_factor; cbv zeta; rewrite en Poly.first_neg_mono.
Qed.

(** The group factors of an element with Laurent logarithms are powers whose
    exponents are Laurent monomials. *)
Lemma gfactors_mono_den_logs pt u :
  wf pt → mono_den_logs pt → u ∈ gfactors pt →
  wf u ∧ mono_den_logs u ∧ Frac.laurent (frac_of (expo u)).
Proof.
move=> wpt L; rewrite (gfactors_dh _ wpt).
move=> /elem_of_dh_factors [b [r [n [br [nr ue]]]]].
have /FMap.elem_of_to_list [mb r0] := br.
have [wb [gb ar]] := wf_dh_map _ wpt b ltac:(by rewrite mb).
rewrite mb in ar.
have [Q eQ] := L b; rewrite mb in eQ.
have ar' : Frac.all_vars (λ x, wf x && negb (is_mod x))
             (Frac.make (Poly.mono n) (Poly.mono Q)).
  by rewrite -eQ; apply: Frac.all_vars_make_mono nr ar.
move: ue; rewrite eQ exp_factor_mono => /SMS.elem_of_singleton ->.
have mr := Frac.laurent_make_mono n Q.
have nr' := Frac.laurent_neq0 _ mr.
split; first exact: wf_mk_exp.
split.
- move=> k; rewrite (dh_map_mk_exp _ _ gb nr') FMap.lookup_singleton.
  by case: bool_decide;
    [exact: Frac.laurent_mono_den|exact: Frac.mono_den_zero].
- have [_ [_ ->]] := mk_exp_mono_num _ _ gb (Frac.laurent_mono_num _ mr).
  by rewrite frac_of_mod_of_frac_wf.
Qed.

End GFactors.

End PreTerm.
