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
  negb (is_gnon_free b) → Frac.all_vars (λ x, negb (is_mod x)) r →
  r ≠ Frac.zero →
  dh_map (mk_exp b r) !!! k = if bool_decide (k = b) then r else Frac.zero.
Proof. by move=> gb ar nr; rewrite dh_map_mk_exp // FMap.lookup_singleton. Qed.

Lemma all_vars_Nmod (r : frac) :
  Frac.all_vars (λ x, wf x && negb (is_mod x)) r →
  Frac.all_vars (λ x, negb (is_mod x)) r.
Proof. by apply: Frac.all_vars_impl => x /andb_True []. Qed.

Lemma all_vars_make_mono_Nmod (r : frac) n :
  n ∈ Poly.car (Frac.num r) →
  Frac.all_vars (λ x, wf x && negb (is_mod x)) r →
  Frac.all_vars (λ x, negb (is_mod x)) (Frac.make (Poly.mono n) (Frac.den r)).
Proof.
by move=> nr ar; apply: all_vars_Nmod; apply: Frac.all_vars_make_mono.
Qed.

Lemma ssum_exp_factor b q n k :
  negb (is_gnon_free b) → q ≠ Poly.zero →
  Frac.all_vars (λ x, negb (is_mod x)) (Frac.make (Poly.mono n) q) →
  Frac.ssum (λ t, dh_map t !!! k) (exp_factor b q n) =
  if bool_decide (k = b) then Frac.make (Poly.mono n) q else Frac.zero.
Proof.
move=> gb nq ar; rewrite /exp_factor.
have nr : Frac.make (Poly.mono n) q ≠ Frac.zero.
  exact: Frac.make_neq0 (PolyGcd.mono_neq0 n) nq.
case: (Poly.first_neg _).
- have nr' : Frac.opp (Frac.make (Poly.mono n) q) ≠ Frac.zero.
    move=> e; apply: nr.
    by rewrite -(Frac.opp_opp (Frac.make _ _)) e Frac.opp_zero.
  rewrite Frac.ssum_inv Frac.ssum_singleton.
  rewrite (lookup_dh_map_mk_exp _ _ _ gb (Frac.all_vars_opp _ _ ar) nr').
  by case: bool_decide; rewrite ?Frac.opp_opp ?Frac.opp_zero.
- by rewrite Frac.ssum_singleton (lookup_dh_map_mk_exp _ _ _ gb ar nr).
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
have [_ [gb ar]] := wm b ltac:(by rewrite mb).
rewrite mb in ar.
have E : ∀ n, n ∈ Poly.car (Frac.num r) →
    Frac.ssum (λ t, dh_map t !!! k) (exp_factor b (Frac.den r) n) =
    if bool_decide (k = b) then Frac.make (Poly.mono n) (Frac.den r)
    else Frac.zero.
  move=> n nr'; apply: ssum_exp_factor => //; first exact: Frac.den_neq0.
  exact: all_vars_make_mono_Nmod.
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
case: (is_dh t); last exact: dh_sum_singleton.
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

Lemma is_exp_mk_exp b r :
  r ≠ Frac.one → Frac.all_vars (λ x, negb (is_mod x)) r →
  is_exp (mk_exp b r) = is_mono_poly (Frac.num r).
Proof.
move=> n1 ar; rewrite /mk_exp bool_decide_eq_false_2 //.
by rewrite [is_exp _]/= frac_of_mod_of_frac.
Qed.

Lemma is_mono_poly_mono n : is_mono_poly (Poly.mono n) = true.
Proof.
rewrite /is_mono_poly Poly.car_mono SMS.pos_singleton SMS.neg_singleton.
by rewrite MSet.elements_singleton MSet.elements_empty.
Qed.

Lemma mk_exp_Ngmul b r n :
  negb (is_gnon_free b) → Frac.all_vars (λ x, negb (is_mod x)) r →
  Frac.num r = Poly.mono n → negb (is_gmul (mk_exp b r)).
Proof.
move=> gb ar nr; case: (decide (r = Frac.one)) => [e1|n1].
  by rewrite /mk_exp bool_decide_eq_true_2 //; exact: Ngnf_Ngmul.
rewrite /is_gmul (is_exp_mk_exp _ _ n1 ar) nr.
by rewrite is_mono_poly_mono; case: is_dh.
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
Proof. by rewrite /gfactors /is_gmul; case: (is_exp pt); case: (is_dh pt). Qed.

Lemma gfactors_elem t x :
  wf t → x ∈ gfactors t → wf x ∧ negb (is_gmul x).
Proof.
move=> wt; rewrite /gfactors.
case E: (is_exp t).
  move=> /SMS.elem_of_singleton ->; split=> //.
  by apply: is_exp_Ngmul; rewrite E.
case D: (is_dh t); last first.
  move=> /SMS.elem_of_singleton ->; split=> //.
  by rewrite /is_gmul D.
move=> /elem_of_dh_factors [b [r [n [br [nr xe]]]]].
have /FMap.elem_of_to_list [mb r0] := br.
have [wb [gb ar]] := wf_dh_map _ wt b ltac:(by rewrite mb).
rewrite mb in ar.
have nq := Frac.den_neq0 r.
have [r' [n' [-> [Er' Hr']]]] := elem_of_exp_factor b (Frac.den r) n x nq xe.
have nr0 : Frac.make (Poly.mono n) (Frac.den r) ≠ Frac.zero.
  exact: Frac.make_neq0 (PolyGcd.mono_neq0 n) nq.
have ar0 := Frac.all_vars_make_mono _ _ _ nr ar.
have ar' : Frac.all_vars (λ x, wf x && negb (is_mod x)) r'.
  by case: Hr' => ->; last exact: Frac.all_vars_opp.
split; last exact: mk_exp_Ngmul gb (all_vars_Nmod _ ar') Er'.
case: Hr' ar' => -> ar'.
- exact: wf_mk_exp.
- apply: wf_mk_exp => //.
  move=> e; apply: nr0.
  by rewrite -(Frac.opp_opp (Frac.make _ _)) e Frac.opp_zero.
Qed.

Variant is_exp_spec pt : bool → Prop :=
| IsExp b e of pt = PT2 O2Exp b e & is_mono_poly (Frac.num (frac_of e)) = true :
  is_exp_spec pt true
| NotExp of base pt = pt & expo pt = one : is_exp_spec pt false.

Lemma is_expP pt : is_exp_spec pt (is_exp pt).
Proof.
case E: (is_exp pt); last by constructor; rewrite /base /expo E.
by case: pt E => [[]|[] ?|[] b e] // E; econstructor.
Qed.

Lemma base_expN pt : negb (is_exp pt) → base pt = pt.
Proof. by case: is_expP. Qed.

Lemma expo_expN pt : negb (is_exp pt) → expo pt = one.
Proof. by case: is_expP. Qed.

Lemma base_exp b e :
  is_mono_poly (Frac.num (frac_of e)) = true → base (PT2 O2Exp b e) = b.
Proof. by move=> me; rewrite /base [is_exp _]/= me. Qed.

Lemma base_Nexp pt : wf pt → negb (is_exp (base pt)).
Proof.
move=> wpt; case E: (is_exp pt).
  case: (is_expP pt) E => [b e ept me|//] _.
  have [_ [_ [_ [_ [_ [gb _]]]]]] := wf_exp_parts _ _ _ wpt ept.
  by rewrite ept base_exp //; exact: Ngnf_Nexp.
by rewrite (base_expN pt ltac:(by rewrite E)) E.
Qed.

Lemma is_gmul_base pt : wf pt → is_gmul (base pt) = is_gmul pt.
Proof.
move=> wpt; case E: (is_exp pt); last first.
  by rewrite (base_expN pt ltac:(by rewrite E)).
have /Is_true_negb -> := is_exp_Ngmul pt ltac:(by rewrite E).
case: (is_expP pt) E => [b e ept me|//] _.
have [_ [_ [_ [_ [_ [gb _]]]]]] := wf_exp_parts _ _ _ wpt ept.
by rewrite ept base_exp //; apply/Is_true_negb; exact: Ngnf_Ngmul.
Qed.

Lemma base_mk_exp b r n :
  r ≠ Frac.one → Frac.all_vars (λ x, negb (is_mod x)) r →
  Frac.num r = Poly.mono n → base (mk_exp b r) = b.
Proof.
move=> n1 ar nr; rewrite /base (is_exp_mk_exp _ _ n1 ar) nr.
by rewrite /mk_exp bool_decide_eq_false_2 // is_mono_poly_mono.
Qed.

Lemma expo_mk_exp b r n :
  r ≠ Frac.one → Frac.all_vars (λ x, negb (is_mod x)) r →
  Frac.num r = Poly.mono n → expo (mk_exp b r) = mod_of_frac r.
Proof.
move=> n1 ar nr; rewrite /expo (is_exp_mk_exp _ _ n1 ar) nr.
by rewrite /mk_exp bool_decide_eq_false_2 // is_mono_poly_mono.
Qed.

Lemma wf_one : wf one.
Proof. by apply/wfP; exact: mod_of_frac_one. Qed.

Lemma wf_base pt : wf pt → wf (base pt).
Proof.
rewrite /base; case: (is_expP pt) => [b e ept _|_ _] wpt //.
by have [_ [_ [_ [_ [wb _]]]]] := wf_exp_parts _ _ _ wpt ept; rewrite ept.
Qed.

Lemma wf_expo pt : wf pt → wf (expo pt).
Proof.
rewrite /expo; case: (is_expP pt) => [b e ept _|_ _] wpt; last exact: wf_one.
have [_ [_ [_ [ee [_ [_ ae]]]]]] := wf_exp_parts _ _ _ wpt ept.
by rewrite ept /= ee; apply: wf_mod_of_frac.
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
  negb (is_gnon_free b) → Frac.all_vars (λ x, negb (is_mod x)) r →
  y ∈ entry_factors b r → base y = b.
Proof.
move=> gb ar /SMS.elem_of_bind [n [nr yn]].
have [r' [n' [-> [nr' Hr']]]] :=
  elem_of_exp_factor b (Frac.den r) n y (Frac.den_neq0 r) yn.
have ar' : Frac.all_vars (λ x, negb (is_mod x)) r'.
  have M := Frac.all_vars_make_mono _ _ _ nr ar.
  by case: Hr' => ->; [exact: M|exact: Frac.all_vars_opp].
case: (decide (r' = Frac.one)) => [->|n1].
  2: exact: base_mk_exp n1 ar' nr'.
by rewrite /mk_exp bool_decide_eq_true_2 // base_expN //; exact: Ngnf_Nexp.
Qed.

Lemma count_entry_factors_ne b r z :
  negb (is_gnon_free b) → Frac.all_vars (λ x, negb (is_mod x)) r →
  base z ≠ b → SMS.count z (entry_factors b r) = 0%Z.
Proof.
move=> gb ar nz; case: (decide (z ∈ entry_factors b r)).
  by move=> /(base_entry_factors _ _ _ gb ar).
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
have K : ∀ k r, (k, r) ∈ FMap.to_list m →
    negb (is_gnon_free k) ∧ Frac.all_vars (λ x, negb (is_mod x)) r.
  move=> k r /FMap.elem_of_to_list [mk nr].
  have [_ [gk ar]] := wm k ltac:(by rewrite mk).
  by rewrite mk in ar; split=> //; apply: all_vars_Nmod.
have S := FMap.to_list_sorted m.
rewrite /dh_factors.
change (foldr _ ∅ (FMap.to_list m)) with
  (foldr (λ p s, entry_factors p.1 p.2 ⊎ s) ∅ (FMap.to_list m)).
elim: (FMap.to_list m) K S => [|[k r] l IH] K /=.
  by rewrite SMS.count_empty entry_factors_zero SMS.count_empty.
move=> /StronglySorted_cons [lk sl].
have [gk ak] := K k r ltac:(by left).
have Kl : ∀ k' r', (k', r') ∈ l →
    negb (is_gnon_free k') ∧ Frac.all_vars (λ x, negb (is_mod x)) r'.
  by move=> k' r' h; apply: (K k' r'); right.
rewrite SMS.count_disj_union.
case: (bool_decide_reflect (base z = k)) => [ek|nk].
- have -> : SMS.count z (foldr (λ p s, entry_factors p.1 p.2 ⊎ s) ∅ l) = 0%Z.
    move: lk Kl; elim: (l) => [|[k' r'] l' IHl] /=.
      by move=> _ _; rewrite SMS.count_empty.
    move=> /Forall_cons_iff [kk' lk'] Kl'.
    have Kl'' : ∀ k0 r0, (k0, r0) ∈ l' →
        negb (is_gnon_free k0) ∧ Frac.all_vars (λ x, negb (is_mod x)) r0.
      by move=> k0 r0 h0; apply: (Kl' k0 r0); right.
    have [gk' ak'] := Kl' k' r' ltac:(by left).
    have nz : base z ≠ k'.
      by move=> e; move: kk'; rewrite -e ek; apply: irreflexivity.
    rewrite SMS.count_disj_union (IHl lk' Kl'').
    by rewrite (count_entry_factors_ne _ _ _ gk' ak' nz).
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

Lemma gfactors_dh t : wf t → gfactors t = dh_factors (dh_map t).
Proof.
move=> wt; rewrite /gfactors; case: (is_expP t) => [b e et me|_ _]; last first.
  case D: (is_dh t) => //.
  have gt : negb (is_gnon_free t) by rewrite is_gnon_freeE D.
  by rewrite (dh_map_Ngnf _ gt) (dh_factors_atom _ gt).
have [em [n1 [n0 [ee [wb [gb ae]]]]]] := wf_exp_parts _ _ _ wt et.
have [n en] : ∃ n, Frac.num (frac_of e) = Poly.mono n.
  by apply/is_mono_polyP; rewrite me.
rewrite em (dh_factors_singleton _ _ n0) (entry_factors_mk_exp _ _ _ gb n0 en).
by rewrite /mk_exp bool_decide_eq_false_2 // -ee -et.
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

Lemma gmul_empty : gmul ∅ = PT0 O0GOne.
Proof.
rewrite /gmul; have -> : dh_sum ∅ = ∅.
  apply/FMap.fmap_eq => k.
  by rewrite lookup_dh_sum_ssum Frac.ssum_empty FMap.lookup_empty.
exact: dh_of_empty.
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
  apply: dh_map_mk_exp => //; rewrite mb in ar.
  have M := all_vars_make_mono_Nmod _ _ nr ar.
  by case: Hr' => ->; [exact: M|exact: Frac.all_vars_opp].
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
move=> wpt; rewrite /is_gmul /base.
case: (is_expP pt) => [b e ept _|_ _] Ng.
  have [_ [_ [_ [_ [_ [gb _]]]]]] := wf_exp_parts _ _ _ wpt ept.
  by rewrite ept.
by rewrite is_gnon_freeE; move: Ng; case: (is_dh pt).
Qed.

Lemma mono_num_expo pt :
  wf pt → negb (is_gmul pt) → Frac.mono_num (frac_of (expo pt)).
Proof.
move=> wpt Ng; rewrite /expo; case: (is_expP pt) => [b e ept me|_ _].
  by rewrite ept /=; apply/is_mono_polyP; rewrite me.
by rewrite frac_of_one; exists ∅; rewrite Frac.num_one Poly.oneE.
Qed.

Lemma dh_map_Ngmul pt :
  wf pt → negb (is_gmul pt) → dh_map pt = {[base pt := frac_of (expo pt)]}.
Proof.
move=> wpt; rewrite /is_gmul /base /expo.
case: (is_expP pt) => [b e ept _|_ _] Ng.
  by have [em _] := wf_exp_parts _ _ _ wpt ept; rewrite em ept.
rewrite frac_of_one dh_map_Ngnf // is_gnon_freeE.
by move: Ng; case: (is_dh pt).
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
  negb (is_gnon_free b) → Frac.all_vars (λ x, negb (is_mod x)) r →
  Frac.mono_num r →
  negb (is_gmul (mk_exp b r)) ∧ base (mk_exp b r) = b ∧
  expo (mk_exp b r) = mod_of_frac r.
Proof.
move=> gb ar [n en]; split; first exact: (mk_exp_Ngmul _ _ _ gb ar en).
case: (decide (r = Frac.one)) => [->|n1].
- have nb := Ngnf_Nexp _ gb.
  rewrite /mk_exp bool_decide_eq_true_2 // (base_expN _ nb) (expo_expN _ nb).
  by rewrite mod_of_frac_one.
- by rewrite (base_mk_exp _ _ _ n1 ar en) (expo_mk_exp _ _ _ n1 ar en).
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
- move=> k; rewrite (dh_map_mk_exp _ _ gb (all_vars_Nmod _ ar') nr').
  rewrite FMap.lookup_singleton.
  by case: bool_decide;
    [exact: Frac.laurent_mono_den|exact: Frac.mono_den_zero].
- have [_ [_ ->]] := mk_exp_mono_num _ _ gb (all_vars_Nmod _ ar')
    (Frac.laurent_mono_num _ mr).
  by rewrite frac_of_mod_of_frac_wf.
Qed.

End GFactors.

End PreTerm.
