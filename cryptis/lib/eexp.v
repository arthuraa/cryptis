From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import base gmap.
From cryptis Require Import term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Extended exponents

    An extended exponent ([eexp]) is a formal sum of exponents: a signed
    multiset of terms, read additively.  [∅] is zero, [⊎] is addition and
    [SMS.inv] is negation.  The exponents themselves are the monomials, and
    [emul] multiplies two sums monomial by monomial with [TMul], so extended
    exponents form a commutative ring ([emul_comm]).

    Group terms form a module over this ring.  [epow t s] raises [t] to the sum
    [s], the product of the powers of [t] by the monomials of [s], so that
    [epow (epow t s) r = epow t (emul s r)] ([epowA]).  Conversely, [log g t]
    reads off the exponent of the base [g] in [t]: the sum of the exponents [e]
    of the group factors [g^e] of [t].  The logarithms are linear ([log_TGMul2],
    [log_epow]), and they determine a term ([log_inj]); in particular, a term
    other than [1] has a logarithm other than [0] ([log_neq0]).

    An equation between terms thus becomes an equation between their
    logarithms, which we analyze with degrees.  The degree of a monomial [m] in
    an atom [h] is [count h m], and [hpart h k s] is the part of [s] of degree
    [k] in [h].  Degrees add up when multiplying ([hhom_emul], [hpart_emul_l]).
    Two facts make them useful:

    - The logarithms of a term have degree 0 in any atom at least as big as
      the term ([hhom_log_small]), and in any atom with a subterm that the term
      lacks ([hhom_log_fresh]).

    - Leading parts do not cancel: two different shifts of a nonzero sum cannot
      agree up to terms of degree 0 ([emul_lead]). *)

Abbreviation eexp := tsms.

Implicit Types (g h t u e m : term) (s r : eexp) (k d : Z).

(** ** The ring of extended exponents *)

(** The product of [s] and [r]: every monomial of [s] times every monomial of
    [r]. *)
Definition emul s r : eexp :=
  SMS.bind (λ e, SMS.map (λ m, TMul {[+ m; e +]}) s) r.

Lemma emul1 s e : emul s {[+ e +]} = SMS.map (λ m, TMul {[+ m; e +]}) s.
Proof. exact: SMS.bind_singleton. Qed.

Lemma emul_singleton e1 e2 :
  emul {[+ e1 +]} {[+ e2 +]} = {[+ TMul {[+ e1; e2 +]} +]}.
Proof. by rewrite emul1 SMS.map_singleton. Qed.

Lemma emul_empty_l r : emul ∅ r = ∅.
Proof.
rewrite /emul -[RHS](SMS.bind_empty_l r); apply: SMS.bind_ext => e _.
exact: SMS.map_empty.
Qed.

Lemma emul_disj_union_l s1 s2 r : emul (s1 ⊎ s2) r = emul s1 r ⊎ emul s2 r.
Proof.
rewrite /emul -SMS.bind_disj_union_l; apply: SMS.bind_ext => e _.
exact: SMS.map_disj_union.
Qed.

Lemma emul_disj_union_r s r1 r2 : emul s (r1 ⊎ r2) = emul s r1 ⊎ emul s r2.
Proof. exact: SMS.bind_disj_union. Qed.

Lemma emul_comm s r : emul s r = emul r s.
Proof.
rewrite /emul /SMS.map SMS.bind_comm; apply: SMS.bind_ext => m _.
by apply: SMS.bind_ext => e _; rewrite (comm (⊎) {[+ e +]}).
Qed.

Lemma emul1A s e1 e2 :
  emul (emul s {[+ e1 +]}) {[+ e2 +]} = emul s {[+ TMul {[+ e1; e2 +]} +]}.
Proof.
rewrite !emul1 SMS.map_map; apply: SMS.map_ext => m _.
apply: count_inj => x _; rewrite !count_TMul2; lia.
Qed.

#[local] Lemma TMulK m e : TMul {[+ TMul {[+ m; e +]}; TInv e +]} = m.
Proof. apply: count_inj => x _; rewrite !count_TMul2 count_TInv; lia. Qed.

#[local] Lemma TMulKV m e : TMul {[+ TMul {[+ m; TInv e +]}; e +]} = m.
Proof. apply: count_inj => x _; rewrite !count_TMul2 count_TInv; lia. Qed.

Lemma count_emul1 s e m :
  SMS.count m (emul s {[+ e +]}) = SMS.count (TMul {[+ m; TInv e +]}) s.
Proof.
have inj m1 m2 : TMul {[+ m1; e +]} = TMul {[+ m2; e +]} → m1 = m2.
  by move=> E; rewrite -(TMulK m1 e) E TMulK.
rewrite emul1 -{1}(TMulKV m e).
exact: (SMS.count_map_inj (λ m', TMul {[+ m'; e +]}) _ s inj).
Qed.

Lemma emul1_inj s r e : emul s {[+ e +]} = emul r {[+ e +]} → s = r.
Proof.
move=> E; apply: SMS.count_inj => m.
by rewrite -(TMulK m e) -!count_emul1 E.
Qed.

Lemma emul1_eq0 s e : emul s {[+ e +]} = ∅ → s = ∅.
Proof. by move=> E; apply: (emul1_inj (e := e)); rewrite E emul_empty_l. Qed.

(** ** Exponentiation by extended exponents *)

Definition epow t s : term := TGMul (SMS.map (TExp t) s).

Lemma epow2 t e1 e2 :
  epow t {[+ e1; e2 +]} = TGMul {[+ TExp t e1; TExp t e2 +]}.
Proof. by rewrite /epow SMS.map_disj_union !SMS.map_singleton. Qed.

Lemma epow_unit s : epow (TGMul ∅) s = TGMul ∅.
Proof.
apply/gtunitP; rewrite /epow gfactors_TGMul SMS.bind_map.
rewrite -[RHS](SMS.bind_empty_l s); apply: SMS.bind_ext => e _.
by rewrite TExp_gunit gfactors_TGMul_empty.
Qed.

#[local] Lemma TGMul_bind (f : term → eexp) s :
  TGMul (SMS.bind f s) = TGMul (SMS.map (λ x, TGMul (f x)) s).
Proof.
apply: gfactors_inj; rewrite !gfactors_TGMul SMS.bind_bind SMS.bind_map.
by apply: SMS.bind_ext => x _; rewrite gfactors_TGMul.
Qed.

Lemma epowA t s r : epow (epow t s) r = epow t (emul s r).
Proof.
rewrite /epow /emul SMS.map_bind TGMul_bind; congr TGMul.
apply: SMS.map_ext => e _.
rewrite TExp_TGMul !SMS.map_map; congr TGMul; apply: SMS.map_ext => m _.
by rewrite /= TExpA.
Qed.

(** ** Logarithms *)

(** The exponent of the base [g] in [t]. *)
Definition log g t : eexp :=
  SMS.bind (λ u, if bool_decide (base u = g) then {[+ expo u +]} else ∅)
    (gfactors t).

(** The coefficient of [e] in [log g t] is the multiplicity of [g^e] in [t]. *)
Lemma count_log g e t :
  negb (is_exp g) → negb (is_gmul g) →
  SMS.count e (log g t) = gcount (TExp g e) t.
Proof.
move=> gNX gNm.
have inj : ∀ e1 e2, TExp g e1 = TExp g e2 → e1 = e2.
  move=> e1 e2; exact: TExp_injr (Ngmul_neq_unit gNm).
rewrite -(SMS.count_map_inj (TExp g) e (log g t) inj) /log SMS.map_bind.
have -> : SMS.bind (λ u, SMS.map (TExp g)
            (if bool_decide (base u = g) then {[+ expo u +]} else ∅))
            (gfactors t)
          = SMS.filter (λ u, base u = g) (gfactors t).
  rewrite /SMS.filter; apply: SMS.bind_ext => u _.
  case: (bool_decide_reflect (base u = g)) => [<-|_].
  - by rewrite SMS.map_singleton TExp_base_expo.
  - exact: SMS.map_empty.
rewrite SMS.count_filter base_TExp // base_expN //.
by rewrite bool_decide_eq_true_2.
Qed.

Lemma log_inj t1 t2 : (∀ g, log g t1 = log g t2) → t1 = t2.
Proof.
move=> e; apply: gcount_inj => u Nu.
have bNX := base_Nexp u.
have bNm : negb (is_gmul (base u)) by rewrite is_gmul_base.
by rewrite -(TExp_base_expo u) -!(count_log _ _ bNX bNm) e.
Qed.

Lemma log_TGMul g s : log g (TGMul s) = SMS.bind (log g) s.
Proof. by rewrite /log gfactors_TGMul SMS.bind_bind. Qed.

Lemma log_unit g : log g (TGMul ∅) = ∅.
Proof. by rewrite log_TGMul SMS.bind_empty. Qed.

Lemma log_TGMul2 g t1 t2 : log g (TGMul {[+ t1; t2 +]}) = log g t1 ⊎ log g t2.
Proof. by rewrite log_TGMul SMS.bind_disj_union !SMS.bind_singleton. Qed.

Lemma log_eq0 t : (∀ g, log g t = ∅) → t = TGMul ∅.
Proof. by move=> e; apply: log_inj => g; rewrite e log_unit. Qed.

Lemma log_neq0 t : t ≠ TGMul ∅ → ∃ g, log g t ≠ ∅.
Proof.
move=> /gfactors_nonempty [u u_t]; exists (base u) => e.
have Nu := Ngmul_gfactors _ _ u_t.
have bNX := base_Nexp u.
have bNm : negb (is_gmul (base u)) by rewrite is_gmul_base.
have : gcount u t ≠ 0%Z by apply/gcount_neq0.
by rewrite -(TExp_base_expo u) -(count_log _ _ bNX bNm) e SMS.count_empty.
Qed.

Lemma log_TExp g t e : log g (TExp t e) = emul (log g t) {[+ e +]}.
Proof.
rewrite emul1 /log gfactors_TExp SMS.bind_map SMS.map_bind.
apply: SMS.bind_ext => u u_t; have Nu := Ngmul_gfactors _ _ u_t.
rewrite base_TExp // expo_TExp //.
case: (bool_decide (base u = g)).
- by rewrite SMS.map_singleton.
- by rewrite SMS.map_empty.
Qed.

Lemma log_epow g t s : log g (epow t s) = emul (log g t) s.
Proof.
rewrite /epow log_TGMul SMS.bind_map /emul.
by apply: SMS.bind_ext => e _; rewrite log_TExp emul1.
Qed.

Lemma log_atom g u :
  negb (is_exp u) → negb (is_gmul u) →
  log g u = if bool_decide (u = g) then {[+ TMul ∅ +]} else ∅.
Proof.
move=> uNX uNm.
by rewrite /log gfactors_Ngmul // SMS.bind_singleton base_expN // expo_expN.
Qed.

Lemma log_TExp_atom g u e :
  negb (is_exp u) → negb (is_gmul u) →
  log g (TExp u e) = if bool_decide (u = g) then {[+ e +]} else ∅.
Proof.
move=> uNX uNm; rewrite log_TExp log_atom //.
case: (bool_decide (u = g)); last exact: emul_empty_l.
by rewrite emul_singleton TMul_unit_l.
Qed.

(** ** Degrees *)

(** [s] is homogeneous of degree [k] in the atom [h]. *)
Definition hhom h k s : Prop := ∀ m, m ∈ s → count h m = k.

(** The part of [s] of degree [k] in [h]. *)
Definition hpart h k s : eexp := SMS.filter (λ m, count h m = k) s.

Lemma count_hpart h k s m :
  SMS.count m (hpart h k s)
  = if bool_decide (count h m = k) then SMS.count m s else 0%Z.
Proof. by rewrite /hpart SMS.count_filter. Qed.

Lemma count_hpart_eq h k s m :
  count h m = k → SMS.count m (hpart h k s) = SMS.count m s.
Proof. by move=> e; rewrite count_hpart bool_decide_eq_true_2. Qed.

Lemma hhom_empty h k : hhom h k ∅.
Proof. by move=> m /SMS.elem_of_count; rewrite SMS.count_empty. Qed.

Lemma hhom_singleton h k e : count h e = k → hhom h k {[+ e +]}.
Proof. by move=> he m /SMS.elem_of_singleton ->. Qed.

Lemma hhom_disj_union h k s1 s2 :
  hhom h k s1 → hhom h k s2 → hhom h k (s1 ⊎ s2).
Proof. by move=> h1 h2 m /SMS.elem_of_disj_union [/h1|/h2]. Qed.

Lemma hhom_emul h k k1 k2 s r :
  hhom h k1 s → hhom h k2 r → k = (k1 + k2)%Z → hhom h k (emul s r).
Proof.
move=> hs hr -> m /SMS.elem_of_bind [e [e_r /SMS.elem_of_map [m' [-> m'_s]]]].
by rewrite count_TMul2 (hs _ m'_s) (hr _ e_r).
Qed.

Lemma hhom_count h k s m : hhom h k s → count h m ≠ k → SMS.count m s = 0%Z.
Proof. by move=> hs ne; apply: SMS.not_elem_of_count => /hs. Qed.

Lemma hpart_disj_union h k s1 s2 :
  hpart h k (s1 ⊎ s2) = hpart h k s1 ⊎ hpart h k s2.
Proof. exact: SMS.bind_disj_union. Qed.

Lemma hpart_hom_eq h k s : hhom h k s → hpart h k s = s.
Proof.
move=> hs; apply: SMS.count_inj => m; rewrite count_hpart.
case: (bool_decide_reflect (count h m = k)) => // ne.
by rewrite (hhom_count hs ne).
Qed.

Lemma hpart_hom_ne h k k' s : hhom h k s → k' ≠ k → hpart h k' s = ∅.
Proof.
move=> hs ne; apply: SMS.count_inj => m; rewrite count_hpart SMS.count_empty.
case: (bool_decide_reflect (count h m = k')) => // e.
by apply: hhom_count hs _; lia.
Qed.

Lemma hpart_emul1 h k s e :
  hpart h k (emul s {[+ e +]}) = emul (hpart h (k - count h e) s) {[+ e +]}.
Proof.
apply: SMS.count_inj => m; rewrite count_hpart !count_emul1 count_hpart.
rewrite count_TMul2 count_TInv.
case: (bool_decide_reflect (count h m = k)) => ?;
  case: (bool_decide_reflect (_ = _)) => ? //; lia.
Qed.

#[local] Lemma hpart_bind h k (f : term → eexp) r :
  hpart h k (SMS.bind f r) = SMS.bind (λ e, hpart h k (f e)) r.
Proof. by rewrite /hpart /SMS.filter SMS.bind_bind. Qed.

Lemma hpart_emul_r h d k s r :
  hhom h d r → hpart h k (emul s r) = emul (hpart h (k - d) s) r.
Proof.
move=> hr; rewrite {1}/emul hpart_bind /emul; apply: SMS.bind_ext => e e_r.
by rewrite -!emul1 hpart_emul1 (hr _ e_r).
Qed.

Lemma hpart_emul_l h d k s r :
  hhom h d s → hpart h k (emul s r) = emul s (hpart h (k - d) r).
Proof.
by move=> hs; rewrite emul_comm (@hpart_emul_r h d k r s hs) emul_comm.
Qed.

(** ** Leading parts *)

#[local] Lemma hpart_top h s :
  s ≠ ∅ → ∃ k, hpart h k s ≠ ∅ ∧ ∀ k', (k < k')%Z → hpart h k' s = ∅.
Proof.
move=> ns.
case: (SMS.max_or_empty (count h) s) => [[w [w_s w_max]]|//].
exists (count h w); split.
  move=> /(f_equal (SMS.count w)); rewrite count_hpart SMS.count_empty.
  by rewrite bool_decide_eq_true_2 //; apply/SMS.elem_of_count.
move=> k' lt; apply: SMS.count_inj => m; rewrite count_hpart SMS.count_empty.
case: (bool_decide_reflect (count h m = k')) => // e.
by apply: SMS.not_elem_of_count => /w_max; lia.
Qed.

#[local] Lemma hpart_bottom h s :
  s ≠ ∅ → ∃ k, hpart h k s ≠ ∅ ∧ ∀ k', (k' < k)%Z → hpart h k' s = ∅.
Proof.
move=> ns.
case: (SMS.max_or_empty (λ m, - count h m)%Z s) => [[w [w_s w_min]]|//].
exists (count h w); split.
  move=> /(f_equal (SMS.count w)); rewrite count_hpart SMS.count_empty.
  by rewrite bool_decide_eq_true_2 //; apply/SMS.elem_of_count.
move=> k' lt; apply: SMS.count_inj => m; rewrite count_hpart SMS.count_empty.
case: (bool_decide_reflect (count h m = k')) => // e.
by apply: SMS.not_elem_of_count => /w_min; lia.
Qed.

(** Leading parts do not cancel.  If [β ≠ 0] and [count h e1 > count h e2], the
    highest part of [β⋅e1] lies above everything in [β⋅e2], and the lowest part
    of [β⋅e2] lies below everything in [β⋅e1]; terms of degree 0 can absorb at
    most one of them. *)
Lemma emul_lead h β e1 e2 r1 r2 :
  hhom h 0 r1 → hhom h 0 r2 → count h e1 ≠ count h e2 →
  r1 ⊎ emul β {[+ e1 +]} = r2 ⊎ emul β {[+ e2 +]} →
  β = ∅.
Proof.
move=> hr1 hr2 ne e.
apply: SMS.count_inj => m0; rewrite SMS.count_empty.
case: (decide (SMS.count m0 β = 0%Z)) => // nm0; exfalso.
have nβ : β ≠ ∅ by move=> E; apply: nm0; rewrite E SMS.count_empty.
have part k : k ≠ 0%Z →
    emul (hpart h (k - count h e1) β) {[+ e1 +]}
    = emul (hpart h (k - count h e2) β) {[+ e2 +]}.
  move=> nk; move/(f_equal (hpart h k)): e.
  rewrite !hpart_disj_union !hpart_emul1 !(hpart_hom_ne _ nk) //.
  by rewrite !(left_id ∅ (⊎)).
clear e.
wlog lt : e1 e2 ne part / (count h e2 < count h e1)%Z.
  move=> H; case: (Z.lt_total (count h e2) (count h e1)) => [|[|]] ?.
  - exact: H.
  - by [].
  - by apply: (H e2 e1) => // k /part.
have [top [ntop above]] := hpart_top h nβ.
have [bot [nbot below]] := hpart_bottom h nβ.
have le : (bot ≤ top)%Z.
  case: (Z.le_gt_cases bot top) => // lt'.
  by case: nbot; apply: above.
case: (decide (top + count h e1 = 0)%Z) => [e0|n0].
- have /part : (bot + count h e2 ≠ 0)%Z by lia.
  rewrite Z.add_simpl_r below; last by lia.
  by rewrite emul_empty_l => E; apply: nbot; apply: emul1_eq0 (eq_sym E).
- move/part: n0.
  rewrite Z.add_simpl_r (above (top + count h e1 - count h e2)%Z); last by lia.
  by rewrite emul_empty_l => E; apply: ntop; apply: emul1_eq0 E.
Qed.

(** ** Degree 0 by size and by freshness *)

Lemma hhom_log_small h g t : tsize t ≤ tsize h → hhom h 0 (log g t).
Proof.
move=> le m /SMS.elem_of_bind [u [u_t]].
case: (bool_decide (base u = g));
  last by rewrite SMS.elem_of_count SMS.count_empty.
by move=> /SMS.elem_of_singleton ->; exact: count_expo_gfactors_big u_t le.
Qed.

Lemma hhom_log_fresh n h g t :
  subterm n h → ¬ subterm n t → hhom h 0 (log g t).
Proof.
move=> n_h n_t m /SMS.elem_of_bind [u [u_t]].
case: (bool_decide (base u = g));
  last by rewrite SMS.elem_of_count SMS.count_empty.
move=> /SMS.elem_of_singleton ->; apply: not_elem_of_count => h_u; apply: n_t.
apply: (subterm_gfactors u_t); transitivity h => //.
exact: subterm_exps h_u.
Qed.
