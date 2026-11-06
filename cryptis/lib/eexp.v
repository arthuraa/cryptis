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

    Equations between terms become equations between their logarithms.
    [ehom h k s] says that every monomial of [s] has exactly [k] occurrences
    of [h]; [k = 0] means independence of [h]. Parts with different counts
    can be compared separately ([ehom_split]). A term's logarithms are
    independent of atoms too large to occur in its exponents, or containing
    a fresh subterm ([ehom_log_small], [ehom_log_fresh]).

    For HMQV, the remaining algebraic step is [emul_linear]: an independent
    remainder cannot be a multiple of [h*u-v]. Substituting [h := v/u]
    annihilates the factor, and a highest monomial proves cancellation.
    The same finite-support argument gives cancellation of a binomial
    ([emul_binomial_eq0]). General products also have no zero divisors
    ([emul_neq0]), so a nonzero sum can be cancelled ([emul_injr]) and
    raising to it is injective in the base ([epow_injl]). *)

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

Lemma emul_empty_r s : emul s ∅ = ∅.
Proof. exact: SMS.bind_empty. Qed.

Lemma emul_inv_r s r : emul s (SMS.inv r) = SMS.inv (emul s r).
Proof. exact: SMS.bind_inv. Qed.

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

(** ** Homogeneous parts and substitution

    A homogeneous sum: every monomial has exactly [k] occurrences of [h].
    In particular, [ehom h 0 s] says that [s] is independent of [h]. *)
Definition ehom h k s := ∀ m, m ∈ s → count h m = k.

Lemma ehom_empty h k : ehom h k ∅.
Proof. by move=> m /SMS.elem_of_count; rewrite SMS.count_empty. Qed.

Lemma ehom_singleton h k e : ehom h k {[+ e +]} ↔ count h e = k.
Proof.
split; first by move=> H; apply: H; apply/SMS.elem_of_singleton.
by move=> he m /SMS.elem_of_singleton ->.
Qed.

Lemma ehom_add h k s r : ehom h k s → ehom h k r → ehom h k (s ⊎ r).
Proof. by move=> hs hr m /SMS.elem_of_disj_union [/hs|/hr]. Qed.

Lemma ehom_emul h a b s r :
  ehom h a s → ehom h b r → ehom h (a + b) (emul s r).
Proof.
move=> hs hr m /SMS.elem_of_bind [e [e_r /SMS.elem_of_map [m' [-> m'_s]]]].
by rewrite count_TMul2 (hs _ m'_s) (hr _ e_r).
Qed.

Lemma ehom_count h k s m : ehom h k s → count h m ≠ k → SMS.count m s = 0%Z.
Proof. by move=> hs ne; apply: SMS.not_elem_of_count => /hs. Qed.

Lemma ehom_split h a b s1 s2 r1 r2 :
  ehom h a s1 → ehom h a r1 → ehom h b s2 → ehom h b r2 → a ≠ b →
  s1 ⊎ s2 = r1 ⊎ r2 → s2 = r2.
Proof.
move=> hs1 hr1 hs2 hr2 ab E; apply: SMS.count_inj => m.
move/(f_equal (SMS.count m)): E; rewrite !SMS.count_disj_union.
case: (decide (count h m = b)) => e.
- by rewrite (ehom_count hs1) ?(ehom_count hr1); lia.
- by rewrite (ehom_count hs2) ?(ehom_count hr2); lia.
Qed.

Lemma ehom_binomial_const h s r e0 e1 :
  ehom h 0 s → ehom h 0 r → count h e0 = 0%Z → count h e1 ≠ 0%Z →
  emul s {[+ e0; e1 +]} = r → s = ∅.
Proof.
move=> hs hr he0 he1 E; apply: (emul1_eq0 (e := e1)).
apply: (ehom_split (h := h) (a := 0%Z) (b := count h e1)
  (s1 := emul s {[+ e0 +]}) (r1 := r)).
- apply: (ehom_emul hs); by rewrite ehom_singleton.
- exact: hr.
- apply: (ehom_emul hs); by rewrite ehom_singleton.
- exact: ehom_empty.
- congruence.
- by rewrite -emul_disj_union_r E (right_id ∅ (⊎)).
Qed.

Lemma ehom_log h k g t :
  (∀ u, u ∈ gfactors t → count h (expo u) = k) → ehom h k (log g t).
Proof.
move=> H m /SMS.elem_of_bind [u [u_t]].
case: (bool_decide (base u = g));
  last by rewrite SMS.elem_of_count SMS.count_empty.
by move=> /SMS.elem_of_singleton ->; exact: H.
Qed.

Lemma ehom_log_small h t : tsize t ≤ tsize h → ∀ g, ehom h 0 (log g t).
Proof.
move=> le g; apply: ehom_log => u u_t.
exact: count_expo_gfactors_big u_t le.
Qed.

Arguments ehom_log_small {h t} _ g.

Lemma ehom_log_fresh n h t :
  subterm n h → ¬ subterm n t → ∀ g, ehom h 0 (log g t).
Proof.
move=> n_h n_t g; apply: ehom_log => u u_t.
apply: not_elem_of_count => h_u; apply: n_t.
apply: (subterm_gfactors u_t); transitivity h => //.
exact: subterm_exps h_u.
Qed.

Arguments ehom_log_fresh {n h t} _ _ g.

(** A highest monomial survives the larger of two shifts. *)
Lemma emul1_max h s :
  (∃ m, m ∈ s ∧ ∀ e1 e2, (count h e1 < count h e2)%Z →
    SMS.count (TMul {[+ m; e2 +]}) (emul s {[+ e1 +]}) = 0%Z) ∨ s = ∅.
Proof.
case: (SMS.max_or_empty (count h) s) => [[m [m_s hmax]]|->]; last by right.
left; exists m; split=> // e1 e2 lt.
rewrite count_emul1; apply: SMS.not_elem_of_count => /hmax.
by rewrite !count_TMul2 count_TInv; lia.
Qed.

Lemma emul_binomial_eq0 h s e1 e2 :
  count h e1 ≠ count h e2 → emul s {[+ e1; e2 +]} = ∅ → s = ∅.
Proof.
move=> ne E; case: (emul1_max h s) => [[m [m_s hmax]]|//].
have nz : SMS.count m s ≠ 0%Z by apply/SMS.elem_of_count.
rewrite emul_disj_union_r in E.
case: (Z.lt_total (count h e1) (count h e2)) => [lt|[//|lt]].
- move/(f_equal (SMS.count (TMul {[+ m; e2 +]}))): E.
  rewrite SMS.count_disj_union (hmax _ _ lt) count_emul1 TMulK SMS.count_empty; lia.
- move/(f_equal (SMS.count (TMul {[+ m; e1 +]}))): E.
  rewrite SMS.count_disj_union (hmax _ _ lt) count_emul1 TMulK SMS.count_empty; lia.
Qed.

Lemma emul1_apart h s e1 e2 :
  count h e1 ≠ count h e2 → emul s {[+ e1 +]} = emul s {[+ e2 +]} → s = ∅.
Proof.
move=> ne E; case: (emul1_max h s) => [[m [m_s hmax]]|//].
have nz : SMS.count m s ≠ 0%Z by apply/SMS.elem_of_count.
case: (Z.lt_total (count h e1) (count h e2)) => [lt|[//|lt]].
- move/(f_equal (SMS.count (TMul {[+ m; e2 +]}))): E.
  rewrite (hmax _ _ lt) count_emul1 TMulK; lia.
- move/(f_equal (SMS.count (TMul {[+ m; e1 +]}))): E.
  rewrite (hmax _ _ lt) count_emul1 TMulK; lia.
Qed.

(** Substitute an invertible monomial for one atom. Other atoms, including
    hashes containing that atom in their inputs, remain unchanged. *)
Definition msubst h u m :=
  TMul (SMS.map (λ a, if bool_decide (a = h) then u else a) (factors m)).

Definition esubst h u s := SMS.map (msubst h u) s.

Lemma msubst_mul h u e1 e2 :
  msubst h u (TMul {[+ e1; e2 +]}) = TMul {[+ msubst h u e1; msubst h u e2 +]}.
Proof.
by rewrite /msubst factors_TMul SMS.bind_disj_union !SMS.bind_singleton
  SMS.map_disj_union TMul_disj_union.
Qed.

Lemma msubst_diag h u : negb (is_mul h) → msubst h u h = u.
Proof.
move=> Nh; rewrite /msubst factors_Nmul // SMS.map_singleton.
by rewrite bool_decide_eq_true_2 // TMul_singleton.
Qed.

Lemma msubst_indep h u m : count h m = 0%Z → msubst h u m = m.
Proof.
move=> hm; rewrite /msubst -[RHS]factorsK; congr TMul.
apply: SMS.map_id_ext => a a_m; rewrite bool_decide_eq_false_2 // => e; subst a.
by move: a_m; rewrite -count_neq0 hm.
Qed.

Lemma esubst_indep h u s : ehom h 0 s → esubst h u s = s.
Proof. move=> hs; apply: SMS.map_id_ext => m /hs; exact: msubst_indep. Qed.

Lemma esubst_add h u s r : esubst h u (s ⊎ r) = esubst h u s ⊎ esubst h u r.
Proof. exact: SMS.map_disj_union. Qed.

Lemma esubst_emul1 h u s e :
  esubst h u (emul s {[+ e +]}) = emul (esubst h u s) {[+ msubst h u e +]}.
Proof.
rewrite /esubst !emul1 !SMS.map_map; apply: SMS.map_ext => m _.
exact: msubst_mul.
Qed.

(** An [h]-independent difference cannot be a multiple of [h*u-v].
    Substitute [h := v/u] to equate the remainders, then cancel the two
    distinct shifts using their highest monomial. *)
Lemma emul_linear h u v s r1 r2 :
  negb (is_mul h) → count h u = 0%Z → count h v = 0%Z →
  ehom h 0 r1 → ehom h 0 r2 →
  r1 ⊎ emul s {[+ TMul {[+ h; u +]} +]} = r2 ⊎ emul s {[+ v +]} → s = ∅.
Proof.
move=> Nh hu hv hr1 hr2 E.
set w := TMul {[+ v; TInv u +]}.
have sub : msubst h w (TMul {[+ h; u +]}) = v.
  rewrite msubst_mul msubst_diag // msubst_indep // /w.
  exact: TMulKV.
have er : r1 = r2.
  have := f_equal (esubst h w) E.
  rewrite !esubst_add !esubst_emul1 sub (msubst_indep _ hv)
    (esubst_indep _ hr1) (esubst_indep _ hr2) => E'.
  apply: SMS.count_inj => m; move/(f_equal (SMS.count m)): E'.
  rewrite !SMS.count_disj_union; lia.
apply: (emul1_apart (h := h) (e1 := TMul {[+ h; u +]}) (e2 := v)).
- by rewrite count_TMul2 count_atom_diag // hu hv; lia.
- apply: SMS.count_inj => m; move/(f_equal (SMS.count m)): E.
  rewrite er !SMS.count_disj_union; lia.
Qed.

(** ** Cancellation of general products

    A nonzero product has a surviving highest part in each atom. We only
    select an actual monomial attaining the maximum; no degree intervals
    are needed. *)

#[local] Definition dpart h k s : eexp := SMS.filter (λ m, count h m = k) s.

#[local] Lemma count_dpart h k s m :
  SMS.count m (dpart h k s)
  = if bool_decide (count h m = k) then SMS.count m s else 0%Z.
Proof. by rewrite /dpart SMS.count_filter. Qed.

#[local] Lemma elem_of_dpart h k s m :
  m ∈ dpart h k s ↔ m ∈ s ∧ count h m = k.
Proof.
rewrite !SMS.elem_of_count count_dpart.
case: (bool_decide_reflect (count h m = k)) => H; first tauto.
by split=> [/(_ eq_refl)|[_ /H]].
Qed.

#[local] Lemma dpart_neq0 h k s m : m ∈ s → count h m = k → dpart h k s ≠ ∅.
Proof.
move=> m_s e /(f_equal (SMS.count m)).
rewrite count_dpart bool_decide_eq_true_2 // SMS.count_empty.
by move: m_s; rewrite SMS.elem_of_count.
Qed.

#[local] Lemma dpart_empty h k : dpart h k ∅ = ∅.
Proof. exact: SMS.bind_empty. Qed.

#[local] Lemma dpart_bind h k (f : term → eexp) r :
  dpart h k (SMS.bind f r) = SMS.bind (λ e, dpart h k (f e)) r.
Proof. by rewrite /dpart /SMS.filter SMS.bind_bind. Qed.

#[local] Lemma bind_dpart h k (f : term → eexp) r :
  SMS.bind f (dpart h k r)
  = SMS.bind (λ e, if bool_decide (count h e = k) then f e else ∅) r.
Proof.
rewrite /dpart /SMS.filter SMS.bind_bind; apply: SMS.bind_ext => e _.
by case: bool_decide; rewrite ?SMS.bind_singleton ?SMS.bind_empty.
Qed.

#[local] Lemma dpart_emul1 h k s e :
  dpart h k (emul s {[+ e +]}) = emul (dpart h (k - count h e) s) {[+ e +]}.
Proof.
apply: SMS.count_inj => m; rewrite count_dpart !count_emul1 count_dpart.
rewrite count_TMul2 count_TInv.
case: (bool_decide_reflect (count h m = k)) => ?;
  case: (bool_decide_reflect (_ = _)) => ? //; lia.
Qed.

#[local] Lemma dpart_emul h a b s r :
  (∀ m e, m ∈ s → e ∈ r → count h m + count h e = a + b → count h e = b)%Z →
  dpart h (a + b) (emul s r) = emul (dpart h a s) (dpart h b r).
Proof.
move=> uniq; rewrite {1}/emul dpart_bind [RHS]/emul bind_dpart.
apply: SMS.bind_ext => e e_r; rewrite -!emul1 dpart_emul1.
case: (bool_decide_reflect (count h e = b)) => [<-|ne].
  by rewrite Z.add_simpl_r.
rewrite -[RHS](emul_empty_l {[+ e +]}); congr emul.
apply: SMS.count_inj => m; rewrite count_dpart SMS.count_empty.
case: (bool_decide_reflect (_ = _)) => // c.
by apply: SMS.not_elem_of_count => m_s; apply: ne; apply: uniq m_s e_r _; lia.
Qed.

#[local] Lemma count_emul_mono s r m e :
  (∀ m', m' ∈ s → m' = m) →
  SMS.count (TMul {[+ m; e +]}) (emul s r) = (SMS.count m s * SMS.count e r)%Z.
Proof.
move=> Hs.
have key x : SMS.count (TMul {[+ m; e +]}) (emul s {[+ x +]})
             = (SMS.count m s * SMS.count e {[+ x +]})%Z.
  rewrite count_emul1 SMS.count_singleton.
  case: (bool_decide_reflect (e = x)) => [<-|ne] /=.
    by rewrite TMulK Z.mul_1_r.
  rewrite Z.mul_0_r; apply: SMS.not_elem_of_count => /Hs E; apply: ne.
  apply: count_inj => y _; move/(f_equal (count y)): E.
  rewrite !count_TMul2 count_TInv; lia.
elim/(SMS.sms_ind (T := term)): r => [|x r IH|x r IH].
- by rewrite emul_empty_r !SMS.count_empty Z.mul_0_r.
- by rewrite emul_disj_union_r !SMS.count_disj_union key IH; ring.
- rewrite emul_disj_union_r emul_inv_r !SMS.count_disj_union !SMS.count_inv.
  by rewrite key IH; ring.
Qed.

#[local] Lemma sms_witness s : s ≠ ∅ → ∃ m, m ∈ s.
Proof.
move=> ns; destruct (elements s) as [|m l] eqn:E.
  by case: ns; exact: SMS.elements_empty_inv.
by exists m; rewrite -SMS.elem_of_elements E; left.
Qed.

(* The monomials of [s] have the same number of occurrences of every atom
   outside of [L]. *)
#[local] Definition agree (L : list term) s :=
  ∀ m1 m2 a, m1 ∈ s → m2 ∈ s → negb (is_mul a) → a ∉ L →
    count a m1 = count a m2.

#[local] Lemma agree_dpart a L k s : agree (a :: L) s → agree L (dpart a k s).
Proof.
move=> hs m1 m2 x /elem_of_dpart [m1_s e1] /elem_of_dpart [m2_s e2] Nx xL.
case: (decide (x = a)) => [->|xa]; first lia.
by apply: hs => //; case/elem_of_cons.
Qed.

(* Induction on the atoms [L] in which monomials may differ: the highest parts
   in the first atom have one atom less to differ in. *)
#[local] Lemma emul_neq0_agree L s r :
  agree L s → agree L r → s ≠ ∅ → r ≠ ∅ → emul s r ≠ ∅.
Proof.
elim: L s r => [|a L IH] s r hs hr ns nr.
  have [m m_s] := sms_witness ns; have [e e_r] := sms_witness nr.
  have Hs m' : m' ∈ s → m' = m.
    move=> m'_s; apply: count_inj => x Nx.
    exact: hs _ _ _ m'_s m_s Nx (not_elem_of_nil x).
  move=> /(f_equal (SMS.count (TMul {[+ m; e +]}))).
  rewrite count_emul_mono // SMS.count_empty.
  by move: m_s e_r; rewrite !SMS.elem_of_count; nia.
case: (SMS.max_or_empty (count a) s) => [[ms [ms_s hsmax]]|//].
case: (SMS.max_or_empty (count a) r) => [[mr [mr_r hrmax]]|//].
move=> E.
apply: (IH (dpart a (count a ms) s) (dpart a (count a mr) r)).
- exact: agree_dpart.
- exact: agree_dpart.
- exact: dpart_neq0 ms_s eq_refl.
- exact: dpart_neq0 mr_r eq_refl.
rewrite -dpart_emul ?E ?dpart_empty //.
by move=> m e /hsmax ? /hrmax ?; lia.
Qed.

(** Extended exponents have no zero divisors. *)
Lemma emul_neq0 s r : s ≠ ∅ → r ≠ ∅ → emul s r ≠ ∅.
Proof.
set L := (elements s ++ elements r) ≫= λ m, elements (factors m).
have ag q : (∀ m, m ∈ q → m ∈ elements s ++ elements r) → agree L q.
  move=> sub m1 m2 a m1_q m2_q _ aL.
  have z m : m ∈ q → count a m = 0%Z.
    move=> m_q; apply: not_elem_of_count => a_m; apply: aL.
    by apply/list_elem_of_bind; exists m; split; last exact: sub.
  by rewrite !z.
move=> ns nr; apply: (emul_neq0_agree _ _ ns nr); apply: ag => m m_q;
  apply/elem_of_app; by [left|right].
Qed.

Lemma emul_injr s r1 r2 : s ≠ ∅ → emul s r1 = emul s r2 → r1 = r2.
Proof.
move=> ns E; apply: SMS.count_inj => m.
case: (decide (SMS.count m (r1 ⊎ SMS.inv r2) = 0%Z)) => [|nz].
  by rewrite SMS.count_disj_union SMS.count_inv; lia.
have nr : r1 ⊎ SMS.inv r2 ≠ ∅.
  by move=> E'; apply: nz; rewrite E' SMS.count_empty.
case: (emul_neq0 ns nr).
by rewrite emul_disj_union_r emul_inv_r E SMS.disj_union_inv_r.
Qed.

Lemma epow_injl s t1 t2 : s ≠ ∅ → epow t1 s = epow t2 s → t1 = t2.
Proof.
move=> ns E; apply: log_inj => g; apply: (emul_injr ns).
by rewrite !(emul_comm s) -!log_epow E.
Qed.
