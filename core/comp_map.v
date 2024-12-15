From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map.
From iris.algebra Require Import excl csum view.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib core.term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CompromisedMap.

Implicit Types n m : nat.

Definition comp_map_authT : Type :=
  nat
  * gmap nat (gset term)
  * gset (nat * term).

Definition comp_map_fragT : Type :=
  option (dfrac * agree nat)
  * gmap nat (gset term)
  * gset (nat * term).

Implicit Types (a : comp_map_authT) (b : comp_map_fragT).

Definition wf_comp_map a :=
  let '(n, H, C) := a in
  (∀ m, m ∈ dom H → m ≤ n) ∧
  (∀ p, p ∈ C → p.1 ≤ n) ∧
  (∀ m1 T1 m2 t2,
      H !! m1 = Some T1 →
      (m2, t2) ∈ C →
      m2 ≤ m1 →
      t2 ∉ T1).

Definition to_comp_map_auth a :=
  let '(n, H, C) := a in
  (Some (to_agree n), H, C).

Definition to_comp_map_frag b :=
  let '(n, H, C) := b in
  (snd <$> n, H, C).

Definition comp_map_frac b :=
  let '(n, H, C) := b in
  fst <$> n.

Definition comp_map_view_rel_raw n a b : Prop :=
  wf_comp_map a ∧
  ✓ comp_map_frac b ∧
  to_comp_map_frag b ≼ to_comp_map_auth a.

Lemma to_comp_map_auth_valid a : ✓ to_comp_map_auth a.
Proof.
case: a => [[] ???] /=; split=> //; split=> //=.
by move=> n; case: (_ !! n) => //.
Qed.
Hint Resolve to_comp_map_auth_valid : core.

Lemma comp_map_frag_valid b :
  ✓ comp_map_frac b → ✓ to_comp_map_frag b → ✓ b.
Proof.
case: b => [[] bn bH bC] /= val_frac [[] /= val_n val_H val_C].
do ![split => //=].
by case: bn => [[dq n]|] //= in val_frac val_n *.
Qed.

Lemma comp_map_frac_included b1 b2 :
  b1 ≼ b2 →
  comp_map_frac b1 ≼ comp_map_frac b2.
Proof.
case: b1 b2 => [[] n1 H1 C1] [[] n2 H2 C2].
rewrite /comp_map_frac !pair_included; case=> [[] incl_n _ _].
case/option_included: incl_n => [->|[[dq1 m1] [] [dq2 m2] [] -> [] ->]] //=.
  exact: ucmra_unit_least.
rewrite pair_included; case => [[/= -> _]|[incl_dq _]] //.
exact: Some_included_mono.
Qed.

Lemma to_comp_map_frag_included b1 b2 :
  b1 ≼ b2 →
  to_comp_map_frag b1 ≼ to_comp_map_frag b2.
Proof.
case: b1 b2 => [[] n1 H1 C1] [[] n2 H2 C2].
rewrite /to_comp_map_frag !pair_included; case=> [[] incl_n incl_H incl_C].
do ![split => //].
case: n1 => [[dq1 n1]|] //= in incl_n *; last exact: ucmra_unit_least.
case: n2 => [[dq2 n2]|] //= in incl_n *.
- by case/Some_pair_included: incl_n.
- case: incl_n => [[?|] H]; inversion H.
Qed.

Lemma comp_map_view_rel_raw_mono n1 n2 a1 a2 b1 b2 :
  comp_map_view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  n2 ≤ n1 →
  comp_map_view_rel_raw n2 a2 b2.
Proof.
case=> [wf_a1 [] val_frac incl_1] /discrete_iff /leibniz_equiv_iff <- {a2}.
move=> /cmra_discrete_included_iff b2_b1 n2_n1.
split => //; split.
- move/comp_map_frac_included: b2_b1; exact: cmra_valid_included.
- trans (to_comp_map_frag b1) => //.
  exact: to_comp_map_frag_included.
Qed.

Lemma comp_map_view_rel_raw_valid n a b :
  comp_map_view_rel_raw n a b → ✓{n} b.
Proof.
case=> [wf_a [] val_dq incl].
apply/cmra_discrete_valid_iff.
apply/comp_map_frag_valid => //.
exact: cmra_valid_included incl.
Qed.

Lemma comp_map_view_rel_raw_unit n : ∃ a, comp_map_view_rel_raw n a ε.
Proof.
exists (0, ∅, ∅); split => //; split => //.
exact: ucmra_unit_least.
Qed.

Canonical comp_map_view_rel :=
  ViewRel comp_map_view_rel_raw
          comp_map_view_rel_raw_mono
          comp_map_view_rel_raw_valid
          comp_map_view_rel_raw_unit.

Global Instance comp_map_view_rel_discrete :
  ViewRelDiscrete comp_map_view_rel.
Proof. move=> ? ? ?; exact. Qed.

End CompromisedMap.

Notation comp_map := (view comp_map_view_rel_raw).
Definition comp_mapO : ofe := viewO comp_map_view_rel_raw.
Definition comp_mapR : cmra := viewR comp_map_view_rel.
Definition comp_mapUR : ucmra := viewUR comp_map_view_rel.

Definition comp_map_auth n HC : comp_map :=
  ●V (n, HC.1, HC.2).

Definition comp_map_frag an HC : comp_map :=
  ◯V ((λ '(dq, n), (dq, to_agree n)) <$> an,
      HC.1,
      HC.2).

Global Typeclasses Opaque comp_map_auth comp_map_frag.

Notation "●CM{ n } a" :=
  (comp_map_auth n a)
  (at level 20, format "●CM{ n }  a").
Notation "◯CM{ dq | n } a" :=
  (comp_map_frag (Some (dq, n)) a)
  (at level 20, format "◯CM{ dq | n }  a").
Notation "◯CM{ n } a" :=
  (comp_map_frag (Some (DfracOwn 1, n)) a)
  (at level 20, format "◯CM{ n }  a").
Notation "◯CM{# q | n } a" :=
  (comp_map_frag (Some (DfracOwn q, n)) a)
  (at level 20, format "◯CM{# q | n }  a").
Notation "◯CM□{ n } a" :=
  (comp_map_frag (Some (DfracDiscarded, n)) a)
  (at level 20, format "◯CM□{ n }  a").
Notation "◯CM a" :=
  (comp_map_frag None a)
  (at level 20, format "◯CM  a").

Lemma comp_map_frag_pcore q n HC :
  pcore (◯CM{# q | n} HC) ≡ Some (◯CM HC).
Proof.
rewrite /comp_map_frag view.view_pcore_eq /=.
rewrite !core_id_core !pair_core /= !core_id_core.
by rewrite /core /= pair_pcore /=.
Qed.

Lemma comp_map_frag_op an HC1 HC2 :
  comp_map_frag an (HC1 ⋅ HC2) ≡
  comp_map_frag an HC1 ⋅ comp_map_frag None HC2.
Proof.
rewrite /comp_map_frag /= -view_frag_op -!pair_op.
by rewrite !ucmra_unit_right_id.
Qed.

Lemma comp_map_frag_split an HC :
  comp_map_frag an HC ≡
  comp_map_frag an HC ⋅ comp_map_frag None HC.
Proof.
rewrite {1}(_ : HC = HC ⋅ HC) ?comp_map_frag_op //.
case: HC => H C.
rewrite -pair_op gset_op union_idemp_L -(_ : H = H ⋅ H) //.
rewrite -leibniz_equiv_iff => n.
rewrite lookup_op; case: (H !! n) => // ?.
by rewrite -Some_op gset_op union_idemp_L.
Qed.

Lemma comp_map_frag_split_empty dq n HC :
  ◯CM{dq|n} HC ≡ ◯CM{dq|n} (∅, ∅) ⋅ ◯CM HC.
Proof.
rewrite /comp_map_frag /= -view_frag_op -!pair_op.
by rewrite !ucmra_unit_left_id ucmra_unit_right_id.
Qed.

Lemma comp_map_frag_dfrac_op dq1 dq2 n HC :
  ◯CM{dq1 ⋅ dq2|n} HC ≡ ◯CM{dq1|n} HC ⋅ ◯CM{dq2|n} HC.
Proof.
rewrite /comp_map_frag /= -view_frag_op -!pair_op -Some_op -pair_op.
rewrite agree_idemp gset_op union_idemp.
set H := HC.1; assert (H ⋅ H ≡ H) as -> => //.
move=> m; rewrite lookup_op; case: (H !! m) => [a|] //.
by rewrite -Some_op gset_op union_idemp.
Qed.

Global Instance comp_map_frag_dfrac_is_op dq dq1 dq2 n HC :
  IsOp dq dq1 dq2 →
  IsOp' (◯CM{dq|n} HC) (◯CM{dq1|n} HC) (◯CM{dq2|n} HC).
Proof.
by move=> ->; rewrite /IsOp' /IsOp comp_map_frag_dfrac_op.
Qed.

Global Instance comp_map_frag_core_id HC : CoreId (◯CM HC).
Proof. rewrite /comp_map_frag. apply _. Qed.

Global Instance comp_map_frag_disc_core_id n HC : CoreId (◯CM□{n} HC).
Proof. rewrite /comp_map_frag. apply _. Qed.

Lemma comp_map_auth_frag_bound_agree an aH aC bdq bn bH bC :
  ✓ (●CM{an} (aH, aC) ⋅ ◯CM{bdq|bn} (bH, bC)) →
  an = bn.
Proof.
move=> /view_both_dfrac_valid /= [_ /(_ 0) val].
case: val => [wf_a [] val_adq incl_a_b].
rewrite !pair_included in incl_a_b.
case: incl_a_b => [[] /= incl_a_b _ _]; move: incl_a_b.
by rewrite Some_included_total to_agree_included leibniz_equiv_iff => ->.
Qed.

Lemma comp_map_frag_bound_agree dq1 dq2 n1 n2 HC1 HC2:
  ✓ (◯CM{dq1|n1} HC1 ⋅ ◯CM{dq2|n2} HC2) →
  n1 = n2.
Proof.
rewrite /comp_map_frag /= -view_frag_op -!pair_op -Some_op -pair_op.
case/view_frag_valid/(_ 0) => - [[] an aH aC] [wf_a [] val_dq incl_a_b].
move: incl_a_b; rewrite !pair_included /= Some_included_total.
case=> [[] incl_n _ _]; apply: to_agree_op_inv_L.
exact: cmra_valid_included incl_n.
Qed.

Lemma comp_map_frag_valid_wf dq n HC H C :
  ✓ (◯CM{dq|n} HC ⋅ ◯CM (H, C)) →
  (∀ m, m ∈ dom H → m ≤ n) ∧
  (∀ p, p ∈ C → p.1 ≤ n).
Proof.
rewrite -comp_map_frag_op /comp_map_frag /=.
case/view_frag_valid/(_ 0) => - [[] an aH aC] [wf_a [] val_dq incl_a_b].
move: incl_a_b; rewrite !pair_included /= Some_included_total.
rewrite to_agree_included leibniz_equiv_iff; case=> [[] -> incl_H incl_C].
have {}incl_H: H ≼ aH by trans (HC.1 ⋅ H).
have {}incl_C: C ≼ aC by trans (HC.2 ⋅ C).
case: wf_a => [bound_H [] bound_C ?].
split.
- move/dom_included: incl_H => incl_H m /incl_H.
  exact: bound_H.
- move/gset_included: incl_C => incl_C p /incl_C.
  exact: bound_C.
Qed.

Lemma comp_map_auth_valid_dis n H C :
  ✓ (●CM{n} (H, C)) →
  wf_comp_map (n, H, C).
Proof. by case/view_auth_valid/(_ 0). Qed.

Lemma comp_map_frag_valid_dis H C :
  ✓ (◯CM (H, ∅) ⋅ ◯CM (∅, C)) →
  ∀ m T n t,
    H !! m = Some T →
    (n, t) ∈ C →
    n ≤ m →
    t ∉ T.
Proof.
rewrite /comp_map_frag /= -view_frag_op -!pair_op.
rewrite !ucmra_unit_right_id ucmra_unit_left_id.
case/view_frag_valid/(_ 0) => - [[] an aH aC] [wf_a [] val_dq incl_a_b].
move: incl_a_b; rewrite !pair_included /=; case=> [[] _ incl_H incl_C].
case: wf_a => [bound_H [] bound_C dis].
move=> m T n t H_T t_C.
move/lookup_included/(_ m): incl_H; rewrite H_T /=.
case aH_m: (aH !! m) => [T'|] /=; last first.
  case/option_included_total => //.
  by case=> [? [] ? [] ? [] ?].
move/Some_included_total/gset_included => T_T' n_m /T_T' t_T'.
by apply: dis n_m t_T' => //; move/gset_included: incl_C; apply.
Qed.

Lemma comp_map_auth_frag_valid_agree n H C m T :
  ✓ (●CM{n} (H, C) ⋅ ◯CM ({[m := T]}, ∅)) →
  ∃ T', H !! m = Some T' ∧ T ⊆ T'.
Proof.
rewrite /comp_map_auth /comp_map_frag /=.
case/view_both_valid/(_ 0)=> [_ [] _].
rewrite !pair_included; case=> [[] _ /lookup_included/(_ m) incl_H _].
rewrite lookup_singleton /= in incl_H.
case/option_included_total: incl_H=> //= - [_ [] T' [] [<-] [] H_m T_T'].
by exists T'; split => //; apply/gset_included.
Qed.

Lemma comp_map_honest_update an aH aC bn bH HC :
  (∀ m t, (m, t) ∈ aC → t ∉ bH) →
  ●CM{an} (aH, aC) ⋅ ◯CM{bn} HC  ~~>
  ●CM{S an} (<[S an := bH]> aH, aC) ⋅ ◯CM{S bn} ({[S bn := bH]}, ∅).
Proof.
move=> dis_a_b.
apply: cmra_update_valid0.
move=> /cmra_discrete_valid/comp_map_auth_frag_bound_agree <- {bn}.
apply: view_update => /=.
rewrite /comp_map_view_rel_raw /= => _ [[] bf_n bf_H bf_C].
case=> [wf_a1 [] val_dq incl_a1_b1].
case: wf_a1 => [bound_aH [] bound_aC aH_aC].
do ![split => //].
- move=> m; rewrite dom_insert_L elem_of_union elem_of_singleton.
  case=> [-> //|/bound_aH m_aH]; lia.
- move=> p /bound_aC p_aC; lia.
- move=> m1 T1 m2 t2.
  case: (decide (m1 = S an)) => [-> {m1}|neq].
  + rewrite lookup_insert; case => <- {T1}.
    by move=> /dis_a_b.
  + rewrite lookup_insert_ne //; exact: aH_aC.
- rewrite /= in val_dq *.
  by case: (bf_n) => [[??]|] /= in val_dq *.
- move: incl_a1_b1; rewrite !pair_included /=.
  case => [[] /= incl_n incl_H incl_C].
  have e : bf_n = None.
    case: (bf_n) => [[dq n]|] //= in val_dq *.
    by case/exclusive_l: val_dq.
  subst bf_n; rewrite !ucmra_unit_right_id in incl_n *.
  have {}incl_C : bf_C ≼ aC by trans (HC.2 ⋅ bf_C).
  rewrite ucmra_unit_left_id. do ![split => //].
  have {}incl_H : bf_H ≼ aH by trans (HC.1 ⋅ bf_H).
  rewrite lookup_included in incl_H.
  rewrite lookup_included => n.
  rewrite lookup_op.
  case: (decide (n = S an)) => [-> {n}|neq].
  + rewrite lookup_singleton lookup_insert.
    move/(_ (S an)): incl_H; case bf_H__an: (bf_H !! S an) => [p|//].
    case/option_included => // - [? [] q [] [->] [] contra ?].
    suff: S an ≤ an by lia.
    apply: bound_aH. by rewrite elem_of_dom contra.
  + rewrite lookup_singleton_ne // lookup_insert_ne // ucmra_unit_left_id.
    exact: incl_H.
Qed.

Lemma comp_map_comp_update an aH aC bdq bn n t :
  n ≤ bn →
  (∀ m T, n ≤ m ≤ bn → aH !! m = Some T → t ∉ T) →
  ●CM{an} (aH, aC) ⋅ ◯CM{bdq|bn} (∅, ∅) ~~>
  ●CM{an} (aH, {[(n, t)]} ∪ aC) ⋅ ◯CM{bdq|bn} (∅, {[(n, t)]}).
Proof.
move=> n_an dis_a_b; apply: cmra_update_valid0.
move => /cmra_discrete_valid/comp_map_auth_frag_bound_agree -> {an}.
apply: view_update => /=.
rewrite /comp_map_view_rel_raw /= => _ [[] bf_n bf_H bf_C].
case=> [wf_a1 [] /= val_bdq incl_a1_b1].
case: wf_a1 => [bound_aH [] bound_aC aH_aC].
do ![split => //].
- move=> p; rewrite elem_of_union elem_of_singleton.
  case=> [-> //|]; apply: bound_aC.
- move=> m1 T1 m2 t2 aH_m1.
  rewrite elem_of_union elem_of_singleton.
  case => [[-> ->]|m2_t2_aC]; last by eauto.
  move=> n_m1; suff ?: m1 ≤ bn by apply: dis_a_b aH_m1; lia.
  by apply: bound_aH; rewrite elem_of_dom aH_m1.
- move: incl_a1_b1; rewrite !pair_included /=.
  case => [[] incl_n incl_H incl_C].
  split=> //. 
  rewrite gset_included gset_op.
  rewrite ucmra_unit_left_id gset_included in incl_C.
  set_solver.
Qed.

Lemma comp_map_comp_update_last n H T C t :
  H !! n = Some T →
  t ∉ T →
  ●CM{n} (H, C) ~~>
  ●CM{n} (H, {[(n, t)]} ∪ C) ⋅ ◯CM (∅, {[(n, t)]}).
Proof.
move=> H_n t_T; apply: view_update_alloc.
rewrite /= /comp_map_view_rel_raw => _ [[] bf_n bf_H bf_C].
case=> [wf_a [] /= val_dq incl_a_b].
case: wf_a => [bound_H [] bound_C H_C].
do ![split => //].
- move=> p; rewrite elem_of_union elem_of_singleton.
  case=> [-> //|]; apply: bound_C.
- move=> m1 T1 m2 t2 H_m1.
  rewrite elem_of_union elem_of_singleton.
  case=> [[-> ->]|m2_t2_C]; last by eauto.
  move=> n_m1.
  have ?: m1 ≤ n by apply: bound_H; rewrite elem_of_dom H_m1.
  have ?: m1 = n by lia. subst m1.
  by rewrite H_n in H_m1; case: H_m1 => <-.
- by rewrite ucmra_unit_left_id.
- move: incl_a_b; rewrite !pair_included /=.
  case=> [[] incl_n incl_H incl_C].
  rewrite ucmra_unit_left_id gset_op ucmra_unit_left_id.
  split => //.
  rewrite gset_included in incl_C. rewrite gset_included. set_solver.
Qed.

Lemma comp_map_frag_discard dq n HC :
  ◯CM{dq|n} HC ~~> ◯CM□{n} HC.
Proof.
apply/view_update_frag; case=> [[] an aH aC].
rewrite /= /comp_map_view_rel_raw => _.
case=> [[] bf_n bf_H bf_C] [wf_a [] /= val_adq incl_a_b].
split=> //.
rewrite !pair_included in incl_a_b *.
case: incl_a_b => [[] incl_n incl_H incl_C].
case: bf_n => [[dq' n']|] /= in val_adq incl_n *; last by do ![split => //].
do ![split => //]. rewrite !Some_valid in val_adq *.
case: dq' => [q'| |q'] //= in val_adq *.
- rewrite (comm op). apply/dfrac_valid_own_discarded.
  by move/dfrac_valid_own_r: val_adq.
- by move/cmra_valid_op_r: val_adq.
Qed.
