From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map.
From iris.algebra Require Import excl csum view.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term.

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
  * gmap nat (agree (gset term))
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

Definition to_comp_map a : comp_map_fragT :=
  let '(n, H, C) := a in
  (Some (DfracOwn 1, to_agree n), to_agree <$> H, C).

Definition comp_map_view_rel_raw n a b : Prop :=
  wf_comp_map a ∧ b ≼ to_comp_map a.

Lemma to_comp_map_valid a : ✓ to_comp_map a.
Proof.
case: a => [[] ???] /=; split=> //; split=> //=.
by move=> n; rewrite lookup_fmap; case: lookup=> [?|].
Qed.
Hint Resolve to_comp_map_valid : core.

Lemma comp_map_view_rel_raw_mono n1 n2 a1 a2 b1 b2 :
  comp_map_view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  n2 ≤ n1 →
  comp_map_view_rel_raw n2 a2 b2.
Proof.
case=> wf_a1 incl_1 /discrete_iff /leibniz_equiv_iff <- {a2}.
move=> /cmra_discrete_included_iff b2_b1 n2_n1.
split=> //. by trans b1.
Qed.

Lemma comp_map_view_rel_raw_valid n a b :
  comp_map_view_rel_raw n a b → ✓{n} b.
Proof.
case=> wf_a incl.
apply/cmra_discrete_valid_iff.
exact: cmra_valid_included incl.
Qed.

Lemma comp_map_view_rel_raw_unit n : ∃ a, comp_map_view_rel_raw n a ε.
Proof.
exists (0, ∅, ∅); split => //; exact: ucmra_unit_least.
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

Definition comp_map_auth dq n HC : comp_map :=
  ●V{dq} (n, HC.1, HC.2).

Definition comp_map_frag an HC : comp_map :=
  ◯V ((λ '(dq, n), (dq, to_agree n)) <$> an,
      to_agree <$> HC.1,
      HC.2).

Notation "●CM{ dq | n } a" :=
  (comp_map_auth dq n a)
  (at level 20, format "●CM{ dq | n }  a").
Notation "●CM{ n } a" :=
  (comp_map_auth (DfracOwn 1) n a)
  (at level 20, format "●CM{ n }  a").
Notation "●CM{# q | n } a" :=
  (comp_map_auth (DfracOwn q) n a)
  (at level 20, format "●CM{# q | n }  a").
Notation "●CM□{ n } a" :=
  (comp_map_auth DfracDiscarded n a)
  (at level 20, format "●CM□{ n }  a").
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

Lemma comp_map_valid_bound adq an aH aC bdq bn bH bC :
  ✓ (●CM{adq|an} (aH, aC) ⋅ ◯CM{bdq|bn} (bH, bC)) →
  an = bn.
Proof.
move=> /view_both_dfrac_valid /= [_ /(_ 0) val].
case: val => _ incl_a_b.
rewrite !pair_included in incl_a_b.
case: incl_a_b => [[] incl_a_b _ _].
case/Some_pair_included: incl_a_b => _.
by rewrite Some_included_total to_agree_included leibniz_equiv_iff => ->.
Qed.

Lemma comp_map_honest_update an aH aC bn bH :
  (∀ m t, (m, t) ∈ aC → t ∉ bH) →
  ●CM{an} (aH, aC) ⋅ ◯CM{bn} (∅, ∅) ~~>
  ●CM{S an} (<[S an := bH]> aH, aC) ⋅ ◯CM{S bn} ({[S bn := bH]}, ∅).
Proof.
move=> dis_a_b.
apply: cmra_update_valid0 => /cmra_discrete_valid/comp_map_valid_bound <- {bn}.
apply: view_update => /=.
rewrite /comp_map_view_rel_raw /= => _ [[] bf_n bf_H bf_C].
case=> [wf_a1 incl_a1_b1].
case: wf_a1 => [bound_aH [] bound_aC aH_aC].
do !split.
- move=> m; rewrite dom_insert_L elem_of_union elem_of_singleton.
  case=> [-> //|/bound_aH m_aH]; lia.
- move=> p /bound_aC p_aC; lia.
- move=> m1 T1 m2 t2.
  case: (decide (m1 = S an)) => [-> {m1}|neq].
  + rewrite lookup_insert; case => <- {T1}.
    by move=> /dis_a_b.
  + rewrite lookup_insert_ne //; exact: aH_aC.
- move: incl_a1_b1; rewrite !pair_included /=.
  case => [[] incl_n incl_H incl_C].
  have {incl_n} ->: bf_n = None.
    case: bf_n => [[bf_dq bf_n]|//] in incl_n *.
    rewrite -Some_op -pair_op Some_included pair_included in incl_n.
    case: incl_n => [[/= contra _]|[/= contra _]].
    + suff [] : False; by exact: id_free_r contra.
    + have /exclusive_l [] : ✓ (DfracOwn 1 ⋅ bf_dq).
      exact: cmra_valid_included contra.
  rewrite ucmra_unit_right_id; split => //; split => //.
  rewrite fmap_empty ucmra_unit_left_id lookup_included in incl_H.
  rewrite map_fmap_singleton fmap_insert lookup_included => n.
  rewrite lookup_op.
  case: (decide (n = S an)) => [-> {n}|neq].
  + rewrite -> lookup_singleton, lookup_insert.
    move/(_ (S an)): incl_H; case bf_H__an: (bf_H !! S an) => [p|//].
    case/option_included => // - [? [] q [] [->] [] contra ?].
    suff: S an ≤ an by lia.
    apply: bound_aH.
    have: S an ∈ dom (to_agree <$> aH) by rewrite elem_of_dom contra.
    by rewrite dom_fmap.
  + rewrite lookup_singleton_ne // lookup_insert_ne // ucmra_unit_left_id.
    exact: incl_H.
Qed.

Lemma comp_map_comp_update an aH aC bdq bn n t :
  n ≤ bn →
  (∀ m T, n ≤ m ≤ bn → aH !! m = Some T → t ∉ T) →
  ●CM{an} (aH, aC) ⋅ ◯CM{bdq|bn} (∅, ∅) ~~>
  ●CM{an} (aH, {[(n, t)]} ∪ aC) ⋅ ◯CM{bdq|bn} (∅, {[(n, t)]}).
Proof.
move=> n_an dis_a_b.
apply: cmra_update_valid0 => /cmra_discrete_valid/comp_map_valid_bound e.
rewrite -{}e {bn} in n_an dis_a_b *.
apply: view_update => /=.
rewrite /comp_map_view_rel_raw /= => _ [[] bf_n bf_H bf_C].
case=> [wf_a1 incl_a1_b1].
case: wf_a1 => [bound_aH [] bound_aC aH_aC].
do ![split => //].
- move=> p; rewrite elem_of_union elem_of_singleton.
  case=> [-> //|]; apply: bound_aC.
- move=> m1 T1 m2 t2 aH_m1.
  rewrite elem_of_union elem_of_singleton.
  case => [[-> ->]|m2_t2_aC]; last by eauto.
  move=> n_m1; suff ?: m1 ≤ an by apply: dis_a_b aH_m1; lia.
  by apply: bound_aH; rewrite elem_of_dom aH_m1.
- move: incl_a1_b1; rewrite !pair_included /=.
  case => [[] incl_n incl_H incl_C].
  rewrite gset_included gset_op.
  rewrite ucmra_unit_left_id gset_included in incl_C.
  split; last by set_solver.
  by split.
Qed.
