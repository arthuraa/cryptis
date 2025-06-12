From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import cmra agree auth csum gset gmap excl frac.
From iris.algebra Require Import functions.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis.
From cryptis Require Import replica primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition db_stateUR : ucmra :=
  discrete_funUR (fun _ : term => authUR (optionUR (exclR (optionO termO)))).

Class dbGS Σ := DbGS {
  dbGS_state : inG Σ db_stateUR;
}.

Local Existing Instance dbGS_state.

Definition dbΣ :=
  #[GFunctor db_stateUR].

Global Instance subG_dbGS Σ : subG dbΣ Σ → dbGS Σ.
Proof. solve_inG. Qed.

Module DB.

Section DB.

Implicit Types db : gmap term term.
Implicit Types γ : gname.
Implicit Types N : namespace.
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types T : coGset term.

Context `{!cryptisGS Σ, !heapGS Σ, !dbGS Σ}.

Definition to_db_state db : db_stateUR :=
  λ t, ● (Excl' (db !! t)).

Definition db_singleton t1 t2 : db_stateUR :=
  discrete_fun_singleton t1 (◯ Excl' (Some t2)).

Definition db_free T : db_stateUR :=
  λ t, if decide (t ∈ T) then ◯ Excl' None else ◯ None.

Definition db_free_diff T1 T2 :
  T1 ⊆ T2 →
  db_free T2 ≡ db_free T1 ⋅ db_free (T2 ∖ T1).
Proof.
move=> sub x.
rewrite /db_free discrete_fun_lookup_op.
case: (decide (x ∈ T1)) => x_T1.
{ rewrite decide_True; try set_solver.
  rewrite decide_False //; set_solver. }
case: (decide (x ∈ T2)) => x_T2.
{ rewrite decide_True //; set_solver. }
rewrite decide_False //; set_solver.
Qed.

Lemma db_update db t1 t2 t2' :
  to_db_state db ⋅ db_singleton t1 t2 ~~>
  to_db_state (<[t1 := t2']> db) ⋅ db_singleton t1 t2'.
Proof.
apply/cmra_discrete_total_update=> db' valid t.
move/(_ t): valid.
rewrite !discrete_fun_lookup_op /to_db_state /db_singleton.
case: (decide (t = t1)) => [-> {t}|t_t1]; last first.
{ rewrite lookup_insert_ne // !discrete_fun_lookup_singleton_ne //. }
rewrite lookup_insert !discrete_fun_lookup_singleton //=.
move: (db' t1); apply/cmra_discrete_total_update.
apply: auth_update.
apply (transitivity (y := (None, None))).
- exact: delete_option_local_update.
- exact: alloc_option_local_update.
Qed.

Lemma db_alloc db t1 t2 :
  to_db_state db ⋅ db_free {[t1]} ~~>
  to_db_state (<[t1 := t2]> db) ⋅ db_singleton t1 t2.
Proof.
apply/cmra_discrete_total_update=> db' valid t.
move/(_ t): valid.
rewrite !discrete_fun_lookup_op /to_db_state /db_free /db_singleton.
case: (decide (t = t1)) => [-> {t}|t_t1]; last first.
{ rewrite lookup_insert_ne // !discrete_fun_lookup_singleton_ne //.
  rewrite decide_False //; set_solver. }
rewrite decide_True // ?elem_of_singleton //.
rewrite lookup_insert !discrete_fun_lookup_singleton //=.
move: (db' t1); apply/cmra_discrete_total_update.
apply: auth_update.
apply: option_local_update.
by apply: exclusive_local_update.
Qed.

Implicit Types (kI kR : term).

Definition db_state kI kR N db : iProp Σ :=
  term_own kI (N.@"client".@kR.@"state") (to_db_state db).

Definition mapsto kI kR N t1 t2 : iProp Σ :=
  term_own kI (N.@"client".@kR.@"state") (db_singleton t1 t2).

Definition free_at kI kR N T : iProp Σ :=
  term_own kI (N.@"client".@kR.@"state") (db_free T).

Lemma free_at_diff kI kR N T1 T2 :
  T1 ⊆ T2 →
  free_at kI kR N T2 ⊣⊢ free_at kI kR N T1 ∗ free_at kI kR N (T2 ∖ T1).
Proof.
move=> sub. by rewrite /free_at db_free_diff // term_own_op.
Qed.

Lemma db_state_mapsto kI kR N db t1 t2 :
  db_state kI kR N db -∗
  mapsto kI kR N t1 t2 -∗
  ⌜db !! t1 = Some t2⌝.
Proof.
iIntros "Hauth Hfrag".
iPoseProof (term_own_valid_2 with "Hauth Hfrag") as "%valid".
move/(_ t1): valid. rewrite /db_singleton.
rewrite discrete_fun_lookup_op /db_state discrete_fun_lookup_singleton.
rewrite auth_both_valid_discrete.
case => incl _.
by move/Excl_included/leibniz_equiv_iff: incl => <-.
Qed.

Lemma db_state_update t2' kI kR N db t1 t2 :
  db_state kI kR N db -∗
  mapsto kI kR N t1 t2 ==∗
  db_state kI kR N (<[t1 := t2']>db) ∗
  mapsto kI kR N t1 t2'.
Proof.
iIntros "Hauth Hfrag".
iMod (term_own_update_2 with "Hauth Hfrag") as "own".
{ eapply (@db_update _ _ _ t2'). }
iDestruct "own" as "[Hauth Hfrag]".
iModIntro. iSplitL "Hauth" => //.
Qed.

Lemma db_state_create t1 t2 kI kR N db :
  db_state kI kR N db -∗
  free_at kI kR N {[t1]} ==∗
  ⌜db !! t1 = None⌝ ∗
  db_state kI kR N (<[t1 := t2]>db) ∗
  mapsto kI kR N t1 t2.
Proof.
iIntros "Hauth Hfree". rewrite /=.
iAssert (⌜db !! t1 = None⌝)%I as "#->".
{ iPoseProof (term_own_valid_2 with "Hauth Hfree") as "%valid".
  move/(_ t1): valid. rewrite /db_state /db_free.
  rewrite discrete_fun_lookup_op decide_True ?elem_of_singleton //.
  rewrite auth_both_valid_discrete.
  by case=> /Excl_included/leibniz_equiv_iff <-. }
iMod (term_own_update_2 _ _ (a' := (_ ⋅ _)) with "Hauth Hfree") as "[Hauth Hfrag]".
{ by apply: (@db_alloc _ t1 t2). }
iModIntro. by iFrame.
Qed.

Lemma client_alloc kI kR N E :
  ↑N.@"client".@kR.@"state" ⊆ E →
  term_token kI E ==∗
  db_state kI kR N ∅ ∗
  free_at kI kR N ⊤ ∗
  term_token kI (E ∖ ↑N.@"client".@kR.@"state").
Proof.
iIntros "%sub token".
iMod (term_own_alloc (N.@"client".@kR.@"state")
        (to_db_state ∅ ⋅ db_free ⊤) with "token")
  as "[[state free] token]"; try solve_ndisj.
{ rewrite /to_db_state /db_free => t /=.
  rewrite discrete_fun_lookup_op lookup_empty /=.
  rewrite -> decide_True; try set_solver.
  rewrite auth_both_valid_discrete Excl_included leibniz_equiv_iff.
  by split. }
by iFrame.
Qed.

End DB.

End DB.
