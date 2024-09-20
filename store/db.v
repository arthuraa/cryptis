From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import cmra agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list functions.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition db_stateUR : ucmra :=
  discrete_funUR (fun _ : term => authUR (optionUR (exclR (optionO termO)))).

Variant operation :=
| Update of term & term
| Create of term & term.

Canonical operationO := leibnizO operation.

Definition db_historyUR : ucmra :=
  authUR (max_prefix_listUR operationO).

Class dbGS Σ := DbGS {
  dbGS_state : inG Σ db_stateUR;
  dbGS_history : inG Σ db_historyUR;
}.

Local Existing Instance dbGS_state.
Local Existing Instance dbGS_history.

Definition dbΣ :=
  #[GFunctor db_stateUR;
    GFunctor db_historyUR].

Global Instance subG_dbGS Σ : subG dbΣ Σ → dbGS Σ.
Proof. solve_inG. Qed.

Module DB.

Section DB.

Implicit Types o : operationO.
Implicit Types os : list operationO.
Implicit Types db : gmap term term.
Implicit Types γ : gname.
Implicit Types N : namespace.
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types T : coGset term.

Definition op_app db o :=
  match o with
  | Update t1 t2 => <[t1 := t2]>db
  | Create t1 t2 =>
      match db !! t1 with
      | Some _ => db
      | None => <[t1 := t2]>db
      end
  end.

Definition to_db os : gmap term term :=
  foldl op_app ∅ os.

Context `{!cryptisGS Σ, !heapGS Σ, !dbGS Σ}.

Definition hist_auth k N os : iProp Σ :=
  term_own k (N.@"hist")
    (● to_max_prefix_list os ⋅ ◯ to_max_prefix_list os).

Definition hist_frag k N os : iProp Σ :=
  term_own k (N.@"hist")
    (◯ to_max_prefix_list os).

Local Instance persistent_hist_frag k N os : Persistent (hist_frag k N os).
Proof. apply _. Qed.

Lemma hist_auth_frag k N os :
  hist_auth k N os -∗
  hist_frag k N os.
Proof. by iIntros "[_ Hown]". Qed.

Lemma hist_frag_agree k N os1 os2 :
  length os1 = length os2 →
  hist_frag k N os1 -∗
  hist_frag k N os2 -∗
  ⌜os2 = os1⌝.
Proof.
move=> lengthE.
iIntros "#hist1 #hist2".
iPoseProof (term_own_valid_2 with "hist1 hist2") as "%valid".
rewrite auth_frag_op_valid to_max_prefix_list_op_valid_L in valid.
iPureIntro.
case: valid => - [[|o os] osE].
- by rewrite app_nil_r in osE.
- rewrite osE app_length /= in lengthE; lia.
- by rewrite app_nil_r in osE.
- rewrite osE app_length /= in lengthE; lia.
Qed.

Lemma hist_frag_prefix_of os1 os2 k N :
  os1 `prefix_of` os2 →
  hist_frag k N os2 -∗
  hist_frag k N os1.
Proof.
iIntros "%os1_os2 #hist_frag". rewrite /hist_frag.
iApply term_own_mono; last by eauto.
apply: auth_frag_mono. exact/to_max_prefix_list_included_L.
Qed.

Lemma hist_update k N os o :
  hist_auth k N os ==∗
  hist_auth k N (os ++ [o]) ∗
  hist_frag k N (os ++ [o]).
Proof.
iIntros "auth".
iMod (term_own_update with "auth") as "auth".
{ apply: auth_update.
  apply: (max_prefix_list_local_update os (os ++ [o])).
  by exists [o]. }
iDestruct "auth" as "[auth #frag]".
iModIntro. iSplit => //. by iSplitL.
Qed.

Definition db_state db : db_stateUR :=
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
  db_state db ⋅ db_singleton t1 t2 ~~>
  db_state (<[t1 := t2']> db) ⋅ db_singleton t1 t2'.
Proof.
apply/cmra_discrete_update=> db' valid t.
move/(_ t): valid.
rewrite !discrete_fun_lookup_op /db_state /db_singleton.
case: (decide (t = t1)) => [-> {t}|t_t1]; last first.
{ rewrite lookup_insert_ne // !discrete_fun_lookup_singleton_ne //. }
rewrite lookup_insert !discrete_fun_lookup_singleton //=.
move: (db' t1); apply/cmra_discrete_update.
apply: auth_update.
apply (transitivity (y := (None, None))).
- exact: delete_option_local_update.
- exact: alloc_option_local_update.
Qed.

Lemma db_alloc db t1 t2 :
  db_state db ⋅ db_free {[t1]} ~~>
  db_state (<[t1 := t2]> db) ⋅ db_singleton t1 t2.
Proof.
apply/cmra_discrete_update=> db' valid t.
move/(_ t): valid.
rewrite !discrete_fun_lookup_op /db_state /db_free /db_singleton.
case: (decide (t = t1)) => [-> {t}|t_t1]; last first.
{ rewrite lookup_insert_ne // !discrete_fun_lookup_singleton_ne //.
  rewrite decide_False //; set_solver. }
rewrite decide_True // ?elem_of_singleton //.
rewrite lookup_insert !discrete_fun_lookup_singleton //=.
move: (db' t1); apply/cmra_discrete_update.
apply: auth_update.
apply: option_local_update.
by apply: exclusive_local_update.
Qed.

Definition state_auth k N db : iProp Σ :=
  term_own k (N.@"state") (db_state db).

Definition mapsto k N t1 t2 : iProp Σ :=
  term_own k (N.@"state") (db_singleton t1 t2).

Definition free_at k N T : iProp Σ :=
  term_own k (N.@"state") (db_free T).

Lemma free_at_diff k N T1 T2 :
  T1 ⊆ T2 →
  free_at k N T2 ⊣⊢ free_at k N T1 ∗ free_at k N (T2 ∖ T1).
Proof.
move=> sub. by rewrite /free_at db_free_diff // term_own_op.
Qed.

Lemma state_auth_mapsto k N db t1 t2 :
  state_auth k N db -∗
  mapsto k N t1 t2 -∗
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

Lemma state_auth_update t2' k N db t1 t2 :
  state_auth k N db -∗
  mapsto k N t1 t2 ==∗
  state_auth k N (<[t1 := t2']>db) ∗
  mapsto k N t1 t2'.
Proof.
iIntros "Hauth Hfrag".
iMod (term_own_update_2 with "Hauth Hfrag") as "own".
{ eapply (@db_update _ _ _ t2'). }
iDestruct "own" as "[Hauth Hfrag]".
iModIntro. iSplitL "Hauth" => //.
Qed.

Lemma state_auth_create t1 t2 k N db :
  state_auth k N db -∗
  free_at k N {[t1]} ==∗
  state_auth k N (op_app db (Create t1 t2)) ∗
  mapsto k N t1 t2.
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
iModIntro. iSplitL "Hauth" => //.
Qed.

Definition client_view k N n : iProp Σ :=
  ∃ os,
    ⌜n = length os⌝ ∗
    hist_auth k N os ∗
    state_auth k N (to_db os).

Definition update_at k N n t1 t2 : iProp Σ :=
  ∃ os, ⌜n = length os⌝ ∗
        hist_frag k N (os ++ [Update t1 t2]).

Definition create_at k N n t1 t2 : iProp Σ :=
  ∃ os, ⌜n = length os⌝ ∗
        hist_frag k N (os ++ [Create t1 t2]).

Definition server_view k N n db : iProp Σ :=
  ∃ os, ⌜n = length os⌝ ∗
        ⌜db = to_db os⌝ ∗
        hist_frag k N os.

Lemma alloc k N E :
  ↑N ⊆ E →
  term_token k E ==∗
  client_view k N 0 ∗
  free_at k N ⊤ ∗
  server_view k N 0 ∅ ∗
  term_token k (E ∖ ↑N).
Proof.
iIntros "%sub token".
iMod (term_own_alloc (N.@"hist")
        (● to_max_prefix_list [] ⋅ ◯ to_max_prefix_list []) with "token")
  as "[hist token]"; try solve_ndisj.
{ apply/auth_both_valid_discrete. split; eauto.
  exact/to_max_prefix_list_valid. }
iMod (term_own_alloc (N.@"state") (db_state ∅ ⋅ db_free ⊤) with "token")
  as "[[state free] token]"; try solve_ndisj.
{ rewrite /db_state /db_free => t /=.
  rewrite discrete_fun_lookup_op lookup_empty /=.
  rewrite -> decide_True; try set_solver.
  rewrite auth_both_valid_discrete Excl_included leibniz_equiv_iff.
  by split. }
iAssert (hist_frag k N []) as "#frag".
{ by iDestruct "hist" as "[??]". }
iModIntro. iSplitR "free token".
{ iExists []. iSplit; eauto. iSplitL "hist" => //. }
iSplitL "free"; try iApply "free".
iSplitR.
{ iExists []. eauto. }
iApply (term_token_drop with "token"). solve_ndisj.
Qed.

Lemma update_client t2' k N n t1 t2 :
  client_view k N n -∗
  mapsto k N t1 t2 ==∗
  client_view k N (S n) ∗
  update_at k N n t1 t2' ∗
  mapsto k N t1 t2'.
Proof.
iIntros "(%os & -> & own_os & own_db) own_frag".
iMod (hist_update _ _ os (Update t1 t2') with "own_os") as "[auth_os #frag_os]".
iMod (state_auth_update t2' with "own_db own_frag") as "[Hstate Hmapsto]".
iModIntro. iSplitL "auth_os Hstate".
{ iExists (os ++ [Update t1 t2']).
  rewrite app_length Nat.add_comm /=. iSplit; first by [].
  iFrame. by rewrite /to_db foldl_app. }
iFrame.
{ iExists _; eauto. }
Qed.

Lemma update_server k N n db t1 t2 :
  server_view k N n db -∗
  update_at k N n t1 t2 -∗
  server_view k N (S n) (<[t1 := t2]>db).
Proof.
iIntros "(%os & -> & -> & #frag) (%os' & %lengthE & #frag')".
iPoseProof (hist_frag_agree _ _ lengthE with "frag []") as "->".
{ iApply (hist_frag_prefix_of with "frag'").
  by exists [Update t1 t2]. }
iExists (os ++ [Update t1 t2]). rewrite app_length Nat.add_comm /=.
do 2!iSplit => //.
by rewrite /to_db foldl_app.
Qed.

Lemma create_client t1 t2 k N n :
  client_view k N n -∗
  free_at k N {[t1]} ==∗
  create_at k N n t1 t2 ∗
  client_view k N (S n) ∗
  mapsto k N t1 t2.
Proof.
iIntros "(%os & -> & hist & state) Hfree".
iMod (hist_update _ _ _ (Create t1 t2) with "hist") as "[hist_auth #hist_frag]".
iMod (state_auth_create t1 t2 with "state Hfree") as "[state mapsto]".
have ->: op_app (to_db os) (Create t1 t2) = to_db (os ++ [Create t1 t2]).
{ by rewrite /to_db foldl_app. }
iModIntro. iFrame. iSplitR; first by iExists os; eauto.
iExists _. iFrame. by rewrite app_length Nat.add_comm.
Qed.

Lemma create_server k N n db t1 t2 :
  db !! t1 = None →
  server_view k N n db -∗
  create_at k N n t1 t2 -∗
  server_view k N (S n) (<[t1 := t2]>db).
Proof.
iIntros "%db_t1 (%os & -> & -> & #frag) (%os' & %lengthE & #frag')".
iAssert (hist_frag k N os') as "#frag''".
{ iApply (hist_frag_prefix_of with "frag'").
  by exists [Create t1 t2]. }
iPoseProof (hist_frag_agree with "frag frag''") as "->" => //.
iExists (os ++ [Create t1 t2]). rewrite app_length Nat.add_comm.
do 2!iSplit => //. iPureIntro. by rewrite /to_db foldl_app /= db_t1.
Qed.

Definition stored_at k N n t1 t2 : iProp Σ :=
  ∃ os, ⌜n = length os⌝ ∗
        hist_frag k N os ∗
        ⌜to_db os !! t1 = Some t2⌝.

Lemma load_client k N n t1 t2 t2' :
  client_view k N n -∗
  mapsto k N t1 t2 -∗
  stored_at k N n t1 t2' -∗
  ⌜t2' = t2⌝.
Proof.
iIntros "(%os & -> & hist & state) t1_t2 (%os' & %lengthE & #Hfrag & %os_t1)".
iPoseProof (hist_auth_frag with "hist") as "#Hfrag'".
iPoseProof (hist_frag_agree with "Hfrag Hfrag'") as "->" => //.
iPoseProof (state_auth_mapsto with "state t1_t2") as "%os_t1'".
iPureIntro. rewrite os_t1 in os_t1'. by case: os_t1' => ->.
Qed.

Lemma load_server k N n db t1 t2 :
  db !! t1 = Some t2 →
  server_view k N n db -∗
  stored_at k N n t1 t2.
Proof.
iIntros "%db_t1 (%os & -> & -> & view)".
iExists os; eauto.
Qed.

Lemma client_view_server_view k N n :
  client_view k N n -∗ ∃ db,
  server_view k N n db.
Proof.
iIntros "(%os & %e_n & hist_auth & _)".
iPoseProof (DB.hist_auth_frag with "hist_auth") as "#hist_frag".
iExists _, os. do !iSplit => //.
Qed.

Lemma server_view_to_0 k N n db :
  server_view k N n db -∗
  server_view k N 0 ∅.
Proof.
iIntros "(%os & %e_n & %e_db & hist_frag)".
iExists [].
do !iSplit => //.
iApply (DB.hist_frag_prefix_of with "hist_frag").
by exists os.
Qed.

Lemma server_view_0 k N db :
  server_view k N 0 db -∗
  ⌜db = ∅⌝.
Proof.
iIntros "(%os & %e_os & -> & #hist_frag)".
case: os => // in e_os *.
Qed.

End DB.

End DB.
