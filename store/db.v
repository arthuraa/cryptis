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
| Store of term & term
| Create of term & term
| Load of term.

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
  | Store t1 t2 => <[t1 := t2]>db
  | Create t1 t2 =>
      match db !! t1 with
      | Some _ => db
      | None => <[t1 := t2]>db
      end
  | Load t1 => db
  end.

Definition to_db os : gmap term term :=
  foldl op_app ∅ os.

Context `{!cryptisGS Σ, !heapGS Σ, !dbGS Σ}.

Definition hist_auth k N os : iProp Σ :=
  term_own k (N.@"hist")
    (● to_max_prefix_list os ⋅ ◯ to_max_prefix_list os).

Definition db_version k N n : iProp Σ :=
  ∃ os, ⌜n = length os⌝ ∗ hist_auth k N os.

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

Definition hist_at k N n os : iProp Σ :=
  ⌜n = length os⌝ ∗ hist_frag k N os.

Lemma hist_at_agree k N n os1 os2 :
  hist_at k N n os1 -∗
  hist_at k N n os2 -∗
  ⌜os1 = os2⌝.
Proof.
iIntros "(-> & #frag1) (%e & #frag2)".
by iPoseProof (hist_frag_agree with "frag1 frag2") as "->".
Qed.

Lemma hist_at0 k N os :
  hist_at k N 0 os -∗
  ⌜os = []⌝.
Proof.
iIntros "(%e_len & #frag)".
by case: os => [|??] in e_len *.
Qed.

Definition db_at k N n db : iProp Σ :=
  ⌜n = 0⌝ ∗ ⌜db = ∅⌝ ∨
  ∃ os, ⌜db = to_db os⌝ ∗ hist_at k N n os.

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

Definition db_state k N db : iProp Σ :=
  term_own k (N.@"state") (to_db_state db).

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

Lemma db_state_mapsto k N db t1 t2 :
  db_state k N db -∗
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

Lemma db_state_update t2' k N db t1 t2 :
  db_state k N db -∗
  mapsto k N t1 t2 ==∗
  db_state k N (<[t1 := t2']>db) ∗
  mapsto k N t1 t2'.
Proof.
iIntros "Hauth Hfrag".
iMod (term_own_update_2 with "Hauth Hfrag") as "own".
{ eapply (@db_update _ _ _ t2'). }
iDestruct "own" as "[Hauth Hfrag]".
iModIntro. iSplitL "Hauth" => //.
Qed.

Lemma db_state_create t1 t2 k N db :
  db_state k N db -∗
  free_at k N {[t1]} ==∗
  db_state k N (op_app db (Create t1 t2)) ∗
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

Lemma db_state_load t1 k N db :
  db_state k N db ==∗
  db_state k N (op_app db (Load t1)).
Proof. by eauto. Qed.

Definition client_view k N n : iProp Σ :=
  db_version k N n ∗
  ∃ db, db_at k N n db ∗ db_state k N db.

Definition op_at k N n (o : operation) : iProp Σ :=
  ∃ os, hist_at k N (S n) (os ++ [o]).

Lemma op_at_agree k N n o1 o2 :
  op_at k N n o1 -∗
  op_at k N n o2 -∗
  ⌜o1 = o2⌝.
Proof.
iIntros "(%os1 & #hist1) (%os2 & #hist2)".
iPoseProof (hist_at_agree with "hist1 hist2") as "%e".
iPureIntro. suff ? : [o1] = [o2] by congruence.
have e': length os1 = length os2.
{ move/(f_equal length): e. rewrite !app_length /=. lia. }
move/(f_equal (drop (length os1))): e.
by rewrite drop_app_length e' drop_app_length.
Qed.

Lemma op_at_intro k N n o :
  db_version k N n ==∗
  db_version k N (S n) ∗ op_at k N n o.
Proof.
iIntros "(%os & -> & auth)".
iMod (hist_update _ _ _ o with "auth") as "[auth #frag]".
iModIntro. iSplit.
- iExists (os ++ [o]). rewrite app_length Nat.add_comm. by iFrame.
- iExists os. iSplit => //. by rewrite app_length /= Nat.add_comm.
Qed.

Lemma db_at_op_at k N n db o :
  db_at k N n db -∗
  op_at k N n o -∗
  db_at k N (S n) (op_app db o).
Proof.
iIntros "#db_at (%os' & #hist')".
iAssert (hist_at k N n os') as "hist''".
{ iDestruct "hist'" as "(%e_n & hist')".
  rewrite app_length /= in e_n.
  iSplit; first by iPureIntro; lia.
  iApply (hist_frag_prefix_of with "hist'").
  by exists [o]. }
iDestruct "db_at" as "[[-> ->]|(%os & -> & #hist)]".
{ iPoseProof (hist_at0 with "hist''") as "->".
  iRight. iExists [o]. rewrite /to_db /=. by eauto. }
iPoseProof (hist_at_agree with "hist hist''") as "{hist''} ->".
iRight. iExists (os' ++ [o]). iSplit => //.
by rewrite /to_db foldl_app.
Qed.

Definition store_at k N n t1 t2 : iProp Σ :=
  op_at k N n (Store t1 t2).

Definition create_at k N n t1 t2 : iProp Σ :=
  op_at k N n (Create t1 t2).

Definition load_at k N n t1 :=
  op_at k N n (Load t1).

Lemma alloc k N E :
  ↑N ⊆ E →
  term_token k E ==∗
  client_view k N 0 ∗
  free_at k N ⊤ ∗
  db_at k N 0 ∅ ∗
  term_token k (E ∖ ↑N).
Proof.
iIntros "%sub token".
iMod (term_own_alloc (N.@"hist")
        (● to_max_prefix_list [] ⋅ ◯ to_max_prefix_list []) with "token")
  as "[hist token]"; try solve_ndisj.
{ apply/auth_both_valid_discrete. split; eauto.
  exact/to_max_prefix_list_valid. }
iMod (term_own_alloc (N.@"state") (to_db_state ∅ ⋅ db_free ⊤) with "token")
  as "[[state free] token]"; try solve_ndisj.
{ rewrite /to_db_state /db_free => t /=.
  rewrite discrete_fun_lookup_op lookup_empty /=.
  rewrite -> decide_True; try set_solver.
  rewrite auth_both_valid_discrete Excl_included leibniz_equiv_iff.
  by split. }
iAssert (hist_at k N 0 []) as "#hist_at".
{ by iDestruct "hist" as "[??]"; do !iSplit => //. }
iAssert (db_at k N 0 ∅) as "#db_at".
{ by iLeft. }
iAssert (db_version k N 0) with "[hist]" as "auth".
{ iExists []. by iFrame. }
iFrame. iModIntro. do !iSplit => //.
iApply (term_token_drop with "token"). solve_ndisj.
Qed.

Lemma store_client t2' k N n t1 t2 :
  client_view k N n -∗
  mapsto k N t1 t2 ==∗
  client_view k N (S n) ∗
  store_at k N n t1 t2' ∗
  mapsto k N t1 t2'.
Proof.
iIntros "(own_version & %db & #db & own_db) own_frag".
iMod (op_at_intro _ _ _ (Store t1 t2') with "own_version")
  as "[own_version #op_at]".
iPoseProof (db_at_op_at with "db op_at") as "db'".
iMod (db_state_update t2' with "own_db own_frag") as "[Hstate Hmapsto]".
iModIntro. iFrame. by iSplit => //.
Qed.

Lemma db_at_store_at k N n db t1 t2 :
  db_at k N n db -∗
  store_at k N n t1 t2 -∗
  db_at k N (S n) (<[t1 := t2]>db).
Proof. iApply db_at_op_at. Qed.

Lemma create_client t1 t2 k N n :
  client_view k N n -∗
  free_at k N {[t1]} ==∗
  create_at k N n t1 t2 ∗
  client_view k N (S n) ∗
  mapsto k N t1 t2.
Proof.
iIntros "(version & %db & #db_at & state) Hfree".
iMod (op_at_intro _ _ _ (Create t1 t2) with "version") as "[version #op_at]".
iMod (db_state_create t1 t2 with "state Hfree") as "[state mapsto]".
iModIntro. iFrame. iSplit => //.
by iApply db_at_op_at.
Qed.

Lemma db_at_create_at k N n db t1 t2 :
  db !! t1 = None →
  db_at k N n db -∗
  create_at k N n t1 t2 -∗
  db_at k N (S n) (<[t1 := t2]>db).
Proof.
iIntros "%db_t1 #db #op".
iPoseProof (db_at_op_at with "db op") as "db'".
by rewrite /= db_t1.
Qed.

Lemma load_client t1 k N n :
  client_view k N n ==∗
  load_at k N n t1 ∗
  client_view k N (S n).
Proof.
iIntros "(version & %db & #db & state)".
iMod (op_at_intro _ _ _ (Load t1) with "version") as "[version #op]".
iFrame. iModIntro. iSplit=> //. iApply (db_at_op_at with "db op").
Qed.

Definition stored_at k N n t1 t2 : iProp Σ :=
  ∃ db, db_at k N n db ∗ ⌜db !! t1 = Some t2⌝.

Lemma load_at_stored_at k N n t1 t2 t1' :
  stored_at k N n t1 t2 -∗
  load_at k N n t1' -∗
  stored_at k N (S n) t1 t2.
Proof.
iIntros "(%db & #db & %db_t1) #load".
iExists db. iSplit => //. iApply (db_at_op_at with "db load").
Qed.

Lemma db_at0 k N db :
  db_at k N 0 db -∗
  ⌜db = ∅⌝.
Proof.
iIntros "[[_ ->]|(%os & -> & #hist)]" => //.
by iPoseProof (hist_at0 with "hist") as "->".
Qed.

Lemma db_at_agree k N n db1 db2 :
  db_at k N n db1 -∗
  db_at k N n db2 -∗
  ⌜db1 = db2⌝.
Proof.
iIntros "#db_at1 #db_at2".
iPoseProof "db_at1" as "[[-> ->]|db_at1']".
{ by iPoseProof (db_at0 with "db_at2") as "->". }
iPoseProof "db_at2" as "[[-> ->]|db_at2']".
{ by iPoseProof (db_at0 with "db_at1") as "->". }
iDestruct "db_at1'" as "(%os1 & -> & #hist1)".
iDestruct "db_at2'" as "(%os2 & -> & #hist2)".
by iPoseProof (hist_at_agree with "hist1 hist2") as "->".
Qed.

Lemma db_at_stored_at k N n db t1 t2 :
  db_at k N n db -∗
  stored_at k N n t1 t2 -∗
  ⌜db !! t1 = Some t2⌝.
Proof.
iIntros "#db1 (%db' & #db2 & %db_t1)".
by iPoseProof (db_at_agree with "db1 db2") as "->".
Qed.

Lemma client_view_stored_at k N n t1 t2 t2' :
  client_view k N n -∗
  mapsto k N t1 t2 -∗
  stored_at k N n t1 t2' -∗
  ⌜t2' = t2⌝.
Proof.
iIntros "(version & %db & #db & state) t1_t2 #stored".
iPoseProof (db_state_mapsto with "state t1_t2") as "%db_t1".
iPoseProof (db_at_stored_at with "db stored") as "%db_t1'".
iPureIntro. rewrite db_t1 in db_t1'. by case: db_t1' => ->.
Qed.

Lemma stored_atI k N n db t1 t2 :
  db !! t1 = Some t2 →
  db_at k N n db -∗
  stored_at k N n t1 t2.
Proof. iIntros "%db_t1 #db_at". iExists db; eauto. Qed.

Lemma client_view_db_at k N n :
  client_view k N n -∗ ∃ db, db_at k N n db.
Proof. iIntros "(_ & %db & #db & _)". eauto. Qed.

Lemma db_at_to_0 k N n db :
  db_at k N n db -∗
  db_at k N 0 ∅.
Proof.
iIntros "_". by iLeft.
Qed.

End DB.

End DB.
