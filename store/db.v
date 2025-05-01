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

Variant operation :=
| Store of term & term
| Create of term & term
| Load of term.

Class dbGS Σ := DbGS {
  dbGS_state : inG Σ db_stateUR;
  dbGS_replica : replicaG Σ (list operation);
}.

Local Existing Instance dbGS_state.
Local Existing Instance dbGS_replica.

Definition dbΣ :=
  #[GFunctor db_stateUR;
    replicaΣ (list operation)].

Global Instance subG_dbGS Σ : subG dbΣ Σ → dbGS Σ.
Proof. solve_inG. Qed.

Module DB.

Section DB.

Implicit Types o : operation.
Implicit Types os : list operation.
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
  db_state kI kR N (op_app db (Create t1 t2)) ∗
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

Lemma db_state_load t1 kI kR N db :
  db_state kI kR N db ==∗
  db_state kI kR N (op_app db (Load t1)).
Proof. by eauto. Qed.

Definition db_client_ready kI kR N db : iProp Σ :=
  ∃ os, ⌜db = to_db os⌝ ∗
        rep_main kI kR N os ∗ rep_current kI kR N [] os.

Definition db_client_waiting kI kR N db o : iProp Σ :=
  ∃ os, ⌜db = to_db os⌝ ∗
        rep_main kI kR N (os ++ [o]).

Definition db_server_ready kI kR N db : iProp Σ :=
  ∃ os, ⌜db = to_db os⌝ ∗ rep_copy kI kR N [] os.

Definition store_call kI kR N t1 t2 : iProp Σ :=
  ∃ os, rep_update kI kR N [] os (os ++ [Store t1 t2]).

Definition store_resp kI kR N : iProp Σ :=
  ∃ os, rep_current kI kR N [] os.

Lemma store_callI t1 t2 kI kR N db :
  db_client_ready kI kR N db ==∗
  db_client_waiting kI kR N db (Store t1 t2) ∗
  store_call kI kR N t1 t2.
Proof.
iIntros "(%os & -> & main & cur)".
iMod (rep_main_update (os ++ [Store t1 t2]) with "main cur")
  as "[main cur]".
by iFrame.
Qed.

Lemma store_callE t1 t2 kI kR N db P :
  Persistent P →
  (P ∨ db_server_ready kI kR N db) -∗
  (P ∨ store_call kI kR N t1 t2) ==∗
  (P ∨ db_server_ready kI kR N (<[t1 := t2]>db)) ∗
  (P ∨ store_resp kI kR N).
Proof.
iIntros "% [#?|(%os & -> & copy)] call".
{ iModIntro. by iSplitL; eauto. }
iDestruct "call" as "[#?|(%os' & upd)]".
{ iModIntro. by iSplitL; eauto. }
iMod (rep_copy_update with "copy upd") as "(<- & copy & upd)".
iFrame. iRight. iFrame. by rewrite /to_db foldl_app.
Qed.

Lemma store_respE kI kR N db t1 t2 :
  db_client_waiting kI kR N db (Store t1 t2) -∗
  store_resp kI kR N -∗
  db_client_ready kI kR N (<[t1 := t2]>db).
Proof.
iIntros "(%os & -> & main) (%os' & cur)".
iPoseProof (rep_main_current with "main cur") as "<-".
iFrame. by rewrite /to_db foldl_app.
Qed.

Definition create_call kI kR N t1 t2 : iProp Σ :=
  ∃ os, rep_update kI kR N [] os (os ++ [Create t1 t2]) ∗
        ⌜to_db os !! t1 = None⌝.

Definition create_resp kI kR N : iProp Σ :=
  ∃ os, rep_current kI kR N [] os.

Lemma create_callI t1 t2 kI kR N db :
  db !! t1 = None →
  db_client_ready kI kR N db ==∗
  db_client_waiting kI kR N db (Create t1 t2) ∗
  create_call kI kR N t1 t2.
Proof.
iIntros "% (%os & -> & main & cur)".
iMod (rep_main_update (os ++ [Create t1 t2]) with "main cur")
  as "[main cur]". by iFrame.
Qed.

Lemma create_callE t1 t2 kI kR N db P :
  Persistent P →
  (P ∨ db_server_ready kI kR N db) -∗
  (P ∨ create_call kI kR N t1 t2) ==∗
  (P ∨ db_server_ready kI kR N (op_app db (Create t1 t2))) ∗
  (P ∨ create_resp kI kR N) ∗
  (P ∨ ⌜db !! t1 = None⌝).
Proof.
iIntros "% ready call"; rewrite -!or_sep2.
iDestruct "ready" as "[?|(%os & -> & copy)]"; eauto.
iDestruct "call" as "[?|(%os' & upd & %)]"; eauto.
iMod (rep_copy_update with "copy upd") as "(-> & copy & upd)".
iModIntro. iRight. iFrame. rewrite /to_db foldl_app. by eauto.
Qed.

Lemma create_respE kI kR N db t1 t2 :
  db_client_waiting kI kR N db (Create t1 t2) -∗
  create_resp kI kR N -∗
  db_client_ready kI kR N (op_app db (Create t1 t2)).
Proof.
iIntros "(%os & -> & main) (%os' & cur)".
iPoseProof (rep_main_current with "main cur") as "<-". iFrame.
by rewrite /to_db foldl_app.
Qed.

Definition load_call kI kR N t1 : iProp Σ :=
  ∃ t2 os, rep_update kI kR N [] os (os ++ [Load t1]) ∗
           ⌜to_db os !! t1 = Some t2⌝.

Definition load_resp kI kR N t2 : iProp Σ :=
  ∃ t1 os, rep_current kI kR N [] (os ++ [Load t1]) ∗
           ⌜to_db os !! t1 = Some t2⌝.

Lemma load_callI t1 t2 kI kR N db :
  db !! t1 = Some t2 →
  db_client_ready kI kR N db ==∗
  db_client_waiting kI kR N db (Load t1) ∗
  load_call kI kR N t1.
Proof.
iIntros "% (%os & -> & main & cur)".
iMod (rep_main_update (os ++ [Load t1]) with "main cur")
  as "[main cur]". iFrame. eauto.
Qed.

Lemma load_callE t1 kI kR N db P :
  Persistent P →
  (P ∨ db_server_ready kI kR N db) -∗
  (P ∨ load_call kI kR N t1) ==∗ ∃ t2,
  (P ∨ ⌜db !! t1 = Some t2⌝) ∗
  (P ∨ db_server_ready kI kR N (op_app db (Load t1))) ∗
  (P ∨ load_resp kI kR N t2).
Proof.
iIntros "% ready load".
iDestruct "ready" as "[?|ready]".
{ iModIntro. iExists inhabitant. rewrite -!or_sep2. by eauto. }
iDestruct "load" as "[?|load]".
{ iModIntro. iExists inhabitant. rewrite -!or_sep2. by eauto. }
iDestruct "ready" as "(%os & -> & copy)".
iDestruct "load" as "(%t2 & %os' & upd & %)".
iMod (rep_copy_update with "copy upd") as "(-> & copy & upd)".
iModIntro. iExists t2. rewrite -!or_sep2. iRight.
iFrame. rewrite /to_db foldl_app. by eauto.
Qed.

Lemma load_respE kI kR N db t1 t2 t2' :
  db !! t1 = Some t2 →
  db_client_waiting kI kR N db (Load t1) -∗
  load_resp kI kR N t2' -∗
  db_client_ready kI kR N db ∗
  ⌜t2' = t2⌝.
Proof.
iIntros "%db_t1 (%os & -> & main) (%t1' & %os' & cur & %db_t1')".
iPoseProof (rep_main_current with "main cur") as "%e".
case: (app_inj_tail _ _ _ _ e) => [<- [<-]] in db_t1' *.
iFrame. rewrite /to_db foldl_app. iPureIntro.
split => //. congruence.
Qed.

Lemma client_alloc kI kR N E :
  ↑N.@"client".@kR ⊆ E →
  term_token kI E ==∗
  db_client_ready kI kR N ∅ ∗
  db_state kI kR N ∅ ∗
  free_at kI kR N ⊤ ∗
  term_token kI (E ∖ ↑N.@"client".@kR).
Proof.
iIntros "%sub token".
iMod (rep_main_alloc (N := N) kI (kR := kR) [] with "token")
  as "(main & cur & token)"; first solve_ndisj.
iFrame.
iMod (term_own_alloc (N.@"client".@kR.@"state")
        (to_db_state ∅ ⋅ db_free ⊤) with "token")
  as "[[state free] token]"; try solve_ndisj.
{ rewrite /to_db_state /db_free => t /=.
  rewrite discrete_fun_lookup_op lookup_empty /=.
  rewrite -> decide_True; try set_solver.
  rewrite auth_both_valid_discrete Excl_included leibniz_equiv_iff.
  by split. }
iFrame. iModIntro. do !iSplit => //.
iApply (term_token_drop with "token"). solve_ndisj.
Qed.

Lemma server_alloc kI kR N E :
  ↑N.@"server".@kI ⊆ E →
  term_token kR E ==∗
  db_server_ready kI kR N ∅ ∗
  term_token kR (E ∖ ↑N.@"server".@kI).
Proof.
iIntros "% token".
iMod (rep_copy_alloc with "token") as "[??]" => //.
by iFrame.
Qed.

Lemma store_client t2' kI kR N db t1 t2 P :
  Persistent P →
  (P ∨ db_client_ready kI kR N db) -∗
  db_state kI kR N db -∗
  mapsto kI kR N t1 t2 ==∗
  (P ∨ db_client_waiting kI kR N db (Store t1 t2')) ∗
  (P ∨ store_call kI kR N t1 t2') ∗
  db_state kI kR N (<[t1 := t2']>db) ∗
  mapsto kI kR N t1 t2'.
Proof.
iIntros "% ready own_db own_frag".
iMod (db_state_update t2' with "own_db own_frag") as "[Hstate Hmapsto]".
iFrame.
iDestruct "ready" as "[#?|ready]"; first by iModIntro; iSplitL; eauto.
iMod (store_callI t1 t2' with "ready") as "[??]". by iFrame.
Qed.

Lemma create_client t1 t2 kI kR N db P :
  Persistent P →
  (P ∨ db_client_ready kI kR N db) -∗
  db_state kI kR N db -∗
  free_at kI kR N {[t1]} ==∗
  (P ∨ db_client_waiting kI kR N db (Create t1 t2)) ∗
  (P ∨ create_call kI kR N t1 t2) ∗
  db_state kI kR N (op_app db (Create t1 t2)) ∗
  mapsto kI kR N t1 t2.
Proof.
iIntros "% ready state Hfree".
iMod (db_state_create t1 t2 with "state Hfree") as "(%db_t1 & state & mapsto)".
iFrame.
iDestruct "ready" as "[#?|ready]".
{ iModIntro; iSplitL; eauto. }
iMod (create_callI t2 with "ready") as "[??]" => //. by iFrame.
Qed.

Lemma load_client t1 t2 kI kR N db P :
  Persistent P →
  (P ∨ db_client_ready kI kR N db) -∗
  db_state kI kR N db -∗
  mapsto kI kR N t1 t2 ==∗
  (P ∨ db_client_waiting kI kR N db (Load t1)) ∗
  (P ∨ load_call kI kR N t1) ∗
  db_state kI kR N db ∗
  mapsto kI kR N t1 t2.
Proof.
iIntros "% ready state mapsto".
iPoseProof (db_state_mapsto with "state mapsto") as "%db_t1".
iFrame.
iDestruct "ready" as "[#?|ready]"; first by iModIntro; iSplitL; eauto.
iMod (load_callI _ _ _ db_t1 with "ready") as "[??]".
by iFrame.
Qed.

End DB.

End DB.
