From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis replica primitives tactics role iso_dh conn rpc.
From cryptis.store Require Import alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Notation dbN := (nroot.@"db").

Record server_state := {
  ss_key : term;
  ss_clients : val;
}.

#[global]
Instance ss_repr : Repr server_state :=
  λ s, (ss_key s, ss_clients s)%V.

Record server_client_state := {
  scs_db   : val;
  scs_name : gname;
  scs_lock : val;
}.

#[global]
Instance scs_repr : Repr server_client_state :=
  λ s, (scs_db s, scs_lock s)%V.

Class storeGS Σ := StoreGS {
  storeGS_db : dbGS Σ;
  storeGS_replica : replicaG Σ (list operation);
}.

Local Existing Instance storeGS_db.
Local Existing Instance storeGS_replica.

Definition storeΣ := #[
  dbΣ;
  replicaΣ (list operation)
].

Global Instance subG_storeGS Σ : subG storeΣ Σ → storeGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (si : sess_info).
Implicit Types (cs : Conn.state).
Implicit Types (kI kR kS t : term) (ts : list term).
Implicit Types (db : gmap term term).
Implicit Types (o : operation) (os : list operation).
Implicit Types accounts : gmap term server_client_state.
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types (failed : bool).

Definition db_client_ready kI kR db : iProp :=
  ∃ os, ⌜db = DB.to_db os⌝ ∗
        rep_main kI kR dbN os ∗ rep_current kI kR dbN [] os.

Definition db_server_ready kI kR db : iProp :=
  ∃ os, ⌜db = DB.to_db os⌝ ∗ rep_copy kI kR dbN [] os.

Definition db_disconnected kI kR : iProp := ∃ db,
  (Conn.failure kI kR ∨ db_client_ready kI kR db) ∗
  DB.db_state kI kR dbN db.

Definition db_connected' kI kR cs : iProp := ∃ db,
  (compromised_session Init cs ∨ db_client_ready kI kR db) ∗
  DB.db_state kI kR dbN db.

Definition db_connected kI kR cs : iProp :=
  RPC.client_connected kI kR cs ∗
  db_connected' kI kR cs.

Lemma db_connected_ok kI kR cs :
  db_connected kI kR cs -∗
  secret kI -∗
  secret kR -∗
  sign_key kI -∗
  sign_key kR -∗
  ◇ □ ¬ compromised_session Init cs.
Proof.
iIntros "(conn & _)".
iApply (RPC.client_connected_ok with "conn").
Qed.

Definition db_mapsto kI kR t1 t2 : iProp :=
  DB.mapsto kI kR dbN t1 t2.

Definition db_free_at kI kR T : iProp :=
  DB.free_at kI kR dbN T.

Lemma db_free_at_diff kI kR T1 T2 :
  T1 ⊆ T2 →
  db_free_at kI kR T2 ⊣⊢ db_free_at kI kR T1 ∗ db_free_at kI kR (T2 ∖ T1).
Proof. iIntros "%sub". by iApply DB.free_at_diff. Qed.

Lemma client_alloc kI kR E :
  ↑dbN.@"client".@kR ⊆ E →
  term_token kI E ={⊤}=∗
  db_disconnected kI kR ∗
  db_free_at kI kR ⊤ ∗
  term_token kI (E ∖ ↑dbN.@"client".@kR).
Proof.
iIntros "%sub kI_token".
rewrite (term_token_difference _ _ _ sub).
iDestruct "kI_token" as "[kI_token ?]". iFrame.
iMod (rep_main_alloc (N := dbN) kI (kR := kR) [] with "kI_token")
  as "(main & cur & kI_token)"; first solve_ndisj.
iMod (DB.client_alloc _ (N := dbN) with "kI_token")
  as "(state & free & kI_token)".
{ solve_ndisj. }
iModIntro. iFrame. iRight. iExists []. by iFrame.
Qed.

Definition public_db db : iProp :=
  [∗ map] t1 ↦ t2 ∈ db, public t1 ∗ public t2.

Lemma public_db_insert db t1 t2 :
  public t1 -∗
  public t2 -∗
  public_db db -∗
  public_db (<[t1 := t2]> db).
Proof.
rewrite /public_db !big_sepM_forall.
iIntros "#p_t1 #p_t2 #p_db %t1' %t2'".
case: (decide (t1' = t1)) => [-> {t1'} | ne].
- rewrite lookup_insert. iIntros "%e". case: e => ->. by eauto.
- by rewrite lookup_insert_ne //.
Qed.

Definition server_db_connected' kI kR cs vdb : iProp := ∃ db,
  public_db db ∗
  SAList.is_alist vdb (repr <$> db) ∗
  (compromised_session Resp cs ∨ db_server_ready kI kR db).

Definition server_db_connected kI kR cs vdb : iProp :=
  RPC.server_connected kI kR cs ∗
  server_db_connected' kI kR cs vdb.

Definition server_handler kI kR cs vdb h : iProp :=
  RPC.wf_handler (server_db_connected' kI kR cs vdb) kI kR cs h.

Definition server_db_disconnected kI kR vdb : iProp := ∃ db,
  public_db db ∗
  SAList.is_alist vdb (repr <$> db) ∗
  (Conn.failure kI kR ∨ db_server_ready kI kR db).

Lemma server_db_alloc kI kR vdb E :
  ↑dbN.@"server".@kI ⊆ E →
  term_token kR E -∗
  SAList.is_alist vdb ∅ ==∗
  term_token kR (E ∖ ↑dbN.@"server".@kI) ∗
  server_db_disconnected kI kR vdb.
Proof.
iIntros "%sub token vdb".
iMod (rep_copy_alloc with "token") as "[? rest]" => //.
iFrame "rest". iModIntro. iExists ∅.
iFrame. rewrite /public_db big_sepM_empty. iSplit => //.
iRight. iExists []. by iFrame.
Qed.

Definition server ss : iProp := ∃ accounts E,
  sign_key (ss_key ss) ∗
  SAList.is_alist (ss_clients ss) (repr <$> accounts) ∗
  term_token (ss_key ss) E ∗
  ⌜∀ kI, TKey Open kI ∉ dom accounts → ↑dbN.@"server".@kI ⊆ E⌝ ∗
  [∗ map] vkI ↦ scs ∈ accounts, ∃ kI, ⌜vkI = TKey Open kI⌝ ∗
     is_lock (scs_name scs) (scs_lock scs)
       (server_db_disconnected kI (ss_key ss) (scs_db scs)).

Lemma serverI kR vclients :
  term_token kR (↑dbN.@"server") -∗
  sign_key kR -∗
  SAList.is_alist vclients ∅ -∗
  server {| ss_key := kR; ss_clients := vclients |}.
Proof.
iIntros "token #p_vk clients".
iExists ∅, (↑dbN.@"server") => /=.
iFrame. iSplit => //. iSplit => //.
iPureIntro. move=> *. solve_ndisj.
Qed.

Definition store_call_pred kI kR si ts : iProp :=
  ∃ t1 t2 os,
    ⌜ts = [t1; t2]⌝ ∗
    rep_update kI kR dbN [] os (os ++ [Store t1 t2]).

Definition store_resp_pred kI kR si ts : iProp :=
  ∃ os, rep_current kI kR dbN [] os.

(* MOVE *)
Lemma to_db_app os o  :
  DB.to_db (os ++ [o]) = DB.op_app (DB.to_db os) o.
Proof. exact: foldl_app. Qed.
(* /MOVE *)

Lemma store_call t2' kI kR cs t1 t2 :
  let P := compromised_session Init cs in
  db_connected' kI kR cs -∗
  db_mapsto kI kR t1 t2 ==∗
  (P ∨ store_call_pred kI kR cs [t1; t2']) ∗
  db_mapsto kI kR t1 t2' ∗
  ∀ ts, P ∨ store_resp_pred kI kR cs ts -∗ db_connected' kI kR cs.
Proof.
iIntros "% (%db & ready & own_db) own_frag".
iMod (DB.db_state_update t2' with "own_db own_frag") as "[Hstate Hmapsto]".
iFrame.
iDestruct "ready" as "[#?|ready]".
{ iModIntro. iSplitR; eauto.
  iIntros "% _". iExists _. iFrame. eauto. }
iDestruct "ready" as "(%os & -> & ready & cur)".
iMod (rep_main_update (os ++ [Store t1 t2']) with "ready cur")
  as "[ready cur]".
iModIntro. iSplitL "cur".
{ iRight. iExists _, _, _. by iFrame. }
iIntros "%ts [#?|(%os' & cur)]".
{ iExists _. iFrame. by eauto. }
iPoseProof (rep_main_current with "ready cur") as "<-".
iExists _. iFrame.
iRight. iExists _. iFrame. by rewrite to_db_app.
Qed.

Lemma store_resp kI kR cs db t1 t2 :
  let P := compromised_session Resp cs in
  (P ∨ db_server_ready kI kR db) -∗
  (P ∨ store_call_pred kI kR cs [t1; t2]) ==∗
  (P ∨ db_server_ready kI kR (<[t1 := t2]>db)) ∗
  (P ∨ store_resp_pred kI kR cs [TInt 0]).
Proof.
iIntros "% [#?|ready] [#?|call]"; try by iModIntro; iSplitL; eauto.
iDestruct "ready" as "(%os & -> & ready)".
iDestruct "call" as "(% & % & %os' & %e & upd)".
case: e => <- <-.
iMod (rep_copy_update with "ready upd") as "(<- & ready & cur)".
iModIntro. iSplitL "ready"; iRight.
- iExists _; iFrame. by rewrite to_db_app.
- iExists _; iFrame.
Qed.

Definition create_call_pred kI kR si ts : iProp :=
  ∃ t1 t2 os, ⌜ts = [t1; t2]⌝ ∗ ⌜DB.to_db os !! t1 = None⌝ ∗
    rep_update kI kR dbN [] os (os ++ [Create t1 t2]).

Definition create_resp_pred kI kR si ts : iProp :=
  ∃ os, rep_current kI kR dbN [] os.

Lemma create_call t1 t2 kI kR cs :
  let P := compromised_session Init cs in
  db_connected' kI kR cs -∗
  db_free_at kI kR {[t1]} ==∗
  (P ∨ create_call_pred kI kR cs [t1; t2]) ∗
  db_mapsto kI kR t1 t2 ∗
  ∀ ts, P ∨ create_resp_pred kI kR cs ts -∗
        db_connected' kI kR cs.
Proof.
iIntros "% (%db & ready & state) free".
iMod (DB.db_state_create t1 t2 with "state free") as "(%db_t1 & state & mapsto)".
rewrite /= db_t1. iFrame.
iDestruct "ready" as "[#?|(%os & -> & ready & cur)]".
{ iModIntro; iSplitR; eauto.
  iIntros "% _". iExists _. iFrame. eauto. }
iMod (rep_main_update (os ++ [Create t1 t2]) with "ready cur")
  as "[ready upd]".
iModIntro. iSplitL "upd".
{ iRight. iExists _, _, _. iFrame. by eauto. }
iIntros "% [#?|(%os' & cur)]".
{ iExists _. iFrame. by eauto. }
iPoseProof (rep_main_current with "ready cur") as "<-".
iExists _. iFrame. iRight.
iExists _. iFrame. by rewrite to_db_app /= db_t1.
Qed.

Lemma create_resp kI kR cs db t1 t2 :
  let P := compromised_session Resp cs in
  (P ∨ db_server_ready kI kR db) -∗
  (P ∨ create_call_pred kI kR cs [t1; t2]) ==∗
  (P ∨ db_server_ready kI kR (<[t1 := t2]>db)) ∗
  (P ∨ create_resp_pred kI kR cs [TInt 0]).
Proof.
iIntros "% [#?|ready] [#?|call]"; try by iModIntro; iSplitL; eauto.
iDestruct "ready" as "(%os & -> & ready)".
iDestruct "call" as "(% & % & %os' & %e & %db_t1 & upd)".
case: e => <- <- in db_t1 *.
iMod (rep_copy_update with "ready upd") as "(<- & ready & cur)".
iModIntro. iSplitL "ready"; iRight.
- iExists _; iFrame. by rewrite to_db_app /= db_t1.
- iExists _; iFrame.
Qed.

Definition load_call_pred kI kR si ts : iProp :=
  ∃ t1 t2 os, ⌜ts = [t1]⌝ ∗ ⌜DB.to_db os !! t1 = Some t2⌝ ∗
              rep_update kI kR dbN [] os (os ++ [Load t1]).

Definition load_resp_pred kI kR si ts : iProp :=
  ∃ t1 t2 os, ⌜ts = [t2]⌝ ∗ ⌜DB.to_db os !! t1 = Some t2⌝ ∗
              rep_current kI kR dbN [] (os ++ [Load t1]).

Lemma load_call t1 t2 kI kR cs :
  let P := compromised_session Init cs in
  db_connected' kI kR cs -∗
  db_mapsto kI kR t1 t2 ==∗
  (P ∨ load_call_pred kI kR cs [t1]) ∗
  db_mapsto kI kR t1 t2 ∗
  ∀ ts, P ∨ load_resp_pred kI kR cs ts -∗
        (P ∨ ⌜ts = [t2]⌝) ∗
        db_connected' kI kR cs.
Proof.
iIntros "% (%db & ready & state) mapsto".
iPoseProof (DB.db_state_mapsto with "state mapsto") as "%db_t1".
iFrame.
iDestruct "ready" as "[#?|(%os & -> & ready & cur)]".
{ iModIntro. iSplitR; eauto.
  iIntros "% _". iSplit; eauto. iExists _. iFrame. by eauto. }
iMod (rep_main_update (os ++ [Load t1]) with "ready cur")
  as "[ready cur]".
iModIntro. iSplitR "ready state".
{ iRight. iExists _, _, _. iFrame. by eauto. }
iIntros "% [#?|(%t1' & %t2' & %os' & -> & %db_t1' & cur)]".
{ iSplit; eauto. iFrame. by eauto. }
iPoseProof (rep_main_current with "ready cur") as "%e".
case: (app_inj_tail _ _ _ _ e) => [<- [<-]] in db_t1' *.
rewrite db_t1' in db_t1. case: db_t1 => ->.
iSplit; eauto. iExists _. iFrame.
iRight. iExists _. iFrame. by rewrite to_db_app.
Qed.

Lemma load_resp kI kR cs db t1 :
  let P := compromised_session Resp cs in
  let t2 := default (TInt 0) (db !! t1) in
  (P ∨ db_server_ready kI kR db) -∗
  (P ∨ load_call_pred kI kR cs [t1]) ==∗
  (P ∨ db_server_ready kI kR db) ∗
  (P ∨ load_resp_pred kI kR cs [t2]).
Proof.
iIntros "%P /= [#?|ready] [#?|call]"; try by iModIntro; iSplitL; eauto.
iDestruct "ready" as "(%os & -> & ready)".
iDestruct "call" as "(%t1' & %t2 & %os' & %e & %db_t1 & upd)".
case: e => <- in db_t1 *.
iMod (rep_copy_update with "ready upd") as "(<- & ready & cur)".
rewrite db_t1 /=. iModIntro.
iSplitL "ready"; iRight.
- iExists (os ++ [Load t1]). rewrite to_db_app /=.
  by iFrame.
- iExists _; iFrame. by eauto.
Qed.

Definition store_ctx : iProp :=
  RPC.rpc_pred dbN "store" store_call_pred store_resp_pred ∗
  RPC.rpc_pred dbN "load" load_call_pred load_resp_pred ∗
  RPC.rpc_pred dbN "create" create_call_pred create_resp_pred ∗
  RPC.ctx.

Lemma store_ctx_alloc E :
  ↑dbN ⊆ E →
  seal_pred_token E -∗
  RPC.ctx ==∗
  store_ctx ∗ seal_pred_token (E ∖ ↑dbN).
Proof.
iIntros "%sub token #?".
rewrite (seal_pred_token_difference (↑dbN)) => //.
iDestruct "token" as "[token ?]". iFrame.
iMod (RPC.rpc_pred_set _ (s := "store") with "token")
  as "[store token]"; try solve_ndisj.
iFrame.
iMod (RPC.rpc_pred_set _ (s := "load") with "token")
  as "[load token]"; try solve_ndisj.
iFrame.
iMod (RPC.rpc_pred_set _ (s := "create") with "token")
  as "[create token]"; try solve_ndisj.
Qed.

Ltac solve_ctx :=
  iIntros "ctx"; repeat (
    try solve [iApply "ctx"];
    iDestruct "ctx" as "[H ctx]";
    first [iApply "H" | iClear "H"]
  ).

Lemma store_ctx_store :
  store_ctx -∗
  RPC.rpc_pred dbN "store" store_call_pred store_resp_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_load :
  store_ctx -∗
  RPC.rpc_pred dbN "load" load_call_pred load_resp_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_create :
  store_ctx -∗
  RPC.rpc_pred dbN "create" create_call_pred create_resp_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_rpc_ctx : store_ctx -∗ RPC.ctx.
Proof. solve_ctx. Qed.

End Defs.

Arguments storeGS Σ : clear implicits.
