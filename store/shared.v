From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib version term gmeta nown.
From cryptis Require Import cryptis primitives tactics role iso_dh conn.
From cryptis.store Require Import alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

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
  storeGS_db   : dbGS Σ;
  storeGS_conn : Conn.connGS Σ;
}.

Local Existing Instance storeGS_db.
Local Existing Instance storeGS_conn.

Definition storeΣ := #[
  dbΣ;
  Conn.connΣ
].

Global Instance subG_storeGS Σ : subG storeΣ Σ → storeGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (si : sess_info).
Implicit Types (cs : Conn.state).
Implicit Types (kI kR kS t : term) (ts : list term).
Implicit Types db : gmap term term.
Implicit Types accounts : gmap term server_client_state.
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types (failed : bool).

Variable N : namespace.

Definition db_disconnected kI kR : iProp := ∃ n failed,
  DB.client_view kI (N.@"client".@kR.@"db") n ∗
  Conn.client_disconnected N kI kR n failed.

Definition db_connected kI kR cs : iProp := ∃ n,
  DB.client_view kI (N.@"client".@kR.@"db") n ∗
  Conn.connected kI kR cs n ∗
  Conn.client_token N kI kR cs.

Lemma db_connected_ok kI kR cs :
  db_connected kI kR cs -∗
  (Conn.failure kI kR -∗ ▷ False) -∗
  ◇ Conn.session_failed cs false.
Proof.
iIntros "(% & ? & conn & _) fail".
iApply (Conn.connected_ok with "conn fail").
Qed.

Definition rem_mapsto kI kR t1 t2 : iProp :=
  DB.mapsto kI (N.@"client".@kR.@"db") t1 t2.

Definition rem_free_at kI kR T : iProp :=
  DB.free_at kI (N.@"client".@kR.@"db") T.

Lemma rem_free_at_diff kI kR T1 T2 :
  T1 ⊆ T2 →
  rem_free_at kI kR T2 ⊣⊢ rem_free_at kI kR T1 ∗ rem_free_at kI kR (T2 ∖ T1).
Proof. iIntros "%sub". by iApply DB.free_at_diff. Qed.

Lemma rem_mapsto_store t2' kI kR t1 t2 n :
  DB.client_view kI (N.@"client".@kR.@"db") n -∗
  rem_mapsto kI kR t1 t2 ==∗
  DB.client_view kI (N.@"client".@kR.@"db") (S n) ∗
  rem_mapsto kI kR t1 t2' ∗
  DB.store_at kI (N.@"client".@kR.@"db") n t1 t2'.
Proof.
iIntros "client mapsto".
iMod (DB.store_client t2' with "client mapsto")
  as "(client & #update & mapsto)".
by iFrame.
Qed.

Lemma rem_mapsto_alloc kI kR t1 t2 n T :
  t1 ∈ T →
  DB.client_view kI (N.@"client".@kR.@"db") n -∗
  rem_free_at kI kR T ==∗
  DB.client_view kI (N.@"client".@kR.@"db") (S n) ∗
  rem_mapsto kI kR t1 t2 ∗
  rem_free_at kI kR (T ∖ {[t1]}) ∗
  DB.create_at kI (N.@"client".@kR.@"db") n t1 t2.
Proof.
iIntros "%t1_T client".
have {}t1_T : {[t1]} ⊆ T by set_solver.
rewrite (rem_free_at_diff _ _ t1_T).
iIntros "[free free']". iFrame "free'".
iMod (DB.create_client _ t2 with "client free") as "(create & client & mapsto)".
iFrame. by eauto.
Qed.

Lemma client_alloc kI kR E :
  ↑N.@"client".@kR ⊆ E →
  term_token kI E ={⊤}=∗
  db_disconnected kI kR ∗
  rem_free_at kI kR ⊤ ∗
  term_token kI (E ∖ ↑N.@"client".@kR).
Proof.
iIntros "%sub kI_token".
rewrite (term_token_difference _ _ _ sub).
iDestruct "kI_token" as "[kI_token ?]". iFrame.
iMod (Conn.client_alloc kI (kR := kR) with "kI_token")
  as "[dis kI_token]" => //.
{ solve_ndisj. }
iMod (DB.alloc _ (N := N.@"client".@kR.@"db") with "kI_token")
  as "(client_view & free & #server_view & kI_token)".
{ solve_ndisj. }
iModIntro. iSplitR "free".
- iExists 0, false. iFrame.
- by iFrame.
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

Definition server_token cs : iProp :=
  Conn.session_failed cs true ∨ ∃ n0,
    Conn.clock N (si_init cs) (si_resp cs) n0 ∗
    Conn.clock N (si_init cs) (si_resp cs) n0.

Definition server_db_connected' kI kR cs n vdb : iProp :=
  ∃ db, public_db db ∗
        SAList.is_alist vdb (repr <$> db) ∗
        (Conn.session_failed cs true ∨
           DB.db_at kI (N.@"client".@kR.@"db") n db) ∗
        server_token cs.

Definition server_db_connected kI kR cs n vdb : iProp :=
  Conn.connected kI kR cs n ∗
  server_db_connected' kI kR cs n vdb.

Definition server_disconnected kI kR n failed : iProp :=
  if failed then Conn.failure kI kR
  else (⌜n = 0⌝ ∗ Conn.never_connected N kI kR ∨ Conn.clock N kI kR n)%I.

Definition server_db_disconnected' kI kR n vdb failed : iProp :=
  ∃ db,
    public_db db ∗
    SAList.is_alist vdb (repr <$> db) ∗
    (⌜failed⌝ ∨ DB.db_at kI (N.@"client".@kR.@"db") n db).

Definition server_db_disconnected kI kR vdb : iProp :=
  ∃ n failed,
    server_disconnected kI kR n failed ∗
    server_db_disconnected' kI kR n vdb failed.

Lemma server_db_alloc kI kR vdb E :
  ↑N.@"server".@kI ⊆ E →
  term_token kR E -∗
  SAList.is_alist vdb ∅ ==∗
  term_token kR (E ∖ ↑N.@"server".@kI) ∗
  server_db_disconnected kI kR vdb.
Proof.
iIntros "%sub token vdb".
iMod (Conn.server_alloc with "token") as "(dis & token)"; eauto.
iModIntro. iFrame "token". iExists 0, false.
iFrame. iExists ∅.
iSplit; first by rewrite /public_db big_sepM_empty.
iFrame. iRight. iLeft. do !iSplit => //.
Qed.

Definition server ss : iProp := ∃ accounts E,
  sign_key (ss_key ss) ∗
  SAList.is_alist (ss_clients ss) (repr <$> accounts) ∗
  term_token (ss_key ss) E ∗
  ⌜∀ kI, TKey Open kI ∉ dom accounts → ↑N.@"server".@kI ⊆ E⌝ ∗
  [∗ map] vkI ↦ scs ∈ accounts, ∃ kI, ⌜vkI = TKey Open kI⌝ ∗
     is_lock (scs_name scs) (scs_lock scs)
       (server_db_disconnected kI (ss_key ss) (scs_db scs)).

Lemma serverI kR vclients :
  term_token kR (↑N.@"server") -∗
  sign_key kR -∗
  SAList.is_alist vclients ∅ -∗
  server {| ss_key := kR; ss_clients := vclients |}.
Proof.
iIntros "token #p_vk clients".
iExists ∅, (↑N.@"server") => /=.
iFrame. iSplit => //. iSplit => //.
iPureIntro. move=> *. solve_ndisj.
Qed.

Definition store_pred kI kR si n ts : iProp := ∃ t1 t2,
  ⌜ts = [t1; t2]⌝ ∗
  DB.store_at kI (N.@"client".@kR.@"db") n t1 t2.

Definition ack_store_pred kI kR si n ts : iProp := True.

Definition load_pred kI kR si n ts : iProp :=
  ∃ t1, ⌜ts = [t1]⌝ ∗
        DB.load_at kI (N.@"client".@kR.@"db") n t1.

Definition ack_load_pred kI kR si n ts : iProp :=
  ∃ t1 t2, ⌜ts = [t2]⌝ ∗
    DB.load_at kI (N.@"client".@kR.@"db") n t1 ∗
    DB.stored_at kI (N.@"client".@kR.@"db") (S n) t1 t2.

Definition create_pred kI kR si n ts : iProp := ∃ t1 t2,
  ⌜ts = [t1; t2]⌝ ∗
  DB.create_at kI (N.@"client".@kR.@"db") n t1 t2.

Definition ack_create_pred kI kR si n ts : iProp := True.

Definition server_handler_post kI kR cs vdb v : iProp :=
  ⌜v = #true⌝ ∗
  (∃ n, server_db_connected kI kR cs n vdb) ∨
  ⌜v = #false⌝ ∗ server_db_disconnected kI kR vdb.

Lemma ack_load_predI skI skR cs n t1 t2 db :
  db !! t1 = Some t2 →
  □ (Conn.session_failed cs true ∨ load_pred skI skR cs n [t1]) -∗
  □ (Conn.session_failed cs true ∨
       DB.db_at skI (N.@"client".@skR.@"db") n db) -∗
  (Conn.session_failed cs true ∨ □ ack_load_pred skI skR cs n [t2]) ∗
  □ (Conn.session_failed cs true ∨
       DB.db_at skI (N.@"client".@skR.@"db") (S n) db).
Proof.
iIntros "%db_t1 #[?|load] #[?|db_at]"; eauto.
iDestruct "load" as "(%t1' & %e & load)".
case: e => <- {t1'}.
iSplit; iRight.
- iModIntro. iExists t1, t2. do !iSplit => //.
  iApply DB.load_at_stored_at => //.
  by iApply DB.stored_atI.
- iModIntro. iApply (DB.db_at_op_at with "db_at load").
Qed.

Definition store_ctx : iProp :=
  seal_pred (N.@"store")      (Conn.conn_pred store_pred) ∗
  seal_pred (N.@"ack_store")  (Conn.conn_pred ack_store_pred) ∗
  seal_pred (N.@"load")       (Conn.conn_pred load_pred) ∗
  seal_pred (N.@"ack_load")   (Conn.conn_pred ack_load_pred) ∗
  seal_pred (N.@"create")     (Conn.conn_pred create_pred) ∗
  seal_pred (N.@"ack_create") (Conn.conn_pred ack_create_pred) ∗
  Conn.ctx N.

Lemma store_ctx_alloc E :
  ↑N ⊆ E →
  seal_pred_token E ==∗
  store_ctx ∗ seal_pred_token (E ∖ ↑N).
Proof.
iIntros "%sub token".
rewrite (seal_pred_token_difference (↑N)) => //.
iDestruct "token" as "[token ?]". iFrame.
iMod (seal_pred_set (N.@"store") with "token")
  as "[store token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"ack_store") with "token")
  as "[ack_store token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"load") with "token")
  as "[load token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"ack_load") with "token")
  as "[ack_load token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"create") with "token")
  as "[create token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"ack_create") with "token")
  as "[ack_create token]"; try solve_ndisj.
iFrame.
iMod (Conn.ctx_alloc (N := N) with "token")
  as "(#iso_dh & ?)"; try solve_ndisj.
Qed.

Ltac solve_ctx :=
  iIntros "ctx"; repeat (
    try solve [iApply "ctx"];
    iDestruct "ctx" as "[H ctx]";
    first [iApply "H" | iClear "H"]
  ).

Lemma store_ctx_store :
  store_ctx -∗ seal_pred (N.@"store") (Conn.conn_pred store_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_store :
  store_ctx -∗ seal_pred (N.@"ack_store") (Conn.conn_pred ack_store_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_load :
  store_ctx -∗ seal_pred (N.@"load") (Conn.conn_pred load_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_load :
  store_ctx -∗ seal_pred (N.@"ack_load") (Conn.conn_pred ack_load_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_create :
  store_ctx -∗ seal_pred (N.@"create") (Conn.conn_pred create_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_create :
  store_ctx -∗ seal_pred (N.@"ack_create") (Conn.conn_pred ack_create_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_conn_ctx : store_ctx -∗ Conn.ctx N.
Proof. solve_ctx. Qed.

End Defs.

Arguments storeGS Σ : clear implicits.
