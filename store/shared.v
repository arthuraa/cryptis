From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis primitives tactics role iso_dh conn rpc.
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
  storeGS_db  : dbGS Σ;
}.

Local Existing Instance storeGS_db.

Definition storeΣ := #[
  dbΣ
].

Global Instance subG_storeGS Σ : subG storeΣ Σ → storeGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !storeGS Σ, !tlockG Σ}.
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

Definition db_disconnected kI kR : iProp := ∃ db,
  (Conn.failure kI kR ∨ DB.db_client_ready kI kR N db) ∗
  DB.db_state kI kR N db.

Definition db_connected kI kR cs : iProp := ∃ db,
  RPC.client_connected kI kR cs ∗
  (compromised_session Init cs ∨ DB.db_client_ready kI kR N db) ∗
  DB.db_state kI kR N db.

Lemma db_connected_ok kI kR cs :
  db_connected kI kR cs -∗
  secret kI -∗
  secret kR -∗
  sign_key kI -∗
  sign_key kR -∗
  ◇ □ ¬ compromised_session Init cs.
Proof.
iIntros "(% & conn & _ & _)".
iApply (RPC.client_connected_ok with "conn").
Qed.

Definition rem_mapsto kI kR t1 t2 : iProp :=
  DB.mapsto kI kR N t1 t2.

Definition rem_free_at kI kR T : iProp :=
  DB.free_at kI kR N T.

Lemma rem_free_at_diff kI kR T1 T2 :
  T1 ⊆ T2 →
  rem_free_at kI kR T2 ⊣⊢ rem_free_at kI kR T1 ∗ rem_free_at kI kR (T2 ∖ T1).
Proof. iIntros "%sub". by iApply DB.free_at_diff. Qed.

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
iMod (DB.client_alloc _ (N := N) with "kI_token")
  as "(ready & state & free & kI_token)".
{ solve_ndisj. }
iModIntro. iSplitR "free".
- by iFrame.
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

Definition server_db_connected' kI kR cs vdb : iProp := ∃ db,
  public_db db ∗
  SAList.is_alist vdb (repr <$> db) ∗
  (compromised_session Resp cs ∨ DB.db_server_ready kI kR N db).

Definition server_db_connected kI kR cs vdb : iProp :=
  RPC.server_connected kI kR cs ∗
  server_db_connected' kI kR cs vdb.

Definition server_handler kI kR cs vdb h : iProp :=
  RPC.wf_handler (server_db_connected' kI kR cs vdb) kI kR cs h.

Definition server_db_disconnected kI kR vdb : iProp := ∃ db,
  public_db db ∗
  SAList.is_alist vdb (repr <$> db) ∗
  (Conn.failure kI kR ∨ DB.db_server_ready kI kR N db).

Lemma server_db_alloc kI kR vdb E :
  ↑N.@"server".@kI ⊆ E →
  term_token kR E -∗
  SAList.is_alist vdb ∅ ==∗
  term_token kR (E ∖ ↑N.@"server".@kI) ∗
  server_db_disconnected kI kR vdb.
Proof.
iIntros "%sub token vdb".
iMod (DB.server_alloc with "token") as "(dis & token)"; eauto.
iModIntro. iFrame "token". iExists ∅.
iFrame.
by rewrite /public_db big_sepM_empty.
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

Definition store_call_pred kI kR si ts : iProp :=
  ∃ t1 t2, ⌜ts = [t1; t2]⌝ ∗ DB.store_call kI kR N t1 t2.

Definition store_resp_pred kI kR si ts : iProp :=
  DB.store_resp kI kR N.

Definition load_call_pred kI kR si ts : iProp :=
  ∃ t1, ⌜ts = [t1]⌝ ∗ DB.load_call kI kR N t1.

Definition load_resp_pred kI kR si ts : iProp :=
  ∃ t2, ⌜ts = [t2]⌝ ∗ DB.load_resp kI kR N t2.

Definition create_call_pred kI kR si ts : iProp :=
  ∃ t1 t2, ⌜ts = [t1; t2]⌝ ∗ DB.create_call kI kR N t1 t2.

Definition create_resp_pred kI kR si ts : iProp :=
  DB.create_resp kI kR N.

Definition store_ctx : iProp :=
  RPC.rpc_pred N "store" store_call_pred store_resp_pred ∗
  RPC.rpc_pred N "load" load_call_pred load_resp_pred ∗
  RPC.rpc_pred N "create" create_call_pred create_resp_pred ∗
  RPC.ctx N.

Lemma store_ctx_alloc E :
  ↑N ⊆ E →
  seal_pred_token E ==∗
  store_ctx ∗ seal_pred_token (E ∖ ↑N).
Proof.
iIntros "%sub token".
rewrite (seal_pred_token_difference (↑N)) => //.
iDestruct "token" as "[token ?]". iFrame.
iMod (RPC.rpc_pred_set _ (s := "store") with "token")
  as "[store token]"; try solve_ndisj.
iFrame.
iMod (RPC.rpc_pred_set _ (s := "load") with "token")
  as "[load token]"; try solve_ndisj.
iFrame.
iMod (RPC.rpc_pred_set _ (s := "create") with "token")
  as "[create token]"; try solve_ndisj.
iFrame.
iMod (RPC.ctx_alloc (N := N) with "token")
  as "(#? & ?)"; try solve_ndisj.
Qed.

Ltac solve_ctx :=
  iIntros "ctx"; repeat (
    try solve [iApply "ctx"];
    iDestruct "ctx" as "[H ctx]";
    first [iApply "H" | iClear "H"]
  ).

Lemma store_ctx_store :
  store_ctx -∗
  RPC.rpc_pred N "store" store_call_pred store_resp_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_load :
  store_ctx -∗
  RPC.rpc_pred N "load" load_call_pred load_resp_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_create :
  store_ctx -∗
  RPC.rpc_pred N "create" create_call_pred create_resp_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_rpc_ctx : store_ctx -∗ RPC.ctx N.
Proof. solve_ctx. Qed.

End Defs.

Arguments storeGS Σ : clear implicits.
