From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis replica primitives tactics role.
From cryptis.examples Require Import iso_dh conn rpc alist.
From cryptis.examples.store Require Import db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Notation dbN := (nroot.@"db").

Record server_state := {
  ss_key : sign_key;
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
  storeGS_replica : replicaG Σ (gmap term term);
}.

Local Existing Instance storeGS_db.
Local Existing Instance storeGS_replica.

Definition storeΣ := #[
  dbΣ;
  replicaΣ (gmap term term)
].

Global Instance subG_storeGS Σ : subG storeΣ Σ → storeGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !Conn.connGS Σ, !RPC.rpcGS Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (si : sess_info).
Implicit Types (cs : Conn.state).
Implicit Types (skI skR : sign_key) (kS t : term) (ts : list term).
Implicit Types (db : gmap term term).
Implicit Types accounts : gmap term server_client_state.
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types (failed : bool).

Definition db_client_ready skI skR db : iProp :=
  rep_main skI skR dbN db ∗ rep_current skI skR dbN ∅ db.

Definition db_server_ready skI skR db : iProp :=
  rep_copy skI skR dbN ∅ db.

Definition db_disconnected skI skR : iProp := ∃ db,
  (Conn.failure skI skR ∨ db_client_ready skI skR db) ∗
  DB.db_state skI skR dbN db.

Definition db_connected' skI skR cs : iProp := ∃ db,
  (compromised_session Init cs ∨ db_client_ready skI skR db) ∗
  DB.db_state skI skR dbN db.

Definition db_connected skI skR cs : iProp :=
  RPC.client_connected skI skR cs ∗
  db_connected' skI skR cs.

Lemma db_connected_ok skI skR cs :
  db_connected skI skR cs -∗
  secret skI -∗
  secret skR -∗
  minted skI -∗
  minted skR -∗
  ◇ □ ¬ compromised_session Init cs.
Proof.
iIntros "(conn & _)".
iApply (RPC.client_connected_ok with "conn").
Qed.

Definition db_mapsto skI skR t1 t2 : iProp :=
  DB.mapsto skI skR dbN t1 t2.

Definition db_free_at skI skR T : iProp :=
  DB.free_at skI skR dbN T.

Lemma db_free_at_diff skI skR T1 T2 :
  T1 ⊆ T2 →
  db_free_at skI skR T2 ⊣⊢ db_free_at skI skR T1 ∗ db_free_at skI skR (T2 ∖ T1).
Proof. iIntros "%sub". by iApply DB.free_at_diff. Qed.

Lemma client_alloc skI skR E :
  ↑dbN.@"client".@(skR : term) ⊆ E →
  term_token skI E ==∗
  db_disconnected skI skR ∗
  db_free_at skI skR ⊤ ∗
  term_token skI (E ∖ ↑dbN.@"client".@(skR : term)).
Proof.
iIntros "%sub skI_token".
rewrite (term_token_difference _ _ _ sub).
iDestruct "skI_token" as "[skI_token ?]". iFrame.
iMod (rep_main_alloc (N := dbN) skI (kR := skR) ∅ with "skI_token")
  as "(main & cur & skI_token)"; first solve_ndisj.
iMod (DB.client_alloc _ (N := dbN) with "skI_token")
  as "(state & free & skI_token)".
{ solve_ndisj. }
iModIntro. iFrame. iRight. by iFrame.
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

Definition server_db_connected' skI skR cs vdb : iProp := ∃ db,
  public_db db ∗
  AList.is_alist vdb (repr <$> db) ∗
  (compromised_session Resp cs ∨ db_server_ready skI skR db).

Definition server_db_connected skI skR cs vdb : iProp :=
  RPC.server_connected skI skR cs ∗
  server_db_connected' skI skR cs vdb.

Definition server_handler skI skR cs vdb h : iProp :=
  RPC.wf_handler (server_db_connected' skI skR cs vdb) skI skR cs h.

Definition server_db_disconnected skI skR vdb : iProp := ∃ db,
  public_db db ∗
  AList.is_alist vdb (repr <$> db) ∗
  (Conn.failure skI skR ∨ db_server_ready skI skR db).

Lemma server_db_alloc skI skR vdb E :
  ↑dbN.@"server".@(skI : term) ⊆ E →
  term_token skR E -∗
  AList.is_alist vdb ∅ ==∗
  term_token skR (E ∖ ↑dbN.@"server".@(skI : term)) ∗
  server_db_disconnected skI skR vdb.
Proof.
iIntros "%sub token vdb".
iMod (rep_copy_alloc with "token") as "[? rest]" => //.
iFrame "rest". iModIntro. iExists ∅.
iFrame. by rewrite /public_db big_sepM_empty.
Qed.

Definition server ss : iProp := ∃ accounts E,
  minted (ss_key ss) ∗
  AList.is_alist (ss_clients ss) (repr <$> accounts) ∗
  term_token (ss_key ss) E ∗
  ⌜∀ skI, Spec.pkey skI ∉ dom accounts → ↑dbN.@"server".@(skI : term) ⊆ E⌝ ∗
  [∗ map] pkI ↦ scs ∈ accounts, ∃ skI, ⌜pkI = Spec.pkey skI⌝ ∗
     is_lock (scs_name scs) (scs_lock scs)
       (server_db_disconnected skI (ss_key ss) (scs_db scs)).

Lemma serverI skR vclients :
  term_token skR (↑dbN.@"server") -∗
  minted skR -∗
  AList.is_alist vclients ∅ -∗
  server {| ss_key := skR; ss_clients := vclients |}.
Proof.
iIntros "token #p_pk clients".
iExists ∅, (↑dbN.@"server") => /=.
iFrame. iSplit => //. iSplit => //.
iPureIntro. move=> *. solve_ndisj.
Qed.

Definition store_call_pred skI skR si t : iProp :=
  ∃ t1 t2 db,
    ⌜t = Spec.of_list [t1; t2]⌝ ∗
    rep_update skI skR dbN ∅ db (<[t1 := t2]> db).

Definition store_resp_pred skI skR si t t' : iProp :=
  ∃ db, rep_current skI skR dbN ∅ db.

Lemma store_call t2' skI skR cs t1 t2 :
  let P := compromised_session Init cs in
  db_connected' skI skR cs -∗
  db_mapsto skI skR t1 t2 ==∗
  (P ∨ store_call_pred skI skR cs (Spec.of_list [t1; t2'])) ∗
  db_mapsto skI skR t1 t2' ∗
  ∀ t', P ∨ store_resp_pred skI skR cs (Spec.of_list [t1; t2']) t' -∗
    db_connected' skI skR cs.
Proof.
iIntros "% (%db & ready & own_db) own_frag".
iMod (DB.db_state_update t2' with "own_db own_frag") as "[Hstate Hmapsto]".
iFrame.
iDestruct "ready" as "[#?|ready]".
{ iModIntro. iSplitR; eauto.
  iIntros "% _". iExists _. iFrame. eauto. }
iDestruct "ready" as "(ready & cur)".
iMod (rep_main_update (<[t1 := t2']>db) with "ready cur")
  as "[ready cur]".
iModIntro. iSplitL "cur".
{ iRight. iExists _, _, _. by iFrame. }
iIntros "%ts [#?|(%db' & cur)]".
{ iExists _. iFrame. by eauto. }
iPoseProof (rep_main_current with "ready cur") as "<-".
iExists _. iFrame. iRight. iFrame.
Qed.

Lemma store_resp skI skR cs db t1 t2 :
  let P := compromised_session Resp cs in
  (P ∨ db_server_ready skI skR db) -∗
  (P ∨ store_call_pred skI skR cs (Spec.of_list [t1; t2])) ==∗
  (P ∨ db_server_ready skI skR (<[t1 := t2]>db)) ∗
  (P ∨ store_resp_pred skI skR cs (Spec.of_list [t1; t2]) (TInt 0)).
Proof.
iIntros "% [#?|ready] [#?|call]"; try by iModIntro; iSplitL; eauto.
iDestruct "call" as "(% & % & %db' & %e & upd)".
case/Spec.of_list_inj: e => <- <-.
iMod (rep_copy_update with "ready upd") as "(<- & ready & cur)".
iModIntro. iSplitL "ready"; iRight; iFrame.
Qed.

Definition create_call_pred skI skR si t : iProp :=
  ∃ t1 t2 db, ⌜t = Spec.of_list [t1; t2]⌝ ∗ ⌜db !! t1 = None⌝ ∗
    rep_update skI skR dbN ∅ db (<[t1 := t2]>db).

Definition create_resp_pred skI skR si t t' : iProp :=
  ∃ db, rep_current skI skR dbN ∅ db.

Lemma create_call t1 t2 skI skR cs :
  let P := compromised_session Init cs in
  db_connected' skI skR cs -∗
  db_free_at skI skR {[t1]} ==∗
  (P ∨ create_call_pred skI skR cs (Spec.of_list [t1; t2])) ∗
  db_mapsto skI skR t1 t2 ∗
  ∀ t, P ∨ create_resp_pred skI skR cs (Spec.of_list [t1; t2]) t -∗
       db_connected' skI skR cs.
Proof.
iIntros "% (%db & ready & state) free".
iMod (DB.db_state_create t1 t2 with "state free") as "(%db_t1 & state & mapsto)".
iFrame.
iDestruct "ready" as "[#?|(ready & cur)]".
{ iModIntro; iSplitR; eauto.
  iIntros "% _". iExists _. iFrame. eauto. }
iMod (rep_main_update (<[t1 := t2]>db) with "ready cur")
  as "[ready upd]".
iModIntro. iSplitL "upd".
{ iRight. iExists _, _, _. iFrame. by eauto. }
iIntros "% [#?|(%db' & cur)]".
{ iExists _. iFrame. by eauto. }
iPoseProof (rep_main_current with "ready cur") as "<-".
iExists _. iFrame. iRight. iFrame.
Qed.

Lemma create_resp skI skR cs db t1 t2 :
  let P := compromised_session Resp cs in
  (P ∨ db_server_ready skI skR db) -∗
  (P ∨ create_call_pred skI skR cs (Spec.of_list [t1; t2])) ==∗
  (P ∨ db_server_ready skI skR (<[t1 := t2]>db)) ∗
  (P ∨ create_resp_pred skI skR cs (Spec.of_list [t1; t2]) (TInt 0)).
Proof.
iIntros "% [#?|ready] [#?|call]"; try by iModIntro; iSplitL; eauto.
iDestruct "call" as "(% & % & %db' & %e & %db_t1 & upd)".
case/Spec.of_list_inj: e => <- <- in db_t1 *.
iMod (rep_copy_update with "ready upd") as "(<- & ready & cur)".
iModIntro. iSplitL "ready"; iRight; iFrame.
Qed.

Definition load_call_pred skI skR si t1 : iProp :=
  ∃ t2 db, ⌜db !! t1 = Some t2⌝ ∗
           rep_update skI skR dbN ∅ db db.

Definition load_resp_pred skI skR si t1 t2 : iProp :=
  ∃ db, ⌜db !! t1 = Some t2⌝ ∗ rep_current skI skR dbN ∅ db.

Lemma load_call t1 t2 skI skR cs :
  let P := compromised_session Init cs in
  db_connected' skI skR cs -∗
  db_mapsto skI skR t1 t2 ==∗
  (P ∨ load_call_pred skI skR cs t1) ∗
  db_mapsto skI skR t1 t2 ∗
  ∀ t2', P ∨ load_resp_pred skI skR cs t1 t2' -∗
        (P ∨ ⌜t2' = t2⌝) ∗
        db_connected' skI skR cs.
Proof.
iIntros "% (%db & ready & state) mapsto".
iPoseProof (DB.db_state_mapsto with "state mapsto") as "%db_t1".
iFrame.
iDestruct "ready" as "[#?|(ready & cur)]".
{ iModIntro. iSplitR; eauto.
  iIntros "% _". iSplit; eauto. iExists _. iFrame. by eauto. }
iMod (rep_main_update db with "ready cur") as "[ready cur]".
iModIntro. iSplitR "ready state".
{ iRight. iExists _. iFrame. by eauto. }
iIntros "% [#?|(%db' & %db_t1' & cur)]".
{ iSplit; eauto. iFrame. by eauto. }
iPoseProof (rep_main_current with "ready cur") as "<-".
rewrite db_t1' in db_t1. case: db_t1 => ->.
iSplit; eauto. iExists _. iFrame. iRight. iFrame.
Qed.

Lemma load_resp skI skR cs db t1 :
  let P := compromised_session Resp cs in
  let t2 := default (TInt 0) (db !! t1) in
  (P ∨ db_server_ready skI skR db) -∗
  (P ∨ load_call_pred skI skR cs t1) ==∗
  (P ∨ db_server_ready skI skR db) ∗
  (P ∨ load_resp_pred skI skR cs t1 t2).
Proof.
iIntros "%P /= [#?|ready] [#?|call]"; try by iModIntro; iSplitL; eauto.
iDestruct "call" as "(%t2 & %db' & %db_t1 & upd)".
iMod (rep_copy_update with "ready upd") as "(<- & ready & cur)".
rewrite db_t1 /=. iModIntro.
iSplitL "ready"; iRight; iFrame. by eauto.
Qed.

Definition store_ctx : iProp :=
  RPC.rpc_pred (dbN.@"store") store_call_pred store_resp_pred ∗
  RPC.rpc_pred (dbN.@"load") load_call_pred load_resp_pred ∗
  RPC.rpc_pred (dbN.@"create") create_call_pred create_resp_pred ∗
  RPC.ctx.

Lemma store_ctx_alloc E :
  ↑dbN ⊆ E →
  RPC.rpc_token E -∗
  RPC.ctx ==∗
  store_ctx ∗ RPC.rpc_token (E ∖ ↑dbN).
Proof.
iIntros "%sub token #?".
rewrite RPC.rpc_token_difference => //.
iDestruct "token" as "[token ?]". iFrame.
iMod (RPC.rpc_pred_set (N := dbN.@"store") with "token")
  as "[store token]"; first solve_ndisj.
iFrame.
iMod (RPC.rpc_pred_set (N := dbN.@"load") with "token")
  as "[load token]"; first solve_ndisj.
iFrame.
iMod (RPC.rpc_pred_set (N := dbN.@"create") with "token")
  as "[create token]"; first solve_ndisj.
by iFrame.
Qed.

Ltac solve_ctx :=
  iIntros "ctx"; repeat (
    try solve [iApply "ctx"];
    iDestruct "ctx" as "[H ctx]";
    first [iApply "H" | iClear "H"]
  ).

Lemma store_ctx_store :
  store_ctx -∗
  RPC.rpc_pred (dbN.@"store") store_call_pred store_resp_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_load :
  store_ctx -∗
  RPC.rpc_pred (dbN.@"load") load_call_pred load_resp_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_create :
  store_ctx -∗
  RPC.rpc_pred (dbN.@"create") create_call_pred create_resp_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_rpc_ctx : store_ctx -∗ RPC.ctx.
Proof. solve_ctx. Qed.

End Defs.

Arguments storeGS Σ : clear implicits.
