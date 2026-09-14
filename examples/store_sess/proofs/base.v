From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis replica primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn alist.
From cryptis.examples.sess Require impl.
From cryptis.examples.sess.proofs Require Import base.
From cryptis.examples.sess Require Import proofs tag.
From cryptis.examples.store Require Import db.
From actris.channel Require Import proto_model proto.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Notation dbN := (nroot.@"db_sess").

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

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ,
          !sessG Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (si : sess_info).
Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t k v : term) (ts : list term).
Implicit Types (db : gmap term term).
Implicit Types accounts : gmap term server_client_state.
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types (failed : bool).

Definition db_client_ready skI skR db : iProp :=
  rep_main skI skR dbN db ∗ rep_sync skI skR dbN ∅ db.

Definition db_server_ready skI skR db : iProp :=
  rep_copy skI skR dbN ∅ db.

Definition db_client_busy skI skR : iProp :=
  ∃ db, rep_main skI skR dbN db.

Definition db_server_busy skI skR : iProp :=
  ∃ db, rep_copy skI skR dbN ∅ db ∗ rep_sync skI skR dbN ∅ db.

Lemma db_connect_call skI skR db :
  db_client_ready skI skR db ==∗
  db_client_busy skI skR ∗ rep_update skI skR dbN ∅ db db.
Proof.
iIntros "[main cur]".
iMod (rep_main_update db with "main cur") as "[main upd]".
iModIntro. by iFrame.
Qed.

Lemma db_connect_resp skI skR db db' :
  db_server_ready skI skR db -∗
  rep_update skI skR dbN ∅ db' db' ==∗
  ⌜db' = db⌝ ∗ db_server_busy skI skR.
Proof.
iIntros "copy upd".
iMod (rep_copy_update with "copy upd") as "(%e & copy & cur)".
iModIntro. iSplit; first by rewrite e.
iExists db'. iFrame.
Qed.

Lemma db_close_resp skI skR db :
  db_server_busy skI skR -∗
  db_client_busy skI skR ==∗
  db_client_ready skI skR db ∗ db_server_ready skI skR db.
Proof.
iIntros "(%db0 & copy & cur) (%db1 & main)".
iPoseProof (rep_main_sync with "main cur") as "->".
iMod (rep_main_update db with "main cur") as "[main upd]".
iMod (rep_copy_update with "copy upd") as "(_ & copy & cur)".
iModIntro. rewrite /db_client_ready /db_server_ready. by iFrame.
Qed.

Definition db_arms skI skR si
    (rec : gmap term term -d> iProto Σ term)
    db : gmap namespace (iMsg Σ term) :=
  <[dbN.@"store" :=
      (∃ k, ∃ v, MSG Spec.of_list [k; v] {{ True }};
         rec (<[k := v]> db))%msg]>
  (<[dbN.@"load" :=
      (∃ k, MSG k {{ ⌜is_Some (db !! k)⌝ }};
         (<? v> MSG v {{ ⌜db !! k = Some v⌝ }}; rec db)%proto)%msg]>
  (<[dbN.@"create" :=
      (∃ k, ∃ v, MSG Spec.of_list [k; v] {{ ⌜db !! k = None⌝ }};
         rec (<[k := v]> db))%msg]>
  {[dbN.@"close" :=
      (MSG (TInt 0) {{ db_client_busy skI skR }};
         (<?> MSG (TInt 0) {{ db_client_ready skI skR db ∗
                              released (si_resp_share si) }};
          END)%proto)%msg]})).

Definition db_st_aux skI skR si
    (rec : gmap term term -d> iProto Σ term) :
    gmap term term -d> iProto Σ term :=
  λ db, iProto_tag Send (db_arms skI skR si rec db).

Global Instance db_st_aux_contractive skI skR si :
  Contractive (db_st_aux skI skR si).
Proof.
move=> n r1 r2 Hr db.
rewrite /db_st_aux /iProto_tag /db_arms.
f_equiv.
apply iMsg_tag_ne.
solve_proto_contractive.
Qed.

Definition db_st skI skR si : gmap term term -d> iProto Σ term :=
  fixpoint (db_st_aux skI skR si).

Lemma db_st_unfold skI skR si db :
  db_st skI skR si db ≡
  iProto_tag Send (db_arms skI skR si (db_st skI skR si) db).
Proof. exact: (fixpoint_unfold (db_st_aux skI skR si) db). Qed.

Lemma db_st_dual_unfold skI skR si db :
  iProto_dual (db_st skI skR si db)
  ≡ iProto_tag Recv (iMsg_dual <$> db_arms skI skR si (db_st skI skR si) db).
Proof. rewrite db_st_unfold iProto_dual_tag //. Qed.

Lemma iProto_le_of_equiv (p q : iProto Σ term) : p ≡ q → ⊢ p ⊑ q.
Proof. intros E. setoid_rewrite E. iApply iProto_le_refl. Qed.

Lemma connected_public_key_or' skI skR rl cs p P :
  connected skI skR rl cs p -∗
  release_token (si_share_of rl cs) -∗
  (public (si_key cs) ∨ P) -∗
  connected skI skR rl cs p ∗
  release_token (si_share_of rl cs) ∗
  ◇ (compromised cs ∨ P).
Proof.
rewrite /connected. iIntros "[gc own] rel disj".
iDestruct (GenConn.connected_public_key_or with "gc rel disj")
  as "(gc & rel & disj)".
by iFrame.
Qed.

Lemma connected_compromised skI skR rl cs p q :
  connected skI skR rl cs p -∗
  compromised cs -∗
  connected skI skR rl cs q.
Proof.
rewrite /connected. iIntros "[gc _] #comp". iFrame.
iLeft. by iApply compromised_public.
Qed.

Lemma connected_failure' skI skR rl cs p :
  connected skI skR rl cs p -∗
  compromised cs -∗
  GenConn.failure skI skR.
Proof.
rewrite /connected. iIntros "[gc _] #comp".
iPoseProof (GenConn.connected_keyE with "gc") as "(-> & -> & _)".
by iApply GenConn.session_failed_failure.
Qed.

Lemma connected_released skI skR rl cs p :
  connected skI skR rl cs p -∗
  released (si_init_share cs) -∗
  released (si_resp_share cs) -∗
  public (si_key cs).
Proof.
rewrite /connected. iIntros "[gc _] #r1 #r2".
iPoseProof (GenConn.connected_released_session with "gc") as "#H".
iApply "H". iNext. by iSplit.
Qed.

Lemma db_store_load : dbN.@"store" ≠ dbN.@"load".
Proof. move=> e; case: (ndot_inj _ _ _ _ e) => _ e2; by discriminate e2. Qed.
Lemma db_store_create : dbN.@"store" ≠ dbN.@"create".
Proof. move=> e; case: (ndot_inj _ _ _ _ e) => _ e2; by discriminate e2. Qed.
Lemma db_store_close : dbN.@"store" ≠ dbN.@"close".
Proof. move=> e; case: (ndot_inj _ _ _ _ e) => _ e2; by discriminate e2. Qed.
Lemma db_load_create : dbN.@"load" ≠ dbN.@"create".
Proof. move=> e; case: (ndot_inj _ _ _ _ e) => _ e2; by discriminate e2. Qed.
Lemma db_load_close : dbN.@"load" ≠ dbN.@"close".
Proof. move=> e; case: (ndot_inj _ _ _ _ e) => _ e2; by discriminate e2. Qed.
Lemma db_create_close : dbN.@"create" ≠ dbN.@"close".
Proof. move=> e; case: (ndot_inj _ _ _ _ e) => _ e2; by discriminate e2. Qed.

Lemma db_arms_store skI skR si rec db :
  db_arms skI skR si rec db !! dbN.@"store" =
  Some (∃ k, ∃ v, MSG Spec.of_list [k; v] {{ True }};
          rec (<[k := v]> db))%msg.
Proof. by rewrite /db_arms lookup_insert_eq. Qed.

Lemma db_arms_load skI skR si rec db :
  db_arms skI skR si rec db !! dbN.@"load" =
  Some (∃ k, MSG k {{ ⌜is_Some (db !! k)⌝ }};
          (<? v> MSG v {{ ⌜db !! k = Some v⌝ }}; rec db)%proto)%msg.
Proof.
rewrite /db_arms lookup_insert_ne; last exact: db_store_load.
by rewrite lookup_insert_eq.
Qed.

Lemma db_arms_create skI skR si rec db :
  db_arms skI skR si rec db !! dbN.@"create" =
  Some (∃ k, ∃ v, MSG Spec.of_list [k; v] {{ ⌜db !! k = None⌝ }};
          rec (<[k := v]> db))%msg.
Proof.
rewrite /db_arms lookup_insert_ne; last exact: db_store_create.
rewrite lookup_insert_ne; last exact: db_load_create.
by rewrite lookup_insert_eq.
Qed.

Lemma db_arms_close skI skR si rec db :
  db_arms skI skR si rec db !! dbN.@"close" =
  Some (MSG (TInt 0) {{ db_client_busy skI skR }};
          (<?> MSG (TInt 0) {{ db_client_ready skI skR db ∗
                               released (si_resp_share si) }};
           END)%proto)%msg.
Proof.
rewrite /db_arms lookup_insert_ne; last exact: db_store_close.
rewrite lookup_insert_ne; last exact: db_load_close.
rewrite lookup_insert_ne; last exact: db_create_close.
by rewrite lookup_singleton_eq.
Qed.

Lemma db_arms_dom skI skR si rec db :
  dom (db_arms skI skR si rec db) =
  {[dbN.@"store"; dbN.@"load"; dbN.@"create"; dbN.@"close"]}.
Proof. rewrite /db_arms !dom_insert_L dom_empty_L. set_solver. Qed.

Definition db_st0 skI skR si : iProto Σ term :=
  iProto_tag Send
    {[dbN.@"connect" :=
        (∃ db, MSG (TInt 0) {{ rep_update skI skR dbN ∅ db db }};
           db_st skI skR si db)%msg]}.

Definition store_params : GenConn.params Σ := {|
  GenConn.init_pred := λ skI skR si rl,
    sess_own skI skR si rl
      (if rl is Init then db_st0 skI skR si
       else iProto_dual (db_st0 skI skR si));
  GenConn.chan_inv := sess_ctx;
|}%I.

Definition store_ctx : iProp := GenConn.ctx dbN store_params.

Lemma store_ctx_alloc E :
  ↑dbN ⊆ E →
  GenConn.base_ctx -∗
  iso_dh_ctx -∗
  iso_dh_token E ==∗
  store_ctx ∗ iso_dh_token (E ∖ ↑dbN).
Proof. exact: GenConn.ctx_alloc. Qed.

Definition db_disconnected skI skR : iProp := ∃ db,
  (GenConn.failure skI skR ∨ db_client_ready skI skR db) ∗
  DB.db_state skI skR dbN db.

Definition db_connected' skI skR cs db : iProp :=
  (compromised cs ∨ db_client_busy skI skR) ∗
  DB.db_state skI skR dbN db.

Definition db_connected skI skR cs : iProp := ∃ db,
  connected skI skR Init cs (db_st skI skR cs db) ∗
  release_token (si_init_share cs) ∗
  db_connected' skI skR cs db.

Lemma db_connected_ok skI skR cs :
  db_connected skI skR cs -∗
  secret skI -∗
  secret skR -∗
  ◇ session_ok cs.
Proof.
iIntros "(%db & (gc & _) & _ & _) s1 s2".
by iApply (GenConn.connected_ok with "gc s1 s2").
Qed.

Lemma db_connected_ok_compromised skI skR cs :
  db_connected skI skR cs -∗
  session_ok cs -∗
  compromised cs -∗
  ▷ False.
Proof.
iIntros "(%db & _ & rel & _) ok comp".
iApply (session_ok_compromised Init with "ok comp rel").
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
iMod (DB.db_state_alloc _ (N := dbN) with "skI_token")
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
- rewrite lookup_insert_eq. iIntros "%e". case: e => ->. by eauto.
- by rewrite lookup_insert_ne //.
Qed.

Definition server_db_connected' skI skR cs vdb db : iProp :=
  public_db db ∗
  AList.is_alist vdb (repr <$> db) ∗
  (compromised cs ∨ db_server_busy skI skR).

Definition server_db_connected skI skR cs vdb : iProp := ∃ db,
  connected skI skR Resp cs (iProto_dual (db_st skI skR cs db)) ∗
  release_token (si_resp_share cs) ∗
  server_db_connected' skI skR cs vdb db.

Definition server_db_disconnected skI skR vdb : iProp := ∃ db,
  public_db db ∗
  AList.is_alist vdb (repr <$> db) ∗
  (GenConn.failure skI skR ∨ db_server_ready skI skR db).

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

Definition server_handler skI skR cs vdb (h : handler) : iProp :=
  □ ∀ db (t : term) p,
    {{{ connected skI skR Resp cs p ∗
        release_token (si_resp_share cs) ∗
        server_db_connected' skI skR cs vdb db ∗
        public t ∗
        (public (si_key cs) ∨
           match (iMsg_dual <$> db_arms skI skR cs (db_st skI skR cs) db)
                   !! handler_tag h with
           | Some m => iMsg_car m t (Next p)
           | None => False
           end) }}}
      handler_val h t
    {{{ (b : bool), RET #b;
        if b then server_db_connected skI skR cs vdb
        else server_db_disconnected skI skR vdb }}}.

Global Instance server_handler_persistent skI skR cs vdb h :
  Persistent (server_handler skI skR cs vdb h).
Proof. apply _. Qed.

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

End Defs.

Arguments storeGS Σ : clear implicits.
