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
From cryptis.examples Require Import iso_dh gen_conn alist sess.
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
          !Sess.sessG Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (si : sess_info).
Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t k v : term) (ts : list term).
Implicit Types (db : gmap term term) (odb : option (gmap term term)).
Implicit Types accounts : gmap term server_client_state.
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types (failed : bool).

Definition db_main' skI skR db : iProp :=
  rep_main skI skR dbN db ∗ rep_current skI skR dbN ∅ db.

Definition db_main skI skR db : iProp :=
  GenConn.failure skI skR ∨ db_main' skI skR db.

Definition db_copy' skI skR db : iProp :=
  rep_copy skI skR dbN ∅ db.

Definition db_copy skI skR db : iProp :=
  GenConn.failure skI skR ∨ db_copy' skI skR db.

Definition db_client_token skI skR odb db : iProp :=
  match odb with
  | Some db' => ⌜db' = db⌝
  | None => db_main' skI skR db
  end.

Definition db_server_token skI skR odb db : iProp :=
  match odb with
  | Some db' => ⌜db' = db⌝ ∗ db_main' skI skR db ∗ db_copy' skI skR db
  | None => db_copy' skI skR db
  end.

Lemma db_update db' skI skR db1 db2 :
  db_main' skI skR db1 -∗
  db_copy' skI skR db2 ==∗
  ⌜db1 = db2⌝ ∗
  db_main' skI skR db' ∗
  db_copy' skI skR db'.
Proof.
iIntros "(main & cur) copy".
iMod (rep_main_update db' with "main cur") as "[main upd]".
iMod (rep_copy_update with "copy upd") as "(<- & ? & ?)".
by iFrame.
Qed.

Lemma db_update_token db' skI skR odb db1 db2 :
  db_client_token skI skR odb db1 -∗
  db_server_token skI skR odb db2 ==∗
  ⌜db1 = db2⌝ ∗ db_server_token skI skR (Some db') db'.
Proof.
iIntros "token1 token2"; case: odb => [db|] /=.
- iDestruct "token1" as "<-".
  iDestruct "token2" as "(<- & main & copy)".
  iMod (db_update db' with "main copy") as "(_ & main & copy)".
  iModIntro. iSplitR; eauto. by iFrame.
- iMod (db_update db' with "token1 token2") as "(<- & main & copy)".
  iModIntro. iSplitR; eauto. by iFrame.
Qed.

Definition db_arms skI skR si
    (rec : option (gmap term term) -d> iProto Σ term)
    (odb : option (gmap term term)) : gmap namespace (iMsg Σ term) :=
  <[dbN.@"store" :=
      (∃ db k v, MSG Spec.of_list [k; v] {{ db_client_token skI skR odb db }};
         rec (Some (<[k := v]> db)))%msg]>
  (<[dbN.@"load" :=
      (∃ db k, MSG k {{ db_client_token skI skR odb db ∗ ⌜is_Some (db !! k)⌝ }};
         (<? v> MSG v {{ ⌜db !! k = Some v⌝ }}; rec (Some db))%proto)%msg]>
  (<[dbN.@"create" :=
      (∃ db k v, MSG Spec.of_list [k; v] {{ db_client_token skI skR odb db
                                            ∗ ⌜db !! k = None⌝ }};
         rec (Some (<[k := v]> db)))%msg]>
  {[dbN.@"close" :=
      (∃ db, MSG (TInt 0) {{ db_client_token skI skR odb db }};
         (<?> MSG (TInt 0) {{ db_main' skI skR db ∗
                              released (si_resp_share si) }};
          END)%proto)%msg]})).

Definition db_st_aux skI skR si
    (rec : option (gmap term term) -d> iProto Σ term) :
    option (gmap term term) -d> iProto Σ term :=
  λ odb, iProto_tag Send (db_arms skI skR si rec odb).

Global Instance db_st_aux_contractive skI skR si :
  Contractive (db_st_aux skI skR si).
Proof.
move=> n r1 r2 Hr odb.
rewrite /db_st_aux /iProto_tag /db_arms.
f_equiv.
apply iMsg_tag_ne.
solve_proto_contractive.
Qed.

Definition db_st skI skR si : option (gmap term term) -d> iProto Σ term :=
  fixpoint (db_st_aux skI skR si).

Lemma db_st_unfold skI skR si odb :
  db_st skI skR si odb ≡
  iProto_tag Send (db_arms skI skR si (db_st skI skR si) odb).
Proof. exact: (fixpoint_unfold (db_st_aux skI skR si) odb). Qed.

Lemma db_st_dual_unfold skI skR si odb :
  iProto_dual (db_st skI skR si odb)
  ≡ iProto_tag Recv (iMsg_dual <$> db_arms skI skR si (db_st skI skR si) odb).
Proof. rewrite db_st_unfold iProto_dual_tag //. Qed.

Lemma connected_public_key_or' skI skR rl cs p P :
  Sess.connected skI skR rl cs p -∗
  release_token (si_share_of rl cs) -∗
  (public (si_key cs) ∨ P) -∗
  Sess.connected skI skR rl cs p ∗
  release_token (si_share_of rl cs) ∗
  ◇ (compromised cs ∨ P).
Proof.
rewrite /Sess.connected. iIntros "[gc own] rel disj".
iDestruct (GenConn.connected_public_key_or with "gc rel disj")
  as "(gc & rel & disj)".
by iFrame.
Qed.

Lemma connected_compromised skI skR rl cs p q :
  Sess.connected skI skR rl cs p -∗
  compromised cs -∗
  Sess.connected skI skR rl cs q.
Proof.
rewrite /Sess.connected. iIntros "[gc _] #comp". iFrame.
iLeft. by iApply compromised_public.
Qed.

Lemma connected_failure' skI skR rl cs p :
  Sess.connected skI skR rl cs p -∗
  compromised cs -∗
  GenConn.failure skI skR.
Proof.
rewrite /Sess.connected. iIntros "[gc _] #comp".
iPoseProof (GenConn.connected_keyE with "gc") as "(-> & -> & _)".
by iApply GenConn.session_failed_failure.
Qed.

Lemma connected_released skI skR rl cs p :
  Sess.connected skI skR rl cs p -∗
  released (si_init_share cs) -∗
  released (si_resp_share cs) -∗
  public (si_key cs).
Proof.
rewrite /Sess.connected. iIntros "[gc _] #r1 #r2".
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

Lemma db_arms_store skI skR si rec odb :
  db_arms skI skR si rec odb !! dbN.@"store" =
  Some (∃ db k v, MSG Spec.of_list [k; v] {{ db_client_token skI skR odb db }};
          rec (Some (<[k := v]> db)))%msg.
Proof. by rewrite /db_arms lookup_insert. Qed.

Lemma db_arms_load skI skR si rec odb :
  db_arms skI skR si rec odb !! dbN.@"load" =
  Some (∃ db k, MSG k {{ db_client_token skI skR odb db ∗ ⌜is_Some (db !! k)⌝ }};
          (<? v> MSG v {{ ⌜db !! k = Some v⌝ }}; rec (Some db))%proto)%msg.
Proof.
rewrite /db_arms lookup_insert_ne; last exact: db_store_load.
by rewrite lookup_insert.
Qed.

Lemma db_arms_create skI skR si rec odb :
  db_arms skI skR si rec odb !! dbN.@"create" =
  Some (∃ db k v, MSG Spec.of_list [k; v] {{ db_client_token skI skR odb db
                                             ∗ ⌜db !! k = None⌝ }};
          rec (Some (<[k := v]> db)))%msg.
Proof.
rewrite /db_arms lookup_insert_ne; last exact: db_store_create.
rewrite lookup_insert_ne; last exact: db_load_create.
by rewrite lookup_insert.
Qed.

Lemma db_arms_close skI skR si rec odb :
  db_arms skI skR si rec odb !! dbN.@"close" =
  Some (∃ db, MSG (TInt 0) {{ db_client_token skI skR odb db }};
          (<?> MSG (TInt 0) {{ db_main' skI skR db ∗
                               released (si_resp_share si) }};
           END)%proto)%msg.
Proof.
rewrite /db_arms lookup_insert_ne; last exact: db_store_close.
rewrite lookup_insert_ne; last exact: db_load_close.
rewrite lookup_insert_ne; last exact: db_create_close.
by rewrite lookup_singleton.
Qed.

Lemma db_arms_dom skI skR si rec odb :
  dom (db_arms skI skR si rec odb) =
  {[dbN.@"store"; dbN.@"load"; dbN.@"create"; dbN.@"close"]}.
Proof. rewrite /db_arms !dom_insert_L dom_empty_L. set_solver. Qed.

Definition store_ctx : iProp :=
  Sess.ctx dbN (λ skI skR si, db_st skI skR si None).

Lemma store_ctx_alloc E :
  ↑dbN ⊆ E →
  GenConn.base_ctx -∗
  iso_dh_ctx -∗
  iso_dh_token E ==∗
  store_ctx ∗ iso_dh_token (E ∖ ↑dbN).
Proof. exact: GenConn.ctx_alloc. Qed.

Definition db_disconnected skI skR : iProp := ∃ db,
  db_main skI skR db ∗
  DB.db_state skI skR dbN db.

Definition db_connected' skI skR cs odb db : iProp :=
  (public (si_key cs) ∨ db_client_token skI skR odb db) ∗
  DB.db_state skI skR dbN db.

Definition db_connected skI skR cs : iProp := ∃ odb db,
  Sess.connected skI skR Init cs (db_st skI skR cs odb) ∗
  release_token (si_init_share cs) ∗
  db_connected' skI skR cs odb db.

Lemma db_connected_ok skI skR cs :
  db_connected skI skR cs -∗
  secret skI -∗
  secret skR -∗
  ◇ session_ok cs.
Proof.
iIntros "(%odb & %db & (gc & _) & _ & _ & _) s1 s2".
by iApply (GenConn.connected_ok with "gc s1 s2").
Qed.

Lemma db_connected_ok_compromised skI skR cs :
  db_connected skI skR cs -∗
  session_ok cs -∗
  compromised cs -∗
  ▷ False.
Proof.
iIntros "(%odb & %db & _ & rel & _) ok comp".
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

Definition server_db_connected' skI skR cs vdb odb db : iProp :=
  public_db db ∗
  AList.is_alist vdb (repr <$> db) ∗
  (public (si_key cs) ∨ db_server_token skI skR odb db).

Definition server_db_connected skI skR cs vdb : iProp := ∃ odb db,
  Sess.connected skI skR Resp cs (iProto_dual (db_st skI skR cs odb)) ∗
  release_token (si_resp_share cs) ∗
  server_db_connected' skI skR cs vdb odb db.

Definition server_db_disconnected skI skR vdb : iProp := ∃ db,
  public_db db ∗
  AList.is_alist vdb (repr <$> db) ∗
  db_copy skI skR db.

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
  □ ∀ odb db (t : term) p,
    {{{ Sess.connected skI skR Resp cs p ∗
        release_token (si_resp_share cs) ∗
        server_db_connected' skI skR cs vdb odb db ∗
        public t ∗
        (public (si_key cs) ∨
           match (iMsg_dual <$> db_arms skI skR cs (db_st skI skR cs) odb)
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
