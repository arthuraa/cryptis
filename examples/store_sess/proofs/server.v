From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list dfrac_agree.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib term gmeta nown cryptis.
From cryptis Require Import replica primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn sess alist.
From cryptis.examples.sess Require impl.
From cryptis.examples.sess.proofs Require Import base.
From cryptis.examples.sess Require Import proofs tag.
From cryptis.examples.store Require Import db.
From cryptis.examples.store_sess Require Import impl.
From cryptis.examples.store_sess.proofs Require Import base.
From actris.channel Require Import proto_model proto.

From iris.heap_lang.lib Require Import lock ticket_lock.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ,
          !sessG Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types (db : gmap term term).

Lemma connected_repoint skI skR rl cs p q :
  connected skI skR rl cs p -∗
  public (si_key cs) -∗
  connected skI skR rl cs q.
Proof.
rewrite /connected. iIntros "[gc _] #pub". iFrame. by iLeft.
Qed.

Lemma wp_server_handle_store skI skR cs vdb :
  cryptis_ctx -∗
  store_ctx -∗
  server_handler skI skR cs vdb
    (Handler (dbN.@"store")
       (λ: "req", Server.handle_store vdb "req";; #true)%V).
Proof.
iIntros "#? #ctx".
rewrite /server_handler /=.
iIntros "!> %odb %db %t %p".
iIntros "!> %Φ (conn & rel & (#p_db & vdb & token) & #p_t & disj) post".
rewrite lookup_fmap db_arms_store /=.
wp_pures. rewrite /Server.handle_store. wp_pures.
iPoseProof (or_sep1 with "token disj") as "token".
iDestruct "token" as "[#pub|[token car]]".
- wp_list_of_term t; wp_pures; last first.
  { iApply ("post" $! true). iModIntro. iExists odb, db.
    iFrame "rel vdb p_db". iSplitL; eauto.
    by iApply (connected_repoint with "conn pub"). }
  wp_list_match => [k v ->|_]; wp_pures; last first.
  { iApply ("post" $! true). iModIntro. iExists odb, db.
    iFrame "rel vdb p_db". iSplitL; eauto.
    by iApply (connected_repoint with "conn pub"). }
  rewrite public_of_list /=. iDestruct "p_t" as "(p_k & p_v & _)".
  wp_bind (AList.insert _ _ _).
  iApply (AList.wp_insert with "vdb").
  iIntros "!> vdb". rewrite -fmap_insert. wp_pures.
  iApply ("post" $! true). iModIntro. iExists (Some (<[k := v]> db)), _.
  iFrame "rel vdb".
  iSplitL; first by iApply (connected_repoint with "conn pub").
  iSplitL; eauto.
  by iApply public_db_insert.
- iDestruct "car" as (p1) "[car #HeqD]".
  rewrite iMsg_exist_eq /=.
  iDestruct "car" as (db' k v) "car".
  rewrite iMsg_base_eq /=. iDestruct "car" as "(%e_t & #Heq1 & token')".
  subst t.
  rewrite !later_equivI_1.
  rewrite public_of_list /=. iDestruct "p_t" as "(p_k & p_v & _)".
  wp_list_of_term_eq ts e; last by rewrite Spec.of_listK in e.
  move/Spec.of_list_inj: e => <- {ts}.
  wp_pures.
  wp_list_match => [k' v' e|ne]; last by case: (ne (eq_refl _)).
  case: e => <- <- {k' v'}. wp_pures.
  wp_bind (AList.insert _ _ _).
  iApply (AList.wp_insert with "vdb").
  iIntros "!> vdb". rewrite -fmap_insert. wp_pures.
  iApply ("post" $! true).
  iExists (Some (<[k := v]> db)), _.
  iFrame "rel vdb".
  iMod (db_update_token (<[k := v]> db) with "token' token") as "(<- & token)".
  iSplitL "conn".
  { iApply (connected_le with "conn"). iModIntro. iNext.
    iRewrite "HeqD". iRewrite -"Heq1". iApply iProto_le_refl. }
  iModIntro. iFrame. by iApply public_db_insert.
Qed.

Lemma wp_server_handle_load skI skR cs vdb :
  cryptis_ctx -∗
  store_ctx -∗
  server_handler skI skR cs vdb
    (Handler (dbN.@"load")
       (λ: "k",
          (match: Server.handle_load vdb "k" with
             SOME "v" => Sess.send (repr cs) "v"
           | NONE => #()
           end);; #true)%V).
Proof.
iIntros "#? #ctx".
rewrite /server_handler /=.
iIntros "!> %odb %db %t %p".
iIntros "!> %Φ (conn & rel & (#p_db & vdb & token) & #p_t & disj) post".
rewrite lookup_fmap db_arms_load /=.
wp_pures. rewrite /Server.handle_load. wp_pures.
iPoseProof (or_sep1 with "token disj") as "disj".
iDestruct "disj" as "[#pub|[token disj]]".
- wp_bind (AList.find _ _).
  iApply (AList.wp_find with "vdb").
  iIntros "!> vdb". rewrite lookup_fmap.
  case e: (db !! t) => [v0|] /=; wp_pures; last first.
  { iApply ("post" $! true). iModIntro. iExists (Some db), db.
    iFrame "rel vdb p_db". iSplitL; eauto.
    by iApply (connected_repoint with "conn pub"). }
  iPoseProof (big_sepM_lookup _ _ _ _ e with "p_db") as "[_ p_v0]".
  wp_bind (Sess.send _ _).
  iApply (wp_send _ _ _ _ v0 (iProto_dual (db_st skI skR cs (Some db)))
           with "[conn]").
  { iSplit => //.
    by iApply (connected_repoint with "conn pub"). }
  iIntros "!> conn". wp_pures.
  iApply ("post" $! true). iModIntro. iExists (Some db), db.
  by iFrame "rel vdb p_db conn"; eauto.
- iDestruct "disj" as (p1) "[car #HeqD]".
  rewrite iMsg_exist_eq /=. iDestruct "car" as (db0 k1) "car".
  rewrite iMsg_base_eq /=. iDestruct "car" as "(%e_t & #Heq1 & token' & %HkS)".
  subst t.
  iMod (db_update_token db with "token' token") as "(-> & token)".
  rewrite !later_equivI_1.
  case: HkS => [v0 Hv0].
  wp_bind (AList.find _ _).
  iApply (AList.wp_find with "vdb").
  iIntros "!> vdb".
  have e2 : (repr <$> db) !! k1 = Some (repr v0) by rewrite lookup_fmap Hv0.
  rewrite e2 /=. wp_pures.
  iPoseProof (big_sepM_lookup _ _ _ _ Hv0 with "p_db") as "[_ p_v0]".
  wp_bind (Sess.send _ _).
  iApply (wp_send_msg _ _ _ _
            (iMsg_dual (∃ v, MSG v {{ ⌜db !! k1 = Some v⌝ }};
                          db_st skI skR cs (Some db))%msg) _
            (iProto_dual (db_st skI skR cs (Some db)))
           with "[conn]").
  { iSplitL "conn".
    { iApply (connected_le with "conn"). iNext.
      iRewrite "HeqD". iRewrite -"Heq1".
      rewrite iMsg_exist_eq iMsg_base_eq.
      iApply iProto_le_of_equiv. exact: iProto_dual_message. }
    iSplit => //.
    iRight. iExists (db_st skI skR cs (Some db)).
    iSplit; last by auto.
    rewrite iMsg_exist_eq /=. iExists v0.
    rewrite iMsg_base_eq /=.
    iSplit; first done.
    iSplit; first by auto.
    by []. }
  iIntros "!> conn". wp_pures.
  iApply ("post" $! true). iModIntro. iExists (Some db), db.
  by iFrame "rel vdb p_db conn"; eauto.
Qed.

Lemma wp_server_handle_create skI skR cs vdb :
  cryptis_ctx -∗
  store_ctx -∗
  server_handler skI skR cs vdb
    (Handler (dbN.@"create")
       (λ: "req", Server.handle_create vdb "req";; #true)%V).
Proof.
iIntros "#? #ctx".
rewrite /server_handler /=.
iIntros "!> %odb %db %t %p".
iIntros "!> %Φ (conn & rel & (#p_db & vdb & token) & #p_t & disj) post".
rewrite lookup_fmap db_arms_create /=.
wp_pures. rewrite /Server.handle_create. wp_pures.
iPoseProof (or_sep1 with "token disj") as "[#pub|[token car]]".
- wp_list_of_term t; wp_pures; last first.
  { iApply ("post" $! true). iModIntro.
    iExists (Some db), db. iFrame "rel vdb p_db".
    iSplitL; eauto.
    by iApply (connected_repoint with "conn pub"). }
  wp_list_match => [k v ->|_]; wp_pures; last first.
  { iApply ("post" $! true). iModIntro.
    iExists (Some db), db. iFrame "rel vdb p_db".
    iSplitL; eauto.
    by iApply (connected_repoint with "conn pub"). }
  rewrite public_of_list /=. iDestruct "p_t" as "(p_k & p_v & _)".
  wp_bind (AList.find _ _).
  iApply (AList.wp_find with "vdb").
  iIntros "!> vdb". rewrite lookup_fmap.
  case e: (db !! k) => [v0|] /=; wp_pures.
  { iApply ("post" $! true). iModIntro.
    iExists (Some db), db. iFrame "rel vdb p_db".
    iSplitL; eauto.
    by iApply (connected_repoint with "conn pub"). }
  wp_bind (AList.insert _ _ _).
  iApply (AList.wp_insert with "vdb").
  iIntros "!> vdb". rewrite -fmap_insert. wp_pures.
  iApply ("post" $! true). iModIntro.
  iExists (Some (<[k := v]> db)), (<[k := v]> db).
  iFrame "rel vdb".
  iSplitL "conn"; first by iApply (connected_repoint with "conn pub").
  iSplit; eauto.
  by iApply public_db_insert.
- iDestruct "car" as (p1) "[car #HeqD]".
  rewrite iMsg_exist_eq /=. iDestruct "car" as (db0 k) "car".
  iDestruct "car" as (v) "car".
  rewrite iMsg_base_eq /=. iDestruct "car" as "(%e_t & #Heq1 & token' & %Hk)".
  subst t.
  rewrite !later_equivI_1.
  rewrite public_of_list /=. iDestruct "p_t" as "(p_k & p_v & _)".
  wp_list_of_term_eq ts e; last by rewrite Spec.of_listK in e.
  move/Spec.of_list_inj: e => <- {ts}.
  wp_pures.
  wp_list_match => [k' v' e|ne]; last by case: (ne (eq_refl _)).
  case: e => <- <- {k' v'}. wp_pures.
  iMod (db_update_token (<[k := v]> db) with "token' token")
    as "(-> & token)".
  wp_bind (AList.find _ _).
  iApply (AList.wp_find with "vdb").
  iIntros "!> vdb". rewrite lookup_fmap Hk /=. wp_pures.
  wp_bind (AList.insert _ _ _).
  iApply (AList.wp_insert with "vdb").
  iIntros "!> vdb". rewrite -fmap_insert. wp_pures.
  iApply ("post" $! true). iModIntro. iExists (Some (<[k := v]> db)), _.
  iFrame "rel vdb".
  iSplitL "conn".
  { iApply (connected_le with "conn"). iNext.
    iRewrite "HeqD". iRewrite -"Heq1". iApply iProto_le_refl. }
  iFrame. by iApply public_db_insert.
Qed.

Lemma wp_server_handle_close skI skR cs vdb :
  cryptis_ctx -∗
  store_ctx -∗
  server_handler skI skR cs vdb
    (Handler (dbN.@"close")
       (λ: <>,
          Sess.send (repr cs) (TInt 0);;
          GenConn.free (repr cs);;
          #false)%V).
Proof.
iIntros "#? #ctx".
rewrite /server_handler /=.
iIntros "!> %odb %db %t %p".
iIntros "!> %Φ (conn & rel & (#p_db & vdb & token) & #p_t & disj) post".
rewrite lookup_fmap db_arms_close /=.
wp_pures.
iDestruct (or_sep1 with "token disj") as "[#pub|[token car]]".
- iDestruct (connected_public_key_or' _ _ _ _ _ False%I
              with "conn rel []") as "(conn & rel & >comp)"; first by iLeft.
  iDestruct "comp" as "[#comp|[]]".
  iPoseProof (connected_failure' with "conn comp") as "#fail".
  wp_bind (Sess.send _ _).
  iApply (wp_send _ _ _ _ (TInt 0) END with "[conn]").
  { iSplit; last by rewrite public_TInt.
    by iApply (connected_repoint with "conn pub"). }
  iIntros "!> conn". wp_pures.
  iDestruct "conn" as "[gc _]".
  wp_apply (GenConn.wp_free with "gc"). iIntros "_".
  wp_pures.
  iApply ("post" $! false). iModIntro. iExists db.
  iFrame "vdb p_db". by iLeft.
- iDestruct "car" as (p1) "[car #HeqD]".
  rewrite iMsg_base_eq /=.
  rewrite iMsg_exist_eq /=.
  iDestruct "car" as "(%db0 & %e_t & #Heq1 & token')".
  rewrite !later_equivI_1.
  iMod (db_update_token db with "token' token") as "(-> & _ & main & copy)".
  iMod (cryptis.examples.iso_dh.proofs.base.release with "rel") as "#relR".
  wp_bind (Sess.send _ _).
  iApply (wp_send_msg _ _ _ _
            (iMsg_dual (MSG (TInt 0)
               {{ db_main' skI skR db ∗
                  released (si_resp_share cs) }}; END)%msg) _
            (iProto_dual END)
           with "[conn main]").
  { iSplitL "conn".
    { iApply (connected_le with "conn"). iNext.
      iRewrite "HeqD". iRewrite -"Heq1".
      rewrite iMsg_base_eq.
      iApply iProto_le_of_equiv. exact: iProto_dual_message. }
    iSplit; first by rewrite public_TInt.
    iRight. iExists END.
    iSplit; last by auto.
    rewrite iMsg_base_eq /=.
    iSplit; first done.
    iSplit; first by auto. by iFrame. }
  iIntros "!> conn". wp_pures.
  iDestruct "conn" as "[gc _]".
  wp_apply (GenConn.wp_free with "gc"). iIntros "_".
  wp_pures.
  iApply ("post" $! false). iModIntro. iExists db.
  iFrame "vdb p_db". by iRight.
Qed.

Lemma wp_handle' N f φ :
  (∀ h, ⌜h = Handler N f⌝ -∗ φ (repr h)) -∗
  WP Sess.handle (Tag N) f {{ φ }}.
Proof. exact: wp_handle. Qed.

Lemma wp_select' skI skR rl cs ms (handlers : list handler) (V : iProp) φ :
  dom ms ⊆ list_to_set (map handler_tag handlers) →
  connected skI skR rl cs (<?> iMsg_tag ms) -∗
  V -∗
  (V -∗ select_vc skI skR rl cs ms handlers φ) -∗
  (∀ p, connected skI skR rl cs p -∗ public (si_key cs) -∗ V -∗ φ NONEV) -∗
  WP Sess.select (repr cs) (repr handlers) {{ φ }}.
Proof. exact: wp_select. Qed.

Lemma wp_server_conn_handler skI skR cs vdb vlock γlock db :
  cryptis_ctx -∗
  store_ctx -∗
  is_lock γlock vlock (server_db_disconnected skI skR vdb) -∗
  {{{ connected skI skR Resp cs (iProto_dual (db_st skI skR cs None)) ∗
      release_token (si_resp_share cs) ∗
      (public (si_key cs) ∨ db_copy' skI skR db) ∗
      public_db db ∗
      AList.is_alist vdb (repr <$> db) ∗
      locked γlock }}}
    Server.conn_handler (repr cs) vdb vlock
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #ctx #lock !> %Φ (conn & rel & copy & #p_db & vdb & locked) post".
iPoseProof (wp_server_handle_store skI skR cs vdb with "[//] [//]") as "#Hst".
iPoseProof (wp_server_handle_load skI skR cs vdb with "[//] [//]") as "#Hld".
iPoseProof (wp_server_handle_create skI skR cs vdb with "[//] [//]") as "#Hcr".
iPoseProof (wp_server_handle_close skI skR cs vdb with "[//] [//]") as "#Hcl".
wp_lam. wp_pures.
iAssert (|={⊤}=> server_db_connected skI skR cs vdb)%I
  with "[conn rel copy vdb]" as ">sdc".
{ iModIntro. iExists None, db. iFrame; eauto. }
wp_pures.

wp_bind (Sess.handle _ _). iApply wp_handle'.
iIntros "%h_cl %e_cl". subst h_cl. wp_list.
wp_pures. wp_bind (Sess.handle _ _). iApply wp_handle'.
iIntros "%h_cr %e_cr". subst h_cr. wp_list.
wp_pures. wp_bind (Sess.handle _ _). iApply wp_handle'.
iIntros "%h_ld %e_ld". subst h_ld. wp_list.
wp_pures. wp_bind (Sess.handle _ _). iApply wp_handle'.
iIntros "%h_st %e_st". subst h_st. wp_list.
wp_pures.

iLöb as "IH".
iDestruct "sdc" as (odb db') "(conn & rel & sdc')".
pose (handlers :=
  [Handler (dbN.@"store")
     (λ: "req", Server.handle_store vdb "req";; #true)%V;
   Handler (dbN.@"load")
     (λ: "k",
        (match: Server.handle_load vdb "k" with
           SOME "v" => Sess.send (repr cs) "v"
         | NONE => #()
         end);; #true)%V;
   Handler (dbN.@"create")
     (λ: "req", Server.handle_create vdb "req";; #true)%V;
   Handler (dbN.@"close")
     (λ: <>,
        Sess.send (repr cs) (TInt 0);;
        GenConn.free (repr cs);;
        #false)%V]).
pose (φ := (λ v : val,
  (⌜v = NONEV⌝ ∗ server_db_connected skI skR cs vdb) ∨
  (∃ b : bool, ⌜v = SOMEV #b⌝ ∗
     if b then server_db_connected skI skR cs vdb
     else server_db_disconnected skI skR vdb))%I).
wp_bind (Sess.select _ _).
iApply (wp_wand _ _ _ φ with "[conn rel sdc']"); last first.
{ iIntros "%v Hv".
  iDestruct "Hv" as "[[-> sdc]|(%b & -> & Hb)]".
  - wp_pures. by iApply ("IH" with "locked post sdc").
  - case: b; wp_pures.
    + by iApply ("IH" with "locked post Hb").
    + wp_apply (release_spec with "[$lock $locked $Hb]").
      iIntros "_". by iApply "post". }
iApply (@wp_select' skI skR Resp cs
          (iMsg_dual <$> db_arms skI skR cs (db_st skI skR cs) odb)
          handlers
          (release_token (si_resp_share cs) ∗
           server_db_connected' skI skR cs vdb odb db')%I
          φ
         with "[conn] [rel sdc'] [] []").
- rewrite dom_fmap_L db_arms_dom /=. set_solver.
- iApply (connected_le with "conn"). iNext.
  iApply iProto_le_of_equiv. exact: db_st_dual_unfold.
- by iFrame.
- iIntros "[rel sdc']".
  rewrite /select_vc /=.
  iSplit.
  { iIntros "%tm %pm conn #p_tm disj".
    iApply ("Hst" $! odb db' tm pm with "[$conn $rel $sdc' $p_tm $disj]").
    iIntros "!> %b Hb". iRight. iExists b. by iFrame. }
  iSplit.
  { iIntros "%tm %pm conn #p_tm disj".
    iApply ("Hld" $! odb db' tm pm with "[$conn $rel $sdc' $p_tm $disj]").
    iIntros "!> %b Hb". iRight. iExists b. by iFrame. }
  iSplit.
  { iIntros "%tm %pm conn #p_tm disj".
    iApply ("Hcr" $! odb db' tm pm with "[$conn $rel $sdc' $p_tm $disj]").
    iIntros "!> %b Hb". iRight. iExists b. by iFrame. }
  iSplit; last done.
  iIntros "%tm %pm conn #p_tm disj".
  iApply ("Hcl" $! odb db' tm pm with "[$conn $rel $sdc' $p_tm $disj]").
  iIntros "!> %b Hb". iRight. iExists b. by iFrame.
- iIntros "%pm conn #pub [rel sdc']".
  iLeft. iSplit => //.
  iExists odb, db'. iFrame "rel sdc'".
  by iApply (connected_repoint with "conn pub").
Qed.

Lemma wp_server_start c skR E :
  ↑dbN.@"server" ⊆ E →
  {{{ channel c ∗ minted skR ∗ term_token skR E }}}
    Server.start skR
  {{{ ss, RET (repr ss); server ss }}}.
Proof.
iIntros "%sub %Ψ (#? & #? & token) post".
wp_lam. wp_pures. wp_apply AList.wp_empty => //.
iIntros "%accounts accounts". wp_pures.
iApply ("post" $! {| ss_key := skR; ss_clients := accounts |}).
iExists ∅, E.
iSplitR => //.
rewrite fmap_empty.
iFrame.
iModIntro.
rewrite big_sepM_empty. iSplit => //.
iPureIntro.
move=> skI _. solve_ndisj.
Qed.

Lemma wp_server_find_client ss skI :
  {{{ cryptis_ctx ∗ server ss }}}
    Server.find_client (repr ss) (Spec.pkey skI)
  {{{ vdb γlock vlock, RET (vdb, vlock)%V;
      server ss ∗
      is_lock γlock vlock
        (server_db_disconnected skI (ss_key ss) vdb) }}}.
Proof.
iIntros "%Φ [#ctx server] post".
iDestruct "server"
  as "(%accounts & %E & #p_pkR & accounts & token & %EP & #locks)".
wp_lam; wp_pures.
wp_bind (AList.find _ _).
iApply (AList.wp_find with "accounts").
iIntros "!> accounts"; rewrite lookup_fmap.
case accounts_skI: (accounts !! Spec.pkey skI) => [scs|]; wp_pures.
- rewrite big_sepM_forall.
  iPoseProof ("locks" $! (Spec.pkey skI) scs with "[//]")
    as "(%skI' & %e & #lock)".
  move/Spec.sign_pkey_inj: e => <- {skI'}.
  iModIntro.
  iApply ("post" $! (scs_db scs) (scs_name scs) (scs_lock scs)).
  iSplit => //.
  iExists accounts, E. iFrame.
  rewrite big_sepM_forall. by eauto.
- have ?: ↑dbN.@"server".@(skI : term) ⊆ E.
  { by apply: EP; rewrite elem_of_dom accounts_skI. }
  rewrite (term_token_difference _ (↑dbN.@"server".@(skI : term))) //.
  iDestruct "token" as "[token_skI token]".
  wp_bind (AList.new #()).
  iApply AList.wp_empty => //.
  iIntros "!> %vdb db". wp_pures.
  wp_bind (newlock #()).
  iDestruct (server_db_alloc with "token_skI db") as ">[_ db]"; eauto.
  iApply (newlock_spec (server_db_disconnected skI (ss_key ss) vdb)
           with "[db]").
  { iFrame. }
  iIntros "!> %vlock %γlock #lock".
  wp_pures.
  wp_bind (AList.insert _ _ _).
  iApply (AList.wp_insert with "accounts").
  iIntros "!> accounts". wp_pures.
  pose scs := {| scs_db := vdb; scs_name := γlock; scs_lock := vlock |}.
  rewrite -(fmap_insert _ _ _ scs).
  iModIntro.
  iApply ("post" $! vdb γlock vlock).
  iSplit => //.
  iExists _, (E ∖ ↑dbN.@"server".@(skI : term)).
  iFrame.
  do !iSplit => //.
  + iPureIntro.
    move=> skI'.
    rewrite dom_insert elem_of_union elem_of_singleton.
    case/Decidable.not_or => fresh1 fresh2.
    have ?: skI' ≠ skI by congruence.
    move/(_ _ fresh2) in EP.
    solve_ndisj.
  + rewrite big_sepM_insert => //.
    iSplit => //.
    iExists _. iSplit => //.
Qed.

(* TODO: This should follow from Sess.wp_confirm *)
Lemma wp_confirm' (P : iProp) c skI skR ga :
  channel c -∗
  cryptis_ctx -∗
  store_ctx -∗
  {{{ public ga ∗ minted skI ∗ minted skR ∗
      (GenConn.failure skI skR ∨ P) }}}
    Sess.confirm c skR (Tag dbN) (ga, Spec.pkey skI)%V
  {{{ cs, RET (repr cs);
      connected skI skR Resp cs (iProto_dual (db_st skI skR cs None)) ∗
      release_token (si_resp_share cs) ∗
      (public (si_key cs) ∨ P) }}}.
Proof.
iIntros "#? #ctx1 #?" (Φ) "!> (#p_ga & #m_skI & #m_skR & P) post".
wp_lam; wp_pures. iApply wp_fupd.
wp_apply (GenConn.wp_confirm P with "[] [$P]").
- eauto.
- eauto.
- do 3!iSplit => //.
  iIntros "!> %b tok".
  iMod (iProto_init (db_st skI skR _ None)) as (γl γr) "(pctx & ownI & ownR)".
  iMod (term_meta_set (sessN.@"names") (γl, γr) with "tok") as "#meta".
  { solve_ndisj. }
  iModIntro. iSplitL "ownI".
  { iExists (γl, γr). iFrame. by eauto. }
  iSplitL "ownR".
  { iExists (γl, γr). iFrame. by eauto. }
  iExists (γl, γr). iFrame. by eauto.
iIntros "%cs (conn & dis & proto & rel & token)".
iApply "post". rewrite /connected. by iFrame.
Qed.

Lemma wp_server_listen c ss :
  {{{ cryptis_ctx ∗ channel c ∗ store_ctx ∗ server ss }}}
    Server.listen c (repr ss)
  {{{ RET #(); server ss }}}.
Proof.
iIntros "%Φ (#cctx & #chan_c & #ctx & server) post".
wp_lam; wp_pures.
wp_apply (Sess.wp_listen with "chan_c cctx [//]").
iIntros "%ga %skA #[p_ga m_skA]". wp_pures.
wp_bind (Server.find_client _ _).
iApply (wp_server_find_client with "[$server]") => //.
iIntros "!> %vdb %γlock %vlock [server #lock]".
wp_pures.
wp_bind (acquire _).
iApply acquire_spec => //.
iIntros "!> (locked & dis)".
iDestruct "dis" as "(%db & #p_db & vdb & ready)".
iAssert (minted (ss_key ss)) as "#?".
{ by iDestruct "server" as "(% & % & ? & _)". }
wp_pures.
wp_apply (wp_confirm' (db_copy' skA (ss_key ss) db)
           with "chan_c cctx ctx [ready]").
{ do 3?(iSplit; [done|]). iExact "ready". }
iIntros "%cs (conn & rel & ready)". wp_pures.
iApply (wp_fork with "[conn rel vdb locked ready]").
{ iModIntro.
  wp_apply (wp_server_conn_handler
             with "cctx ctx lock [$conn $rel $ready $vdb $locked]") => //. }
iApply "post".
by iFrame.
Qed.

End Verif.
