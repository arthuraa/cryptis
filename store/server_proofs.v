From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import gmeta nown role iso_dh.
From cryptis.store Require Import impl shared alist db connection_proofs.
From cryptis.store.server_proofs
  Require Import load store create close.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Context `{!storeGS Σ}.

Implicit Types (cs : conn_state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_server_conn_handler_body c cs n ldb db :
  channel c -∗
  store_ctx N -∗
  {{{ is_conn_state cs n ∗
      server_connected cs n db ∗
      SAList.is_alist ldb (repr <$> db) }}}
    Server.conn_handler_body N c (repr cs) ldb
  {{{ v, RET v; server_handler_post cs ldb v }}}.
Proof.
iIntros "#chan_c #ctx !> %Φ (conn & server & db) post".
wp_lam. wp_pures.
rewrite !Connection.subst_select /=.
iApply (wp_wand with "[conn server db] post").
iCombine "server db" as "I". iRevert "conn I".
iApply wp_connection_select => //=; do !iSplitR => //.
- by iApply wp_server_handle_store.
- by iApply wp_server_handle_load.
- by iApply wp_server_handle_create.
- by iApply wp_server_handle_close.
Qed.

Lemma wp_server_conn_handler c cs n vdb db vlock γlock :
  channel c -∗
  is_lock γlock vlock (account_inv (si_init cs) (si_resp cs) vdb) -∗
  store_ctx N -∗
  {{{ is_conn_state cs n ∗
      server_connected cs n db ∗
      SAList.is_alist vdb (repr <$> db) ∗
      locked γlock }}}
    Server.conn_handler N c (repr cs) vdb vlock
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan_c #lock #ctx".
iLöb as "IH" forall (n db).
iIntros "!> %Φ (conn & server & db & locked) post".
wp_rec. wp_pures. wp_bind (Server.conn_handler_body _ _ _ _).
iApply (wp_server_conn_handler_body with "[# //] [# //] [$]") => //.
iIntros "!> %v (%n' & %db' & [state|state])".
- iDestruct "state" as "(-> & conn & server & db)".
  wp_pures. by iApply ("IH" with "[$]").
- iDestruct "state" as "(-> & conn & server & db)".
  wp_pures. wp_bind (release _).
  iApply (release_spec with "[lock locked server db]").
  { iFrame "locked". iSplit => //.
    iExists db'. by iFrame. }
  iIntros "!> _". wp_pures.
  by iApply (wp_connection_close with "conn").
Qed.

Lemma wp_server_find_client ss kI :
  {{{ cryptis_ctx ∗ server ss }}}
    Server.find_client (repr ss) (TKey Dec kI)
  {{{ vdb γlock vlock, RET (vdb, vlock)%V;
      server ss ∗
      is_lock γlock vlock
        (account_inv kI (ss_key ss) vdb) }}}.
Proof.
iIntros "%Φ [#ctx server] post".
iDestruct "server"
  as "(%accounts & %E & #p_vkR & accounts & token & %EP & #locks)".
wp_lam; wp_pures.
wp_bind (SAList.find _ _).
iApply (SAList.wp_find with "accounts").
iIntros "!> accounts"; rewrite lookup_fmap.
case accounts_kI: (accounts !! TKey Dec kI) => [scs|]; wp_pures.
- rewrite big_sepM_forall.
  iPoseProof ("locks" $! (TKey Dec kI) scs with "[//]")
    as "(%kI' & %e & #lock)".
  case: e => <- {kI'}.
  iModIntro.
  iApply ("post" $! (scs_db scs) (scs_name scs) (scs_lock scs)).
  iSplit => //.
  iExists accounts, E. iFrame.
  rewrite big_sepM_forall. by eauto.
- have ?: ↑dbSN kI ⊆ E.
  { by apply: EP; rewrite elem_of_dom accounts_kI. }
  rewrite (term_token_difference _ (↑dbSN kI)) //.
  iDestruct "token" as "[token_kI token]".
  iAssert (db_not_signed_up kI (ss_key ss))
    with "[token_kI]" as "not_signed_up".
  { by iFrame. }
  wp_bind (SAList.new #()).
  iApply SAList.wp_empty => //.
  iIntros "!> %vdb db". wp_pures.
  wp_bind (newlock #()).
  iApply (newlock_spec (account_inv kI (ss_key ss) vdb)
           with "[not_signed_up db]").
  { iExists ∅. iFrame.
    iSplit; first by rewrite /public_db big_sepM_empty.
    iRight. iLeft. by iFrame. }
  iIntros "!> %vlock %γlock #lock".
  wp_pures.
  wp_bind (SAList.insert _ _ _).
  iApply (SAList.wp_insert with "accounts").
  iIntros "!> accounts". wp_pures.
  pose scs := {| scs_db := vdb; scs_name := γlock; scs_lock := vlock |}.
  rewrite -(fmap_insert _ _ _ scs).
  iModIntro.
  iApply ("post" $! vdb γlock vlock).
  iSplit => //.
  iExists _, (E ∖ ↑dbSN kI).
  iFrame.
  do !iSplit => //.
  + iPureIntro.
    move=> kI'.
    rewrite dom_insert elem_of_union elem_of_singleton.
    case/Decidable.not_or => fresh1 fresh2.
    have ?: kI' ≠ kI by congruence.
    move/(_ _ fresh2) in EP.
    solve_ndisj.
  + rewrite big_sepM_insert => //.
    iSplit => //.
    iExists _. iSplit => //.
Qed.

Lemma wp_server_wait_init c cs vdb db γlock vlock :
  cs_role cs = Resp →
  {{{ cryptis_ctx ∗ channel c ∗ store_ctx N ∗
      is_conn_state cs 0 ∗
      server_connecting cs db ∗
      term_token (si_key cs) (↑nroot.@"server".@"begin") ∗
      term_token (si_key cs) (↑nroot.@"server".@"end") ∗
      SAList.is_alist vdb (repr <$> db) ∗
      is_lock γlock vlock (
        account_inv (si_init cs) (si_resp cs) vdb) ∗
      locked γlock }}}
    Server.wait_init N c (repr cs) vdb vlock
  {{{ RET #(); True }}} .
Proof.
iIntros "%e_rl %Φ
  (#ctx & #chan_c & #ctx' & conn & server & not_started & not_ended &
   db & #lock & locked) post".
wp_lam; wp_pures.
iPoseProof (store_ctx_init with "ctx'") as "?".
iCombine "server not_started not_ended db locked post" as "I".
iRevert "conn I".
iApply wp_connection_recv => //.
iIntros "!> %m conn
  (server & not_started & not_ended & db & locked & post) #m_m #p_m".
iMod (ack_init_predI with "server not_started not_ended p_m")
  as "H" => //.
wp_pures.
iMod "H" as "(server & #p_m')".
wp_bind (tint _). iApply wp_tint.
wp_bind (Connection.send _ _ _ _).
iPoseProof (store_ctx_ack_init with "ctx'") as "?".
iApply (wp_connection_send with "[//] [//] [] [//] conn") => //.
{ by rewrite public_TInt. }
iIntros "!> conn". wp_pures.
wp_bind (Server.conn_handler _ _ _ _ _).
iApply (wp_server_conn_handler with "[//] [//] [//] [$]").
iIntros "!> _". wp_pures.
iModIntro. iRight. iExists _. iSplit => //.
by iApply "post".
Qed.

Lemma wp_server_listen c ss dq ph :
  {{{ cryptis_ctx ∗ channel c ∗ store_ctx N ∗
      server ss ∗ ●Ph{dq} ph }}}
    Server.listen N c (repr ss)
  {{{ RET #(); server ss ∗ ●Ph{dq} ph }}}.
Proof.
iIntros "%Φ (#? & #chan_c & #ctx & server & phase) post".
wp_lam; wp_pures.
iPoseProof (store_ctx_dh_auth_ctx with "ctx") as "dh".
wp_bind (Connection.listen _ _ _ _).
iApply (wp_connection_listen
         with "[# //] [# //] [# //] [#] [phase]") => //;
  try by solve_ndisj.
{ by iDestruct "server" as "(% & % & ? & _)". }
iIntros "!> %cs (hon & resP)". wp_pures.
iDestruct "resP" as "(conn & %e_kR & <- & %e_rl & token)".
wp_bind (Server.find_client _ _).
iApply (wp_server_find_client with "[$]").
iIntros "!> %vdb %γlock %vlock [server #lock]".
wp_pure _ credit:"c".
wp_pures.
wp_bind (acquire _).
iApply acquire_spec => //.
iIntros "!> (locked & %db & account & db)". rewrite -e_kR.
iMod (server_connectingI with "[//] hon c account") as "[hon account]".
wp_pures.
iApply (wp_fork with "[conn locked db account token]").
{ iModIntro.
  rewrite (term_token_difference _ (↑nroot.@"server".@"begin")); last by solve_ndisj.
  iDestruct "token" as "[not_started token]".
  iPoseProof (@term_token_drop _ _ (↑nroot.@"server".@"end")
               with "token") as "not_ended"; first by solve_ndisj.
  iApply (wp_server_wait_init
           with "[conn locked db account not_started not_ended] []") => //.
  iFrame. eauto. }
iApply "post".
by iFrame.
Qed.

End Verif.
