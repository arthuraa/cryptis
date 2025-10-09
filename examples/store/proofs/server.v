From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib cryptis primitives tactics.
From cryptis Require Import role iso_dh conn rpc alist.
From cryptis.examples.store Require Import impl.
From cryptis.examples.store.proofs Require Import base db.
From cryptis.examples.store.proofs.server Require Import load store create.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !RPC.rpcGS Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : Conn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_server_start c skR E :
  ↑dbN.@"server" ⊆ E →
  {{{ channel c ∗ minted skR ∗ term_token skR E }}}
    Server.start skR
  {{{ ss, RET (repr ss); server ss }}}.
Proof.
iIntros "%sub %Ψ (#? & #? & token) post".
wp_lam. wp_pures. wp_apply AList.wp_empty => //.
iIntros "%accounts accounts". wp_pures.
iApply ("post" $! {| ss_key := skR; ss_clients := accounts |}) .
iExists ∅, E.
iSplitR => //.
rewrite fmap_empty.
iFrame.
iModIntro.
rewrite big_sepM_empty. iSplit => //.
iPureIntro.
move=> skI _. solve_ndisj.
Qed.

Lemma wp_server_conn_handler skI skR cs vdb vlock γlock :
  is_lock γlock vlock (server_db_disconnected skI skR vdb) -∗
  cryptis_ctx -∗
  store_ctx -∗
  {{{ server_db_connected skI skR cs vdb ∗
      locked γlock }}}
    Server.conn_handler (repr cs) vdb vlock
  {{{ RET #(); True }}}.
Proof.
iIntros "#lock #? #ctx".
iIntros "!> %Φ ((conn & db) & locked) post".
iPoseProof (RPC.server_connected_keys with "conn") as "#[-> ->]".
iPoseProof (store_ctx_rpc_ctx with "[//]") as "?".
wp_lam. wp_pures.
wp_apply wp_server_handle_create; eauto. iIntros "% #?". wp_list.
wp_apply wp_server_handle_load; eauto. iIntros "% #?". wp_list.
wp_apply wp_server_handle_store; eauto. iIntros "% #?". wp_list.
wp_apply (RPC.wp_server with "[$conn db]").
{ iSplit => //. iSplit; last first.
  { rewrite /=. do !iSplit => //. }
  by []. }
iIntros "(dis & %db & #p_db & vdb & ready)".
wp_pures.
rewrite Conn.session_failed_failure.
wp_apply (release_spec with "[$locked dis vdb ready]") => //.
iSplit => //. by iFrame.
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

Lemma wp_server_listen c ss :
  {{{ cryptis_ctx ∗ channel c ∗ store_ctx ∗ server ss }}}
    Server.listen c (repr ss)
  {{{ RET #(); server ss }}}.
Proof.
iIntros "%Φ (#? & #chan_c & #ctx & server) post".
wp_lam; wp_pures.
iPoseProof (store_ctx_rpc_ctx with "ctx") as "?".
wp_apply (RPC.wp_listen
         with "[# //] [# //] [# //] [#]") => //;
  try by solve_ndisj.
iIntros "%ga %skA #[p_ga p_skA]". wp_pures.
wp_bind (Server.find_client _ _).
iApply (wp_server_find_client with "[$server]") => //.
iIntros "!> %vdb %γlock %vlock [server #lock]".
wp_pure _ credit:"c".
wp_pures.
wp_bind (acquire _).
iApply acquire_spec => //.
iIntros "!> (locked & dis)".
iDestruct "dis" as "(%db & #p_db & vdb & ready)".
iAssert (minted (ss_key ss)) as "#?".
{ by iDestruct "server" as "(% & % & ? & _)". }
wp_pures.
wp_apply (RPC.wp_confirm (db_server_ready skA (ss_key ss) db)
           with "[] [] [] [$ready]") => //.
{ do 3!iSplit => //. }
iIntros "%cs (conn & ready)".
wp_pures.
iApply (wp_fork with "[conn vdb locked ready]").
{ iModIntro.
  wp_apply (wp_server_conn_handler
             with "[] [] [] [$conn $locked $vdb $ready]") => //. }
iApply "post".
by iFrame.
Qed.

End Verif.
