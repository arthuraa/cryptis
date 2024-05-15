From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.
From cryptis.store Require Import impl shared alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeGS Σ}.

Local Instance STORE : PK := PK_DH (λ _ _ _ _, True)%I.

Implicit Types (cs : cst) (ss : sst).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma ack_storeI kS n :
  store_ctx N -∗
  minted kS -∗
  public (TEnc kS (Spec.tag (N.@"ack_store") (TInt n))).
Proof.
iIntros "(_ & _ & #ctx & _) #s_kS".
iApply public_TEncIS => //.
- by rewrite minted_TKey.
- iModIntro. by iExists n.
- by rewrite minted_TInt.
- by rewrite public_TInt; eauto.
Qed.

Lemma wp_server_handle_store E c ss m :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public m -∗
  {{{ server N ss }}}
    Server.handle_store N c (repr ss) m @ E
  {{{ (v : option val), RET (repr v); server N ss }}}.
Proof.
iIntros "%sub #chan_c #ctx #p_m !> %Φ state post".
rewrite /Server.handle_store. wp_pures.
wp_tsdec m; wp_pures; last by iApply ("post" $! None).
wp_list_of_term m; wp_pures; last by iApply ("post" $! None).
wp_list_match => [n' t1 t2 ->|_]; wp_pures; last by iApply ("post" $! None).
wp_bind (to_int _). iApply wp_to_int.
case: Spec.to_intP => [ {}n' -> | _]; wp_pures; last by iApply ("post" $! None).
iDestruct "state" as "(%n & %kvs & %db & #handshake & #minted_key & ts & 
                       db & %kvs_db & #pub_db & view)".
wp_load. wp_pures.
case: bool_decide_reflect => [[<-]|ne]; wp_pures; last first.
{ iModIntro. iApply ("post" $! None).
  iExists n, kvs, db. iFrame. by eauto. }
wp_load. wp_pures.
replace (n + 1)%Z with (S n : Z) by lia.
wp_store. wp_load. wp_bind (AList.insert _ _ _).
wp_pures. iApply AList.wp_insert; eauto. iIntros "!> %kvs' %kvs'_db'".
iDestruct (store_predE with "handshake [#] [//] p_m") as "(p_t1 & p_t2 & wf')".
{ case: sst_ok => //.
  iDestruct "view" as "(%γ & ? & ?)". eauto. }
wp_store. wp_bind (tint _). iApply wp_tint.
wp_tsenc.
iApply wp_fupd.
wp_bind (send _ _). iApply wp_send => //.
{ iModIntro. iApply ack_storeI => //. }
wp_pures. iApply ("post" $! (Some #())).
iExists (S n), kvs', (<[t1 := t2]>db). iFrame.
do 4!iSplitR => //.
{ iModIntro. iApply big_sepM_insert_2 => //. eauto. }
case: sst_ok; eauto.
iDestruct "wf'" as "(%γ1 & wf1 & update)".
iDestruct "view" as "(%γ2 & #wf2 & #view)".
iPoseProof (wf_key_agree with "handshake wf1 wf2") as "<-".
iPoseProof (DB.update_server with "view update") as "view'".
iModIntro. iExists γ1. iSplit => //.
Qed.

Lemma wp_server_handle_load E c ss m :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public m -∗
  {{{ server N ss }}}
    Server.handle_load N c (repr ss) m @ E
  {{{ (v : option val), RET (repr v); server N ss }}}.
Proof.
iIntros "%sub #chan_c #ctx #p_m !> %Φ state post".
rewrite /Server.handle_load. wp_pures.
iDestruct "state" as "(%n & %kvs & %db & #handshake & #minted_key & ts &
                       db & %kvs_db & #pub_db & #view)".
wp_load. wp_pures. wp_load. wp_pures.
iAssert (server N ss) with "[ts db view]" as "state".
{ iExists n, kvs, db. iFrame. eauto. }
wp_tsdec m; wp_pures; last by iApply ("post" $! None).
wp_list_of_term m; wp_pures; last by iApply ("post" $! None).
wp_list_match => [timestamp t1 ->| _]; wp_pures; last by iApply ("post" $! None).
wp_bind (to_int _). iApply wp_to_int.
case: Spec.to_intP => [ {m} n' -> | _]; wp_pures; last by iApply ("post" $! None).
case: bool_decide_reflect => [[<-]|?]; wp_pures; last by iApply ("post" $! None).
wp_bind (AList.find _ _). iApply AList.wp_find => //.
iIntros "!> _".
case db_t1: (db !! t1) => [t2|]; wp_pures; last by iApply ("post" $! None).
wp_list. wp_bind (tint _). iApply wp_tint. wp_list. wp_term_of_list.
wp_pures. wp_tsenc. wp_bind (send _ _).
iApply (wp_send with "[//] [#]") => //; last by wp_pures;
  iApply ("post" $! (Some #())).
iDestruct "ctx" as "(_ & _ & _ & _ & ? & _)".
iModIntro.
rewrite big_sepM_delete //. iDestruct "pub_db" as "[[? ?] _]".
iApply public_TEncIS => //.
- rewrite minted_TKey.
  iPoseProof (public_minted with "p_m") as "{p_m} p_m".
  by rewrite minted_TEnc; iDestruct "p_m" as "[??]".
- iModIntro. iExists n, (sst_ok ss), t1, t2. iSplit => //.
  do 2!iSplit => //.
  case: sst_ok => //.
  iDestruct "view" as "(%γ & key & view)".
  iExists γ. iSplit => //. iApply DB.load_server; eauto.
- rewrite minted_of_list /= minted_TInt -[minted t1]public_minted.
  rewrite -[minted t2]public_minted; eauto.
- iIntros "!> _". by rewrite public_of_list /= public_TInt; eauto.
Qed.

Lemma wp_server_conn_handler_body E c ss :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  {{{ server N ss }}}
    Server.conn_handler_body N c (repr ss) @ E
  {{{ v, RET v; server N ss }}}.
Proof.
iIntros "% #chan_c #ctx !> %Φ state post". rewrite /Server.conn_handler_body.
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m #p_m". wp_pures.
wp_bind (Server.handle_store _ _ _ _).
iApply (wp_server_handle_store with "chan_c ctx p_m state") => //.
iIntros "!> %res state".
case: res => [?|] /=; wp_pures; first by iApply "post".
wp_bind (Server.handle_load _ _ _ _).
iApply (wp_server_handle_load with "chan_c ctx p_m state") => //.
iIntros "!> %res state".
case: res => [?|] /=; wp_pures; first by iApply "post".
by iApply "post".
Qed.

Lemma wp_server_conn_handler E c ss :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  {{{ server N ss }}}
    Server.conn_handler N c (repr ss) @ E
  {{{ v, RET v; False }}}.
Proof.
iIntros "% #chan_c #ctx".
iLöb as "IH". iIntros "!> %Φ state post". wp_rec.
wp_pures. wp_bind (Server.conn_handler_body _ _ _).
iApply (wp_server_conn_handler_body with "[# //] [# //] [$]") => //.
iIntros "!> %n' state". wp_pures.
by iApply ("IH" with "[$]").
Qed.

Lemma wp_server_listen E c kR dq ph T :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  {{{ cryptis_ctx ∗ channel c ∗ store_ctx N ∗
      public (TKey Enc kR) ∗ ●H{dq|ph} T }}}
    Server.listen N c (TKey Dec kR) (TKey Enc kR) @ E
  {{{ RET #(); False }}}.
Proof.
iIntros "% %". iLöb as "IH".
iIntros "%Φ (#? & #chan_c & #ctx & #p_ek & hon) post".
wp_pures. wp_rec. wp_pures. wp_bind (pk_dh_resp _ _ _ _).
iAssert (pk_dh_ctx N (λ _ _ _ _, True)%I) as "#?".
  by iDestruct "ctx" as "(_ & _ & _ & _ & _ & ?)".
iApply (wp_pk_dh_resp with "[# //] [# //] [# //] [# //] [hon]") => //.
  iFrame. by eauto.
iIntros "!> %res (hon & resP)". case: res => [[pkI kS]|]; wp_pures; last first.
  iApply ("IH" with "[hon] [$]"). iFrame. by eauto.
iDestruct "resP" as "(%kI & -> & #p_pkI & #s_kS & _ & #sessW & key)".
wp_tag. wp_bind (mkskey _). iApply wp_mkskey. wp_pures.
wp_bind (Fork _). iApply (wp_fork with "[key]"); last first.
  iModIntro. wp_pures. iApply ("IH" with "[-post] post"). iFrame.
  by eauto.
iClear "IH". iModIntro. rewrite /Server.wait_init. wp_pures.
iRevert "key". iApply wp_sess_recv => //.
  by rewrite minted_tag.
iIntros "!> %t key #p_t".
wp_pures. wp_bind (AList.empty _).
iApply AList.wp_empty => //. iIntros "!> %kvs %kvs0".
wp_alloc ldb as "Hdb". wp_pures.
wp_alloc ts as "Hts".
iDestruct (initE with "[//] p_t") as "{p_t} p_t".
pose (ss := {| sst_ts := ts;
               sst_key := Spec.tag (nroot.@"keys".@"sym") kS;
               sst_db := ldb;
               sst_ok := in_honest kI kR T |}).
iAssert (handshake_done N (sst_key ss) (sst_ok ss)) as "#done".
{ iExists kI, kR, kS, ph, T; eauto. }
iAssert (▷ server N ss)%I with "[Hts Hdb key]" as "state".
{ iExists 0, kvs, ∅. iFrame.
  rewrite minted_tag /= big_sepM_empty.
  do 4!iSplitR => //.
  case e_ok: in_honest => //.
  iDestruct "key" as "(#sec & _ & #key)".
  iAssert (∀ kt, public (TKey kt (sst_key ss)) -∗ ◇ False)%I as "{sec} sec".
  { iIntros "%kt #p_kS'".
    iPoseProof (public_sym_keyE with "[//] p_kS'") as ">sym".
    by iApply "sec". }
  iDestruct "p_t" as "[p_t|p_t]".
    by iDestruct ("sec" with "p_t") as ">[]".
  iModIntro. iDestruct "p_t" as "(%ok & %γ & #done' & frag)".
  iPoseProof (handshake_done_session_key with "done' key") as "->".
  rewrite e_ok.
  iExists γ. eauto. }
wp_pures.
iApply (wp_server_conn_handler _ ss with "[#] [#] [$]") => //.
by iIntros "!> % []".
Qed.

End Verif.
