From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role dh_auth.
From cryptis.store Require Import impl shared alist db.
From cryptis.store.server_proofs
  Require Import load store create.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeGS Σ}.

Implicit Types (cs : cst) (ss : sst).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_server_conn_handler_body E c ss :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  {{{ server ss }}}
    Server.conn_handler_body N c (repr ss) @ E
  {{{ v, RET v; server ss }}}.
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
wp_bind (Server.handle_create _ _ _ _).
iApply (wp_server_handle_create with "chan_c ctx p_m state") => //.
iIntros "!> %res state".
case: res => [?|] /=; wp_pures; first by iApply "post".
by iApply "post".
Qed.

Lemma wp_server_conn_handler E c ss :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  {{{ server ss }}}
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
      public (TKey Dec kR) ∗ ●H{dq|ph} T }}}
    Server.listen N c (TKey Enc kR) (TKey Dec kR) @ E
  {{{ RET #(); False }}}.
Proof.
iIntros "% %". iLöb as "IH".
iIntros "%Φ (#? & #chan_c & #ctx & #p_ek & hon) post".
wp_pures. wp_rec. wp_pures. wp_bind (responder _ _ _ _).
iAssert (dh_auth_ctx (N.@"auth")) as "#?".
  by iDestruct "ctx" as "(_ & _ & _ & _ & _ & _ & _ & ?)".
iApply (wp_responder inhabitant
         with "[# //] [# //] [# //] [# //] [hon]") => //;
  try by solve_ndisj.
iIntros "!> %res (hon & resP)". case: res => [[pkI kS]|]; wp_pures; last first.
  iApply ("IH" with "[hon] [$]"). iFrame. by eauto.
iDestruct "resP" as "(%kI & -> & #m_kI & #m_kS & #sessR & #sec_key)".
wp_bind (Fork _). iApply wp_fork; last first.
  iModIntro. wp_pures. iApply ("IH" with "[-post] post"). iFrame.
  by eauto.
iClear "IH". iModIntro. rewrite /Server.wait_init. wp_pures.
iAssert True%I as "I"; first by []. iRevert "I". iApply wp_sess_recv => //.
iIntros "!> %t _ #p_t".
wp_pures. wp_bind (AList.empty _).
iApply AList.wp_empty => //. iIntros "!> %kvs %kvs0".
wp_alloc ldb as "Hdb". wp_pures.
wp_alloc ts as "Hts".
iDestruct (initE with "[//] [//] [//] p_t") as "{p_t} p_t".
set si := SessInfo _ _ _ _ _.
pose (ss := {| sst_si := si;
               sst_ts := ts;
               sst_db := ldb; |}).
iAssert (▷ server ss)%I with "[Hts Hdb]" as "state".
{ iExists _, 0, kvs, ∅. iFrame.
  rewrite big_sepM_empty. do 5!iSplitR => //. }
wp_pures.
iApply (wp_server_conn_handler _ ss with "[#] [#] [$]") => //.
by iIntros "!> % []".
Qed.

End Verif.
