From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role conn rpc.
From cryptis.store Require Import impl shared alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeGS Σ}.

Implicit Types (cs : Conn.state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_server_handle_store c kI kR cs (vdb : val) :
  {{{ channel c ∗ cryptis_ctx ∗ store_ctx N }}}
    RPC.handle N "store" c (Server.handle_store c (repr cs) vdb)
  {{{ h, RET h; server_handler N kI kR cs vdb h }}}.
Proof.
iIntros "%Φ (#chan_c & #? & #ctx) post".
iPoseProof (store_ctx_store with "ctx") as "?".
iPoseProof (store_ctx_rpc_ctx with "ctx") as "?".
wp_lam; wp_pures. wp_apply RPC.wp_handle; last by eauto.
do 3!iSplit => //. clear Φ.
iIntros "!> %n %ts !> %Φ (#p_ts & #inv_ts & %db & #p_db & db & #db_at) post".
wp_pures.
wp_list_match => [t1 t2 ->|?]; wp_pures; last first.
{ iDestruct "inv_ts" as "[fail|inv_ts]"; last first.
  { by iDestruct "inv_ts" as "(% & % & -> & ?)". }
  wp_list. iApply ("post" $! None). iModIntro. iFrame.
  rewrite /=. iSplit; eauto. }
wp_bind (SAList.insert _ _ _).
iApply (SAList.wp_insert with "db").
iIntros "!> db". rewrite -fmap_insert.
wp_pures. wp_list. wp_pures. iApply ("post" $! (Some _)).
rewrite /=.
iModIntro. iSplit; first by eauto.
iFrame.
iDestruct "p_ts" as "(p_t1 & p_t2 & _)".
iSplit; first by iApply public_db_insert.
iDestruct "inv_ts" as "[fail|inv_ts]"; eauto.
iDestruct "inv_ts" as "(%t1' & %t2' & %e & store_at)".
case: e => <- <-.
iDestruct "db_at" as "[fail|db_at]"; eauto.
iRight. iApply (DB.db_at_store_at with "db_at store_at").
Qed.

End Verif.
