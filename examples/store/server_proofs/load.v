From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis primitives tactics.
From cryptis.examples Require Import iso_dh conn rpc.
From cryptis.examples.store Require Import impl shared alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !RPC.rpcGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : Conn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Ltac failure := iLeft; iFrame; eauto.

Lemma wp_server_handle_load skI skR cs (vdb : val) :
  {{{ cryptis_ctx ∗ store_ctx  }}}
    RPC.handle (Tag $ (dbN.@"load")) (Server.handle_load (repr cs) vdb)
  {{{ h, RET (repr h); server_handler skI skR cs vdb h }}}.
Proof.
iIntros "%Φ (#? & #ctx) post".
iPoseProof (store_ctx_load with "ctx") as "?".
iPoseProof (store_ctx_rpc_ctx with "ctx") as "?".
wp_lam; wp_pures.
wp_apply RPC.wp_handle; last by eauto.
do 2!iSplit => //. clear Φ.
iIntros "!> %ts !> %Φ (#p_ts & inv_ts & %db & #p_db & db & ready) post".
wp_pures. wp_list_match => [t1 ->| ?]; wp_pures; last first.
{ iApply ("post" $! None). by iFrame. }
wp_bind (SAList.find _ _). iApply (SAList.wp_find with "db") => //.
iIntros "!> db". rewrite lookup_fmap.
iMod (load_resp with "ready inv_ts") as "[ready inv_ts]".
case db_t1: (db !! t1) => [t2'|]; wp_pures; last first.
{ iApply ("post" $! None). by iFrame. }
wp_list. wp_pures. iModIntro.
iApply ("post" $! (Some _)). iFrame. do !iSplit; eauto.
rewrite /public_db big_sepM_forall /=.
by iDestruct ("p_db" $! t1 t2' with "[//]") as "[??]".
Qed.

End Verif.
