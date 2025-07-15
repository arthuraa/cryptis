From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh conn rpc alist.
From cryptis.examples.store Require Import impl.
From cryptis.examples.store.proofs Require Import base db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !Conn.connGS Σ, !RPC.rpcGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : Conn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Ltac failure := iLeft; iFrame; eauto.

Lemma wp_server_handle_create skI skR cs (vdb : val) :
  {{{ cryptis_ctx ∗ store_ctx }}}
    RPC.handle (Tag $ dbN.@"create") (Server.handle_create (repr cs) vdb)
  {{{ h, RET (repr h); server_handler skI skR cs vdb h }}}.
Proof.
iIntros "%Φ (#ctx & #ctx') post".
iPoseProof (store_ctx_create with "[//]") as "?".
iPoseProof (store_ctx_rpc_ctx with "[//]") as "?".
wp_lam. wp_pures.
wp_apply RPC.wp_handle; last by eauto.
do 2!iSplit => //. clear Φ.
iIntros "!> %ts !> %Φ (#p_ts & inv_ts & %db & #p_db & db & ready) post".
wp_list_match => [t1 t2 ->| ?]; wp_pures; last first.
{ iApply ("post" $! None). iFrame.
  iDestruct "inv_ts" as "[fail|inv_ts]"; eauto. }
rewrite /=. iDestruct "p_ts" as "(p_t1 & p_t2 & _)".
wp_bind (AList.find _ _). iApply (AList.wp_find with "db") => //.
iIntros "!> db". rewrite lookup_fmap.
case db_t1: (db !! t1) => [t2'|]; wp_pures.
{ iApply ("post" $! None). by iFrame. }
iMod (create_resp with "ready inv_ts") as "[ready inv_ts]".
wp_bind (AList.insert _ _ _).
iApply (AList.wp_insert with "db").
iIntros "!> db". rewrite -fmap_insert. wp_pures.
wp_list. wp_pures. iApply ("post" $! (Some _)).
iModIntro. rewrite /= public_TInt. iFrame. iSplit => //.
by iApply public_db_insert.
Qed.

End Verif.
