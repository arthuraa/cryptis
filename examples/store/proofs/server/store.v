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

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !RPC.rpcGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeGS Σ}.

Implicit Types (cs : Conn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_server_handle_store skI skR cs (vdb : val) :
  {{{ cryptis_ctx ∗ store_ctx }}}
    RPC.handle (Tag $ dbN.@"store") (Server.handle_store (repr cs) vdb)
  {{{ h, RET (repr h); server_handler skI skR cs vdb h }}}.
Proof.
iIntros "%Φ (#? & #ctx) post".
iPoseProof (store_ctx_store with "ctx") as "?".
iPoseProof (store_ctx_rpc_ctx with "ctx") as "?".
wp_lam; wp_pures. wp_apply RPC.wp_handle; last by eauto.
do 2!iSplit => //. clear Φ.
iIntros "!> %ts !> %Φ (#p_ts & inv_ts & %db & #p_db & db & ready) post".
wp_pures.
wp_list_match => [t1 t2 ->|?]; wp_pures; last first.
{ iApply ("post" $! None). by iFrame. }
iMod (store_resp with "ready inv_ts") as "[ready inv_ts]".
wp_bind (AList.insert _ _ _).
iApply (AList.wp_insert with "db").
iIntros "!> db". rewrite -fmap_insert.
wp_pures. wp_list. wp_pures. iApply ("post" $! (Some _)).
iFrame. rewrite /= public_TInt. iModIntro.
iDestruct "p_ts" as "(? & ? & _)". iSplit => //.
by iApply public_db_insert.
Qed.

End Verif.
