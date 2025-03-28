From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role iso_dh conn rpc.
From cryptis.store Require Import impl shared alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : Conn.state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Ltac failure := iLeft; iFrame; eauto.

Lemma wp_server_handle_create c kI kR cs (vdb : val) :
  {{{ channel c ∗ cryptis_ctx ∗ store_ctx N }}}
    RPC.handle N "create" c (Server.handle_create c (repr cs) vdb)
  {{{ h, RET (repr h); server_handler N kI kR cs vdb h }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & #ctx') post".
iPoseProof (store_ctx_create with "[//]") as "?".
iPoseProof (store_ctx_rpc_ctx with "[//]") as "?".
wp_lam. wp_pures.
wp_apply RPC.wp_handle; last by eauto.
do 3!iSplit => //. clear Φ.
iIntros "!> %n %ts !> %Φ (#p_ts & #inv_ts & %db & #p_db & db & #db_at) post".
wp_list_match => [t1 t2 ->| ?]; wp_pures; last first.
{ iApply ("post" $! None). iFrame.
  iDestruct "inv_ts" as "[fail|inv_ts]"; eauto.
  by iDestruct "inv_ts" as "(% & % & -> & ?)". }
rewrite /=. iDestruct "p_ts" as "(p_t1 & p_t2 & _)".
wp_bind (SAList.find _ _). iApply (SAList.wp_find with "db") => //.
iIntros "!> db". rewrite lookup_fmap.
wp_bind (match: _ with InjL <> => _ | InjR <> => _ end)%E.
iAssert (compromised_session Resp cs ∨
           DB.db_at kI (N.@"client".@kR.@"db")
             (S n) (DB.op_app db (Create t1 t2)))%I
  as "#db_at'".
{ iDestruct "inv_ts" as "[?|inv_ts]"; eauto.
  iDestruct "inv_ts" as "(%t1' & %t2' & %e & create_at)".
  case: e => <- <-.
  iDestruct "db_at" as "[?|db_at]"; eauto.
  iRight. by iApply (DB.db_at_create_at with "db_at"). }
iApply (wp_wand _ _ _ (λ v,
  ∃ (b : bool), ⌜v = #((if b then 1 else 0) : Z)⌝ ∗
                server_db_connected' N kI kR cs vdb (S n)
  ) with "[db]")%I.
{ case db_t1: (db !! t1) => [t2'|]; wp_pures.
  { iExists false; iModIntro; iFrame.
    by rewrite /= db_t1; eauto. }
  wp_bind (SAList.insert _ _ _).
  iApply (SAList.wp_insert with "db").
  iIntros "!> db". rewrite -fmap_insert.
  wp_pures.
  iFrame. iExists true. rewrite /= db_t1.
  iModIntro. do !iSplit => //.
  by iApply public_db_insert. }
iIntros "% (%b & -> & db)".
wp_pures.
wp_bind (tint _). iApply wp_tint.
wp_list.
wp_pures.
iApply ("post" $! (Some _)).
iModIntro. rewrite /= public_TInt. by iSplit; eauto.
Qed.

End Verif.
