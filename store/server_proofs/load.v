From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis primitives tactics.
From cryptis Require Import role iso_dh conn rpc.
From cryptis.store Require Import impl shared alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : Conn.state).
Implicit Types skI skR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Ltac failure := iLeft; iFrame; eauto.

Lemma wp_server_handle_load c skI skR cs (vdb : val) :
  {{{ channel c ∗ cryptis_ctx ∗ store_ctx N  }}}
    RPC.handle N "load" c (Server.handle_load c (repr cs) vdb)
  {{{ h, RET (repr h); server_handler N skI skR cs vdb h }}}.
Proof.
iIntros "%Φ (#chan_c & #? & #ctx) post".
iPoseProof (store_ctx_load with "ctx") as "?".
iPoseProof (store_ctx_rpc_ctx with "ctx") as "?".
wp_lam; wp_pures.
wp_apply RPC.wp_handle; last by eauto.
do 3!iSplit => //. clear Φ.
iIntros "!> %ts !> %Φ (#p_ts & inv_ts & %db & #p_db & db & ready) post".
wp_pures. wp_list_match => [t1 ->| ?]; wp_pures; last first.
{ iDestruct "inv_ts" as "[fail|(% & -> & ?)]" => //.
  iApply ("post" $! None).
  iModIntro. iSplit; eauto. by iFrame. }
wp_bind (SAList.find _ _). iApply (SAList.wp_find with "db") => //.
iIntros "!> db". rewrite lookup_fmap.
iAssert (compromised_session Resp cs ∨ DB.load_call skI skR N t1)%I
  with "[inv_ts]" as "inv_ts".
{ iDestruct "inv_ts" as "[?|(%t1' & %e & inv_ts)]"; eauto.
  case: e => <-. by iFrame. }
iMod (DB.load_callE with "ready inv_ts") as "(%t2 & #db_t1 & ready & load_at)".
case db_t1: (db !! t1) => [t2'|]; wp_pures; last first.
{ iDestruct "db_t1" as "[fail|%]" => //.
  iApply ("post" $! None). iFrame. by iModIntro. }
wp_list. wp_pures. iModIntro.
iApply ("post" $! (Some _)). iFrame. do !iSplit; eauto.
- rewrite /public_db big_sepM_forall /=.
  by iDestruct ("p_db" $! t1 t2' with "[//]") as "[??]".
- iDestruct "db_t1" as "[?|%e]"; eauto.
  case: e => -> in db_t1 *.
  iDestruct "load_at" as "[?|load_at]"; eauto. iRight. by iFrame.
Qed.

End Verif.
