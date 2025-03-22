From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis primitives tactics.
From cryptis Require Import role conn rpc.
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
  {{{ h, RET h; server_handler N skI skR cs vdb h }}}.
Proof.
iIntros "%Φ (#chan_c & #? & #ctx) post".
iPoseProof (store_ctx_load with "ctx") as "?".
iPoseProof (store_ctx_rpc_ctx with "ctx") as "?".
wp_lam; wp_pures.
wp_apply RPC.wp_handle; last by eauto.
do 3!iSplit => //. clear Φ.
iIntros "!> %n %ts !> %Φ (#p_ts & #inv_ts & %db & #p_db & db & #db_at) post".
wp_pures. wp_list_match => [t1 ->| ?]; wp_pures; last first.
{ iDestruct "inv_ts" as "[fail|(% & -> & ?)]" => //.
  iApply ("post" $! None).
  iModIntro. rewrite /=. iSplit; eauto. iFrame.
  iSplit; eauto. }
wp_bind (SAList.find _ _). iApply (SAList.wp_find with "db") => //.
iIntros "!> db". rewrite lookup_fmap.
case db_t1: (db !! t1) => [t2|]; wp_pures; last first.
{ iApply ("post" $! None). iFrame. iModIntro. iSplit => //.
  iDestruct "db_at" as "[fail|db_at]"; eauto.
  iDestruct "inv_ts" as "[fail|(% & %e & load_at)]"; eauto.
  iRight. iApply (DB.db_at_op_at with "db_at load_at"). }
wp_list. wp_pures. iModIntro.
iApply ("post" $! (Some _)). iFrame. do !iSplit; eauto.
- rewrite /public_db big_sepM_forall /=.
  by iDestruct ("p_db" $! t1 t2 with "[//]") as "[??]".
- iDestruct "inv_ts" as "[fail|(% & %e & load_at)]"; eauto.
  case: e => <-.
  iDestruct "db_at" as "[fail|db_at]"; eauto.
  iRight. iExists t1, t2. do 2!iSplit => //; eauto.
  iApply DB.load_at_stored_at; eauto.
  iApply DB.stored_atI; eauto.
- iDestruct "inv_ts" as "[fail|(% & %e & load_at)]"; eauto.
  case: e => <-.
  iDestruct "db_at" as "[fail|db_at]"; eauto.
  iRight. iApply (DB.db_at_op_at with "db_at load_at").
Qed.

End Verif.
