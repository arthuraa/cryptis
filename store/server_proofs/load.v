From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis primitives tactics.
From cryptis Require Import role rpc.
From cryptis.store Require Import impl shared alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeGS Σ}.

Implicit Types (cs : RPC.state).
Implicit Types skI skR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Ltac failure := iLeft; iFrame; eauto.

Lemma wp_server_handle_load c skI skR cs vdb :
  RPC.cs_role cs = Resp →
  channel c -∗
  store_ctx N -∗
  RPC.handler_correct
    (server_db_connected' N skI skR cs vdb)
    skI skR cs
    (N.@"load", Server.handle_load N c (repr cs) vdb).
Proof.
iIntros "%e_rl #chan_c #ctx".
iPoseProof (store_ctx_load with "ctx") as "?".
iPoseProof (store_ctx_ack_load with "ctx") as "?".
rewrite /RPC.handler_correct /= /RPC.handler_correct_gen.
wp_lam; wp_pures. iModIntro. iExists _. iSplit => //.
iIntros "!> %n %ts !> %Φ (conn & db & #p_ts & #inv_ts) post".
wp_pures.
iApply (wp_wand with "[conn db] post").
iDestruct "db" as "(%db & #p_db & db & #db_at)".
wp_pures.
wp_list_match => [t1 ->| _]; wp_pures; last by failure.
wp_bind (SAList.find _ _). iApply (SAList.wp_find with "db") => //.
iIntros "!> db". rewrite lookup_fmap.
case db_t1: (db !! t1) => [t2|]; wp_pures; last by failure.
wp_list.
rewrite -e_rl.
iPoseProof (ack_load_predI with "inv_ts db_at") as "[? #?]" => //.
wp_apply (RPC.wp_write with "[//] [] [] [] [$]") => //.
- rewrite /public_db big_sepM_forall.
  iDestruct ("p_db" $! t1 t2 with "[//]") as "[??]".
  by rewrite /=; eauto.
iIntros "conn". wp_pures.
wp_apply (RPC.wp_tick with "conn"). iIntros "conn". wp_pures.
iModIntro. iRight. iExists _. iSplit => //.
iSplit => //. iExists (S n). iFrame.
rewrite e_rl. by iSplit => //.
Qed.

End Verif.
