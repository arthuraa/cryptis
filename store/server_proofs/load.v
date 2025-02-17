From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta nown.
From cryptis Require Import cryptis primitives tactics.
From cryptis Require Import role conn.
From cryptis.store Require Import impl shared alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeGS Σ}.

Implicit Types (cs : Conn.state).
Implicit Types skI skR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Ltac failure := iLeft; iFrame; eauto.

Lemma wp_server_handle_load c skI skR cs n n0 vdb :
  Conn.cs_role cs = Resp →
  channel c -∗
  store_ctx N -∗
  Conn.handler_correct
    (server_db_connected' N skI skR cs n n0 vdb)
    (server_handler_post N skI skR cs n0 vdb)
    skI skR cs n n0
    (N.@"load", Server.handle_load N c (repr cs) vdb).
Proof.
iIntros "%e_rl #chan_c #ctx".
iPoseProof (store_ctx_load with "ctx") as "?".
iPoseProof (store_ctx_ack_load with "ctx") as "?".
rewrite /Conn.handler_correct /=. wp_lam; wp_pures.
iModIntro. iExists _. iSplit => //.
iIntros "!> %ts conn #p_ts #inv_ts (%db & #p_db & db & #db_at & token)".
wp_pures.
wp_list_match => [t1 ->| _]; wp_pures; last by failure.
wp_bind (SAList.find _ _). iApply (SAList.wp_find with "db") => //.
iIntros "!> db". rewrite lookup_fmap.
case db_t1: (db !! t1) => [t2|]; wp_pures; last by failure.
wp_list.
iPoseProof (ack_load_predI with "inv_ts db_at") as "[? #?]" => //.
wp_apply (Conn.wp_write with "[//] [] [] [] [$]") => //.
- rewrite /public_db big_sepM_forall.
  iDestruct ("p_db" $! t1 t2 with "[//]") as "[??]".
  by rewrite /=; eauto.
iIntros "conn". wp_pures.
wp_apply (Conn.wp_tick with "conn"). iIntros "conn". wp_pures.
iModIntro. iRight. iExists _. iSplit => //.
iLeft. iSplit => //. iExists (S n). iFrame.
by iSplit => //.
Qed.

End Verif.
