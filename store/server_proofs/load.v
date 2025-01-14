From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta nown.
From cryptis Require Import cryptis primitives tactics.
From cryptis Require Import role iso_dh.
From cryptis.store Require Import impl shared alist db connection_proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeGS Σ}.

Implicit Types (cs : conn_state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Ltac failure := iLeft; iFrame.

Lemma wp_server_handle_load c cs ldb db n :
  cs_role cs = Resp →
  channel c -∗
  store_ctx N -∗
  handler_correct
    (server_handler_inv cs n ldb db)
    (server_handler_post cs ldb)
    cs
    (N.@"load", Server.handle_load N c (repr cs) ldb)
    n.
Proof.
iIntros "%e_rl #chan_c #ctx".
iPoseProof (store_ctx_load with "ctx") as "?".
iPoseProof (store_ctx_ack_load with "ctx") as "?".
rewrite /handler_correct e_rl /=. wp_lam; wp_pures.
iModIntro. iExists _. iSplit => //.
iIntros "!> %m _ #p_m #conn rel ts (server & db)".
wp_pures.
wp_bind (Connection.timestamp _).
iApply (wp_connection_timestamp with "ts"). iIntros "!> ts".
wp_pures.
wp_list_of_term m; wp_pures; last by failure.
wp_list_match => [timestamp t1 ->| _]; wp_pures; last by failure.
wp_bind (to_int _). iApply wp_to_int.
case: Spec.to_intP => [ {m} n' -> | _]; wp_pures; last by failure.
case: bool_decide_reflect => [[<-]|?]; wp_pures; last by failure.
wp_bind (SAList.find _ _). iApply (SAList.wp_find with "db") => //.
iIntros "!> db". rewrite lookup_fmap.
case db_t1: (db !! t1) => [t2|]; wp_pures; last by failure.
wp_list. wp_bind (tint _). iApply wp_tint. wp_list. wp_term_of_list.
wp_pures.
iPoseProof (ack_load_predI db_t1 with "server") as "#[??]".
wp_bind (Connection.send _ _ _ _).
iApply (wp_connection_send with "[//] [//] [] [] conn") => //.
{ by iIntros "!> _". }
iIntros "!> _". wp_pures. iModIntro.
iRight. iExists _. iSplit => //. iExists _, _. iLeft. by iFrame.
Qed.

End Verif.
