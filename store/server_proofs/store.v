From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role iso_dh.
From cryptis.store Require Import impl shared alist db connection_proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeGS Σ}.

Implicit Types (cs : conn_state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Ltac failure := iLeft; iFrame.

Lemma wp_server_handle_store c kI kR cs n n0 vdb :
  cs_role cs = Resp →
  channel c -∗
  store_ctx N -∗
  handler_correct
    (server_db_connected' kI kR cs n n0 vdb)
    (server_handler_post kI kR cs n0 vdb)
    kI kR cs n n0
    (N.@"store", Server.handle_store N c (repr cs) vdb).
Proof.
iIntros "%e_rl #chan_c #ctx".
iPoseProof (store_ctx_store with "ctx") as "?".
iPoseProof (store_ctx_ack_store with "ctx") as "?".
rewrite /handler_correct /=. wp_lam; wp_pures.
iModIntro. iExists _. iSplit => //.
iIntros "!> %ts conn #p_ts #inv_m db". wp_pures.
wp_list_match => [t1 t2 ->|_]; wp_pures; last by failure.
iDestruct "db" as "(%db & #p_db & db & #db_at & token)".
wp_bind (SAList.insert _ _ _).
iApply (SAList.wp_insert with "db").
iIntros "!> db". rewrite -fmap_insert.
wp_pures.
wp_apply (@wp_nil term).
wp_apply (wp_connection_write with "[] [] [] [] [$]") => //.
{ iRight. by eauto. }
iIntros "conn". wp_pures. 
wp_apply (wp_connection_tick with "[$]"). iIntros "conn". wp_pures.
iModIntro. iRight. iExists _. iSplit => //.
iLeft. iSplit => //. iExists (S n). iFrame.
rewrite /=.
iDestruct "p_ts" as "(p_t1 & p_t2 & _)".
iSplit; first by iApply public_db_insert.
iDestruct "inv_m" as "[fail|inv_m]"; eauto.
iDestruct "inv_m" as "(%t1' & %t2' & %e & store_at)".
case: e => <- <-.
iDestruct "db_at" as "[fail|db_at]"; eauto.
iRight. iApply (DB.db_at_store_at with "db_at store_at").
Qed.

End Verif.
