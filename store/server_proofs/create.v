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

Ltac failure := iLeft; iFrame; eauto.

Lemma wp_server_handle_create c kI kR cs n n0 vdb :
  cs_role cs = Resp →
  channel c -∗
  store_ctx N -∗
  handler_correct
    (server_db_connected' kI kR cs n n0 vdb)
    (server_handler_post kI kR cs n0 vdb)
    kI kR cs n n0
    (N.@"create", Server.handle_create N c (repr cs) vdb).
Proof.
iIntros "%e_rl #chan_c #ctx".
iPoseProof (store_ctx_create with "ctx") as "?".
iPoseProof (store_ctx_ack_create with "ctx") as "?".
rewrite /handler_correct /=. wp_lam; wp_pures.
iModIntro. iExists _. iSplit => //.
iIntros "!> %ts conn #p_ts #inv_ts db".
iDestruct "db" as "(%db & #p_db & db & #db_at & token)".
wp_pures.
wp_list_match => [t1 t2 ->| _]; wp_pures; last by failure.
wp_bind (SAList.find _ _). iApply (SAList.wp_find with "db") => //.
iIntros "!> db". rewrite lookup_fmap.
wp_bind (match: _ with InjL <> => _ | InjR <> => _ end)%E.
iApply (wp_frame_wand with "conn").
iAssert (session_failed cs true ∨
           DB.db_at kI (dbCN kR.@"state")
             (S n + n0) (DB.op_app db (Create t1 t2)))%I
  as "#db_at'".
{ iDestruct "inv_ts" as "[?|inv_ts]"; eauto.
  iDestruct "inv_ts" as "(%t1' & %t2' & %e & create_at)".
  case: e => <- <-.
  iDestruct "db_at" as "[?|db_at]"; eauto.
  iRight. by iApply (DB.db_at_create_at with "db_at"). }
iApply (wp_wand _ _ _ (λ v,
  ∃ (b : bool), ⌜v = #((if b then 1 else 0) : Z)⌝ ∗
                server_db_connected' kI kR cs (S n) n0 vdb
  ) with "[db token]")%I.
{ case db_t1: (db !! t1) => [t2'|]; wp_pures.
  { iExists false; iModIntro; iFrame.
    by rewrite /= db_t1; eauto. }
  wp_bind (SAList.insert _ _ _).
  iApply (SAList.wp_insert with "db").
  iIntros "!> db". rewrite -fmap_insert.
  wp_pures.
  iFrame. iExists true. rewrite /= db_t1.
  iModIntro. do !iSplit => //.
  iDestruct "p_ts" as "(? & ? & _)".
  by iApply public_db_insert. }
iIntros "% (%b & -> & db) conn".
wp_pures.
wp_bind (tint _). iApply wp_tint.
wp_list.
wp_pures.
wp_apply (wp_connection_write with "[//] [] [] [] [$]") => //.
- rewrite /= public_TInt. iDestruct "p_ts" as "(? & ? & _)".
  by eauto.
- by iRight.
iIntros "conn". wp_pures.
wp_apply (wp_connection_tick with "[$]"). iIntros "conn".
wp_pures.
iModIntro. iRight. iExists _. iSplit => //.
iLeft. iSplit => //. iExists (S n). by iFrame.
Qed.

End Verif.
