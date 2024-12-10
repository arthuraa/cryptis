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

Lemma wp_server_handle_create c cs n ldb db :
   channel c -∗
  store_ctx N -∗
  handler_correct
    (server_handler_inv cs n ldb db)
    (server_handler_post cs ldb)
    cs
    (N.@"create", Server.handle_create N c (repr cs) ldb)
    n.
Proof.
iIntros "#chan_c #ctx".
iPoseProof (store_ctx_create with "ctx") as "?".
iPoseProof (store_ctx_ack_create with "ctx") as "?".
rewrite /handler_correct. wp_lam; wp_pures.
iModIntro. iExists _. iSplit => //.
iIntros "!> %m #p_m #inv_m conn (server & db)".
wp_pures.
wp_bind (Connection.timestamp _).
iApply (wp_connection_timestamp with "conn").
iIntros "!> conn". wp_pures.
wp_list_of_term m; wp_pures; last by failure.
wp_list_match => [timestamp t1 t2 ->| _]; wp_pures; last by failure.
wp_bind (to_int _). iApply wp_to_int.
case: Spec.to_intP => [ {m} n' ->| _]; wp_pures; last by failure.
case: bool_decide_reflect => [[<-] {n'}|?]; wp_pures; last by failure.
wp_bind (SAList.find _ _). iApply (SAList.wp_find with "db") => //.
iIntros "!> db". rewrite lookup_fmap.
wp_bind (match: _ with InjL <> => _ | InjR <> => _ end)%E.
iApply (wp_wand _ _ _ (λ v, ∃ (b : bool) n' db',
  ⌜v = #((if b then 1 else 0) : Z)⌝ ∗
  is_conn_state cs n' ∗
  server_connected cs n' db' ∗
  SAList.is_alist ldb (repr <$> db')) with "[conn db server]")%I.
{ case db_t1: (db !! t1) => [t2'|]; wp_pures.
  { by iExists false, _, _; iFrame. }
  wp_bind (SAList.insert _ _ _).
  iApply (SAList.wp_insert with "db").
  iIntros "!> db".
  rewrite -fmap_insert.
  iPoseProof (create_predE with "server p_m inv_m") as "server" => //.
  wp_pures.
  wp_bind (Connection.tick _).
  iApply (wp_connection_tick with "conn").
  iIntros "!> conn".
  wp_pures.
  iExists true, _, _. by iFrame. }
iIntros "% (%b & %n' & %db' & -> & conn & server & db)".
wp_pures.
wp_bind (tint _). iApply wp_tint.
wp_list.
wp_bind (tint _). iApply wp_tint.
wp_list.
wp_term_of_list.
wp_pures.
wp_bind (Connection.send _ _ _ _).
iApply (wp_connection_send with "[//] [//] [] [] conn") => //.
- rewrite !public_of_list /= !public_TInt. eauto.
  iDestruct "p_m" as "(_ & ? & ? & _)". by eauto.
- iRight. by iModIntro.
iIntros "!> conn".
wp_pures.
iModIntro. iRight. iExists _. iSplit => //. iExists _, _. iLeft.
by iFrame.
Qed.

End Verif.
