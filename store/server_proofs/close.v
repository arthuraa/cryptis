From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role dh_auth.
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

Lemma wp_server_handle_close E c cs n ldb db :
  ↑cryptisN ⊆ E →
  ↑nroot.@"db" ⊆ E →
  channel c -∗
  store_ctx N -∗
  handler_correct
    (server_handler_inv cs n ldb db)
    (server_handler_post cs ldb)
    cs
    (N.@"close", Server.handle_close N c (repr cs) ldb)
    n E.
Proof.
iIntros "%sub %sub' #chan_c #ctx".
iPoseProof (store_ctx_close with "ctx") as "?".
iPoseProof (store_ctx_ack_close with "ctx") as "?".
rewrite /handler_correct. wp_lam; wp_pures. iModIntro.
iExists _. iSplit => //. iIntros "!> %m #p_m #inv_m conn (server & db)".
wp_pures. wp_bind (Connection.timestamp _).
iApply (wp_connection_timestamp with "conn").
iIntros "!> conn". wp_pures.
wp_bind (to_int _). iApply wp_to_int.
case: Spec.to_intP => [ {m} n' ->| _]; wp_pures; last by failure.
case: bool_decide_reflect => [[<-] {n'}|?]; last by wp_pures; failure.
iPoseProof (ack_close_predI with "server inv_m") as "{p_m} >H" => //.
wp_pures. iMod "H" as "(server & #p_m)".
wp_bind (tint _). iApply wp_tint.
wp_bind (Connection.send _ _ _ _).
iApply (wp_connection_send with "[//] [//] [] p_m conn") => //.
- by rewrite public_TInt.
iIntros "!> conn". wp_pures.
iRight. iModIntro. iExists _. iSplit => //.
iExists _, _. iRight. by iFrame.
Qed.

End Verif.
