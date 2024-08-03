From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta nown cryptis.
From cryptis Require Import primitives tactics role dh_auth.
From cryptis.store Require Import impl shared db connection_proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types (cs : conn_state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_close E c kI kR cs :
  ↑cryptisN ⊆ E →
  ↑nroot.@"db" ⊆ E →
  channel c -∗
  store_ctx N -∗
  {{{ client_connected kI kR cs }}}
    Client.close N c (repr cs) @ E
  {{{ RET #();
      client_disconnected kI kR }}}.
Proof.
iIntros "% % #chan_c (_ & _ & _ & _ & _ & _ & _ & _ & #close & #ack & _)".
iIntros "!> %Φ client post".
iDestruct "client" as "(%γI & %n & %beginning & <- & <- & conn & client)".
wp_lam; wp_pures.
wp_bind (Connection.timestamp _).
iApply (wp_connection_timestamp with "conn").
iIntros "!> conn". wp_pures.
wp_bind (tint _). iApply wp_tint. wp_pures.
iMod (close_predI with "conn client") as "(conn & client & #p_m1)" => //.
wp_bind (Connection.send _ _ _ _).
iApply (wp_connection_send with "[//] close [] [//] conn") => //.
{ by rewrite public_TInt. }
iIntros "!> conn". wp_pures.
iCombine "client post" as "I". iRevert "conn I".
iApply wp_connection_recv => //.
iIntros "!> %m conn (client & post) #m_m #inv'".
iMod (ack_close_predE with "conn client inv'") as "(conn & client)" => //.
wp_pures. wp_bind (Connection.close _ _).
iApply (wp_connection_close with "conn"). iIntros "!> _".
wp_pures.
iRight. iModIntro. iExists _. iSplit; eauto.
iApply "post".
iExists _, _. by eauto.
Qed.

End Verif.
