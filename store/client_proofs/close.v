From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta nown cryptis.
From cryptis Require Import primitives tactics role iso_dh.
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

Lemma wp_client_close c kI kR cs :
  channel c -∗
  store_ctx N -∗
  {{{ db_connected kI kR cs }}}
    Client.close N c (repr cs)
  {{{ RET #(); db_disconnected kI kR }}}.
Proof.
iIntros "#chan_c (_ & _ & _ & _ & _ & _ & _ & _ & #close & #ack & _)".
iIntros "!> %Φ client post".
iDestruct "client" as "(%n & %beginning & client & conn)".
iPoseProof (client_connected_wf_conn_state with "conn") as "#?".
wp_lam; wp_pures.
wp_apply (wp_connection_timestamp_client with "conn"). iIntros "conn".
iAssert (⌜cs_role cs = Init⌝)%I as "%e_rl".
{ by iDestruct "conn" as "(? & ? & ? & ?)". }
wp_pures. wp_apply wp_tint. wp_pures.
iMod (close_predI with "client conn") as "(client & #p_m1)" => //.
wp_bind (Connection.send _ _ _ _).
wp_apply (wp_connection_send with "[//] close [] [] [//]") => //.
{ by rewrite public_TInt. }
{ by iIntros "!> _". }
iIntros "_". wp_pures.
iDestruct "client" as "(client & conn)".
iDestruct "conn" as "(% & % & #? & ts & rel & end & #ending & #conn)".
iCombine "client end post" as "I". iRevert "ts rel I".
have ->: si_init_share cs = cs_share cs.
{ by rewrite /cs_share e_rl. }
iApply wp_connection_recv => //.
iIntros "!> %m ts rel (client & end & post) #m_m #inv'".
iMod (ack_close_predE with "[ts rel end client] inv'")
  as "[ts client]" => //.
{ iFrame. rewrite /cs_share e_rl /=. iFrame. eauto. }
wp_pures. wp_apply (wp_connection_close with "ts").
iIntros "_". wp_pures.
iRight. iModIntro. iExists _. iSplit; eauto.
by iApply "post".
Qed.

End Verif.
