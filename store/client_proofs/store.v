From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role iso_dh.
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

Lemma wp_client_send_store c kI kR cs t1 t2 t2' :
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  public t2' -∗ (* FIXME: t1 and t2' shouldn't have to be public already *)
  {{{ client_connected kI kR cs ∗ rem_mapsto kI kR t1 t2 }}}
    Client.send_store N c (repr cs) t1 t2'
  {{{ RET #(); client_connected kI kR cs ∗ rem_mapsto kI kR t1 t2' }}}.
Proof.
iIntros "#chan_c (_ & _ & #? & _) #p_t1 #p_t2' !> %Φ [client mapsto] post".
iDestruct "client"
  as "(%n & %beginning & <- & <- & %e_rl & #conn & rel & ts & client)".
iMod (rem_mapsto_update t2' with "client mapsto")
  as "(client & mapsto & #update)".
wp_lam. wp_pures.
wp_apply (wp_connection_timestamp with "ts"); iIntros "ts".
wp_pures. wp_apply (wp_connection_tick with "ts"). iIntros "ts".
iPoseProof (store_predI with "client update") as "#?".
wp_pures. wp_list. wp_bind (tint _). iApply wp_tint. wp_list.
wp_term_of_list. wp_pures.
iApply (wp_connection_send with "[//] [//] [] [#] conn") => //.
{ rewrite public_of_list /= public_TInt. by eauto. }
{ by iIntros "!> _". }
iIntros "!> _".
iApply ("post" with "[ts rel client mapsto]").
by iFrame; eauto.
Qed.

Lemma wp_client_ack_store c kI kR cs :
  channel c -∗
  store_ctx N -∗
  {{{ client_connected kI kR cs }}}
    Client.ack_store N c (repr cs)
  {{{ RET #(); client_connected kI kR cs }}}.
Proof.
iIntros "#chan_c (_ & _ & _ & #? & _) !> %Φ client post".
iDestruct "client"
  as "(%n & %beginning & <- & <- & %e_rl & #conn & rel & ts & client)".
rewrite /Client.ack_store. wp_pures.
wp_apply (wp_connection_timestamp with "ts"). iIntros "ts".
wp_pures.
iCombine "client post" as "I". iRevert "ts rel I".
iApply wp_connection_recv => //.
iIntros "!> %m ts rel (client & post) #m_m _".
wp_pures. wp_apply wp_tint.
wp_eq_term e; wp_pures; last by iLeft; iFrame.
iRight. iModIntro. iExists _. iSplit => //.
iApply "post". by iExists _, _; iFrame; eauto.
Qed.

Lemma wp_client_store c kI kR cs t1 t2 t2' :
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  public t2' -∗
  {{{ client_connected kI kR cs ∗ rem_mapsto kI kR t1 t2 }}}
    Client.store N c (repr cs) t1 t2'
  {{{ RET #(); client_connected kI kR cs ∗ rem_mapsto kI kR t1 t2' }}}.
Proof.
iIntros "#chan_c #ctx #p_t1 #p_t2 !> %Φ [client mapsto] post".
rewrite /Client.store.
wp_pures. wp_bind (Client.send_store _ _ _ _ _).
iApply (wp_client_send_store with "[] [] [] [//] [$client $mapsto] [post]")
  => //.
iIntros "!> [client mapsto]". wp_pures.
iApply (wp_client_ack_store with "[] [] [client] [post mapsto]") => //.
iIntros "!> client". iApply "post". by iFrame.
Qed.

End Verif.
