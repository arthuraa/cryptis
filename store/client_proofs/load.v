From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list dfrac_agree.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta nown cryptis.
From cryptis Require Import primitives tactics.
From cryptis Require Import role iso_dh.
From cryptis.store Require Import impl shared db connection_proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_load c kI kR cs t1 t2 :
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  {{{ client_connected kI kR cs ∗
      rem_mapsto kI kR t1 t2 }}}
    Client.load N c (repr cs) t1
  {{{ t2', RET (repr t2');
      client_connected kI kR cs ∗
      rem_mapsto kI kR t1 t2 ∗
      public t2' ∗
      session_failed_or cs ⌜t2' = t2⌝ }}}.
Proof.
iIntros "#chan_c #ctx #p_t1 !> %Φ [client mapsto] post".
iDestruct "ctx" as "(_ & _ & _ & _ & load & ack_load & _)".
iDestruct "client"
  as "(%n & %beginning & <- & <- & %e_rl & #conn & rel & ts & client)".
rewrite /Client.load. wp_pures. wp_bind (Connection.timestamp _).
iApply (wp_connection_timestamp with "ts"). iIntros "!> ts".
wp_bind (tint _). iApply wp_tint.
wp_pures. wp_apply (wp_connection_tick with "ts"). iIntros "ts".
wp_pures. wp_list. wp_term_of_list.
iMod (load_predI _ _ _ t1 with "client") as "(client & #load_at & #?)".
wp_bind (Connection.send _ _ _ _).
iApply (wp_connection_send with "[//] load [] [#]") => //.
{ rewrite public_of_list /= public_TInt. by eauto. }
{ by iIntros "!> _". }
iIntros "!> _". wp_pures.
iCombine "client mapsto post" as "I". iRevert "ts rel I".
iApply wp_connection_recv => //.
iIntros "!> %ts ts rel (client & mapsto & post) #p_m #inv_m". wp_pures.
wp_list_of_term ts; wp_pures; last by iLeft; iFrame.
wp_list_match => [n' t2' -> {ts}|_]; wp_pures; last by iLeft; iFrame.
wp_eq_term e; last by wp_pures; iLeft; iFrame.
subst n'. wp_pures.
iPoseProof (ack_loadE with "client load_at mapsto p_m inv_m") as "#p_t2'".
iRight. iModIntro. iExists _. iSplit => //.
iApply "post".
iFrame.
by iSplit => //; eauto.
Qed.

End Verif.
