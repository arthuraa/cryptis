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

Lemma wp_client_create c kI kR cs t1 t2 :
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  public t2 -∗
  {{{ client_connected kI kR cs ∗
      rem_free_at kI kR {[t1]} }}}
    Client.create N c (repr cs) t1 t2
  {{{ (b : bool), RET #b;
      client_connected kI kR cs ∗
      rem_mapsto kI kR t1 t2 }}}.
Proof.
iIntros "#chan_c (_ & _ & _ & _ & _ & _ & #create & #ack & _) #p_t1 #p_t2".
iIntros "!> %Φ [client free] post".
iDestruct "client" as "(%n & %beginning & <- & <- & conn & client)".
rewrite /Client.create. wp_pures.
iMod (@rem_mapsto_alloc _ _ _ _ _ t1 t2 with "client free")
  as "(client & mapsto & _ & #created)".
{ by rewrite elem_of_singleton. }
wp_bind (Connection.timestamp _).
iApply (wp_connection_timestamp with "conn").
iIntros "!> conn". wp_pures.
wp_bind (Connection.tick _).
iApply (wp_connection_tick with "conn"). iIntros "!> conn".
iDestruct (create_predI with "client p_t1 p_t2 created")
  as "#p_m1".
wp_list. wp_bind (tint _). iApply wp_tint. wp_list. wp_term_of_list. wp_pures.
wp_bind (Connection.send _ _ _ _).
iApply (wp_connection_send with "[//] create [] [//] conn") => //.
{ by rewrite public_of_list /= public_TInt; eauto. }
iIntros "!> conn". wp_pures.
iCombine "client mapsto post" as "I". iRevert "conn I".
iApply wp_connection_recv => //.
iIntros "!> %m conn (client & mapsto & post) #m_m #inv'".
wp_pures. wp_list_of_term m; wp_pures; last by iLeft; iFrame.
wp_list_match => [ts' k' v' b -> {m}|_] /=; wp_pures; last by iLeft; iFrame.
wp_bind (tint _). iApply wp_tint.
wp_eq_term e; wp_pures; last by iLeft; iFrame.
subst ts'.
wp_eq_term e; wp_pures; last by iLeft; iFrame.
subst k'.
wp_eq_term e; wp_pures; last by iLeft; iFrame.
subst v'.
wp_bind (tint _). iApply wp_tint.
wp_bind (eq_term _ _). iApply wp_eq_term. wp_pures.
iRight. iModIntro. iExists _. iSplit => //. iApply "post".
iFrame. iExists _, _. iFrame. do !iSplit => //.
Qed.

End Verif.
