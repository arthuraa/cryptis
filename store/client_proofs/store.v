From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.
From cryptis.store Require Import impl shared db.
From cryptis.store.client_proofs Require Import common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Local Instance STORE : PK := PK_DH (λ _ _ _ _, True)%I.

Implicit Types (cs : cst).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_get_timestamp E cs (n : nat) :
  {{{ cst_ts cs ↦ #n }}}
    Client.get_timestamp (repr cs) @ E
  {{{ RET #n; cst_ts cs ↦ #n }}}.
Proof.
rewrite /Client.get_timestamp.
iIntros "%Φ Hn post".
wp_pures. wp_load. iApply "post". iModIntro. by iFrame.
Qed.

Lemma wp_client_incr_timestamp E cs (n : nat) :
  {{{ cst_ts cs ↦ #n }}}
    Client.incr_timestamp (repr cs) @ E
  {{{ RET #(); cst_ts cs ↦ #(S n) }}}.
Proof.
iIntros "%Ψ Hn post".
rewrite /Client.incr_timestamp; wp_pures; wp_load; wp_store.
iApply "post"; iFrame.
rewrite (_ : (n + 1)%Z = (S n)%nat :> Z); last by lia.
by iFrame.
Qed.

Lemma wp_client_get_session_key E cs :
  {{{ True }}}
    Client.get_session_key (repr cs) @ E
  {{{ RET (repr (Spec.mkskey (cst_key cs))); True }}}.
Proof.
rewrite /Client.get_session_key.
iIntros "%Φ ? post". wp_pures. by iApply "post".
Qed.

Lemma wp_client_send_store E c cs t1 t2 t2' :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  public t2' -∗ (* FIXME: t1 and t2' do not have to be public already *)
  {{{ client N cs ∗ rem_mapsto cs t1 t2 }}}
    Client.send_store N c (repr cs) t1 t2' @ E
  {{{ RET #(); client N cs ∗ rem_mapsto cs t1 t2' }}}.
Proof.
rewrite /Client.send_store /rem_mapsto.
iIntros "% #chan_c (_ & #? & _) #p_t1 #p_t2' !> %Φ [client mapsto] post".
iDestruct "client" as "(%n & #handshake & #key & #minted & ts & client)".
iMod (DB.update_client t2' with "client mapsto") as "(client & #update & mapsto)".
wp_pures. wp_bind (Client.get_timestamp _).
iApply (wp_client_get_timestamp with "ts"); iIntros "!> ts".
wp_pures. wp_bind (Client.incr_timestamp _).
iApply (wp_client_incr_timestamp with "ts"). iIntros "!> ts".
wp_pures. wp_bind (Client.get_session_key _).
iApply (wp_client_get_session_key with "[//]"); iIntros "!> _".
wp_pures. wp_list. wp_bind (tint _). iApply wp_tint. wp_list.
wp_term_of_list. wp_tsenc. wp_pures.
iPoseProof ("post" with "[client ts mapsto]") as "post".
{ iFrame. iExists (S n). iFrame. by eauto. }
iApply (wp_send with "[//] [#]") => //. iClear "post".
iModIntro. iApply public_TEncIS => //.
- by rewrite minted_TKey.
- iModIntro. iExists (cst_name cs), n, t1, t2', (cst_ok cs).
  do 5?iSplit => //.
- rewrite minted_of_list /= minted_TInt; do ![iSplit => //];
  by iApply public_minted.
- iModIntro. iIntros "_". rewrite public_of_list /= public_TInt. iSplit => //.
  by eauto.
Qed.

Lemma wp_client_ack_store E c cs :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  {{{ client N cs }}}
    Client.ack_store N c (repr cs) @ E
  {{{ RET #(); client N cs }}}.
Proof.
iIntros "% #chan_c (_ & _ & #? & _) !> %Φ client post".
rewrite /Client.ack_store. wp_pures.
iDestruct "client" as "(%n & #handshake & #key & #minted & ts & client)".
wp_bind (Client.get_timestamp _).
iApply (wp_client_get_timestamp with "ts"). iIntros "!> ts". wp_pures.
wp_bind (Client.get_session_key _).
iApply (wp_client_get_session_key with "[//]") => //.
iIntros "!> _". wp_pures.
iCombine "client post ts" as "I". iRevert "I".
iApply wp_sess_recv => //. iIntros "!> %m (client & post & ts) _".
wp_pures. wp_bind (tint _). iApply wp_tint.
wp_eq_term e; wp_pures; iModIntro; last first.
  iLeft. by iFrame.
iRight. iExists _; iSplit => //. iApply "post".
iExists n. by iFrame; eauto.
Qed.

Lemma wp_client_store E c cs t1 t2 t2' :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  public t2' -∗
  {{{ client N cs ∗ rem_mapsto cs t1 t2 }}}
    Client.store N c (repr cs) t1 t2' @ E
  {{{ RET #(); client N cs ∗ rem_mapsto cs t1 t2' }}}.
Proof.
iIntros "% #chan_c #ctx #p_t1 #p_t2 !> %Φ [client mapsto] post".
rewrite /Client.store.
wp_pures. wp_bind (Client.send_store _ _ _ _ _).
iApply (wp_client_send_store with "[] [] [] [//] [$client $mapsto] [post]")
  => //.
iIntros "!> [client mapsto]". wp_pures.
iApply (wp_client_ack_store with "[] [] [client] [post mapsto]") => //.
iIntros "!> client". iApply "post". by iFrame.
Qed.

End Verif.
