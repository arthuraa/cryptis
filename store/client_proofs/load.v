From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role dh_auth.
From cryptis.store Require Import impl shared db.
From cryptis.store.client_proofs Require Import common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types (cs : cst).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_load E c cs t1 t2 :
  ↑N ⊆ E →
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  {{{ client cs ∗ rem_mapsto cs t1 t2 }}}
    Client.load N c (repr cs) t1 @ E
  {{{ t2', RET (repr t2');
      client cs ∗
      rem_mapsto cs t1 t2 ∗
      (session_fail cs ∨ ⌜t2' = t2⌝) }}}.
Proof.
iIntros "% % #chan_c #ctx #p_t1 !> %Φ [client mapsto] post".
iDestruct "client" as "(%n & #sessI & #key & #minted_key & ts & view)".
rewrite /Client.load. wp_pures.
wp_bind (Client.get_timestamp _).
iApply (wp_client_get_timestamp with "ts").
iIntros "!> ts". wp_bind (tint _). iApply wp_tint.
wp_pures. wp_bind (Client.get_session_key _).
iApply (wp_client_get_session_key with "[//]"). iIntros "!> _". wp_pures.
wp_list. wp_term_of_list. wp_tsenc. wp_pures.
wp_bind (send _ _). iApply wp_send; eauto.
  iDestruct "ctx" as "(_ & _ & _ & ? & _)".
  iModIntro. iApply public_TEncIS; eauto.
  - by rewrite minted_TKey.
  - rewrite minted_of_list /= minted_TInt.
    iPoseProof (public_minted with "p_t1") as "?". by eauto.
  - iIntros "!> _". rewrite public_of_list /= public_TInt; eauto.
wp_pures.
iCombine "view mapsto post ts" as "I". iRevert "I". iApply wp_sess_recv => //.
iIntros "!> %ts (view & mapsto & post & ts) #p_t2'". wp_pures.
wp_list_of_term ts; wp_pures; last by iLeft; iFrame.
wp_list_match => [n' t1' t2' -> {ts}|_]; wp_pures; last by iLeft; iFrame.
wp_eq_term e; last by wp_pures; iLeft; iFrame.
subst n'. wp_pures.
wp_eq_term e; last by wp_pures; iLeft; iFrame.
subst t1'.
iDestruct (ack_loadE with "ctx sessI key view mapsto p_t2'")
  as "{p_t2'} (#p_t2' & #e_t2')".
wp_pures. iModIntro. iRight. iExists _; iSplit; eauto.
iApply ("post" $! t2'). iFrame. iSplitL => //.
iExists n. iFrame. by eauto.
Qed.

End Verif.
