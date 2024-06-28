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

Lemma wp_client_create E c cs t1 t2 :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  public t2 -∗
  {{{ client cs ∗ rem_free_at cs {[t1]} }}}
    Client.create N c (repr cs) t1 t2 @ E
  {{{ (b : bool), RET #b;
      client cs ∗
      rem_mapsto cs t1 t2 }}}.
Proof.
iIntros "% #chan_c (_ & _ & _ & _ & _ & #? & #? & _)
         #p_t1 #p_t2' !> %Φ [client free] post".
iDestruct "client" as "(%n & #handshake & #key & #minted & ts & client)".
rewrite /Client.create. wp_pures.
wp_bind (Client.get_timestamp _).
iApply (wp_client_get_timestamp with "ts").
iIntros "!> ts". wp_pures.
wp_bind (Client.get_session_key _).
iApply wp_client_get_session_key => //.
iIntros "!> _". wp_pures.
wp_list. wp_bind (tint _). iApply wp_tint. wp_list. wp_term_of_list. wp_pures.
wp_tsenc. wp_pures.
iMod (DB.create_client t1 t2 with "client free")
  as "(#create & client & up)".
wp_bind (send _ _). iApply wp_send => //.
{ iApply public_TEncIS => //.
  - by rewrite minted_TKey.
  - iModIntro. iExists n, t1, t2, cs, (cst_name cs).
    by eauto 8.
  - rewrite minted_of_list /= minted_TInt.
    rewrite -[minted t1]public_minted -[minted t2]public_minted.
    by eauto.
  - iIntros "!> !> _".
    rewrite public_of_list /= public_TInt. by eauto. }
wp_pures.
iCombine "post ts client up" as "I". iRevert "I".
iApply wp_sess_recv => //.
iIntros "!> %m (post & ts & client & up) #p_m". wp_pures.
wp_list_of_term m; wp_pures; last by iLeft; iFrame.
wp_list_match => [ts' k' v' b -> {m}|_] /=; wp_pures; last by iLeft; iFrame.
wp_bind (tint _). iApply wp_tint.
wp_eq_term e; wp_pures; last by iLeft; iFrame.
subst ts'.
wp_eq_term e; wp_pures; last by iLeft; iFrame.
subst k'.
wp_eq_term e; wp_pures; last by iLeft; iFrame.
subst v'.
wp_bind (Client.incr_timestamp _).
iApply (wp_client_incr_timestamp with "ts").
iIntros "!> ts".
wp_pures. wp_bind (tint _). iApply wp_tint.
wp_bind (eq_term _ _). iApply wp_eq_term. wp_pures.
iRight. iModIntro. iExists _. iSplit => //. iApply "post".
iFrame. iExists (S n). iFrame. do !iSplit => //.
Qed.

End Verif.
