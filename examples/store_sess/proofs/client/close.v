From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list dfrac_agree.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown cryptis.
From cryptis Require Import replica primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn sess.
From cryptis.examples.sess Require impl.
From cryptis.examples.sess.proofs Require Import base.
From cryptis.examples.sess Require Import proofs tag.
From cryptis.examples.store Require Import db.
From cryptis.examples.store_sess Require Import impl.
From cryptis.examples.store_sess.proofs Require Import base.
From actris.channel Require Import proto_model proto.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ,
          !sessG Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types (db : gmap term term).

Lemma wp_client_close skI skR cs :
  cryptis_ctx -∗
  store_ctx -∗
  {{{ db_connected skI skR cs }}}
    Client.close (repr cs)
  {{{ RET #(); db_disconnected skI skR ∗ public (si_key cs) }}}.
Proof.
iIntros "#? #ctx !> %Φ client post".
iDestruct "client" as "(%db & conn & rel & ready & state)".
wp_lam; wp_pures.
wp_bind (tag _ _). iApply wp_tag.
wp_bind (Sess.send _ _).
iApply (wp_send_msg _ _ _ _
          (iMsg_tag (db_arms skI skR cs (db_st skI skR cs) db)) _
          (<?> MSG (TInt 0) {{ db_client_ready skI skR db ∗
                               released (si_resp_share cs) }}; END)%proto
          with "[conn ready]").
{ iSplitL "conn".
  { iApply (connected_le with "conn"). iNext.
    iApply iProto_le_of_equiv. exact: db_st_unfold. }
  iSplitR; first by rewrite public_tag public_TInt.
  iDestruct "ready" as "[#comp|busy]".
  { iLeft. by iApply compromised_public. }
  iRight.
  iApply (iMsg_tag_intro _ _ (db_arms_close _ _ _ _ _)).
  rewrite iMsg_base_eq /=.
  iSplit; first done.
  iSplitR "busy"; first by auto.
  iExact "busy". }
iIntros "!> conn". wp_pures.
wp_apply (wp_recv with "conn").
iIntros "%t' %p' (#p_t' & conn & disj)".
iDestruct (connected_public_key_or' with "conn rel disj")
  as "(conn & rel & >disj)".
iDestruct "disj" as "[#comp|ack]".
- wp_pures.
  iPoseProof (connected_failure' with "conn comp") as "#fail".
  iDestruct "conn" as "[gc _]".
  wp_apply (GenConn.wp_free with "gc"). iIntros "_".
  iApply "post". iSplitR "".
  { iExists db. iFrame "state". by iLeft. }
  by iApply compromised_public.
- rewrite iMsg_base_eq /=.
  iDestruct "ack" as "(_ & _ & ack & #rel_resp)".
  iMod (release with "rel") as "#rel_init".
  iPoseProof (connected_released with "conn rel_init rel_resp") as "#p_k".
  wp_pures.
  iDestruct "conn" as "[gc _]".
  wp_apply (GenConn.wp_free with "gc"). iIntros "_".
  iApply "post". iFrame "p_k".
  iExists db. iFrame "state". by iRight.
Qed.

End Verif.
