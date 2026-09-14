From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis replica primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn sess alist.
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
Local Existing Instance storeGS_replica.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ,
          !sessG Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types (db : gmap term term).

Lemma wp_connect' (P : iProp) c skI skR :
  channel c -∗
  cryptis_ctx -∗
  store_ctx -∗
  minted skI -∗
  minted skR -∗
  {{{ GenConn.failure skI skR ∨ P }}}
    Sess.connect c skI (Spec.pkey skR) (Tag dbN)
  {{{ cs, RET (repr cs);
      connected skI skR Init cs (db_st0 skI skR cs) ∗
      release_token (si_init_share cs) ∗
      (public (si_key cs) ∨ P) }}}.
Proof.
iIntros "#? #? #? #? #? %Φ !> HP post".
wp_lam; wp_pures.
wp_apply (GenConn.wp_connect P with "[] [HP]"); eauto 10.
iIntros "%cs (conn & HP & own & rel & token)".
iApply ("post" $! cs). rewrite /connected. by iFrame.
Qed.

Lemma wp_client_connect c skI skR :
  channel c -∗
  cryptis_ctx -∗
  store_ctx -∗
  minted skI -∗
  minted skR -∗
  {{{ db_disconnected skI skR }}}
    Client.connect c skI (Spec.pkey skR)
  {{{ cs, RET (repr cs);
      db_connected skI skR cs }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_ekI #p_ekR".
iIntros "!> %Φ client post".
iDestruct "client" as "(%db & ready & state)".
wp_lam. wp_pures.
wp_apply (wp_connect' (db_client_ready skI skR db)
           with "chan_c ctx ctx' p_ekI p_ekR [$ready]").
iIntros "%cs (conn & rel & ready)". wp_pures.
iDestruct (connected_public_key_or' with "conn rel ready")
  as "(conn & rel & >ready)".
iAssert (|==> (public (si_key cs) ∨ rep_update skI skR dbN ∅ db db) ∗
              (compromised cs ∨ db_client_busy skI skR))%I
  with "[ready]" as ">[upd busy]".
{ iDestruct "ready" as "[#comp|ready]".
  - iModIntro. iSplitR "".
    + iLeft. by iApply compromised_public.
    + by iLeft.
  - iMod (db_connect_call with "ready") as "[busy upd]".
    iModIntro. iSplitL "upd"; first by iRight.
    by iRight. }
wp_bind (tag _ _). iApply wp_tag.
wp_bind (Sess.send _ _).
iApply (wp_send_msg _ _ _ _
          (iMsg_tag {[dbN.@"connect" :=
             (∃ db', MSG (TInt 0) {{ rep_update skI skR dbN ∅ db' db' }};
                db_st skI skR cs db')%msg]}) _
          (db_st skI skR cs db) with "[conn upd]").
{ iSplitL "conn"; first by rewrite /db_st0 /iProto_tag.
  iSplitR; first by rewrite public_tag public_TInt.
  iDestruct "upd" as "[#fail|upd]"; first by iLeft.
  iRight.
  iApply (iMsg_tag_intro _ _ (lookup_singleton_eq _ _)).
  rewrite iMsg_exist_eq /=. iExists db.
  rewrite iMsg_base_eq /=.
  iSplit; first done.
  iSplitR "upd"; first by auto.
  iExact "upd". }
iIntros "!> conn". wp_pures.
iApply "post". iModIntro. iExists db. iFrame.
Qed.

End Verif.
