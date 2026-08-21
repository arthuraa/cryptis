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

Lemma wp_client_load skI skR cs t1 t2 :
  cryptis_ctx -∗
  store_ctx -∗
  public t1 -∗
  {{{ db_connected skI skR cs ∗
      db_mapsto skI skR t1 t2 }}}
    Client.load (repr cs) t1
  {{{ t2', RET (repr t2');
      db_connected skI skR cs ∗
      db_mapsto skI skR t1 t2 ∗
      public t2' ∗
      (compromised cs ∨ ⌜t2' = t2⌝) }}}.
Proof.
iIntros "#? #ctx #p_t1 !> %Φ [client mapsto] post".
iDestruct "client" as "(%odb & %db & conn & rel & token & state)".
iPoseProof (DB.db_state_mapsto with "state mapsto") as "%Hk".
wp_lam; wp_pures.
wp_bind (tag _ _). iApply wp_tag.
wp_bind (Sess.send _ _).
iApply (wp_send_msg _ _ _ _
          (iMsg_tag (db_arms skI skR cs (db_st skI skR cs) odb)) _
          (<? v> MSG v {{ ⌜db !! t1 = Some v⌝ }};
             db_st skI skR cs (Some db))%proto
          with "[conn token]").
{ iSplitL "conn".
  { iApply (connected_le with "conn"). iNext.
    by rewrite db_st_unfold. }
  iSplitR; first by rewrite public_tag.
  iDestruct "token" as "[#?|token]"; eauto.
  iRight.
  iApply (iMsg_tag_intro _ _ (db_arms_load _ _ _ _ _)).
  rewrite iMsg_exist_eq /=. iExists db, t1.
  rewrite iMsg_base_eq /=. iFrame.
  iSplit; first done.
  iSplit; first by eauto.
  auto. }
iIntros "!> conn". wp_pures.
iApply wp_fupd.
wp_apply (wp_recv with "conn").
iIntros "%t2' %p' (#p_t2' & conn & disj)".
iDestruct (connected_public_key_or' with "conn rel disj")
  as "(conn & rel & >disj)".
iDestruct "disj" as "[#comp|car]".
- iModIntro. iApply "post". iFrame "mapsto p_t2'".
  iSplitL; last by iLeft.
  iExists (Some db). iFrame "rel state". iSplit; eauto.
  by iApply (connected_compromised with "conn comp").
- rewrite iMsg_exist_eq /=. iDestruct "car" as "(%v & car)".
  rewrite iMsg_base_eq /=.
  iDestruct "car" as "(-> & Heq & %Hv)".
  rewrite later_equivI_1.
  iModIntro. iApply "post". iFrame "mapsto p_t2'".
  iSplitL; last by rewrite Hk in Hv; case: Hv => ->; iRight.
  iExists (Some db). iFrame "rel state".
  iSplit; eauto.
  iApply (connected_le with "conn"). iNext.
  iRewrite -"Heq". iApply iProto_le_refl.
Qed.

End Verif.
