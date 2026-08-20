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

Lemma wp_client_store skI skR cs t1 t2 t2' :
  cryptis_ctx -∗
  store_ctx -∗
  public t1 -∗
  public t2' -∗
  {{{ db_connected skI skR cs ∗ db_mapsto skI skR t1 t2 }}}
    Client.store (repr cs) t1 t2'
  {{{ RET #(); db_connected skI skR cs ∗ db_mapsto skI skR t1 t2' }}}.
Proof.
iIntros "#? #ctx #p_t1 #p_t2 !> %Φ [client mapsto] post".
iDestruct "client" as "(%odb & %db & conn & rel & token & state)".
iMod (DB.db_state_update t2' with "state mapsto") as "[state mapsto]".
wp_lam. wp_pures. wp_list. wp_term_of_list.
wp_bind (tag _ _). iApply wp_tag.
wp_bind (Sess.send _ _).
iApply (wp_send_msg _ _ _ _
          (iMsg_tag (db_arms skI skR cs (db_st skI skR cs) odb)) _
          (db_st skI skR cs (Some (<[t1 := t2']> db)))
          with "[conn token]").
{ iSplitL "conn".
  { iApply (connected_le with "conn"). iNext.
    iApply iProto_le_of_equiv. exact: db_st_unfold. }
  iSplitR.
  { rewrite public_tag public_of_list /=. by iFrame "#". }
  iDestruct "token" as "[#?|token]"; eauto.
  iRight.
  iApply (iMsg_tag_intro _ _ (db_arms_store _ _ _ _ _)).
  rewrite iMsg_exist_eq /=. iExists db, t1, t2'.
  rewrite iMsg_base_eq /=.
  by do !iSplit. }
iIntros "!> conn". wp_pures.
iApply "post". iFrame "mapsto". iModIntro.
iExists (Some (<[t1 := t2']> db)), _. iFrame. by iRight.
Qed.

End Verif.
