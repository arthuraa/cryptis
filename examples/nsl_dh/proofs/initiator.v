From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.examples.nsl_dh Require Import impl.
From cryptis.examples.nsl_dh.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !nsl_dhGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : aenc_key).
Implicit Types (failed : bool).
Implicit Types (si : sess_info).
Implicit Types (N : namespace).

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); eauto.

Lemma wp_initiator_send_msg1 c skI skR :
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    minted skI ∗
    minted skR
  }}}
    initiator_send_msg1 c skI (Spec.pkey skR)
  {{{ (a : term), RET (a, TExp (TInt 0) a);
      let ga := TExp (TInt 0) a in
      dh_key skI skR a ∗
      release_token ga ∗
      peer_share_token ga ∗
      ready_token ga ∗
      term_token ga (⊤ ∖ ↑nsl_dhN)
  }}}.
Proof.
iIntros "%Ψ (#chan_c & #ctx & #(m1_pred & ? & ?) & #m_skI & #m_skR) Hpost".
rewrite /initiator_send_msg1.
wp_pures. wp_apply wp_pkey. wp_pures.
set pkI := Spec.pkey skI.
wp_apply (wp_mk_dh_keys skI skR); first by iFrame "#".
iIntros "%a #dh_a rel peer ready res tok".
set ga := TExp (TInt 0) a.
wp_pures. wp_list. wp_term_of_list. wp_pures.
wp_apply wp_aenc => //.
{ iDestruct "dh_a" as "(#m_a & _)".
  rewrite minted_of_list /= minted_TExp minted_TInt /= minted_pkey.
  by do !iSplit. }
{ iRight. iSplit.
  - iModIntro. iExists ga, skI. iSplit => //.
    iIntros "#corr".
    iApply (public_dh_share with "dh_a").
    by iModIntro.
  - iIntros "!> #p_skR". rewrite public_of_list /=. do !iSplit => //.
    + iApply (public_dh_share with "dh_a"). iModIntro. by eauto.
    + by iApply public_aenc_key. }
iIntros "%m1 #p_m1". wp_pures.
wp_apply wp_send => //.
wp_pures.
iApply ("Hpost" $! a). by iFrame "∗ #".
Qed.

Lemma wp_initiator_recv_msg2 c skI skR a N :
  let ga := TExp (TInt 0) a in
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx
  }}}
    initiator_recv_msg2 c skI (Spec.pkey skR) (Tag N) a ga
  {{{ r, RET (repr r);
    ⌜r = None⌝ ∨ ∃ gb : term,
    ⌜r = Some gb⌝ ∗
    (public ga ∧ public gb ∨ msg2_pred' skI skR ga gb N)
  }}}.
Proof. Admitted.

Lemma initiator_process_msg2 skI skR a gb N φ failed :
  let ga := TExp (TInt 0) a in
  let gab := TExp gb a in
  let si := SessInfo skI skR ga gb gab in
  nsl_dh_pred N φ -∗
  dh_key skI skR a -∗
  peer_share_token ga -∗
  ready_token ga -∗
  failed_early skI skR failed -∗
  (public ga ∧ public gb ∨ msg2_pred' skI skR ga gb N) ={⊤}=∗
  session skI skR si ∗
  □ (⌜failed⌝ → public (si_key si)) ∗
  (public (si_key si) ∨ φ skI skR si Init).
Proof. Admitted.

Lemma wp_initiator_send_msg3 c skI skR a gb :
  let ga := TExp (TInt 0) a in
  let si := SessInfo skI skR ga gb (TExp gb a) in
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx
  }}}
    initiator_send_msg3 c skI (Spec.pkey skR) a ga gb
  {{{ RET (repr (si_key si)); True }}}.
Proof. Admitted.

Lemma wp_initiator failed c skI skR N φ :
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    nsl_dh_pred N φ ∗
    minted skI ∗
    minted skR ∗
    failed_early skI skR failed
  }}}
    initiator c skI (Spec.pkey skR) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session skI skR si ∗
        □ (⌜failed⌝ → public (si_key si)) ∗
        release_token (si_init_share si) ∗
        term_token (si_init_share si) (⊤ ∖ ↑nsl_dhN) ∗
        (public (si_key si) ∨ φ skI skR si Init)
  }}}.
Proof. Admitted.

Lemma wp_initiator_weak c skI skR N :
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    nsl_dh_pred N (λ _ _ _ _, True)%I ∗
    minted skI ∗
    minted skR
  }}}
    initiator c skI (Spec.pkey skR) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session_weak skI skR si ∗
        term_token (si_init_share si) (⊤ ∖ ↑nsl_dhN)
  }}}.
Proof. Admitted.

End Verif.
