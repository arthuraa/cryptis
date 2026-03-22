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
      fail_token ga ∗
      peer_share_token ga ∗
      ready_token ga ∗
      term_token ga (⊤ ∖ ↑nsl_dhN)
  }}}.
Proof. Admitted.

Lemma wp_initiator_recv_msg2 c skI skR a φ N failed :
  let ga := TExp (TInt 0) a in
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    nsl_dh_pred N φ ∗
    dh_key skI skR a ∗
    fail_token ga ∗
    peer_share_token ga ∗
    ready_token ga ∗
    failed_early skI skR failed
  }}}
    initiator_recv_msg2 c skI (Spec.pkey skR) (Tag N) a ga
  {{{ r, RET (repr r);
    ⌜r = None⌝ ∨ ∃ gb : term,
    let si := SessInfo skI skR ga gb (TExp gb a) in
    ⌜r = Some gb⌝ ∗
    session skI skR si ∗
    □ (⌜failed⌝ → public (si_key si)) ∗
    (public (si_key si) ∨ φ skI skR si Init)
  }}}.
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
