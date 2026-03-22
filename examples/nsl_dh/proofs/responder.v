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

Implicit Types (rl : role) (t pkI pkR ga kS : term).
Implicit Types (skI skR : aenc_key).
Implicit Types (failed : bool).
Implicit Types (si : sess_info) (osi : option sess_info).
Implicit Types (N : namespace) (data : term).
Implicit Types (ores : option (term * term)).

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); eauto.

Lemma wp_responder_recv_msg1 c skR :
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    minted skR
  }}}
    responder_recv_msg1 c skR
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ ga skI,
        ⌜r = Some (ga, Spec.pkey skI)⌝ ∗
        minted ga ∗ minted skI ∗
        □ (public skI ∨ public skR → public ga) }}}.
Proof. Admitted.

Lemma wp_responder_send_msg2 c skI skR ga N φ failed :
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    nsl_dh_pred N φ ∗
    minted skI ∗
    minted skR ∗
    minted ga ∗
    □ (public skI ∨ public skR → public ga) ∗
    (∀ b,
        let gb := TExp (TInt 0) b in
        let gab := TExp ga b in
        let si := SessInfo skI skR ga gb gab in
        res_token (si_resp_share si) ={⊤}=∗
        φ (si_init si) (si_resp si) si Init ∗
        φ (si_init si) (si_resp si) si Resp) ∗
    failed_early skI skR failed
  }}}
    responder_send_msg2 c skR ga (Spec.pkey skI) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ b,
      let gb := TExp (TInt 0) b in
      let gab := TExp ga b in
      let si := SessInfo skI skR ga gb gab in
      ⌜r = Some (b, gb)⌝ ∗
      release_token gb ∗
      term_token gb (⊤ ∖ ↑nsl_dhN) ∗
      φ skI skR si Resp }}}.
Proof. Admitted.

Lemma wp_responder_recv_msg3 c skI skR ga b :
  let gb := TExp (TInt 0) b in
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    minted skI ∗
    minted skR ∗
    minted ga ∗
    □ (public skI ∨ public skR → public ga) ∗
    dh_key skI skR b ∗
    release_token gb
  }}}
    responder_recv_msg3 c skR (Spec.pkey skI) b gb ga
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ b,
      let gb := TExp (TInt 0) b in
      let gab := TExp ga b in
      let si := SessInfo skI skR ga gb gab in
      ⌜r = Some (si_key si)⌝ ∗
      session skI skR si ∗
      release_token gb }}}.
Proof. Admitted.

End Verif.
