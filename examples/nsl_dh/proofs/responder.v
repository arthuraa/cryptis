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
Proof.
iIntros "%Ψ (#chan_c & #ctx & #(m1_pred & ? & ?) & #m_skR) Hpost".
rewrite /responder_recv_msg1.
wp_pures. wp_apply wp_pkey. wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m) "#p_m".
wp_apply wp_adec => //. iSplit; last by protocol_failure.
iClear "p_m" => {m}. iIntros "%m1 #m_m1 #inv_m1".
wp_list_of_term m1; last by protocol_failure.
wp_list_match => [ga pkI {m1} ->|_]; last by protocol_failure.
rewrite minted_of_list /=.
iDestruct "m_m1" as "(#m_ga & #m_pkI & _)".
wp_apply wp_is_aenc_key => //.
iSplit; last by protocol_failure.
iIntros "%skI -> #m_skI". wp_pures.
iApply ("Hpost" $! (Some (ga, Spec.pkey skI))).
iRight. iExists ga, skI. iModIntro. do !iSplit => //.
iDestruct "inv_m1" as "[#p_m1|[#inv_m1 _]]".
- rewrite public_of_list /=.
  iDestruct "p_m1" as "(#p_ga & _)".
  by iIntros "!> _".
- iDestruct "inv_m1" as "(%ga' & %skI' & %e & #s_ga)".
  case/Spec.of_list_inj: e => <- /Spec.aenc_pkey_inj <-.
  done.
Qed.

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
    responder_send_msg2 c skR (Spec.pkey skI) ga (Tag N)
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

Lemma wp_responder_simple c skR N :
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    nsl_dh_pred N (λ _ _ _ _, True)%I ∗
    minted skR
  }}}
    responder c skR (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI si,
      ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
      session skI skR si ∗
      release_token (si_resp_share si) ∗
      term_token (si_resp_share si) (⊤ ∖ ↑nsl_dhN)
  }}}.
Proof. Admitted.

End Verif.
