From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.examples.iso_dh Require Import impl.
From cryptis.examples.iso_dh.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !iso_dhGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t pkI pkR ga kS : term).
Implicit Types (skI skR : sign_key).
Implicit Types (failed : bool).
Implicit Types (si : sess_info) (osi : option sess_info).
Implicit Types (N : namespace) (data : term).
Implicit Types (ores : option (term * term)).

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); eauto.

Lemma wp_responder_listen c :
  {{{ channel c ∗ cryptis_ctx  }}}
    responder_listen c
  {{{ ga skI, RET (ga, Spec.pkey skI); public ga ∗ minted skI }}}.
Proof.
iIntros "%Φ [#chan_c #ctx] post". wp_lam. wp_pures.
iApply (wp_frame_wand with "post").
wp_apply wp_do_until'. iIntros "!>".
wp_pures. wp_apply wp_recv => //.
iIntros "%m1 #p_m1". wp_pures.
wp_list_of_term m1; wp_pures; last by eauto.
wp_list_match => [ga pkI ->|_]; wp_pures; last by eauto.
rewrite public_of_list /=. iDestruct "p_m1" as "(? & ? & _)".
wp_apply wp_is_verify_key; first by iApply public_minted.
iSplit; last by wp_pures; eauto. iIntros "%skI -> #m_skI".
wp_pures. iModIntro. iRight. iExists _; iSplit => //.
iIntros "post". by iApply "post"; eauto.
Qed.

Lemma wp_responder_confirm failed c skI skR ga N φ :
  {{{ channel c ∗ cryptis_ctx ∗
      iso_dh_ctx ∗ iso_dh_pred N φ ∗
      public ga ∗ minted skI ∗ minted skR ∗
      (∀ b,
          let gb := TExp (TInt 0) b in
          let gab := TExp ga b in
          let si := SessInfo skI skR ga gb gab in
          term_token (si_resp_share si) (↑iso_dhN.@"res") ={⊤}=∗
           φ (si_init si) (si_resp si) si Init ∗
           φ (si_init si) (si_resp si) si Resp) ∗
      if failed then public skI ∨ public skR
      else True }}}
    responder_confirm c skR ga (Spec.pkey skI) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session skI skR si ∗
        □ (⌜failed⌝ → public (si_key si)) ∗
        release_token (si_resp_share si) ∗
        term_token (si_resp_share si) (⊤ ∖ ↑iso_dhN) ∗
        φ skI skR si Resp }}}.
Proof.
set pkR := Spec.pkey skR.
iIntros "%Φ (#chan_c & #? & (#? & #?) & #N_φ &
             #p_ga & #m_skI & #m_skR & res & #failed) Hpost".
wp_lam. wp_pures. wp_apply wp_pkey. wp_pures.
wp_apply (wp_mk_nonce_freshN ∅
          (λ b, ⌜failed⌝ ∨ released ga ∧ released (TExp (TInt 0) b))%I
          iso_dh_key_share
          (λ b, {[TExp (TInt 0) b]}))
       => //.
- iIntros "%". rewrite elem_of_empty. iIntros "[]".
- iIntros "%b".
  rewrite big_sepS_singleton minted_TExp minted_TInt /= bi.True_and.
  iModIntro. by iApply bi.equiv_iff.
iIntros "%b _ _ #m_b #s_b #dh_gb token".
rewrite bi.intuitionistic_intuitionistically.
set gb := TExp (TInt 0) b.
set gab := TExp ga b.
pose si := SessInfo skI skR ga gb gab.
rewrite big_sepS_singleton.
iDestruct (release_tokenI with "token") as "[token_rel token]" => //.
rewrite (term_token_difference gb (↑iso_dhN.@"failed")); last by solve_ndisj.
iDestruct "token" as "[token_failed token]".
iPoseProof (term_token_difference gb (↑iso_dhN.@"res") with "token")
  as "[res_token token]"; first by solve_ndisj.
iMod ("res" $! b with "res_token") as "[resI resR]".
iMod (iso_dh_ready_alloc N skI skR si with "[//] resI") as "#ready".
iAssert (public gb) as "#p_gb".
{ iApply public_TExp_iff; eauto.
  rewrite minted_TInt. iRight. do ![iSplit => //].
  iApply "dh_gb". iPureIntro. by rewrite exps_TExpN. }
wp_pure _ credit:"H1".
wp_pure _ credit:"H2".
wp_apply wp_mk_keyshare => //.
iIntros "_". wp_pures. wp_list. wp_term_of_list.
wp_apply wp_sign; eauto.
{ rewrite public_of_list /=. do !iSplit => //.
  - by rewrite public_verify_key.
  - by rewrite public_Tag. }
{ iRight. iModIntro.
  iExists ga, b, _, N. do ![iSplitR => //].
  case: failed; eauto.
  rewrite bi.False_or. by eauto. }
iIntros "%m2 #?". wp_pures. wp_apply wp_send; eauto.
wp_pures. wp_apply wp_recv => //. iIntros "%m3 #p_m3".
wp_apply wp_verify; eauto. iSplit; last by protocol_failure.
iIntros "{p_m3} %m3' #p_m3 #inv_m3".
set pkI := Spec.pkey skI.
wp_pures. wp_list_of_term m3'; last by protocol_failure.
wp_list_match => [ga' gb' pkR' -> {m3}|]; last by protocol_failure.
wp_eq_term e; last by protocol_failure. subst ga'.
wp_eq_term e; last by protocol_failure. subst gb'.
wp_eq_term e; last by protocol_failure. subst pkR'.
rewrite public_of_list /=.
wp_pure _ credit:"H3".
wp_apply wp_texp.
wp_pure _ credit:"H4".
wp_pures. wp_list. wp_term_of_list.
wp_pures.
wp_apply wp_derive_senc_key. rewrite -/(released_session si).
iAssert (▷ (⌜failed⌝ ∨ released_session si) → public (si_key si))%I as "s_k1".
{ iIntros "#released".
  rewrite public_senc_key public_of_list /=.
  do !iSplit => //; try by iApply sign_key_public.
  - by iApply public_verify_key.
  - by iApply public_verify_key.
  - iApply public_TExp => //. by iApply "s_b". }
iAssert (|={⊤}=>
           □ (⌜failed⌝ → public (si_key si)) ∗
             ((public (si_init si) ∨ public (si_resp si)) ∨
              □ (public (si_key si) → ▷ released_session si)))%I
  with "[token_failed H4]" as "> (#comp & i_m3)".
{ case: failed.
  { iMod (term_meta_set (iso_dhN.@"failed") true with "token_failed")
      as "#?"; first by solve_ndisj.
    iAssert (public (si_key si)) as "#?".
    { iApply "s_k1". by eauto. }
    iModIntro. iSplit; first by eauto.
    by eauto. }
  iDestruct "inv_m3" as "[comp|#inv]".
  { iMod (term_meta_set (iso_dhN.@"failed") true with "token_failed")
      as "#?"; first by solve_ndisj.
    iModIntro. iSplit; first by iIntros "!> []".
    by eauto. }
  iDestruct "inv" as "(%a & %gb' & %skR' & %e_m3 & comp)".
  case/Spec.of_list_inj: e_m3
    => -> <- /Spec.sign_pkey_inj <- {ga gb' skR'}
    in gb gab si *.
  rewrite !TExp_TExpN TExpC2 in gab si *.
  iDestruct "comp" as "[comp|comp]".
  - iMod (term_meta_set (iso_dhN.@"failed") true with "token_failed")
      as "#?"; first by solve_ndisj.
    iModIntro. iSplit; first by iIntros "!> []".
    by eauto.
  - iMod (term_meta_set (iso_dhN.@"failed") false with "token_failed")
      as "#?"; first by solve_ndisj.
    iModIntro. iSplit; first by iIntros "!> []".
    by eauto. }
iAssert (minted (si_key si)) as "#m_kS".
{ rewrite minted_senc !minted_of_list /= !minted_TExp minted_TInt.
  do !iSplit => //; iApply public_minted => //.
  - by iApply public_verify_key.
  - by iApply public_verify_key. }
wp_pures. iApply ("Hpost" $! (Some (si_key si))).
iModIntro. iRight. iExists si. iFrame. do !iSplit => //.
- iIntros "!> #?". iApply "s_k1". by eauto.
- iApply (term_token_drop with "token"). solve_ndisj.
Qed.

Lemma wp_responder_confirm_weak c skR ga skI N :
  {{{ channel c ∗ cryptis_ctx ∗
      iso_dh_ctx ∗ iso_dh_pred N (λ _ _ _ _, True)%I ∗
      minted skR ∗ minted skI ∗
      public ga }}}
    responder_confirm c skR ga (Spec.pkey skI) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session_weak skI skR si ∗
        term_token (si_resp_share si) (⊤ ∖ ↑iso_dhN) }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & #? & #? & #m_skR & #m_skI & #p_ga) Hpost".
iApply wp_fupd. wp_apply (wp_responder_confirm false); first by eauto 10.
iIntros "%osi [->|Hsi]"; first by iApply ("Hpost" $! None); eauto.
iDestruct "Hsi" as "(%si & -> & #sess & #sec & rel & tok & _)".
iMod (unrelease Resp with "rel") as "#un". iModIntro.
iApply ("Hpost" $! (Some (si_key si))). iRight. iFrame. iSplit => //.
by iApply unreleased_session_weak.
Qed.

Lemma wp_responder c skR N :
  {{{ channel c ∗ cryptis_ctx ∗
      iso_dh_ctx ∗ iso_dh_pred N (λ _ _ _ _, True)%I ∗ minted skR }}}
    responder c skR (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI si,
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session skI skR si ∗
        release_token (si_resp_share si) ∗
        term_token (si_resp_share si) (⊤ ∖ ↑iso_dhN) }}}.
Proof.
iIntros "%Φ (#? & #? & #? & #? & #?) post".
wp_lam; wp_pures.
wp_apply wp_responder_listen; first by eauto.
iIntros "%ga %skI (#p_ga & #m_skI)".
wp_pures.
wp_apply (wp_responder_confirm false); first by eauto 10.
iIntros "%osi [->|Hosi]"; wp_pures; first by iApply ("post" $! None); eauto.
iDestruct "Hosi" as "(%si & -> & #? & #? & rel & token & _)".
wp_pures.
iModIntro. iApply ("post" $! (Some (Spec.pkey _, si_key si))).
iRight. iExists skI, si. by iFrame; eauto 10.
Qed.

Lemma wp_responder_weak c skR N :
  {{{ channel c ∗ cryptis_ctx ∗
      iso_dh_ctx ∗ iso_dh_pred N (λ _ _ _ _, True)%I ∗ minted skR }}}
    responder c skR (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI si,
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session_weak skI skR si ∗
        term_token (si_resp_share si) (⊤ ∖ ↑iso_dhN) }}}.
Proof.
iIntros "%Φ (#? & #? & #? & #?) post". iApply wp_fupd.
wp_apply wp_responder; first by eauto.
iIntros "%osi [->|Hosi]"; first by iApply ("post" $! None); eauto.
iDestruct "Hosi" as "(%skI & %si & -> & #? & rel & token)".
iMod (unrelease Resp with "rel") as "#un".
iModIntro. iApply ("post" $! (Some (Spec.pkey _, si_key si))).
iRight. iExists skI, si. iFrame. iSplit => //.
by iApply unreleased_session_weak.
Qed.

End Verif.
