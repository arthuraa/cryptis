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

Lemma wp_resp failed c skR N φ :
  {{{ channel c ∗ cryptis_ctx ∗
      nsl_dh_ctx ∗ nsl_dh_pred N φ ∗
      minted skR ∗
      (∀ skI ga b,
          let gb := TExp (TInt 0) b in
          let gab := TExp ga b in
          let si := SessInfo skI skR ga gb gab in
          term_token (si_resp_share si) (↑nsl_dhN.@"res") ={⊤}=∗
           φ (si_init si) (si_resp si) si Init ∗
           φ (si_init si) (si_resp si) si Resp) ∗
      if failed then public skR else True }}}
    resp c skR (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI si,
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session skI skR si ∗
        □ (⌜failed⌝ → public (si_key si)) ∗
        release_token (si_resp_share si) ∗
        term_token (si_resp_share si) (⊤ ∖ ↑nsl_dhN) ∗
        φ skI skR si Resp }}}.
Proof.
set pkR := Spec.pkey skR.
iIntros "%Φ (#chan_c & #? & (#? & #? & #?) & #N_φ &
             #m_skR & res & #failed) Hpost".
wp_lam. wp_pures. wp_apply wp_pkey. wp_pures. rewrite -/pkR.
(* Receive and decrypt msg1 *)
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#p_m1".
wp_apply wp_adec => //. iSplit; last protocol_failure.
iClear "p_m1" => {m1}. iIntros "%m1 #m_m1 #inv_m1".
wp_list_of_term m1; last protocol_failure.
wp_list_match => [ga nI pkI {m1} ->|]; last protocol_failure.
rewrite minted_of_list /= public_of_list /=.
iDestruct "m_m1" as "(#m_ga & #m_nI & #m_pkI & _)".
wp_apply wp_is_aenc_key => //. iSplit; last protocol_failure.
iIntros "%skI -> #m_skI {m_pkI}". wp_pures.
(* Extract nI secrecy *)
iAssert (▷ (public skI ∨ public skR) → public nI)%I as "#s_nI".
{ iDestruct "inv_m1" as "[(? & ? & _)|[#inv_m1 _]]"; eauto.
  iIntros "#fail".
  iDestruct "inv_m1" as "(%ga' & %nI' & %skI' & %e & s_nI)".
  case/Spec.of_list_inj: e => <- <- /Spec.aenc_pkey_inj <-.
  by iApply "s_nI". }
iAssert (public ga) as "#p_ga".
{ iDestruct "inv_m1" as "[(? & _)|[_ #?]]"; eauto. }
(* Create DH share b *)
wp_apply (wp_mk_nonce_freshN ∅
          (λ b, ⌜failed⌝ ∨ released ga ∧ released (TExp (TInt 0) b))%I
          nsl_dh_key_share
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
rewrite (term_token_difference gb (↑nsl_dhN.@"failed")); last by solve_ndisj.
iDestruct "token" as "[token_failed token]".
iPoseProof (term_token_difference gb (↑nsl_dhN.@"res") with "token")
  as "[res_token token]"; first by solve_ndisj.
iMod ("res" $! skI ga b with "res_token") as "[resI resR]".
iMod (nsl_dh_ready_alloc N skI skR si with "[//] resI") as "#ready".
iAssert (public gb) as "#p_gb".
{ iApply public_TExp_iff; eauto.
  rewrite minted_TInt. iRight. do ![iSplit => //].
  iApply "dh_gb". iPureIntro. by rewrite exps_TExpN. }
(* Create confirmation nonce nR *)
wp_pure _ credit:"H1".
wp_pure _ credit:"H2".
wp_apply wp_mk_keyshare => //. iIntros "_". wp_pures.
wp_apply (wp_mk_nonce (λ _, public skI ∨ public skR)%I (λ _, False)%I) => //.
iIntros "%nR _ #m_nR #s_nR _ _".
rewrite bi.intuitionistic_intuitionistically.
(* Encrypt and send msg2 *)
wp_pures. wp_list. wp_term_of_list.
wp_apply wp_aenc; eauto.
{ rewrite minted_of_list /= minted_pkey. by do !iSplit => //. }
{ iRight. iSplit.
  + iModIntro. iExists ga, b, nI, nR, skR, N. iSplit => //.
    do !iSplit => //.
    case: failed; eauto.
    rewrite bi.False_or. by eauto.
  + iIntros "!> #p_skI". rewrite public_of_list /=.
    do !iSplit => //; first by iApply public_aenc_key.
    - iApply "s_nI". by eauto.
    - iApply "s_nR". by eauto. }
iIntros "%m2 #?". wp_pures. wp_apply wp_send; eauto.
(* Receive and decrypt msg3 *)
wp_pures. wp_apply wp_recv => //. iIntros "%m3 #p_m3".
wp_apply wp_adec => //. iSplit; last by protocol_failure.
iClear "p_m3" => {m3}. iIntros "%m3 #m_m3 #inv_m3".
wp_list_of_term m3; last by protocol_failure.
wp_list_match => [ga' gb' pkI' nR' -> {m3}|]; last by protocol_failure.
wp_eq_term e; last by protocol_failure. subst ga'.
wp_eq_term e; last by protocol_failure. subst gb'.
wp_eq_term e; last by protocol_failure. subst pkI'.
wp_eq_term e; last by protocol_failure. subst nR'.
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
  do !iSplit => //; try by iApply public_aenc_key.
  iApply public_TExp => //. by iApply "s_b". }
iAssert (|={⊤}=>
           □ (⌜failed⌝ → public (si_key si)) ∗
             ((public (si_init si) ∨ public (si_resp si)) ∨
              □ (public (si_key si) → ▷ released_session si)))%I
  with "[token_failed H3]" as "> (#comp & i_m3)".
{ case: failed.
  { iMod (term_meta_set (nsl_dhN.@"failed") true with "token_failed")
      as "#?"; first by solve_ndisj.
    iAssert (public (si_key si)) as "#?".
    { iApply "s_k1". by eauto. }
    iModIntro. iSplit; first by eauto.
    by eauto. }
  iDestruct "inv_m3" as "[(p_ga' & p_gb' & p_pkI & p_nR & _)|[#inv #p_inv]]".
  { (* Forge case: public nR → corruption *)
    iMod (lc_fupd_elim_later_pers with "H3 [p_nR]") as "#corr".
    { iApply "s_nR". eauto. }
    iMod (term_meta_set (nsl_dhN.@"failed") true with "token_failed")
      as "#?"; first by solve_ndisj.
    iModIntro. iSplit; first by iIntros "!> []".
    by eauto. }
  iDestruct "inv" as "(%a & %gb' & %nR' & %skI' & %e_m3 & s_k2)".
  case/Spec.of_list_inj: e_m3
    => -> <- /Spec.aenc_pkey_inj <- <- {ga gb' pkI' nR' skI'}
    in gb gab si *.
  rewrite !TExp_TExpN TExpC2 in gab si *.
  iDestruct "s_k2" as "[corr|#s_k2]".
  - iMod (term_meta_set (nsl_dhN.@"failed") true with "token_failed")
      as "#?"; first by solve_ndisj.
    iModIntro. iSplit; first by iIntros "!> []".
    by eauto.
  - iMod (term_meta_set (nsl_dhN.@"failed") false with "token_failed")
      as "#?"; first by solve_ndisj.
    iModIntro. iSplit; first by iIntros "!> []".
    by eauto. }
iAssert (minted (si_key si)) as "#m_kS".
{ rewrite minted_senc !minted_of_list /= !minted_TExp minted_TInt.
  do !iSplit => //; iApply public_minted => //.
  - by iApply public_aenc_key.
  - by iApply public_aenc_key. }
wp_pures. iApply ("Hpost" $! (Some (Spec.pkey skI, si_key si))).
iModIntro. iRight. iExists skI, si. iFrame. do !iSplit => //.
- iIntros "!> #?". iApply "s_k1". by eauto.
- iApply (term_token_drop with "token"). solve_ndisj.
Qed.

Lemma wp_resp_simple c skR N :
  {{{ channel c ∗ cryptis_ctx ∗
      nsl_dh_ctx ∗ nsl_dh_pred N (λ _ _ _ _, True)%I ∗ minted skR }}}
    resp c skR (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI si,
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session skI skR si ∗
        release_token (si_resp_share si) ∗
        term_token (si_resp_share si) (⊤ ∖ ↑nsl_dhN) }}}.
Proof.
iIntros "%Φ (#chan_c & #? & #? & #? & #?) Hpost".
wp_apply (wp_resp false); first by eauto 10.
iIntros "%osi [->|Hosi]"; first by iApply ("Hpost" $! None); eauto.
iDestruct "Hosi" as "(%skI & %si & -> & #? & #? & rel & token & _)".
iApply ("Hpost" $! (Some (Spec.pkey _, si_key si))).
iRight. iExists skI, si. by iFrame; eauto 10.
Qed.

Lemma wp_resp_weak c skR N :
  channel c ∗ cryptis_ctx ∗ nsl_dh_ctx ∗
  nsl_dh_pred N (λ _ _ _ _, True)%I ∗ minted skR -∗
  {{{ True }}}
    resp c skR (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI si,
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session_weak skI skR si ∗
        term_token (si_resp_share si) (⊤ ∖ ↑nsl_dhN) }}}.
Proof.
iIntros "(#? & #? & #? & #? & #?) !> %Φ _ post". iApply wp_fupd.
wp_apply (wp_resp false); first by eauto 10.
iIntros "%osi [->|Hosi]"; first by iApply ("post" $! None); eauto.
iDestruct "Hosi" as "(%skI & %si & -> & #? & #? & rel & token & _)".
iMod (unrelease Resp with "rel") as "#un".
iModIntro. iApply ("post" $! (Some (Spec.pkey _, si_key si))).
iRight. iExists skI, si. iFrame. iSplit => //.
by iApply unreleased_session_weak.
Qed.

End Verif.
