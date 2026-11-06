From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.lib Require Import dh.
From cryptis.examples.iso_dh Require Import impl.
From cryptis.examples.iso_dh.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !iso_dhGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (rl : role) (t pkI pkR ga kS : term).
Implicit Types (skI skR : sign_key).
Implicit Types (si : sess_info) (osi : option sess_info).
Implicit Types (N : namespace) (data : term).
Implicit Types (ores : option (term * term)).
Implicit Types (φ : sess_info → role → iProp) (ρ : sess_info → iProp).

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

Lemma wp_responder_confirm c skI skR ga N φ ρ ψ :
  {{{ channel c ∗ cryptis_ctx ∗
      iso_dh_ctx ∗ iso_dh_pred N φ ρ ∗
      public ga ∗ minted skI ∗ minted skR ∗
      (∀ b : nonce,
          let si := SessInfo skI skR ga (TExp (TInt 0) b) (TExp ga b) in
          term_token (si_resp_share si) (⊤ ∖ ↑iso_dhN) ={⊤}=∗
          φ si Init ∗ ψ si) }}}
    responder_confirm c skR ga (Spec.pkey skI) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ b : nonce,
        let si := SessInfo skI skR ga (TExp (TInt 0) b) (TExp ga b) in
        ⌜r = Some (si_key si)⌝ ∗
        session ρ Resp si ∗ ψ si ∗
        (compromised Resp si ∨ φ si Resp) }}}.
Proof.
set pkR := Spec.pkey skR.
iIntros "%Φ (#chan_c & #? & (#? & #?) & #N_φ &
             #p_ga & #m_skI & #m_skR & hook) Hpost".
wp_lam. wp_pures. wp_apply wp_pkey. wp_pures.
wp_apply (wp_mk_nonce_freshN ∅
          (λ b, ρ (SessInfo skI skR ga (TExp (TInt 0) b) (TExp ga b)))
          dh_key_share
          (λ b, {[TExp (TInt 0) b]}))
       => //.
- by iIntros "% %contra".
- iIntros "%b".
  rewrite big_sepS_singleton minted_TExp //.
  rewrite minted_TInt /= bi.True_and.
  iModIntro. by iApply bi.equiv_iff.
iIntros "%b _ #m_b #s_b #dh_gb _ token".
have Nm_b : negb (is_mul (TNonce b)) by [].
(* [dh.v] takes the generator as a parameter; ISO-DH always uses [TInt 0]. *)
have NInt : negb (is_exp (TInt 0)) by [].
have NIntM : negb (is_gmul (TInt 0)) by [].
iAssert (public (TInt 0)) as "#p_g"; first by rewrite public_TInt.
set gb := TExp (TInt 0) b.
set gab := TExp ga b.
pose si := SessInfo skI skR ga gb gab.
rewrite big_sepS_singleton.
rewrite (term_token_difference gb (↑iso_dhN)) //.
iDestruct "token" as "[token_N token]".
iDestruct (term_token_difference gb (↑iso_dhN.@"compromised") with "token_N")
  as "[comp_token token_N]"; first solve_ndisj.
iDestruct (term_token_difference gb (↑iso_dhN.@"usage") with "token_N")
  as "[use_token token_N]"; first solve_ndisj.
iDestruct (term_token_difference gb (↑iso_dhN.@"ready") with "token_N")
  as "[ready_token _]"; first solve_ndisj.
iMod (term_meta_set (iso_dhN.@"usage") N with "use_token") as "#use";
  first done.
iMod ("hook" $! b with "token") as "[gift ψ]".
iMod (iso_dh_ready_alloc N si Init with "N_φ gift") as "#ready".
iAssert (public gb) as "#p_gb";
  first by iApply (public_dh_share NInt NIntM Nm_b).
wp_pure _ credit:"H1".
wp_pure _ credit:"H2".
wp_apply wp_mk_keyshare => //.
iIntros "_". wp_pures. wp_list. wp_term_of_list.
wp_apply wp_sign; eauto.
{ rewrite public_of_list /=. do !iSplit => //.
  - by rewrite public_verify_key.
  - by rewrite public_Tag. }
{ iRight. iModIntro.
  iExists ga, b, skI, N, φ, ρ. by do !iSplit. }
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
wp_apply wp_derive_senc_key.
iAssert (minted (si_key si)) as "#m_kS".
{ rewrite minted_senc minted_of_list /= !minted_pkey.
  do !iSplit => //; try by iApply public_minted.
  by iApply all_minted_TExp; iSplit; first iApply public_minted. }
iAssert (□ (▷ □ ρ si → public (si_key si)))%I as "#s_k1".
{ iIntros "!> #r".
  rewrite public_senc_key public_of_list /=.
  do !iSplit => //; try by iApply sign_key_public.
  - by iApply public_verify_key.
  - by iApply public_verify_key.
  - iApply public_TExp => //. by iApply "s_b". }
(* A valid signature on [m3] was either forged, or produced by the honest
   initiator, which may still have given up on the session. *)
iAssert (|={⊤}=>
           session ρ Resp si ∗ (compromised Resp si ∨ φ si Resp))%I
  with "[comp_token ready_token H4]" as "> (#sess & res)".
{ iDestruct "inv_m3" as "[#comp|#inv]".
  - iMod (term_meta_set (iso_dhN.@"compromised") true with "comp_token")
      as "#c"; first solve_ndisj.
    iModIntro. iSplit; last by iLeft.
    iSplit; first done. iSplit; first done.
    iLeft. iSplit; first done. by iSplit; first iLeft.
  - iDestruct "inv" as "(%a & %gb' & %skR' & %e_m3 & #comp)".
    case/Spec.of_list_inj: e_m3
      => -> <- /Spec.sign_pkey_inj <- {ga gb' skR'}
      in gb gab si *.
    rewrite TExpC in gab si *.
    iDestruct "comp"
      as "[#comp|(%N' & %φ' & %ρ' & #use' & #N_φ' & #ok & #ready_R)]".
    + iMod (term_meta_set (iso_dhN.@"compromised") true with "comp_token")
        as "#c"; first solve_ndisj.
      iModIntro. iSplit; last by iLeft.
      iSplit; first done. iSplit; first done.
      iLeft. iSplit; first done. by iSplit.
    + iPoseProof (term_meta_agree with "use use'") as "%e".
      subst N'.
      iDestruct (iso_dh_pred_agree with "N_φ N_φ'") as "[_ #ρ_eq]".
      iSpecialize ("ρ_eq" $! si).
      iMod (term_meta_set (iso_dhN.@"compromised") false with "comp_token")
        as "#nc"; first solve_ndisj.
      iMod ("ready_R" with "N_φ ready_token") as "res".
      iMod (lc_fupd_elim_later with "H4 res") as "res".
      iModIntro. iSplit; last by iRight.
      iSplit; first done. iSplit; first done.
      iRight. iSplit.
      * iIntros "!> #c". by iDestruct (term_meta_agree with "c nc") as %?.
      * iIntros "!> #p_k". iDestruct ("ok" with "p_k") as "#r". iNext.
        by iRewrite "ρ_eq". }
wp_pures. iApply ("Hpost" $! (Some (si_key si))).
iModIntro. iRight. iExists b. iFrame. by iSplit.
Qed.

Lemma wp_responder c skR N φ ρ ψ :
  {{{ channel c ∗ cryptis_ctx ∗
      iso_dh_ctx ∗ iso_dh_pred N φ ρ ∗ minted skR ∗
      (∀ skI ga (b : nonce),
          let si := SessInfo skI skR ga (TExp (TInt 0) b) (TExp ga b) in
          term_token (si_resp_share si) (⊤ ∖ ↑iso_dhN) ={⊤}=∗
          φ si Init ∗ ψ si) }}}
    responder c skR (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI ga (b : nonce),
        let si := SessInfo skI skR ga (TExp (TInt 0) b) (TExp ga b) in
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session ρ Resp si ∗ ψ si ∗
        (compromised Resp si ∨ φ si Resp) }}}.
Proof.
iIntros "%Φ (#? & #? & #? & #? & #? & hook) post".
wp_lam; wp_pures.
wp_apply wp_responder_listen; first by eauto.
iIntros "%ga %skI (#p_ga & #m_skI)".
wp_pures.
wp_apply (wp_responder_confirm _ _ _ _ _ _ _ ψ with "[hook]").
{ iFrame "#". iIntros "%b". iApply "hook". }
iIntros "%osi [->|Hosi]"; wp_pures; first by iApply ("post" $! None); eauto.
iDestruct "Hosi" as "(%b & -> & #sess & ψ & res)".
set si := SessInfo skI skR ga (TExp (TInt 0) b) (TExp ga b).
wp_pures.
iModIntro. iApply ("post" $! (Some (Spec.pkey skI, si_key si))).
iRight. iExists skI, ga, b. iFrame. by iSplit.
Qed.

End Verif.
