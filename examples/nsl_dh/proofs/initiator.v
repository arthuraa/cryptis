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
Proof.
move=> ga.
iIntros "%Ψ (#chan_c & #ctx & #(m1_pred & m2_pred & ?)) Hpost".
rewrite /initiator_recv_msg2.
wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m) "#p_m".
wp_apply wp_adec => //. iSplit; last by protocol_failure.
iClear "p_m" => {m}. iIntros "%m2 #m_m2 #inv_m2".
wp_list_of_term m2; last by protocol_failure.
wp_list_match => [ga' gb pkR' N' {m2} ->|_]; last by protocol_failure.
wp_eq_term e; last by protocol_failure. subst ga'.
wp_eq_term e; last by protocol_failure. subst pkR'.
wp_eq_term e; last by protocol_failure. subst N'.
wp_pures.
iApply ("Hpost" $! (Some gb)). iRight. iExists gb.
iModIntro. iSplit => //.
iDestruct "inv_m2" as "[#p_m2|[#inv_m2 _]]".
- (* public plaintext *)
  iLeft. rewrite public_of_list /=.
  iDestruct "p_m2" as "(#p_ga & #p_gb & _)".
  by iSplit.
- (* msg2_pred *)
  iDestruct "inv_m2" as
    "(%ga0 & %gb0 & %skR0 & %N0 & %e_m2 & inv_m2)".
  case/Spec.of_list_inj: e_m2
      => <- <- /Spec.aenc_pkey_inj <- /Tag_inj <-.
  by iRight.
Qed.

Lemma initiator_process_msg2 skI skR a gb N φ failed :
  let ga := TExp (TInt 0) a in
  let gab := TExp gb a in
  let si := SessInfo skI skR ga gb gab in
  £ 1 -∗
  nsl_dh_pred N φ -∗
  minted skI -∗
  minted skR -∗
  dh_key skI skR a -∗
  peer_share_token ga -∗
  ready_token ga -∗
  failed_early skI skR failed -∗
  (public ga ∧ public gb ∨ msg2_pred' skI skR ga gb N) ={⊤}=∗
  session skI skR si ∗
  □ (⌜failed⌝ → public (si_key si)) ∗
  (public (si_key si) ∨ φ skI skR si Init).
Proof.
move=> ga gab si.
iIntros "Hc1 #N_φ #m_skI #m_skR #dh_a ptok rtok failed_e inv".
iDestruct "dh_a" as "(#m_a & #s_a & #pred_a)".
iDestruct "inv" as "[#pub|inv_m2]".
- (* Case 1: public plaintext — attacker forged message *)
  iDestruct "pub" as "(#p_ga & #p_gb)".
  rewrite public_TExp_iff; first last. { by case. }
  iDestruct "p_ga" as "[[_ #p_a]|(_ & _ & #dp_a)]".
  + (* Sub-case: public a — contradiction with peer_share_token *)
    iDestruct ("s_a" with "p_a") as "#later_ns".
    iMod (lc_fupd_elim_later_pers with "Hc1 later_ns") as "#ns".
    iExFalso.
    iDestruct "ns" as "[#ps_none|(%gb' & #ps_some & _)]".
    * by iApply (term_meta_token with "ptok ps_none").
    * by iApply (term_meta_token with "ptok ps_some").
  + (* Sub-case: dh_pred a ga — derive corruption *)
    iPoseProof ("pred_a" $! ga with "dp_a") as "#later_ks".
    iMod (lc_fupd_elim_later_pers with "Hc1 later_ks") as "#[#corr _]".
    iMod (set_peer_share ga None with "ptok") as "#ps_none".
    iAssert (public a) as "#p_a".
    { iApply "s_a". iNext. iModIntro. iLeft. done. }
    iAssert (minted gb) as "#m_gb". { by iApply public_minted. }
    iAssert (minted (si_key si)) as "#m_k".
    { rewrite minted_senc minted_of_list /= !minted_pkey !minted_TExp minted_TInt /=.
      by do !iSplit. }
    iAssert (public (si_key si)) as "#p_k".
    { rewrite public_senc_key public_of_list /=.
      iSplit; [by iApply public_aenc_key|].
      iSplit; [by iApply public_aenc_key|].
      iSplit; [iApply public_TExp; [by rewrite public_TInt|done]|].
      iSplit; [done|].
      iSplit; [|done].
      iApply public_TExp => //. }
    iModIntro. do !iSplit => //.
    * iIntros "!> _". done.
    * by iLeft.
    * by iIntros "!> _".
    * by iLeft.
- (* Case 2: msg2_pred — proper invariant *)
  iDestruct "inv_m2" as "(%b & %e_gb & #dh_b & #ps_gb & ready)".
  subst gb.
  iDestruct "dh_b" as "(#m_b & #s_b & #pred_b)".
  set gb := TExp (TInt 0) b.
  case: failed.
  + (* failed = true: corruption *)
    rewrite /=. iDestruct "failed_e" as "#corr".
    iMod (set_peer_share ga None with "ptok") as "#ps_none".
    iAssert (public a) as "#p_a".
    { iApply "s_a". iNext. iModIntro. iLeft. done. }
    iAssert (public gb) as "#p_gb".
    { iApply (public_dh_share with "[#]").
      { do !iSplit; eauto. }
      by iModIntro. }
    iAssert (minted (si_key si)) as "#m_k".
    { rewrite minted_senc minted_of_list /= !minted_pkey !minted_TExp minted_TInt /=.
      by do !iSplit. }
    iAssert (public (si_key si)) as "#p_k".
    { rewrite public_senc_key public_of_list /=.
      iSplit; [by iApply public_aenc_key|].
      iSplit; [by iApply public_aenc_key|].
      iSplit; [iApply public_TExp; [by rewrite public_TInt|done]|].
      iSplit; [done|].
      iSplit; [|done].
      by iApply (public_TExp with "p_gb p_a"). }
    iModIntro. do !iSplit => //.
    * iIntros "!> _". done.
    * by iLeft.
    * by iIntros "!> _".
    * by iLeft.
  + (* failed = false: honest case *)
    iClear "failed_e".
    iMod (set_peer_share ga (Some gb) with "ptok") as "#ps_ga".
    iPoseProof (dh_key_public_released skI skR a gb
                 with "[#] ps_ga") as "#rel_a".
    { do !iSplit; eauto. }
    iPoseProof (dh_key_public_released skI skR b ga
                 with "[#] ps_gb") as "#rel_b".
    { do !iSplit; eauto. }
    iAssert (minted (si_key si)) as "#m_k".
    { rewrite minted_senc minted_of_list /= !minted_pkey !minted_TExp minted_TInt /=.
      by do !iSplit. }
    (* Get φ from nsl_dh_ready *)
    iMod ("ready" $! φ with "N_φ rtok") as "later_φ".
    iMod (lc_fupd_elim_later with "Hc1 later_φ") as "φ_res".
    iModIntro. iSplit.
    { (* session *)
      do !iSplit => //.
      - (* released → public *)
        iIntros "!> #[#rel_ga #rel_gb]".
        iAssert (public a) as "#p_a".
        { iApply "rel_a". iNext. by iSplit. }
        iAssert (public b) as "#p_b".
        { iApply "rel_b". iNext. by iSplit. }
        rewrite public_senc_key public_of_list /=.
        iSplit; [by iApply public_aenc_key|].
        iSplit; [by iApply public_aenc_key|].
        iSplit; [iApply public_TExp; [by rewrite public_TInt|done]|].
        iSplit; [iApply public_TExp; [by rewrite public_TInt|done]|].
        iSplit; [|done].
        iApply public_TExp.
        + iApply public_TExp; [by rewrite public_TInt|done].
        + done.
      - (* public → released OR corruption *)
        iRight. iIntros "!> #p_k".
        rewrite public_senc_key public_of_list /=.
        iDestruct "p_k" as "(_ & _ & _ & _ & #p_gab & _)".
        have e_gab : gab = TExpN (TInt 0) [a; b] by rewrite /gab /gb TExp_TExpN.
        rewrite e_gab public_TExp2_iff; first last. { by case. }
        iDestruct "p_gab" as "[[_ #p_b]|[[_ #p_a]|(_ & #dpa & _)]]".
        + iDestruct ("rel_b" with "p_b") as ">[#? #?]". by iSplit.
        + iDestruct ("rel_a" with "p_a") as ">[#? #?]". by iSplit.
        + iPoseProof ("pred_a" $! (TExpN (TInt 0) [a; b]) with "dpa")
            as "#contra".
          iAssert (▷ False)%I as ">[]".
          { iModIntro. iDestruct "contra" as "[_ %contra]".
            by rewrite /nsl_dh_key_share exps_TExpN /= in contra. } }
    iSplit.
    { by iIntros "!> []". }
    iRight.
    have -> : si = SessInfo skI skR ga gb (TExp ga b).
    { by rewrite /si /gab /ga /gb !TExp_TExpN TExpC2. }
    iExact "φ_res".
Qed.

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
