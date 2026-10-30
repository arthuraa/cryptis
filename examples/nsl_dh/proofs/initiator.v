From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.lib Require Import dh.
From cryptis.examples.nsl_dh Require Import impl.
From cryptis.examples.nsl_dh.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !nsl_dhGS Σ}.
Abbreviation iProp := (iProp Σ).

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
  {{{ (a : nonce), RET (TNonce a, TExp (TInt 0) a);
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
wp_apply (wp_mk_dh_keys ∅ skI skR); first by iFrame "#".
{ iIntros "%t". rewrite elem_of_empty. by iIntros "[]". }
iIntros "%a _ #dh_a rel peer ready res tok".
set ga := TExp (TInt 0) a.
wp_pures. wp_list. wp_term_of_list. wp_pures.
wp_apply wp_aenc => //.
{ iDestruct "dh_a" as "(#m_a & _)".
  rewrite minted_of_list /= minted_TExp //.
  rewrite minted_TInt /= minted_pkey.
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

Lemma initiator_process_msg2 skI skR (a : nonce) gb N φ failed :
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
  minted gb ∗
  (public gb ∨ □ msg3_pred skR gb ∧ □ (public skR → public gb)) ∗
  (public (si_key si) ∨ φ skI skR si Init).
Proof.
move=> ga gab si.
iIntros "Hc1 #N_φ #m_skI #m_skR #dh_a ptok rtok failed_e inv".
iDestruct "dh_a" as "(#m_a & #s_a & #pred_a)".
have Nm_a : negb (is_mul a) by [].
iDestruct "inv" as "[#pub|inv_m2]".
- (* Case 1: public plaintext — attacker forged message *)
  iDestruct "pub" as "(#p_ga & #p_gb)".
  iPoseProof (public_exp_inv_same (t1 := a) with "p_ga") as "exp_a_inv";
    first by rewrite (exps_TExp1 Nm_a) /SMS.pos SMS.car_singleton;
             set_solver.
  iDestruct "exp_a_inv" as "[#p_a | (%t3 & %base_t3 & %t3_sub & #base_a)]".
  + (* Sub-case: public a — contradiction with peer_share_token *)
    iDestruct ("s_a" with "p_a") as "#later_ns".
    iMod (lc_fupd_elim_later_pers with "Hc1 later_ns") as "#ns".
    iExFalso.
    iDestruct "ns" as "[#ps_none|(%gb' & #ps_some & _)]".
    * by iApply (term_meta_token with "ptok ps_none").
    * by iApply (term_meta_token with "ptok ps_some").
  + (* Sub-case: exp_pred a t3 — derive corruption *)
    iPoseProof ("pred_a" $! t3 with "base_a") as "#later_ks".
    iMod (lc_fupd_elim_later_pers with "Hc1 later_ks") as "#[#corr _]".
    iMod (set_peer_share ga None with "ptok") as "#ps_none".
    iAssert (public a) as "#p_a".
    { iApply "s_a". iNext. iModIntro. iLeft. done. }
    iAssert (minted gb) as "#m_gb". { by iApply public_minted. }
    iAssert (minted (si_key si)) as "#m_k".
    { rewrite minted_senc minted_of_list /= !minted_pkey.
      do !iSplit => //.
      - by iApply all_minted_TExp; rewrite minted_TInt; iSplit.
      - by iApply all_minted_TExp; iSplit. }
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
    * by iLeft.
- (* Case 2: msg2_pred — proper invariant *)
  iDestruct "inv_m2" as "(%b & %e_gb & %b_ga & #dh_b & #ps_gb & ready)".
  subst gb.
  iDestruct "dh_b" as "(#m_b & #s_b & #pred_b)".
  have Nm_b : negb (is_mul b) by [].
  have Nm_b' : Is_true (negb (is_mul b)) := Nm_b.
  set gb := TExp (TInt 0) b.
  have b_a : TNonce b ≠ TNonce a.
  { move=> e. apply: b_ga. rewrite /ga -e.
    apply: (@STExp2 _ _ (TNonce b)) => //.
    by rewrite (elem_of_factors_Nmul _ Nm_b). }
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
    iAssert (minted gb) as "#m_gb". { by iApply public_minted. }
    iAssert (minted (si_key si)) as "#m_k".
    { rewrite minted_senc minted_of_list /= !minted_pkey.
      do !iSplit => //.
      - by iApply all_minted_TExp; rewrite minted_TInt; iSplit.
      - by iApply all_minted_TExp; iSplit. }
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
    iAssert (minted gb) as "#m_gb".
    { rewrite minted_TExp //.
      rewrite minted_TInt /=. by iSplit. }
    iAssert (minted (si_key si)) as "#m_k".
    { rewrite minted_senc minted_of_list /= !minted_pkey.
      do !iSplit => //.
      - by iApply all_minted_TExp; rewrite minted_TInt; iSplit.
      - by iApply all_minted_TExp; iSplit. }
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
        have e_gab : gab = TExp (TInt 0) (TMul {[+ TNonce a; TNonce b +]}).
          by rewrite /gab /gb TExpC TExpA.
        rewrite e_gab.
        have exps_share :
            SMS.pos (exps (TExp (TInt 0) (TMul {[+ TNonce a; TNonce b +]})))
            ≡ₚ [TNonce a; TNonce b].
        { by rewrite (exps_TExp2 Nm_a Nm_b) SMS.pos_make_nil_r. }
        iPoseProof (public_exp_inv (t1 := a) with "p_gab")
          as "(%t & %t_in & H)";
          first by rewrite exps_share; set_solver.
        rewrite exps_share elem_of_cons list_elem_of_singleton in t_in.
        iDestruct "H" as "[#p_t|(%t3 & %base_t3 & %exps_sub & #base_t)]".
        { case: t_in => ->.
          - iDestruct ("rel_a" with "p_t") as ">[#? #?]". by iSplit.
          - iDestruct ("rel_b" with "p_t") as ">[#? #?]". by iSplit. }
        rewrite exps_share in exps_sub.
        iAssert (▷ □ nsl_dh_key_share skI skR t3)%I as "#ks".
        { case: t_in => ->; [by iApply "pred_a" | by iApply "pred_b"]. }
        iAssert (▷ False)%I as ">[]".
        { iModIntro. iDestruct "ks" as "[_ %contra]". iPureIntro.
          move: contra exps_sub.
          rewrite SMS.elements_pos_neg /SMS.pos /SMS.neg length_app.
          case: (SMS.car (exps t3)) => [[|c [|??]] ns] /= len sub; try lia.
          - by have := sub (TNonce a); set_solver.
          - have [a_c b_c] : TNonce a ∈ [c] ∧ TNonce b ∈ [c] by set_solver.
            rewrite !list_elem_of_singleton in a_c b_c. congruence. } }
    iSplit.
    { by iIntros "!> []". }
    iSplit; first done.
    iSplit.
    { (* msg3_pred ∧ public skR → public gb *)
      iRight. iSplit.
      - (* □ msg3_pred skR gb *)
        iIntros "!> %ga' %b' %e_gb' #ps_gb'".
        iPoseProof (has_peer_share_agree with "ps_gb ps_gb'") as "%e".
        case: e => e_ga. subst ga'.
        have Nm_bp : negb (is_mul (TNonce b')) by [].
        have e_b : b = b'.
        { rewrite /gb in e_gb'.
          have NmInt : negb (is_gmul (TInt 0)) by [].
    have e := TExp_injr _ _ _ NmInt e_gb'. congruence. }
        subst b'.
        iSplitR "".
        + (* ▷ (released ga ∧ released gb) → public ga *)
          iIntros "#[#r_ga #r_gb]".
          iApply public_TExp. { by rewrite public_TInt. }
          iApply "rel_a". iNext. by iSplit.
        + (* public (TExp ga b) ↔ ▷ (released ga ∧ released gb) *)
          iSplit.
          * iIntros "#p_gab".
            have e_gab :
              TExp ga b = TExp (TInt 0) (TMul {[+ TNonce a; TNonce b +]}).
            { by rewrite /ga TExpA. }
            rewrite e_gab.
            have exps_share :
                SMS.pos
                  (exps (TExp (TInt 0) (TMul {[+ TNonce a; TNonce b +]})))
                ≡ₚ [TNonce a; TNonce b].
            { by rewrite (exps_TExp2 Nm_a Nm_b) SMS.pos_make_nil_r. }
            iPoseProof (public_exp_inv (t1 := a) with "p_gab")
              as "(%t & %t_in & H)";
              first by rewrite exps_share; set_solver.
            rewrite exps_share elem_of_cons list_elem_of_singleton in t_in.
            iDestruct "H" as "[#p_t|(%t3 & %base_t3 & %exps_sub & #base_t)]".
            { case: t_in => ->.
              - iDestruct ("rel_a" with "p_t") as ">[#? #?]". by iSplit.
              - iDestruct ("rel_b" with "p_t") as ">[#? #?]". by iSplit. }
            rewrite exps_share in exps_sub.
            iAssert (▷ □ nsl_dh_key_share skI skR t3)%I as "#ks".
            { case: t_in => ->; [by iApply "pred_a" | by iApply "pred_b"]. }
            iAssert (▷ False)%I as ">[]".
            { iModIntro. iDestruct "ks" as "[_ %contra]". iPureIntro.
              move: contra exps_sub.
              rewrite SMS.elements_pos_neg /SMS.pos /SMS.neg.
              rewrite length_app.
              case: (SMS.car (exps t3)) => [[|c [|??]] ns] /= len sub;
                try lia.
              - by have := sub (TNonce a); set_solver.
              - have [a_c b_c] : TNonce a ∈ [c] ∧ TNonce b ∈ [c] by set_solver.
                rewrite !list_elem_of_singleton in a_c b_c. congruence. }
          * iIntros "#[#r_ga #r_gb]".
            iAssert (public a) as "#p_a". { iApply "rel_a". iNext. by iSplit. }
            iAssert (public b) as "#p_b". { iApply "rel_b". iNext. by iSplit. }
            iApply public_TExp.
            { iApply public_TExp. { by rewrite public_TInt. } done. }
            done.
      - (* □ (public skR → public gb) *)
        iIntros "!> #p_skR".
        iApply (public_dh_share with "[#]").
        { do !iSplit; eauto. }
        iModIntro. by iRight. }
    iRight.
    have -> : si = SessInfo skI skR ga gb (TExp ga b).
    { by rewrite /si /gab /ga /gb TExpC. }
    iExact "φ_res".
Qed.

Lemma wp_initiator_send_msg3 c skI skR a gb :
  let ga := TExp (TInt 0) a in
  let si := SessInfo skI skR ga gb (TExp gb a) in
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    minted skR ∗
    minted gb ∗
    (public gb ∨ □ msg3_pred skR gb ∧ □ (public skR → public gb))
  }}}
    initiator_send_msg3 c skI (Spec.pkey skR) a ga gb
  {{{ RET (repr (si_key si)); True }}}.
Proof.
move=> ga si.
iIntros "%Ψ (#chan & #ctx & #(m1_pred & m2_pred & m3_pred) &
         #m_skR & #m_gb & #inv_m3) Hpost".
rewrite /initiator_send_msg3. wp_pures.
wp_apply wp_pkey. wp_pures.
wp_bind (texp _ _). iApply wp_texp. wp_pures.
wp_list. wp_term_of_list. wp_pures.
wp_apply wp_aenc => //.
iIntros "%m3 #p_m3". wp_pures.
wp_apply wp_send => //. wp_pures.
iApply wp_derive_senc_key. iNext.
by iApply "Hpost".
Qed.

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
Proof.
iIntros "%Ψ (#chan & #ctx & #(m1_pred & m2_pred & m3_pred) & #N_φ &
         #m_skI & #m_skR & failed_e) Hpost".
rewrite /initiator. wp_pures.
(* Step 1: Send msg1 *)
wp_apply wp_initiator_send_msg1.
{ by iFrame "#". }
iIntros "%a (#dh_a & rel & ptok & rtok & tok)".
set ga := TExp (TInt 0) a.
wp_pures.
(* Step 2: Recv msg2 *)
wp_bind (initiator_recv_msg2 _ _ _ _ _ _).
wp_apply wp_initiator_recv_msg2.
{ by iFrame "#". }
iIntros "%r [->|(%gb & -> & inv)]".
- (* None case *)
  wp_pures. iApply ("Hpost" $! None). by iLeft.
- (* Some gb case *)
  wp_pure _ credit:"Hc1". wp_pures.
  set si := SessInfo skI skR ga gb (TExp gb a).
  iMod (initiator_process_msg2 skI skR a gb N φ failed
          with "Hc1 N_φ m_skI m_skR dh_a ptok rtok failed_e inv")
    as "(#sess & #failed_p & #m_gb & #inv_m3 & p_k_or_φ)".
  (* Step 3: Send msg3 *)
  wp_apply wp_initiator_send_msg3; first by iFrame "#".
  iIntros "_". wp_pures.
  iApply ("Hpost" $! (Some (si_key si))). iRight. iExists si.
  iModIntro. iSplit; first done.
  by iFrame "sess failed_p rel tok p_k_or_φ".
Qed.

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
Proof.
iIntros "%Ψ (#chan & #ctx & #N_ctx & #N_φ & #m_skI & #m_skR) Hpost".
iApply wp_fupd.
wp_apply (wp_initiator false c skI skR N (λ _ _ _ _, True)%I).
{ by iFrame "#". }
iIntros "%r [->|(%si & -> & #sess & _ & rel & tok & _)]".
- iModIntro. iApply ("Hpost" $! None). by iLeft.
- iMod (unrelease Init si with "rel") as "#unrel".
  iModIntro. iApply ("Hpost" $! (Some (si_key si))).
  iRight. iExists si. iSplit; first done. iFrame "tok".
  by iApply unreleased_session_weak.
Qed.

End Verif.
