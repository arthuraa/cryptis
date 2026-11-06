From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
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
Abbreviation iProp := (iProp Σ).

Implicit Types (rl : role) (t pkI pkR ga kS : term).
Implicit Types (skI skR : aenc_key).
Implicit Types (si : sess_info).
Implicit Types (N : namespace).
Implicit Types (φ : sess_info → role → iProp) (ρ : sess_info → iProp).

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
iIntros "%Ψ (#chan_c & #ctx & #(m1_pred & _) & #m_skR) Hpost".
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

#[local] Lemma wp_responder_send_msg2 c skI skR ga N φ ρ ψ :
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    nsl_dh_pred N φ ρ ∗
    minted skI ∗
    minted skR ∗
    minted ga ∗
    □ (public skI ∨ public skR → public ga) ∗
    (∀ b : nonce,
        let si := SessInfo skI skR ga (TExp (TInt 0) b) (TExp ga b) in
        term_token (si_resp_share si) (⊤ ∖ ↑nsl_dhN) ={⊤}=∗
        φ si Init ∗ ψ si)
  }}}
    responder_send_msg2 c skR (Spec.pkey skI) (Tag N) ga
  {{{ (b : nonce), RET (TNonce b, TExp (TInt 0) b);
      let gb := TExp (TInt 0) b in
      let si := SessInfo skI skR ga gb (TExp ga b) in
      dh_key skI skR False b ∗
      resp_peer gb skI ga ∗
      usage gb N ∗
      term_token gb (↑nsl_dhN.@"compromised") ∗
      term_token gb (↑nsl_dhN.@"ready") ∗
      ψ si }}}.
Proof.
iIntros "%Ψ (#chan & #ctx & #(m1_pred & m2_pred & _) & #N_φ &
         #m_skI & #m_skR & #m_ga & #s_ga & hook) Hpost".
rewrite /responder_send_msg2.
wp_pures. wp_apply wp_pkey. wp_pures.
wp_apply (wp_mk_dh_keys {[ga]} skI skR (λ _, False%I)); first by iFrame "#".
{ iIntros "%t %t_in". rewrite elem_of_singleton in t_in. by subst t. }
iIntros "%b %fresh_b #dh_b token".
have b_ga : ¬ subterm b ga.
{ apply: fresh_b. by rewrite elem_of_singleton. }
set gb := TExp (TInt 0) b.
set si := SessInfo skI skR ga gb (TExp ga b).
wp_pures.
rewrite (term_token_difference gb (↑nsl_dhN)) //.
iDestruct "token" as "[token_N token]".
iDestruct (term_token_difference gb (↑nsl_dhN.@"compromised") with "token_N")
  as "[comp_token token_N]"; first solve_ndisj.
iDestruct (term_token_difference gb (↑nsl_dhN.@"ready") with "token_N")
  as "[ready_token token_N]"; first solve_ndisj.
iDestruct (term_token_difference gb (↑nsl_dhN.@"usage") with "token_N")
  as "[use_token token_N]"; first solve_ndisj.
iDestruct (term_token_difference gb (↑nsl_dhN.@"peer") with "token_N")
  as "[peer_token _]"; first solve_ndisj.
iMod (term_meta_set (nsl_dhN.@"usage") N with "use_token") as "#use";
  first done.
iMod (term_meta_set (nsl_dhN.@"peer") (skI, ga) with "peer_token")
  as "#peer"; first done.
iMod ("hook" $! b with "token") as "[gift ψ]".
iMod (nsl_dh_ready_alloc N si Init with "N_φ gift") as "#ready".
wp_list. wp_term_of_list. wp_pures.
iPoseProof "dh_b" as "(#m_b & #s_b & #pred_b)".
wp_apply wp_aenc => //.
{ rewrite minted_of_list /= minted_pkey.
  do !iSplit => //.
  - by iApply all_minted_TExp; rewrite minted_TInt; iSplit.
  - rewrite [Tag]unlock. by rewrite minted_TInt. }
{ iRight. iSplit.
  - iModIntro. iExists ga, gb, skR, N. iSplit => //.
    iExists b. by do !iSplit.
  - iIntros "!> #p_skI".
    rewrite public_of_list /=.
    do !iSplit => //.
    + by iApply "s_ga"; iLeft.
    + iApply (public_dh_share with "dh_b"). iModIntro. by iLeft.
    + by iApply public_aenc_key.
    + rewrite [Tag]unlock. by rewrite public_TInt. }
iIntros "%m2 #p_m2". wp_pures.
wp_apply wp_send => //. wp_pures.
iApply ("Hpost" $! b). by iFrame "∗ #".
Qed.

(* A forged [m3] reveals the responder's share, which only a leaked long-term
   key explains.  Otherwise the initiator vouches for the session. *)
#[local] Lemma wp_responder_recv_msg3 c skI skR ga (b : nonce) N φ ρ :
  let gb := TExp (TInt 0) b in
  let si := SessInfo skI skR ga gb (TExp ga b) in
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    nsl_dh_pred N φ ρ ∗
    minted skI ∗
    minted skR ∗
    minted ga ∗
    dh_key skI skR False b ∗
    resp_peer gb skI ga ∗
    usage gb N ∗
    term_token gb (↑nsl_dhN.@"compromised") ∗
    term_token gb (↑nsl_dhN.@"ready")
  }}}
    responder_recv_msg3 c skR (Spec.pkey skI) ga b gb
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨
      ⌜r = Some (si_key si)⌝ ∗
      session ρ Resp si ∗
      (compromised Resp si ∨ φ si Resp) }}}.
Proof.
move=> gb si.
iIntros "%Ψ (#chan & #ctx & #nsl_ctx & #N_φ & #m_skI & #m_skR & #m_ga &
         #dh_b & #peer & #use & comp_token & ready_token) Hpost".
iPoseProof "nsl_ctx" as "(_ & _ & m3_pred & _)".
iPoseProof "dh_b" as "(#m_b & #s_b & #pred_b)".
have Nm_b : negb (is_mul b) by [].
rewrite /responder_recv_msg3. wp_pures.
wp_apply wp_pkey. wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m) "#p_m".
wp_apply wp_adec => //. iSplit; last by protocol_failure.
iClear "p_m" => {m}. iIntros "%m3 #m_m3 #inv_m3".
wp_pure _ credit:"c1".
wp_eq_term e; last by protocol_failure. subst m3.
wp_pures.
wp_bind (texp _ _). iApply wp_texp. wp_pures.
wp_list. wp_term_of_list. wp_pures.
iAssert (minted (si_key si)) as "#m_k".
{ rewrite minted_si_key /si_seed minted_of_list /= !minted_pkey.
  do !iSplit => //;
    by iApply all_minted_TExp; rewrite ?minted_TInt; iSplit. }
iPoseProof (key_release _ _ _ si with "nsl_ctx N_φ use m_k") as "#rel".

iAssert (|={⊤}=> session ρ Resp si ∗ (compromised Resp si ∨ φ si Resp))%I
  with "[c1 comp_token ready_token]" as "> [#sess res]".
{ iDestruct "inv_m3" as "[#p_gb|[#inv_m3 _]]".
  - iAssert (|={⊤}=> public skI ∨ public skR)%I with "[c1]" as "> #comp".
    { iPoseProof (public_exp_inv_same (t1 := b) with "p_gb") as "[#p_b|H]";
        first by rewrite (exps_TExp1 Nm_b) /SMS.pos SMS.car_singleton;
                 set_solver.
      - iDestruct ("s_b" with "p_b") as "#f".
        by iMod (lc_fupd_elim_later_pers with "c1 f") as "#[]".
      - iDestruct "H" as "(%t3 & _ & _ & #p)".
        iPoseProof ("pred_b" $! t3 with "p") as "#ks".
        iMod (lc_fupd_elim_later_pers with "c1 ks") as "#[comp _]".
        by iModIntro. }
    iMod (term_meta_set (nsl_dhN.@"compromised") true with "comp_token")
      as "#c"; first solve_ndisj.
    iModIntro. iSplit; last by iLeft.
    iSplit; first done. iSplit; first done.
    iLeft. iSplit; first done. by iSplit.
  - iDestruct ("inv_m3" $! skI ga b with "[//] peer")
      as "(%a & %e_ga & #dh_a & #nc & %N' & #use' & #ready)".
    iPoseProof (term_meta_agree with "use use'") as "<-".
    subst ga.
    iDestruct (honest_session with "nsl_ctx N_φ dh_a dh_b nc use m_k")
      as "[_ #ok]".
    iMod (term_meta_set (nsl_dhN.@"compromised") false with "comp_token")
      as "#nc_R"; first solve_ndisj.
    iMod ("ready" with "N_φ ready_token") as "res".
    iMod (lc_fupd_elim_later with "c1 res") as "res".
    iModIntro. iSplit; last by iRight.
    iSplit; first done. iSplit; first done.
    iRight. iSplit; last done.
    iIntros "!> #c". by iDestruct (term_meta_agree with "c nc_R") as %?. }
wp_bind (session_key _). iApply (wp_session_key si). wp_pures.
iApply ("Hpost" $! (Some (si_key si))). iRight. iModIntro. by iFrame "∗ #".
Qed.

Lemma wp_responder_confirm c skI skR ga N φ ρ ψ :
  {{{ channel c ∗ cryptis_ctx ∗ nsl_dh_ctx ∗ nsl_dh_pred N φ ρ ∗
      minted skI ∗ minted skR ∗ minted ga ∗
      □ (public skI ∨ public skR → public ga) ∗
      (∀ b : nonce,
          let si := SessInfo skI skR ga (TExp (TInt 0) b) (TExp ga b) in
          term_token (si_resp_share si) (⊤ ∖ ↑nsl_dhN) ={⊤}=∗
          φ si Init ∗ ψ si) }}}
    responder_confirm c skR (Spec.pkey skI) (Tag N) ga
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ b : nonce,
        let si := SessInfo skI skR ga (TExp (TInt 0) b) (TExp ga b) in
        ⌜r = Some (si_key si)⌝ ∗
        session ρ Resp si ∗ ψ si ∗
        (compromised Resp si ∨ φ si Resp) }}}.
Proof.
iIntros "%Ψ (#chan & #ctx & #nsl_ctx & #N_φ & #m_skI & #m_skR & #m_ga &
         #s_ga & hook) Hpost".
rewrite /responder_confirm. wp_pures.
wp_apply (wp_responder_send_msg2 _ _ _ _ _ _ _ ψ with "[hook]");
  first by iFrame "∗ #".
iIntros "%b (#dh_b & #peer & #use & comp_token & ready_token & ψ)".
wp_pures.
wp_apply (wp_responder_recv_msg3 with "[comp_token ready_token]");
  first by iFrame "∗ #".
iIntros "%r [->|(-> & #sess & res)]".
{ iApply ("Hpost" $! None). by iLeft. }
iApply ("Hpost" $! (Some _)). iRight. iExists b. iFrame. by iSplit.
Qed.

Lemma wp_responder c skR N φ ρ ψ :
  {{{ channel c ∗ cryptis_ctx ∗ nsl_dh_ctx ∗ nsl_dh_pred N φ ρ ∗ minted skR ∗
      (∀ skI ga (b : nonce),
          let si := SessInfo skI skR ga (TExp (TInt 0) b) (TExp ga b) in
          term_token (si_resp_share si) (⊤ ∖ ↑nsl_dhN) ={⊤}=∗
          φ si Init ∗ ψ si) }}}
    responder c skR (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI ga (b : nonce),
        let si := SessInfo skI skR ga (TExp (TInt 0) b) (TExp ga b) in
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session ρ Resp si ∗ ψ si ∗
        (compromised Resp si ∨ φ si Resp) }}}.
Proof.
iIntros "%Ψ (#chan & #ctx & #nsl_ctx & #N_φ & #m_skR & hook) Hpost".
rewrite /responder /responder_listen. wp_pures.
wp_bind (responder_recv_msg1 _ _).
wp_apply wp_responder_recv_msg1; first by iFrame "#".
iIntros "%r [->|(%ga & %skI & -> & #m_ga & #m_skI & #s_ga)]".
{ wp_pures. iApply ("Hpost" $! None). by iLeft. }
wp_pures.
wp_bind (responder_confirm _ _ _ _ _).
wp_apply (wp_responder_confirm _ _ _ _ _ _ _ ψ with "[hook]").
{ iFrame "#". iIntros "%b". iApply "hook". }
iIntros "%r [->|(%b & -> & #sess & ψ & res)]".
{ wp_pures. iApply ("Hpost" $! None). by iLeft. }
wp_pures.
iApply ("Hpost" $! (Some (Spec.pkey skI, si_key _))).
iRight. iExists skI, ga, b. iFrame. iModIntro. by iSplit.

Qed.

End Verif.
