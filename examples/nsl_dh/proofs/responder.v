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
    responder_send_msg2 c skR (Spec.pkey skI) (Tag N) ga
  {{{ (b : term), RET (b, TExp (TInt 0) b);
      let gb := TExp (TInt 0) b in
      let gab := TExp ga b in
      let si := SessInfo skI skR ga gb gab in
      dh_key skI skR b ∗
      has_peer_share gb (Some ga) ∗
      release_token gb ∗
      term_token gb (⊤ ∖ ↑nsl_dhN) ∗
      φ skI skR si Resp }}}.
Proof.
iIntros "%Ψ (#chan & #ctx & #(m1_pred & m2_pred & m3_pred) & #N_φ &
         #m_skI & #m_skR & #m_ga & #s_ga & φ_cb & failed_e) Hpost".
rewrite /responder_send_msg2.
wp_pures. wp_apply wp_pkey. wp_pures.
wp_apply (wp_mk_dh_keys skI skR); first by iFrame "#".
iIntros "%b #dh_b rel ptok rtok res tok".
set gb := TExp (TInt 0) b.
wp_pures.
(* Set peer share for gb *)
iMod (set_peer_share gb (Some ga) with "ptok") as "#ps_gb".
(* Get φ from callback *)
set gab := TExp ga b.
set si := SessInfo skI skR ga gb gab.
iMod ("φ_cb" $! b with "res") as "[φ_init φ_resp]".
(* Allocate nsl_dh_ready *)
iMod (nsl_dh_ready_alloc N skI skR si with "N_φ φ_init") as "#ready".
(* Build and encrypt msg2 *)
wp_list. wp_term_of_list. wp_pures.
iDestruct "dh_b" as "(#m_b & #s_b & #pred_b)".
wp_apply wp_aenc => //.
{ (* minted plaintext *)
  rewrite minted_of_list /= minted_pkey !minted_TExp minted_TInt /=.
  rewrite Tag_unseal /Tag_def minted_TInt.
  by do !iSplit. }
{ (* encryption invariant *)
  iRight. iSplit.
  - (* □ msg2_pred skI plaintext *)
    iModIntro. iExists ga, gb, skR, N. iSplit => //.
    iExists b. do !iSplit => //.
  - (* □ (public skI → public plaintext) *)
    iIntros "!> #p_skI".
    rewrite public_of_list /=.
    do !iSplit => //.
    + by iApply "s_ga"; iLeft.
    + iApply (public_dh_share with "[#]").
      { do !iSplit; eauto. }
      iModIntro. by iLeft.
    + by iApply public_aenc_key.
    + rewrite Tag_unseal /Tag_def. by rewrite public_TInt. }
iIntros "%m2 #p_m2". wp_pures.
wp_apply wp_send => //. wp_pures.
iApply ("Hpost" $! b). by iFrame "∗ #".
Qed.

Lemma wp_responder_recv_msg3 c skI skR ga b :
  let gb := TExp (TInt 0) b in
  let gab := TExp ga b in
  let si := SessInfo skI skR ga gb gab in
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    minted skI ∗
    minted skR ∗
    minted ga ∗
    □ (public skI ∨ public skR → public ga) ∗
    dh_key skI skR b ∗
    has_peer_share gb (Some ga) ∗
    release_token gb
  }}}
    responder_recv_msg3 c skR (Spec.pkey skI) ga b gb
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨
      ⌜r = Some (si_key si)⌝ ∗
      session skI skR si ∗
      release_token gb }}}.
Proof.
move=> gb gab si.
iIntros "%Ψ (#chan & #ctx & #(m1_pred & m2_pred & m3_pred) &
         #m_skI & #m_skR & #m_ga & #s_ga & #dh_b & #ps_gb & rel) Hpost".
iDestruct "dh_b" as "(#m_b & #s_b & #pred_b)".
rewrite /responder_recv_msg3. wp_pures.
wp_apply wp_pkey. wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m) "#p_m".
wp_apply wp_adec => //. iSplit; last by protocol_failure.
iClear "p_m" => {m}. iIntros "%m3 #m_m3 #inv_m3".
(* Check eq_term m3 gb *)
wp_pure _ credit:"Hc1".
wp_eq_term e; last by protocol_failure. subst m3.
wp_pures.
(* Compute gab and session key *)
wp_bind (texp _ _). iApply wp_texp. wp_pures.
wp_list. wp_term_of_list. wp_pures.
(* Do case analysis and credit elimination while still in WP context *)
iPoseProof (dh_key_public_released skI skR b ga
             with "[#] ps_gb") as "#rel_b".
{ do !iSplit; eauto. }
iAssert (minted (si_key si)) as "#m_k".
{ rewrite minted_senc minted_of_list /= !minted_pkey !minted_TExp minted_TInt /=.
  by do !iSplit. }
iDestruct "inv_m3" as "[#p_gb|(#inv_m3 & _)]".
- (* public gb — case split via public_TExp_iff *)
  rewrite public_TExp_iff; first last. { by case. }
  iDestruct "p_gb" as "[[_ #p_b]|(_ & _ & #dp_b)]".
  + (* public b — contradiction with release_token *)
    iDestruct ("s_b" with "p_b") as "#later_ns".
    iMod (lc_fupd_elim_later_pers with "Hc1 later_ns") as "#ns".
    iExFalso.
    iDestruct "ns" as "[#ps_none|(%ga' & #ps_some & #r_gb & _)]".
    * by iPoseProof (has_peer_share_agree with "ps_gb ps_none") as "%".
    * by iApply (term_meta_token with "rel r_gb").
  + (* dh_pred b gb — derive corruption *)
    iPoseProof ("pred_b" $! gb with "dp_b") as "#later_ks".
    iMod (lc_fupd_elim_later_pers with "Hc1 later_ks") as "#[#corr _]".
    wp_bind (derive_senc_key _). iApply wp_derive_senc_key. iNext. wp_pures.
    iApply ("Hpost" $! (Some (si_key si))). iRight. iModIntro. iSplit => //.
    iFrame "rel". do !iSplit => //.
    * (* released → public *)
      iIntros "!> #[#r_ga #r_gb]".
      iAssert (public b) as "#p_b".
      { iApply "rel_b". iNext. by iSplit. }
      iAssert (public ga) as "#p_ga".
      { iApply "s_ga". done. }
      rewrite public_senc_key public_of_list /=.
      iSplit; [by iApply public_aenc_key|].
      iSplit; [by iApply public_aenc_key|].
      iSplit; [done|].
      iSplit; [iApply public_TExp; [by rewrite public_TInt|done]|].
      iSplit; [|done].
      iApply public_TExp => //.
    * by iLeft.
- (* msg3_pred — honest case *)
  iPoseProof ("inv_m3" $! ga b with "[%] ps_gb") as "[#rel_ga_gb #gab_iff]".
  { done. }
  wp_bind (derive_senc_key _). iApply wp_derive_senc_key. iNext. wp_pures.
  iApply ("Hpost" $! (Some (si_key si))). iRight. iModIntro. iSplit => //.
  iFrame "rel". do !iSplit => //.
  * (* released → public *)
    iIntros "!> #[#r_ga #r_gb]".
    iAssert (public ga) as "#p_ga".
    { iApply "rel_ga_gb". by iSplit. }
    iAssert (public b) as "#p_b".
    { iApply "rel_b". iNext. by iSplit. }
    rewrite public_senc_key public_of_list /=.
    iSplit; [by iApply public_aenc_key|].
    iSplit; [by iApply public_aenc_key|].
    iSplit; [done|].
    iSplit; [iApply public_TExp; [by rewrite public_TInt|done]|].
    iSplit; [|done].
    iApply "gab_iff". by iSplit.
  * (* public → released OR corruption *)
    iRight. iIntros "!> #p_k".
    rewrite public_senc_key public_of_list /=.
    iDestruct "p_k" as "(_ & _ & _ & _ & #p_gab & _)".
    by iApply "gab_iff".
Qed.

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
Proof.
iIntros "%Ψ (#chan & #ctx & #nsl_ctx & #N_φ & #m_skR) Hpost".
rewrite /responder /responder_listen. wp_pures.
(* Step 1: recv msg1 *)
wp_bind (responder_recv_msg1 _ _).
wp_apply wp_responder_recv_msg1.
{ by iFrame "#". }
iIntros "%r [->|(%ga & %skI & -> & #m_ga & #m_skI & #s_ga)]".
{ wp_pures. iApply ("Hpost" $! None). by iLeft. }
wp_pures.
(* Step 2: send msg2 via responder_confirm *)
rewrite /responder_confirm. wp_pures.
iAssert (failed_early skI skR false) as "fe". { done. }
wp_apply (wp_responder_send_msg2 _ _ _ _ _ (λ _ _ _ _, True)%I false).
{ iFrame "∗ #". iIntros "%b res".
  iMod (term_meta_set (nsl_dhN.@"res") () with "res") as "#_"; first by solve_ndisj.
  by iFrame. }
iIntros "%b (#dh_b & #ps_gb & rel & tok & _)".
set gb := TExp (TInt 0) b.
wp_pures.
(* Step 3: recv msg3 *)
wp_apply (wp_responder_recv_msg3 c skI skR ga b with "[$]").
iIntros "%r2 [->|(%e_r2 & #sess & rel2)]".
{ wp_pures. iApply ("Hpost" $! None). by iLeft. }
subst r2. wp_pures.
set gab := TExp ga b.
set si := SessInfo skI skR ga gb gab.
iApply ("Hpost" $! (Some (Spec.pkey skI, si_key si))).
iRight. iExists skI, si. iModIntro. iSplit => //.
by iFrame "∗ #".
Qed.

End Verif.
