From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role session.
From cryptis.examples.pk_auth Require Import impl shared.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PK.

Context `{!heapGS Σ, !cryptisGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).
Implicit Types (skI skR : aenc_key).

Variable N : namespace.

Context `{!PK}.

Lemma public_msg1I skI skR nI :
  let sI := mk_key_share nI in
  pk_auth_ctx N -∗
  session_weak' N skI skR nI -∗
  minted nI -∗
  □ is_priv_key nI skI skR -∗
  minted skI -∗
  minted skR -∗
  public (TSeal (Spec.pkey skR) (Spec.tag (Tag $ N.@"m1") (Spec.of_list [sI; Spec.pkey skI]))).
Proof.
rewrite /=.
iIntros "(_ & #m1P & _ & _) #meta #s_nI #p_nI #m_skI #m_skR".
iPoseProof (mk_key_share_secret_of with "s_nI p_nI") as "p_sI".
iApply public_aencIS; eauto.
- rewrite minted_of_list /= mk_key_share_minted minted_pkey. by eauto.
- iModIntro. iExists (mk_key_share nI), skI. do !iSplit => //.
  + iIntros "!> #?". iApply "p_sI". by eauto.
  + iRight. by iExists nI; eauto.
iIntros "!> #p_dkR". rewrite public_of_list /= public_aenc_key.
do !iSplit => //. iApply "p_sI". iModIntro. by iRight.
Qed.

Lemma public_msg2E skI skR sI sR :
  pk_auth_ctx N -∗
  secret_of sI skI skR -∗
  public (TSeal (Spec.pkey skI)
            (Spec.tag (Tag $ N.@"m2") (Spec.of_list [sI; sR; Spec.pkey skR]))) -∗
  ▷ (minted sR ∧ secret_of sR skI skR ∧ resp_accepted N skI skR sI sR).
Proof.
iIntros "(_ & _ & #m2P & _) #started #p_m2".
iPoseProof (public_aencE with "p_m2 m2P") as "{p_m2} (m_m2 & p_m2)".
rewrite minted_of_list /= minted_pkey public_of_list /=.
iDestruct "m_m2" as "(?&?&?&_)".
iDestruct "p_m2" as "[p_m2 | p_m2]".
- iDestruct "p_m2" as "(p_sI & p_sR & _ & _)".
  iSpecialize ("started" with "p_sI").
  iModIntro.
  iSplit; eauto.
  iSplit.
    iModIntro. by iSplit; eauto.
  by iLeft.
- iDestruct "p_m2" as "(#p_m2 & #s_m2)".
  iModIntro.
  iDestruct "p_m2" as "(%sI' & %sR' & %skR' & %e_m2 & sRP & ?)".
  case/Spec.of_list_inj: e_m2 => <- <- /Spec.aenc_pkey_inj <-.
  do !iSplit => //.
Qed.

Lemma init_finish skI skR nI sR :
  let sI := mk_key_share nI in
  let kS := mk_session_key Init nI sR in
  pk_auth_ctx N -∗
  session_weak' N skI skR nI -∗
  minted nI -∗
  □ is_priv_key nI skI skR -∗
  secret_of sR skI skR -∗
  resp_accepted N skI skR sI sR -∗
  term_token nI (⊤ ∖ ↑N.@"success") -∗
  init_confirm skI skR ={⊤}=∗
  ▷ (□ confirmation Init skI skR kS ∗
     session_weak N Init skI skR kS ∗
     init_finished N skR sR ∗
     (corruption skI skR ∨
      session_key_meta_token N skI skR kS (↑N.@"init") ∗
      session_key N skI skR kS)).
Proof.
iIntros "%sI %kS (#ctx & _) #sess #s_nI #p_nI #p_sR #accepted token confirm".
iMod ("confirm" $! nI sR) as "#confirm".
iAssert (secret_of sI skI skR) as "p_sI".
  by iApply mk_key_share_secret_of.
rewrite (term_token_difference _ (↑N.@"init")) //; last solve_ndisj.
iDestruct "token" as "[init_token token]".
rewrite (term_token_difference _ (↑N.@"resp") (_ ∖ _)) //; last solve_ndisj.
iDestruct "token" as "[resp_token token]".
rewrite (term_token_difference _ (↑N.@"session") (_ ∖ _)); last solve_ndisj.
set S := N.@"session".
iDestruct "token" as "[token_sess token]".
iDestruct "accepted" as "[fail|accepted]".
  iPoseProof ("p_sI" with "fail") as "fail'".
  iModIntro. iModIntro. iFrame. iSplit; eauto. iSplit.
    iExists _, _; eauto.
  iSplit; eauto.
  iLeft. iApply "p_sR". by iApply "p_sI".
iDestruct "accepted"
  as "(%nI' & %nR &
       #sess' & #sess'' &
       %e_sI & -> & #p_nR & #accepted & confirmed)".
move/mk_key_share_inj: e_sI => <-.
iDestruct (session_weak'_agree with "sess' sess") as "(_ & _)".
iMod (session_begin _ Init nI nR (skI, skR) with "ctx [resp_token] token_sess")
  as "[#sessI _]".
- solve_ndisj.
- by iSplitR.
iModIntro. iModIntro. iFrame. iSplit; eauto. iSplitR.
  by iExists _, _; eauto.
iSplitR.
  iRight. iExists nI, nR, skI. do !iSplit => //; by eauto.
iRight. iSplitL.
  iExists nI, nR; by eauto.
iExists nI, nR; do !iSplit => //; eauto.
Qed.

Lemma public_msg3I skI skR sI sR :
  pk_auth_ctx N -∗
  minted skR -∗
  minted sR -∗
  secret_of sR skI skR -∗
  init_finished N skR sR -∗
  public (TSeal (Spec.pkey skR) (Spec.tag (Tag $ N.@"m3") sR)).
Proof.
iIntros "(_ & _ & _ & #p_m3) #p_eR #s_sR #p_sR #finished".
iApply public_aencIS; eauto.
iIntros "!> #p_dkR". iApply "p_sR". by iRight.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_pk_auth_init c skI skR :
  channel c -∗
  cryptis_ctx -∗
  pk_auth_ctx N -∗
  minted skI -∗
  minted skR -∗
  {{{ init_confirm skI skR }}}
    pk_auth_init N c mk_key_share_impl (mk_session_key_impl Init)
    skI (Spec.pkey skR)
  {{{ okS, RET (repr okS);
      if okS is Some kS then
        minted kS ∗
        □ confirmation Init skI skR kS ∗
        session_weak N Init skI skR kS ∗
        (corruption skI skR ∨
          session_key_meta_token N skI skR kS (↑N.@"init") ∗
          session_key N skI skR kS)
      else True }}}.
Proof.
rewrite /pk_auth_init.
iIntros "#chan_c #ctx #ctx' #m_skI #m_skR %Ψ !> confirm Hpost".
wp_pures. wp_apply wp_pkey. wp_pures.
wp_bind (mk_key_share_impl _).
iApply (wp_mk_key_share skI skR) => //.
iIntros "!> %nI (#s_nI & #p_nI & token)".
rewrite (term_token_difference _ (↑N.@"success")); eauto.
iDestruct "token" as "[token_succ token]".
iMod (session_weak'_set N skI skR _ with "token_succ") as "#sess".
wp_pures.
iPoseProof (mk_key_share_secret_of with "s_nI p_nI") as "p_sI".
wp_list. wp_term_of_list. wp_apply wp_aenc'. wp_pures.
wp_bind (send _ _). iApply (wp_send with "[] [#]"); eauto.
  by iApply (public_msg1I with "[]"); eauto.
wp_pures. wp_bind (recv _). iApply wp_recv; eauto.
iIntros "%m2 #p_m2". wp_adec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_list_match => [sI' sR pkR' {m2} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst sI'.
wp_eq_term e; last protocol_failure; subst pkR'.
iPoseProof (public_msg2E with "[//] [//] [//]")
  as "{p_m2} (s_sR & p_sR & accepted)".
wp_pures.
iMod (init_finish with "ctx' sess s_nI p_nI p_sR accepted token confirm")
  as "(#confirmed & #sess_weak & #finished & session)"; eauto.
wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
iIntros "!> _". wp_pures. wp_apply wp_aenc'. wp_pures. wp_bind (send _ _).
iApply wp_send => //.
  by iApply public_msg3I.
wp_pures. iApply ("Hpost" $! (Some (mk_session_key Init nI sR))).
iFrame. iModIntro. iSplit; eauto. by iApply mk_session_key_minted.
Qed.

End PK.
