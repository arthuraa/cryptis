From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role session.
From cryptis.pk_auth Require Import impl shared.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PK.

Context `{!heapGS Σ, !cryptisGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : aenc_key).

Variable N : namespace.

Context `{!PK}.

Lemma public_msg1E skI skR sI :
  pk_auth_ctx N -∗
  public (TSeal (Spec.pkey skR)
            (Spec.tag (Tag $ N.@"m1") (Spec.of_list [sI; Spec.pkey skI]))) -∗
  ▷ (minted sI ∧ minted skI ∧ readable_by sI skI skR ∧ init_started N skI skR sI).
Proof.
iIntros "(_ & #m1P & _ & _) #p_m1".
iPoseProof (public_aencE with "p_m1 m1P") as "{p_m1} (m_m1 & p_m1)".
rewrite minted_of_list public_of_list /= minted_pkey.
iDestruct "m_m1" as "(m_sI & m_skI & _)".
iDestruct "p_m1" as "[p_m1 | p_m1]".
- iModIntro.
  iDestruct "p_m1" as "(? & _)". iSplit; eauto. iSplit; eauto. iSplit.
    by iIntros "!> ?".
  by iLeft.
- iDestruct "p_m1" as "{m1P} (#m1P & _)".
  iModIntro.
  iDestruct "m1P" as "(%sI' & %skI' & %e_m1 & p_sI & accepted)".
  case/Spec.of_list_inj: e_m1 => <- /Spec.aenc_pkey_inj <-.
  by eauto.
Qed.

Lemma resp_accept E skI skR sI nR :
  ↑N ⊆ E →
  let kS := mk_session_key Resp nR sI in
  term_token nR ⊤ -∗
  resp_confirm skR -∗
  pk_auth_ctx N -∗
  □ is_priv_key nR skI skR -∗
  init_started N skI skR sI ={E}=∗
  □ confirmation Resp skI skR kS ∗
  session_weak' N skI skR nR ∗
  session_weak N Resp skI skR kS ∗
  resp_waiting N skI skR sI nR ∗
  resp_accepted N skI skR sI (mk_key_share nR).
Proof.
iIntros (?) "%kS token conf (#ctx & _) #p_nR #started".
iMod ("conf" $! skI sI nR) as "#conf".
rewrite (term_token_difference _ (↑N.@"session")) //.
iDestruct "token" as "[token_sess token]".
rewrite (term_token_difference _ (↑N.@"success") (_ ∖ _)) //; last first.
  solve_ndisj.
iDestruct "token" as "[token_succ _]".
iMod (session_weak'_set N skI skR nR with "token_succ") as "#sess".
iDestruct "started" as "[#fail|(%nI & -> & #sess' & #p_nI)]".
  iModIntro. iFrame. iSplit; eauto. iSplit => //. iSplit.
    by iExists _, _; eauto.
  iSplitL; iLeft => //.
  by iFrame.
rewrite -mk_session_keyC in @kS *.
iMod (session_begin _ Resp nI nR (skI, skR)
       with "ctx [] token_sess") as "[#sessR waiting]".
- solve_ndisj.
- rewrite /=. by eauto.
iFrame. iModIntro. iSplit; eauto. iSplit => //. iSplit.
  rewrite mk_session_keyC in @kS *.
  by iExists _, _; eauto.
iSplitL.
  iRight. iExists nI. by eauto.
iRight. iExists nI, nR.
by do !iSplit => //.
Qed.

Lemma public_msg2I skI skR sI sR :
  pk_auth_ctx N -∗
  minted skI -∗
  minted skR -∗
  minted sI -∗
  readable_by sI skI skR -∗
  minted sR -∗
  secret_of sR skI skR -∗
  resp_accepted N skI skR sI sR -∗
  public (TSeal (Spec.pkey skI)
            (Spec.tag (Tag $ N.@"m2") (Spec.of_list [sI; sR; Spec.pkey skR]))).
Proof.
iIntros "(_ & _ & #? & _) #m_skI #m_skR #s_sI #p_sI #s_sR #p_sR #accepted".
iApply public_aencIS; eauto.
- rewrite minted_of_list /= minted_pkey; eauto.
- iModIntro. iExists sI, sR, skR. by eauto.
iIntros "!> #p_dkI". rewrite public_of_list /= public_aenc_key.
do !iSplit => //.
- iApply "p_sI". by iLeft.
- iApply "p_sR". iModIntro. by iLeft.
Qed.

Lemma public_msg3E skI skR sR :
  pk_auth_ctx N -∗
  secret_of sR skI skR -∗
  public (TSeal (Spec.pkey skR) (Spec.tag (Tag $ N.@"m3") sR)) -∗
  ▷ init_finished N skR sR.
Proof.
iIntros "(_ & _ & _ & #?) #p_sR #p_m3".
iDestruct (public_aencE with "p_m3 [//]") as "{p_m3} [m_m3 p_m3]".
iDestruct "p_m3" as "[p_m3 | p_m3]".
- by iLeft.
- by iDestruct "p_m3" as "(#p_m3 & _)".
Qed.

Lemma resp_finish E skI skR sI nR :
  let sR := mk_key_share nR in
  let kS := mk_session_key Resp nR sI in
  ↑N ⊆ E →
  pk_auth_ctx N -∗
  session_weak' N skI skR nR -∗
  minted nR -∗
  □ is_priv_key nR skI skR -∗
  init_finished N skR sR -∗
  resp_waiting N skI skR sI nR ={E}=∗
  ▷ (corruption skI skR ∨
     session_key_meta_token N skI skR kS (↑N.@"resp") ∗
     session_key N skI skR kS).
Proof.
iIntros "%sR %kS % #(ctx & _) #sess #s_nR #p_nR [#fail|#finished] waiting".
  iPoseProof (mk_key_share_secret_of with "s_nR p_nR") as "p_sR".
  iModIntro. iLeft. by iApply "p_sR".
iDestruct "finished"
  as "(%nI' & %nR' & %skI' &
       #sessWI & #sessWR & %e_sR & p_nI & _ & confirmedI & sessI & sessR')".
move/mk_key_share_inj: e_sR => <- {nR'}.
iDestruct "waiting" as "[[#fail token]|waiting]".
  by iDestruct (session_not_ready with "ctx sessR' token") as "[]"; eauto.
iDestruct "waiting" as "(%nI & -> & #sessR & #confirmedR & waiting)".
move: @kS; rewrite -mk_session_keyC => kS.
iPoseProof (session_agree with "sessR sessR'") as "{sessR'} %e" => //.
case: e => <- <-.
iPoseProof (session_weak'_agree with "sessWR sess") as "(_ & _)".
iMod ("waiting" with "[] sessI") as "[_ >finished]".
  solve_ndisj.
rewrite /=.
iModIntro. iModIntro. iRight. iSplitL.
  iExists nI, nR. by eauto.
iExists nI, nR. by do !iSplit => //.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_pk_auth_resp c skR :
  channel c -∗
  cryptis_ctx -∗
  pk_auth_ctx N -∗
  minted skR -∗
  {{{ resp_confirm skR }}}
    pk_auth_resp N c mk_key_share_impl (mk_session_key_impl Resp) skR
  {{{ res, RET (repr res);
      if res is Some (pkI, kS) then
         ∃ skI, ⌜pkI = Spec.pkey skI⌝ ∗
                minted skI ∗
                minted kS ∗
                □ confirmation Resp skI skR kS ∗
                session_weak N Resp skI skR kS ∗
                (corruption skI skR ∨
                   session_key_meta_token N skI skR kS (↑N.@"resp") ∗
                   session_key N skI skR kS)
       else True }}}.
Proof.
iIntros "#? #ctx #ctx' #m_skR %Ψ !> confirm Hpost".
iPoseProof "ctx'" as "(inv & _)".
rewrite /pk_auth_resp; wp_pures.
wp_apply wp_pkey. wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#Hm1".
wp_adec m1; last protocol_failure.
wp_list_of_term m1; last protocol_failure.
wp_list_match => [sI pkI {m1} ->|_]; last protocol_failure.
iPoseProof (public_minted with "Hm1") as "m_m1".
rewrite minted_TSeal minted_tag minted_of_list /=.
iDestruct "m_m1" as "(_ & _ & m_pkI & _)".
wp_apply wp_is_aenc_key; eauto. iSplit; last protocol_failure.
iIntros "%skI -> #m_skI". wp_pures.
iDestruct (public_msg1E with "[] Hm1")
  as "{Hm1} (s_sI & p_eI & p_sI & started)"; eauto.
wp_pures.
wp_bind (mk_key_share_impl _). iApply (wp_mk_key_share skI skR) => //.
iIntros "!> %nR (#s_nR & #p_nR & token)".
iMod (resp_accept with "token confirm [//] [//] [//]")
  as "(#confirmed & #? & #sess_weak & waiting & #accepted)" => //.
wp_pures. wp_list; wp_term_of_list. wp_apply wp_aenc'. wp_pures.
iAssert (secret_of (mk_key_share nR) skI skR) as "p_sR".
  by iApply mk_key_share_secret_of.
wp_bind (send _ _). iApply wp_send => //.
  iApply public_msg2I; eauto.
  by iApply mk_key_share_minted.
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m3 #p_m3". wp_adec m3; last protocol_failure.
wp_eq_term e; last protocol_failure; subst m3.
iPoseProof (public_msg3E with "[//] [//] [//]") as "finished".
wp_pures.
iMod (resp_finish with "[] [] [] [] [] waiting") as "session" => //.
wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
iIntros "!> _". wp_pures.
iApply ("Hpost" $! (Some (_, mk_session_key Resp nR sI))).
iModIntro. iFrame.
do 3!iSplit => //; eauto.
by iApply mk_session_key_minted => //.
Qed.

End PK.
