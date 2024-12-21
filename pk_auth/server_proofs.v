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

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).

Variable N : namespace.

Context `{!PK}.

Lemma public_msg1E kI kR sI :
  pk_auth_ctx N -∗
  public (TSeal (TKey Seal kR) (Spec.tag (N.@"m1") (Spec.of_list [sI; TKey Seal kI]))) -∗
  ▷ (minted sI ∧ public (TKey Seal kI) ∧ readable_by sI kI kR ∧
     init_started N kI kR sI).
Proof.
iIntros "(_ & #m1P & _ & _) #p_m1".
iPoseProof (public_TSealE with "p_m1 m1P") as "{p_m1} [p_m1 | p_m1]".
- iModIntro. rewrite public_of_list /=.
  iDestruct "p_m1" as "(? & ? & ? & _)". iSplit; eauto. iSplit; eauto. iSplit.
    by iIntros "!> ?".
  by iLeft.
- iDestruct "p_m1" as "{m1P} (#m1P & #s_m1 & #p_m1)".
  iModIntro.
  iDestruct "m1P" as "(%sI' & %kI' & %e_m1 & p_pkI & p_sI & accepted)".
  case/Spec.of_list_inj: e_m1 => <- <-.
  rewrite minted_of_list /=. iDestruct "s_m1" as "(#s_sI & _)".
  do !iSplit => //.
Qed.

Lemma resp_accept dq n E kI kR sI nR :
  ↑N ⊆ E →
  let kS := mk_session_key Resp nR sI in
  term_token nR ⊤ -∗
  resp_confirm kR -∗
  pk_auth_ctx N -∗
  ●Ph{dq} n -∗
  □ is_priv_key nR kI kR -∗
  init_started N kI kR sI ={E}=∗
  ●Ph{dq} n ∗
  □ confirmation Resp kI kR kS ∗
  session_weak' N kI kR nR n ∗
  session_weak N Resp kI kR kS n ∗
  resp_waiting N kI kR sI nR ∗
  resp_accepted N kI kR sI (mk_key_share nR).
Proof.
iIntros (?) "%kS token conf (#ctx & _) hon #p_nR #started".
iMod ("conf" $! kI sI nR) as "#conf".
rewrite (term_token_difference _ (↑N.@"session")) //.
iDestruct "token" as "[token_sess token]".
rewrite (term_token_difference _ (↑N.@"success") (_ ∖ _)) //; last first.
  solve_ndisj.
iDestruct "token" as "[token_succ _]".
iMod (session_weak'_set N kI kR nR n with "[#] token_succ") as "#sess".
  by iApply phase_auth_frag.
iDestruct "started" as "[#fail|(%n' & %nI & -> & #sess' & #p_nI)]".
  iModIntro. iFrame. iSplit; eauto. iSplit => //. iSplit.
    by iExists _, _; eauto.
  iSplitL; iLeft => //.
  by iFrame.
rewrite -mk_session_keyC in @kS *.
iMod (session_begin _ Resp nI nR (kI, kR)
       with "ctx [] token_sess") as "[#sessR waiting]".
- solve_ndisj.
- rewrite /=. by eauto.
iAssert (⌜n' ≤ n⌝)%I as "%n'n".
  iDestruct "sess'" as "[hon' _]".
  by iApply (phase_auth_frag_agree with "[hon]").
iPoseProof (phase_auth_frag with "hon") as "#?".
iFrame. iModIntro. iSplit; eauto. iSplit => //. iSplit.
  rewrite mk_session_keyC in @kS *.
  by iExists _, _; eauto.
iSplitL.
  iRight. iExists nI. by eauto.
iRight. iExists n, n', nI, nR.
by do !iSplit => //.
Qed.

Lemma public_msg2I kI kR sI sR :
  pk_auth_ctx N -∗
  public (TKey Seal kI) -∗
  public (TKey Seal kR) -∗
  minted sI -∗
  readable_by sI kI kR -∗
  minted sR -∗
  secret_of sR kI kR -∗
  resp_accepted N kI kR sI sR -∗
  public (TSeal (TKey Seal kI) (Spec.tag (N.@"m2") (Spec.of_list [sI; sR; TKey Seal kR]))).
Proof.
iIntros "(_ & _ & #? & _) #p_eI #p_eR #s_sI #p_sI #s_sR #p_sR #accepted".
iApply public_TSealIS; eauto.
- iModIntro. iExists sI, sR, kR. by eauto.
- rewrite minted_of_list /=; eauto.
iIntros "!> #p_dkI". rewrite public_of_list /=. do !iSplit => //.
- by iApply "p_sI"; iLeft.
- iApply "p_sR". iModIntro. by iLeft.
Qed.

Lemma public_msg3E kI kR sR :
  pk_auth_ctx N -∗
  secret_of sR kI kR -∗
  public (TSeal (TKey Seal kR) (Spec.tag (N.@"m3") sR)) -∗
  ▷ init_finished N kR sR.
Proof.
iIntros "(_ & _ & _ & #?) #p_sR #p_m3".
iDestruct (public_TSealE with "p_m3 [//]") as "{p_m3} [p_m3|p_m3]".
- iDestruct "p_m3" as "[_ p_m3]". by iLeft.
- by iDestruct "p_m3" as "(#p_m3 & _)".
Qed.

Lemma resp_finish E kI kR sI nR n :
  let sR := mk_key_share nR in
  let kS := mk_session_key Resp nR sI in
  ↑N ⊆ E →
  pk_auth_ctx N -∗
  session_weak' N kI kR nR n -∗
  minted nR -∗
  □ is_priv_key nR kI kR -∗
  init_finished N kR sR -∗
  resp_waiting N kI kR sI nR ={E}=∗
  ▷ (corruption kI kR ∨
     session_key_meta_token N kI kR kS (↑N.@"resp") ∗
     session_key N kI kR kS n).
Proof.
iIntros "%sR %kS % #(ctx & _) #sess #s_nR #p_nR [#fail|#finished] waiting".
  iPoseProof (mk_key_share_secret_of with "s_nR p_nR") as "p_sR".
  iModIntro. iLeft. by iApply "p_sR".
iDestruct "finished"
  as "(%nI' & %nR' & %kI' & %n' &
       #sessWI & #sessWR & %e_sR & p_nI & _ & confirmedI & sessI & sessR')".
move/mk_key_share_inj: e_sR => <- {nR'}.
iDestruct "waiting" as "[[#fail token]|waiting]".
  by iDestruct (session_not_ready with "ctx sessR' token") as "[]"; eauto.
iDestruct "waiting" as "(%nI & -> & #sessR & #confirmedR & waiting)".
move: @kS; rewrite -mk_session_keyC => kS.
iPoseProof (session_agree with "sessR sessR'") as "{sessR'} %e" => //.
case: e => <- <-.
iPoseProof (session_weak'_agree with "sessWR sess") as "(_ & _ & ->)".
iMod ("waiting" with "[] sessI") as "[_ >finished]".
  solve_ndisj.
rewrite /=.
iModIntro. iModIntro. iRight. iSplitL.
  iExists nI, nR. by eauto.
iExists nI, nR. by do !iSplit => //.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_pk_auth_resp c kR dq n T :
  channel c -∗
  cryptis_ctx -∗
  pk_auth_ctx N -∗
  public (TKey Seal kR) -∗
  honest n T -∗
  {{{ resp_confirm kR ∗ ●Ph{dq} n }}}
    pk_auth_resp N c mk_key_share_impl (mk_session_key_impl Resp) kR
  {{{ res, RET (repr res);
      ●Ph{dq} n ∗
      if res is Some (pkI, kS) then
         ∃ kI, ⌜pkI = TKey Seal kI⌝ ∗
               public pkI ∗
               minted kS ∗
               □ confirmation Resp kI kR kS ∗
               session_weak N Resp kI kR kS n ∗
               if in_honest kI kR T then
                session_key_meta_token N kI kR kS (↑N.@"resp") ∗
                session_key N kI kR kS n
               else True
       else True }}}.
Proof.
iIntros "#? #ctx #ctx' #e_kR #hon %Ψ !> [confirm phase] Hpost".
iPoseProof "ctx'" as "(inv & _)".
rewrite /pk_auth_resp; wp_pures.
wp_apply wp_pkey. wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#Hm1".
wp_adec m1; last protocol_failure.
wp_list_of_term m1; last protocol_failure.
wp_list_match => [sI pkI {m1} ->|_]; last protocol_failure.
wp_is_key_eq kt kI et; last protocol_failure; subst pkI.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Seal)); last protocol_failure.
case: kt => // _.
iDestruct (public_msg1E with "[] Hm1")
  as "{Hm1} (s_sI & p_eI & p_sI & started)"; eauto.
wp_pures.
wp_bind (mk_key_share_impl _). iApply (wp_mk_key_share kI kR) => //.
iIntros "!> %nR (#s_nR & #p_nR & token)".
iMod (resp_accept with "token confirm [//] phase [//] [//]")
  as "(phase & #confirmed & #? & #sess_weak & waiting & #accepted)" => //.
wp_pures. wp_list; wp_term_of_list. wp_apply wp_aenc. wp_pures.
iAssert (secret_of (mk_key_share nR) kI kR) as "p_sR".
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
case: (decide (TKey Open kI ∈ T ∧ TKey Open kR ∈ T)) => [[kIP kRP]|pub]; last first.
  wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
  iIntros "!> _". wp_pures.
  iApply ("Hpost" $! (Some (TKey Seal kI, mk_session_key Resp nR sI))).
  iModIntro. iFrame. iExists kI.
  rewrite /in_honest bool_decide_decide decide_False //.
  do 3!iSplit => //; eauto.
  by iApply mk_session_key_minted => //.
iDestruct "session" as "[[#fail|#fail]|session]".
- wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
  iIntros "!> _".
  iPoseProof (secret_atI _ kIP with "hon") as "sec".
  iMod (honest_public with "ctx sec phase fail") as "contra"; eauto.
  wp_pures. by iDestruct "contra" as ">[]".
- wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
  iIntros "!> _".
  iPoseProof (secret_atI _ kRP with "hon") as "sec".
  iMod (honest_public with "ctx sec phase fail") as "contra"; eauto.
  wp_pures. by iDestruct "contra" as ">[]".
wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
iIntros "!> _". wp_pures.
iApply ("Hpost" $! (Some (TKey Seal kI, mk_session_key Resp nR sI))).
iModIntro. iFrame. iExists kI.
rewrite /in_honest bool_decide_decide decide_True //.
do 3!iSplit => //; eauto.
by iApply mk_session_key_minted => //.
Qed.

End PK.
