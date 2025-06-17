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

Lemma public_msg1I kI kR nI :
  let sI := mk_key_share nI in
  pk_auth_ctx N -∗
  session_weak' N kI kR nI -∗
  minted nI -∗
  □ is_priv_key nI kI kR -∗
  aenc_key kI -∗
  public (TKey Seal kR) -∗
  public (TSeal (TKey Seal kR) (Spec.tag (Tag $ N.@"m1") (Spec.of_list [sI; TKey Seal kI]))).
Proof.
rewrite /=.
iIntros "(_ & #m1P & _ & _) #meta #s_nI #p_nI #aenc_kI #p_ekR".
iPoseProof (aenc_key_public with "aenc_kI") as "p_ekI".
iPoseProof (mk_key_share_secret_of with "s_nI p_nI") as "p_sI".
iApply public_TSealIS; eauto.
- iModIntro. iExists (mk_key_share nI), kI. do !iSplit => //.
  + iIntros "!> #?". iApply "p_sI". by eauto.
  + iRight. by iExists nI; eauto.
- rewrite minted_of_list /= mk_key_share_minted. by eauto.
iIntros "!> #p_dkR". rewrite public_of_list /=. do !iSplit => //.
iApply "p_sI". iModIntro. iRight. by iSplit.
Qed.

Lemma public_msg2E kI kR sI sR :
  pk_auth_ctx N -∗
  secret_of sI kI kR -∗
  public (TSeal (TKey Seal kI) (Spec.tag (Tag $ N.@"m2") (Spec.of_list [sI; sR; TKey Seal kR]))) -∗
  ▷ (minted sR ∧ secret_of sR kI kR ∧ resp_accepted N kI kR sI sR).
Proof.
iIntros "(_ & _ & #m2P & _) #started #p_m2".
iPoseProof (public_TSealE with "p_m2 m2P") as "{p_m2} [p_m2 | p_m2]".
- rewrite public_of_list /=.
  iDestruct "p_m2" as "(? & p_sI & p_sR & _ & _)".
  iSpecialize ("started" with "p_sI").
  iModIntro.
  iSplit; eauto.
  iSplit.
    iModIntro. by iSplit; eauto.
  by iLeft.
- iDestruct "p_m2" as "(#p_m2 & #s_m2 & #?)". rewrite minted_of_list /=.
  iModIntro.
  iDestruct "p_m2" as "(%sI' & %sR' & %kR' & %e_m2 & sRP & ?)".
  iDestruct "s_m2" as "(s_sI & s_sR & _)".
  case/Spec.of_list_inj: e_m2 => <- <- <-.
  do !iSplit => //.
Qed.

Lemma init_finish kI kR nI sR :
  let sI := mk_key_share nI in
  let kS := mk_session_key Init nI sR in
  pk_auth_ctx N -∗
  session_weak' N kI kR nI -∗
  minted nI -∗
  □ is_priv_key nI kI kR -∗
  secret_of sR kI kR -∗
  resp_accepted N kI kR sI sR -∗
  term_token nI (⊤ ∖ ↑N.@"success") -∗
  init_confirm kI kR ={⊤}=∗
  ▷ (□ confirmation Init kI kR kS ∗
     session_weak N Init kI kR kS ∗
     init_finished N kR sR ∗
     (corruption kI kR ∨
      session_key_meta_token N kI kR kS (↑N.@"init") ∗
      session_key N kI kR kS)).
Proof.
iIntros "%sI %kS (#ctx & _) #sess #s_nI #p_nI #p_sR #accepted token confirm".
iMod ("confirm" $! nI sR) as "#confirm".
iAssert (secret_of sI kI kR) as "p_sI".
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
iMod (session_begin _ Init nI nR (kI, kR) with "ctx [resp_token] token_sess")
  as "[#sessI _]".
- solve_ndisj.
- by iSplitR.
iModIntro. iModIntro. iFrame. iSplit; eauto. iSplitR.
  by iExists _, _; eauto.
iSplitR.
  iRight. iExists nI, nR, kI. do !iSplit => //; by eauto.
iRight. iSplitL.
  iExists nI, nR; by eauto.
iExists nI, nR; do !iSplit => //; eauto.
Qed.

Lemma public_msg3I kI kR sI sR :
  pk_auth_ctx N -∗
  public (TKey Seal kR) -∗
  minted sR -∗
  secret_of sR kI kR -∗
  init_finished N kR sR -∗
  public (TSeal (TKey Seal kR) (Spec.tag (Tag $ N.@"m3") sR)).
Proof.
iIntros "(_ & _ & _ & #p_m3) #p_eR #s_sR #p_sR #finished".
iApply public_TSealIS; eauto.
iIntros "!> #p_dkR". iApply "p_sR". iRight. by iSplit.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_pk_auth_init c kI kR :
  channel c -∗
  cryptis_ctx -∗
  pk_auth_ctx N -∗
  aenc_key kI -∗
  public (TKey Seal kR) -∗
  {{{ init_confirm kI kR }}}
    pk_auth_init N c mk_key_share_impl (mk_session_key_impl Init)
    kI (TKey Seal kR)
  {{{ okS, RET (repr okS);
      if okS is Some kS then
        minted kS ∗
        □ confirmation Init kI kR kS ∗
        session_weak N Init kI kR kS ∗
        (corruption kI kR ∨
          session_key_meta_token N kI kR kS (↑N.@"init") ∗
          session_key N kI kR kS)
      else True }}}.
Proof.
rewrite /pk_auth_init.
iIntros "#chan_c #ctx #ctx' #aenc_kI #p_kR %Ψ !> confirm Hpost".
wp_pures. wp_apply wp_pkey. wp_pures.
wp_bind (mk_key_share_impl _).
iApply (wp_mk_key_share kI kR) => //.
iIntros "!> %nI (#s_nI & #p_nI & token)".
rewrite (term_token_difference _ (↑N.@"success")); eauto.
iDestruct "token" as "[token_succ token]".
iMod (session_weak'_set N kI kR _ with "token_succ") as "#sess".
wp_pures.
iPoseProof (mk_key_share_secret_of with "s_nI p_nI") as "p_sI".
wp_list. wp_term_of_list. wp_apply wp_aenc. wp_pures.
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
iIntros "!> _". wp_pures. wp_apply wp_aenc. wp_pures. wp_bind (send _ _).
iApply wp_send => //.
  by iApply public_msg3I.
wp_pures. iApply ("Hpost" $! (Some (mk_session_key Init nI sR))).
iFrame. iModIntro. iSplit; eauto. by iApply mk_session_key_minted.
Qed.

End PK.
