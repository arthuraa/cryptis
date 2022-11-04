From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics nown.
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

Lemma public_msg1I n T kI kR nI :
  let sI := mk_key_share nI in
  pk_auth_ctx N -∗
  session_weak' N kI kR nI n T -∗
  minted nI -∗
  □ is_priv_key nI kI kR -∗
  public (TKey Enc kI) -∗
  public (TKey Enc kR) -∗
  public (TEnc kR (Spec.tag (N.@"m1") (Spec.of_list [sI; TKey Enc kI]))).
Proof.
iIntros "(_ & #m1P & _ & _) #meta #s_nI #p_nI #p_ekI #p_ekR".
iPoseProof (mk_key_share_secret_of with "s_nI p_nI") as "p_sI".
iApply public_TEncIS; eauto.
- iModIntro. iExists (mk_key_share nI), kI. do !iSplit => //.
  + iIntros "!> #?". iApply "p_sI". by eauto.
  + iRight. by iExists n, T, nI; eauto.
- rewrite minted_of_list /= mk_key_share_minted. by eauto.
iIntros "!> #p_dkR". rewrite public_of_list /=. do !iSplit => //.
iApply "p_sI". iModIntro. by iRight.
Qed.

Lemma public_msg2E kI kR sI sR :
  pk_auth_ctx N -∗
  secret_of sI kI kR -∗
  public (TEnc kI (Spec.tag (N.@"m2") (Spec.of_list [sI; sR; TKey Enc kR]))) -∗
  ▷ (minted sR ∧ secret_of sR kI kR ∧ resp_accepted N kI kR sI sR).
Proof.
iIntros "(_ & _ & #m2P & _) #started #p_m2".
iPoseProof (public_TEncE with "p_m2 m2P") as "{p_m2} [p_m2 | p_m2]".
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

Lemma init_finish dq n T E kI kR nI sR :
  let sI := mk_key_share nI in
  let kS := mk_session_key Init nI sR in
  ↑N ⊆ E →
  pk_auth_ctx N -∗
  ●H{dq|n} T -∗
  session_weak' N kI kR nI n T -∗
  minted nI -∗
  □ is_priv_key nI kI kR -∗
  secret_of sR kI kR -∗
  resp_accepted N kI kR sI sR -∗
  nonce_meta_token nI (⊤ ∖ ↑N.@"success") -∗
  init_confirm kI kR ={E}=∗
  ▷ (●H{dq|n} T ∗
     □ confirmation Init kI kR kS ∗
     session_weak N Init kI kR kS n T ∗
     init_finished N kR sR ∗
     (corruption kI kR ∨
      session_key_meta_token N Init kI kR kS ⊤ ∗
      session_key N kI kR kS n T)).
Proof.
iIntros "%sI %kS % (#ctx & _) hon #sess #s_nI #p_nI #p_sR #accepted token confirm".
iMod ("confirm" $! nI sR) as "#confirm".
iAssert (secret_of sI kI kR) as "p_sI".
  by iApply mk_key_share_secret_of.
rewrite (term_meta_token_difference _ (↑N.@"token")) //; last solve_ndisj.
set TK := N.@"token".
iDestruct "token" as "[token_token token]".
rewrite (term_meta_token_difference _ (↑N.@"session") (_ ∖ _)); last first.
  solve_ndisj.
set S := N.@"session".
iDestruct "token" as "[token_sess token]".
rewrite (term_meta_token_difference _ (↑TK.@Init) (↑TK)); last first.
  solve_ndisj.
iDestruct "token_token" as "[token_init token_token]".
rewrite (term_meta_token_difference _ (↑TK.@Resp) (_ ∖ _)); last first.
  solve_ndisj.
iDestruct "token_token" as "[token_resp _]".
iDestruct "accepted" as "[fail|accepted]".
  iPoseProof ("p_sI" with "fail") as "fail'".
  iModIntro. iModIntro. iFrame. iSplit; eauto. iSplit.
    iExists _, _; eauto.
  iSplit; eauto.
  iLeft. iApply "p_sR". by iApply "p_sI".
iDestruct "accepted"
  as "(%n' & %T' & %n'' & %T'' & %nI' & %nR & %n''n' &
       #sess' & #sess'' &
       %e_sI & -> & #p_nR & #accepted & confirmed)".
move/mk_key_share_inj: e_sI => <-.
iDestruct (session_weak'_agree with "sess' sess") as "(_ & _ & -> & ->)".
iAssert (⌜n' = n ∧ T = T'⌝)%I as "#[-> <-]".
  iDestruct "sess''" as "[hon' _]".
  iPoseProof (honest_auth_frag_agree with "hon hon'") as "#[%n'n %T'T]".
  iSplit; last by eauto.
  iPureIntro; lia.
iMod (session_begin _ Init nI nR (kI, kR) with "ctx [token_resp] token_sess")
  as "[#sessI _]".
- solve_ndisj.
- by iSplitR.
iMod (own_alloc (reservation_map_token ⊤)) as "(%γ & map)".
  by apply reservation_map_token_valid.
iMod (term_meta_set _ _ γ (TK.@Init) with "token_init") as "#meta" => //.
iModIntro. iModIntro. iFrame. iSplit; eauto. iSplitR.
  by iExists _, _; eauto.
iSplitR.
  iRight. iExists nI, nR, kI, n, T. do !iSplit => //; by eauto.
iRight. iSplitL.
  iExists nI, nR, γ; by eauto.
iExists nI, nR; do !iSplit => //; eauto.
Qed.

Lemma public_msg3I kI kR sI sR :
  pk_auth_ctx N -∗
  public (TKey Enc kR) -∗
  minted sR -∗
  secret_of sR kI kR -∗
  init_finished N kR sR -∗
  public (TEnc kR (Spec.tag (N.@"m3") sR)).
Proof.
iIntros "(_ & _ & _ & #p_m3) #p_eR #s_sR #p_sR #finished".
iApply public_TEncIS; eauto.
iIntros "!> #p_dkR". iApply "p_sR". by iRight.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_pk_auth_init c kI kR dq n T E :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  pk_auth_ctx N -∗
  public (TKey Enc kI) -∗
  public (TKey Enc kR) -∗
  {{{ init_confirm kI kR ∗ ●H{dq|n} T }}}
    pk_auth_init N c mk_key_share_impl (mk_session_key_impl Init)
    (TKey Dec kI) (TKey Enc kI) (TKey Enc kR) @ E
  {{{ okS, RET (repr okS);
      ●H{dq|n} T ∗
      if okS is Some kS then
        minted kS ∗
        □ confirmation Init kI kR kS ∗
        session_weak N Init kI kR kS n T ∗
        if in_honest kI kR T then
          session_key_meta_token N Init kI kR kS ⊤ ∗
          session_key N kI kR kS n T
        else True
      else True }}}.
Proof.
rewrite /pk_auth_init /in_honest bool_decide_decide.
iIntros (??) "#chan_c #ctx #ctx' #p_kI #p_kR %Ψ !> [confirm hon] Hpost".
wp_pures. wp_bind (mk_key_share_impl _).
iApply (wp_mk_key_share _ kI kR) => //.
iIntros "!> %nI (#s_nI & #p_nI & token)".
rewrite (term_meta_token_difference _ (↑N.@"success")); eauto.
iDestruct "token" as "[token_succ token]".
iMod (session_weak'_set N kI kR _ _ _ with "[#] token_succ") as "#sess".
  by iApply honest_auth_frag.
wp_pures.
iPoseProof (mk_key_share_secret_of with "s_nI p_nI") as "p_sI".
wp_list. wp_term_of_list. wp_tenc => /=. wp_pures.
wp_bind (send _ _). iApply (wp_send with "[] [#]"); eauto.
  by iApply (public_msg1I with "[]"); eauto.
wp_pures. wp_bind (recv _). iApply wp_recv; eauto.
iIntros "%m2 #p_m2". wp_tdec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_list_match => [sI' sR pkR' {m2} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst sI'.
wp_eq_term e; last protocol_failure; subst pkR'.
iPoseProof (public_msg2E with "[//] [//] [//]")
  as "{p_m2} (s_sR & p_sR & accepted)".
wp_pures.
iMod (init_finish with "ctx' hon sess s_nI p_nI p_sR accepted token confirm")
  as "(hon & #confirmed & #sess_weak & #finished & session)"; eauto.
wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
iIntros "!> _". wp_pures. wp_tenc. wp_pures. wp_bind (send _ _).
iApply wp_send => //.
  by iApply public_msg3I.
case: decide => [[kIP kRP]|_]; last first.
  wp_pures. iApply ("Hpost" $! (Some (mk_session_key Init nI sR))).
  iFrame. iModIntro. iSplit; eauto. by iApply mk_session_key_minted.
iDestruct "session" as "[[#fail|#fail]|session]".
- iMod (honest_public with "ctx hon fail") as "#contra"; eauto; try solve_ndisj.
  wp_pures. iDestruct "contra" as ">[]".
- iMod (honest_public with "ctx hon fail") as "#contra"; eauto; try solve_ndisj.
  wp_pures. iDestruct "contra" as ">[]".
wp_pures. iApply ("Hpost" $! (Some (mk_session_key Init nI sR))).
iFrame. iModIntro. iSplit; eauto. by iApply mk_session_key_minted.
Qed.

End PK.
