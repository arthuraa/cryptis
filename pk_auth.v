From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics nown.
From cryptis Require Import role session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PK.

Context `{!heapGS Σ, !cryptisG Σ, !sessionG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).

Variable N : namespace.

Definition pk_auth_init : val :=
  λ: "c" "mk_key_share" "mk_sess_key" "skI" "pkI" "pkR",
  let: "nIsI" := "mk_key_share" #() in
  let: "nI"   := Fst "nIsI" in
  let: "sI"   := Snd "nIsI" in
  let: "m1"   := tenc (N.@"m1") "pkR" (term_of_list ["sI"; "pkI"]) in
  send "c" "m1";;
  bind: "m2"   := tdec (N.@"m2") "skI" (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["sI'"; "sR"; "pkR'"] := "m2" in
  assert: eq_term "sI'" "sI" && eq_term "pkR'" "pkR" in
  let: "k" := "mk_sess_key" "nI" "sR" in
  let: "m3" := tenc (N.@"m3") "pkR" "sR" in
  send "c" "m3";;
  SOME "k".

Definition pk_auth_resp : val :=
  λ: "c" "mk_key_share" "mk_sess_key" "skR" "pkR",
  bind: "m1" := tdec (N.@"m1") "skR" (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["sI"; "pkI"] := "m1" in
  bind: "kt" := is_key "pkI" in
  assert: "kt" = repr Enc in
  let: "nRsR" := "mk_key_share" #() in
  let: "nR" := Fst "nRsR" in
  let: "sR" := Snd "nRsR" in
  let: "m2" := tenc (N.@"m2") "pkI" (term_of_list ["sI"; "sR"; "pkR"]) in
  send "c" "m2";;
  bind: "m3" := tdec (N.@"m3") "skR" (recv "c") in
  assert: eq_term "m3" "sR" in
  let: "k" := "mk_sess_key" "nR" "sI" in
  SOME ("pkI", "k").

(** We are going to use the following naming conventions:

- [kI], [kR]: The identities of the initiator of the protocol and of the
  responder.  A nonce used to generate their key pair.

- [nI], [sI]: The private key generated by the initiator, and the corresponding
  key share.  In the case of a traditional NSL protocol, [sI = nI], so the
  private key is actually known to the responder.  In the case of a
  Diffie-Hellman exchange, the two will be different.

- [nR], [sR]: Similar, but for the responder.

- [kS]: A session key generated from the keying material exchanged by the
  parties. *)

Definition corruption kI kR : iProp :=
  pterm (TKey Dec kI) ∨ pterm (TKey Dec kR).

Global Instance corruptionC : Comm (⊣⊢) corruption.
Proof. by move=> k k'; rewrite /corruption [(_ ∨ _)%I]comm. Qed.

Global Instance corruption_persistent kI kR :
  Persistent (corruption kI kR).
Proof. apply _. Qed.

(** [readable_by t kI kR] *)
Definition readable_by t kI kR : iProp :=
  □ (corruption kI kR → pterm t).

#[global]
Instance readable_by_persistent t kI kR : Persistent (readable_by t kI kR).
Proof. apply _. Qed.

Definition secret_of t kI kR : iProp :=
  □ (pterm t ↔ ▷ corruption kI kR).

#[global]
Instance secret_of_persistent t kI kR : Persistent (secret_of t kI kR).
Proof. apply _. Qed.

Class PK := {
  is_priv_key : term → term → term → iProp;
  is_priv_key_persistent :>
    ∀ n kI kR, Persistent (is_priv_key n kI kR);

  mk_key_share : term → term;

  mk_key_share_inj :> Inj (=) (=) mk_key_share;

  mk_key_share_sterm :
    ∀ n, sterm (mk_key_share n) ⊣⊢ sterm n;

  mk_key_share_secret_of :
    ∀ n kI kR, sterm n -∗ is_priv_key n kI kR -∗
    secret_of (mk_key_share n) kI kR;

  mk_session_key : role → term → term → term;

  mk_session_keyC :
    ∀ nI nR, mk_session_key Init nI (mk_key_share nR) =
             mk_session_key Resp nR (mk_key_share nI);

  mk_session_key_sterm :
    ∀ rl t1 t2, sterm t1 -∗ sterm t2 -∗ sterm (mk_session_key rl t1 t2);

  mk_key_share_impl : val;
  wp_mk_key_share : ∀ E kI kR,
    {{{ True }}}
      mk_key_share_impl #() @ E
    {{{ (n : term), RET (n, mk_key_share n) : val;
        sterm n ∗ is_priv_key n kI kR ∗
        nonce_meta_token n ⊤
    }}};

  mk_session_key_impl : role → val;
  wp_mk_session_key : ∀ E rl (n s : term),
    {{{ True }}}
      mk_session_key_impl rl n s @ E
    {{{ RET mk_session_key rl n s : val; True}}};

}.

Context `{!PK}.

Definition session_ress rl nI nR (_ : term * term) : iProp :=
  if rl is Init then nonce_meta_token nI (↑N.@"token".@Resp)
  else True.

Definition init_started kI kR sI : iProp :=
  pterm sI ∨ ∃ nI, ⌜sI = mk_key_share nI⌝ ∗ is_priv_key nI kI kR.

Definition msg1_pred kR m1 : iProp :=
  ∃ sI kI,
    ⌜m1 = Spec.of_list [sI; TKey Enc kI]⌝ ∧
    pterm (TKey Enc kI) ∧
    readable_by sI kI kR ∧
    init_started kI kR sI.

Definition resp_accepted kI kR sI sR : iProp :=
  pterm sI ∨
  ∃ nI nR,
    ⌜sI = mk_key_share nI⌝ ∧
    ⌜sR = mk_key_share nR⌝ ∧
    is_priv_key nR kI kR ∧
    session (N.@"session") Resp nI nR (kI, kR).

Definition resp_waiting kI kR sI nR : iProp :=
  pterm sI ∗ nonce_meta_token nR ⊤ ∨
  ∃ nI,
    ⌜sI = mk_key_share nI⌝ ∧
    session (N.@"session") Resp nI nR (kI, kR) ∧
    waiting_for_peer (N.@"session") session_ress Resp nI nR (kI, kR).

Definition msg2_pred kI m2 : iProp :=
  ∃ sI sR kR,
    ⌜m2 = Spec.of_list [sI; sR; TKey Enc kR]⌝ ∧
    secret_of sR kI kR ∧
    resp_accepted kI kR sI sR.

Definition init_finished kR sR : iProp :=
  pterm sR ∨
  ∃ nI nR kI,
    ⌜sR = mk_key_share nR⌝ ∧
    is_priv_key nI kI kR ∧
    is_priv_key nR kI kR ∧
    session (N.@"session") Init nI nR (kI, kR) ∧
    session (N.@"session") Resp nI nR (kI, kR).

Definition msg3_pred := init_finished.

Definition session_key_token rl kS : iProp :=
  ∃ nI nR, ⌜kS = mk_session_key Init nI (mk_key_share nR)⌝ ∗
           nonce_meta_token nI (↑N.@"token".@rl).

Definition session_key kI kR kS : iProp :=
  ∃ nI nR,
    ⌜kS = mk_session_key Init nI (mk_key_share nR)⌝ ∗
    is_priv_key nI kI kR ∗
    is_priv_key nR kI kR ∗
    session (N.@"session") Init nI nR (kI, kR) ∗
    session (N.@"session") Resp nI nR (kI, kR).

Global Instance session_key_persistent kI kR kS :
  Persistent (session_key kI kR kS).
Proof. apply _. Qed.

Definition ctx : iProp :=
  session_ctx (N.@"session") session_ress ∧
  enc_pred (N.@"m1") msg1_pred ∧
  enc_pred (N.@"m2") msg2_pred ∧
  enc_pred (N.@"m3") msg3_pred.

Lemma pk_auth_alloc E E' :
  ↑N ⊆ E →
  nown_token session_name (↑N.@"session") -∗
  enc_pred_token E ={E'}=∗ ctx.
Proof.
iIntros (sub) "token1 token2".
iMod (session_alloc _ session_ress with "token1") as "#H0"; eauto.
rewrite (enc_pred_token_difference (↑N.@"m1") E); last solve_ndisj.
iDestruct "token2" as "[t1 token2]".
iMod (enc_pred_set (N.@"m1") msg1_pred with "t1") as "#H1" => //.
rewrite (enc_pred_token_difference (↑N.@"m2")); last solve_ndisj.
iDestruct "token2" as "[t2 token2]".
iMod (enc_pred_set (N.@"m2") msg2_pred with "t2") as "#H2" => //.
rewrite (enc_pred_token_difference (↑N.@"m3")); last solve_ndisj.
iDestruct "token2" as "[t3 token2]".
iMod (enc_pred_set (N.@"m3") msg3_pred with "t3") as "#H3" => //.
by iModIntro; do !iSplit => //.
Qed.

Global Instance persistent_ctx : Persistent ctx.
Proof. apply _. Qed.

Lemma pterm_msg1I kI kR nI :
  let sI := mk_key_share nI in
  ctx -∗
  sterm nI -∗
  is_priv_key nI kI kR -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  pterm (TEnc kR (Spec.tag (N.@"m1") (Spec.of_list [sI; TKey Enc kI]))).
Proof.
iIntros "(_ & #m1P & _ & _) #s_nI #p_nI #p_ekI #p_ekR".
iPoseProof (mk_key_share_secret_of with "s_nI p_nI") as "p_sI".
iApply pterm_TEncIS; eauto.
- by iApply pterm_sterm.
- iModIntro. iExists (mk_key_share nI), kI. do !iSplit => //.
  + iIntros "!> #?". iApply "p_sI". by eauto.
  + iRight. by iExists nI; eauto.
- rewrite sterm_of_list /= mk_key_share_sterm.
  do !iSplit => //. by iApply pterm_sterm.
iIntros "!> #p_dkR". rewrite pterm_of_list /=. do !iSplit => //.
iApply "p_sI". iModIntro. by iRight.
Qed.

Lemma pterm_msg1E kI kR sI :
  ctx -∗
  pterm (TEnc kR (Spec.tag (N.@"m1") (Spec.of_list [sI; TKey Enc kI]))) -∗
  ▷ (sterm sI ∧ pterm (TKey Enc kI) ∧ readable_by sI kI kR ∧
     init_started kI kR sI).
Proof.
iIntros "(_ & #m1P & _ & _) #p_m1".
iPoseProof (pterm_TEncE with "p_m1 m1P") as "{p_m1} [p_m1 | p_m1]".
- iModIntro. rewrite pterm_of_list /=.
  iDestruct "p_m1" as "(? & ? & ? & _)". iSplit => //.
    by iApply pterm_sterm.
  iSplit; eauto.
  iSplit.
    by iIntros "!> ?".
  by iLeft.
- iDestruct "p_m1" as "{m1P} (#m1P & #s_m1 & #p_m1)".
  iModIntro.
  iDestruct "m1P" as "(%sI' & %kI' & %e_m1 & p_pkI & p_sI & accepted)".
  case/Spec.of_list_inj: e_m1 => <- <-.
  rewrite sterm_of_list /=. iDestruct "s_m1" as "(#s_sI & _)".
  do !iSplit => //.
Qed.

Lemma resp_accept E kI kR sI nR :
  ↑N ⊆ E →
  nonce_meta_token nR ⊤ -∗
  ctx -∗
  is_priv_key nR kI kR -∗
  init_started kI kR sI ={E}=∗
  resp_waiting kI kR sI nR ∗
  resp_accepted kI kR sI (mk_key_share nR).
Proof.
iIntros (?) "token (#ctx & _) #p_nR [#fail|(%nI & -> & #p_nI)]".
  iModIntro. iSplitL; iLeft => //.
  by iFrame.
rewrite (term_meta_token_difference _ (↑N.@"session")) //.
iDestruct "token" as "[token _]".
iMod (session_begin _ Resp nI nR (kI, kR)
       with "ctx [//] token") as "[#sessR waiting]".
  solve_ndisj.
iModIntro. iSplitL.
  iRight. iExists nI. by eauto.
iRight. iExists nI, nR. by eauto.
Qed.

Lemma pterm_msg2I kI kR sI sR :
  ctx -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  sterm sI -∗
  readable_by sI kI kR -∗
  sterm sR -∗
  secret_of sR kI kR -∗
  resp_accepted kI kR sI sR -∗
  pterm (TEnc kI (Spec.tag (N.@"m2") (Spec.of_list [sI; sR; TKey Enc kR]))).
Proof.
iIntros "(_ & _ & #? & _) #p_eI #p_eR #s_sI #p_sI #s_sR #p_sR #accepted".
iApply pterm_TEncIS; eauto.
- by iApply pterm_sterm.
- iModIntro. iExists sI, sR, kR. by eauto.
- rewrite sterm_of_list /=. do ![iSplit => //].
  by iApply pterm_sterm.
iIntros "!> #p_dkI". rewrite pterm_of_list /=. do !iSplit => //.
- by iApply "p_sI"; iLeft.
- iApply "p_sR". iModIntro. by iLeft.
Qed.

Lemma pterm_msg2E kI kR sI sR :
  ctx -∗
  secret_of sI kI kR -∗
  pterm (TEnc kI (Spec.tag (N.@"m2") (Spec.of_list [sI; sR; TKey Enc kR]))) -∗
  ▷ (sterm sR ∧ secret_of sR kI kR ∧ resp_accepted kI kR sI sR).
Proof.
iIntros "(_ & _ & #m2P & _) #started #p_m2".
iPoseProof (pterm_TEncE with "p_m2 m2P") as "{p_m2} [p_m2 | p_m2]".
- rewrite pterm_of_list /=.
  iDestruct "p_m2" as "(? & p_sI & p_sR & _ & _)".
  iSpecialize ("started" with "p_sI").
  iModIntro.
  iSplit; first by iApply pterm_sterm.
  iSplit.
    iModIntro. by iSplit; eauto.
  by iLeft.
- iDestruct "p_m2" as "(#p_m2 & #s_m2 & #?)". rewrite sterm_of_list /=.
  iModIntro.
  iDestruct "p_m2" as "(%sI' & %sR' & %kR' & %e_m2 & sRP & ?)".
  iDestruct "s_m2" as "(s_sI & s_sR & _)".
  case/Spec.of_list_inj: e_m2 => <- <- <-.
  do !iSplit => //.
Qed.

Lemma init_finish E kI kR nI sR :
  let sI := mk_key_share nI in
  let kS := mk_session_key Init nI sR in
  ↑N ⊆ E →
  ctx -∗
  sterm nI -∗
  is_priv_key nI kI kR -∗
  secret_of sR kI kR -∗
  resp_accepted kI kR sI sR -∗
  nonce_meta_token nI ⊤ ={E}=∗
  ▷ (init_finished kR sR ∗
     (corruption kI kR ∨ session_key_token Init kS ∗ session_key kI kR kS)).
Proof.
iIntros "%sI %kS % (#ctx & _) #s_nI #p_nI #p_sR #accepted token".
iAssert (secret_of sI kI kR) as "p_sI".
  by iApply mk_key_share_secret_of.
rewrite (term_meta_token_difference _ (↑N.@"token")) //.
set T := N.@"token".
iDestruct "token" as "[token fresh]".
rewrite (term_meta_token_difference _ (↑N.@"session") (_ ∖ _)); last first.
  solve_ndisj.
set S := N.@"session".
iDestruct "fresh" as "[fresh _]".
rewrite (term_meta_token_difference _ (↑T.@Init) (↑T)); last first.
  solve_ndisj.
iDestruct "token" as "[token_init token]".
rewrite (term_meta_token_difference _ (↑T.@Resp) (_ ∖ _)); last first.
  solve_ndisj.
iDestruct "token" as "[token_resp _]".
iDestruct "accepted" as "[fail|accepted]".
  iPoseProof ("p_sI" with "fail") as "fail'".
  iModIntro. iModIntro. iSplit.
    iLeft. iApply "p_sR". by iApply "p_sI".
  by eauto.
iDestruct "accepted" as "(%nI' & %nR & %e_sI & -> & p_nR & accepted)".
move/mk_key_share_inj: e_sI => <-.
iMod (session_begin _ Init nI nR (kI, kR)
       with "ctx token_resp fresh") as "[#sessI _]".
  solve_ndisj.
iModIntro. iModIntro. iSplitR.
  iRight. iExists nI, nR, kI. by eauto.
iRight. iSplitL.
  iExists nI, nR; by eauto.
by iExists nI, nR; eauto.
Qed.

Lemma pterm_msg3I kI kR sI sR :
  ctx -∗
  pterm (TKey Enc kR) -∗
  sterm sR -∗
  secret_of sR kI kR -∗
  init_finished kR sR -∗
  pterm (TEnc kR (Spec.tag (N.@"m3") sR)).
Proof.
iIntros "(_ & _ & _ & #p_m3) #p_eR #s_sR #p_sR #finished".
iApply pterm_TEncIS => //.
  by iApply pterm_sterm.
iIntros "!> #p_dkR". iApply "p_sR". by iRight.
Qed.

Lemma pterm_msg3E kI kR sR :
  ctx -∗
  secret_of sR kI kR -∗
  pterm (TEnc kR (Spec.tag (N.@"m3") sR)) -∗
  ▷ init_finished kR sR.
Proof.
iIntros "(_ & _ & _ & #?) #p_sR #p_m3".
iDestruct (pterm_TEncE with "p_m3 [//]") as "{p_m3} [p_m3|p_m3]".
- iDestruct "p_m3" as "[_ p_m3]". by iLeft.
- by iDestruct "p_m3" as "(#p_m3 & _)".
Qed.

Lemma resp_finish E kI kR sI nR :
  let sR := mk_key_share nR in
  let kS := mk_session_key Resp nR sI in
  ↑N ⊆ E →
  ctx -∗
  sterm nR -∗
  is_priv_key nR kI kR -∗
  init_finished kR sR -∗
  resp_waiting kI kR sI nR ={E}=∗
  ▷ (corruption kI kR ∨ session_key_token Resp kS ∗ session_key kI kR kS).
Proof.
iIntros "%sR %kS % #(ctx & _) #s_nR #p_nR [#fail|#finished] waiting".
  iPoseProof (mk_key_share_secret_of with "s_nR p_nR") as "p_sR".
  iModIntro. iLeft. by iApply "p_sR".
iDestruct "finished"
  as "(%nI' & %nR' & %kI' & %e_sR & p_nI & _ & sessI & sessR')".
move/mk_key_share_inj: e_sR => <- {nR'}.
iDestruct "waiting" as "[[#fail token]|waiting]".
  by iDestruct (session_not_ready with "ctx sessR' token") as "[]"; eauto.
iDestruct "waiting" as "(%nI & -> & #sessR & waiting)".
iPoseProof (session_agree with "sessR sessR'") as "{sessR'} %e" => //.
case: e => <- <-.
iMod ("waiting" with "[] sessI") as "finished".
  solve_ndisj.
iModIntro. iModIntro. iRight. iSplitL.
  iExists nI, nR. rewrite mk_session_keyC. by eauto.
iExists nI, nR. by rewrite mk_session_keyC; eauto.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Lemma wp_pk_auth_init c kI kR E :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  ctx -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  {{{ True }}}
    pk_auth_init c mk_key_share_impl (mk_session_key_impl Init)
    (TKey Dec kI) (TKey Enc kI) (TKey Enc kR) @ E
  {{{ okS, RET (repr okS);
      if okS is Some kS then
        sterm kS ∗
        (corruption kI kR ∨ session_key_token Init kS ∗ session_key kI kR kS)
      else True }}}.
Proof.
rewrite /pk_auth_init.
iIntros (??) "#chan_c #ctx #p_kI #p_kR %Ψ !> _ Hpost".
wp_pures. wp_bind (mk_key_share_impl _).
iApply (wp_mk_key_share _ kI kR) => //.
iIntros "!> %nI (#s_nI & #p_nI & token)". wp_pures.
iPoseProof (mk_key_share_secret_of with "s_nI p_nI") as "p_sI".
wp_list. wp_term_of_list. wp_tenc => /=. wp_pures.
wp_bind (send _ _). iApply wp_send; eauto.
  by iApply pterm_msg1I.
wp_pures. wp_bind (recv _). iApply wp_recv; eauto.
iIntros "%m2 #p_m2". wp_tdec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_list_match => [sI' sR pkR' {m2} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst sI'.
wp_eq_term e; last protocol_failure; subst pkR'.
iPoseProof (pterm_msg2E with "[//] [//] [//]")
  as "{p_m2} (s_sR & p_sR & accepted)".
wp_pures.
iMod (init_finish with "ctx s_nI p_nI p_sR accepted token")
  as "(#finished & session)"; eauto.
wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
iIntros "!> _". wp_pures. wp_tenc. wp_pures. wp_bind (send _ _).
iApply wp_send => //.
  by iApply pterm_msg3I.
wp_pures. iApply ("Hpost" $! (Some (mk_session_key Init nI sR))).
iFrame. iModIntro. by iApply mk_session_key_sterm.
Qed.

Lemma wp_pk_auth_resp c kR E :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  ctx -∗
  pterm (TKey Enc kR) -∗
  {{{ True }}}
    pk_auth_resp c mk_key_share_impl (mk_session_key_impl Resp)
      (TKey Dec kR) (TKey Enc kR) @ E
  {{{ res, RET (repr res);
      if res is Some (pkI, kS) then
         ∃ kI, ⌜pkI = TKey Enc kI⌝ ∧
               pterm pkI ∧
               sterm kS ∧
               (corruption kI kR ∨
                session_key_token Resp kS ∗
                session_key kI kR kS)
       else True }}}.
Proof.
iIntros (??) "#? #ctx #e_kR %Ψ !> _ Hpost".
iPoseProof "ctx" as "(inv & _)".
rewrite /pk_auth_resp; wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#Hm1".
wp_tdec m1; last protocol_failure.
wp_list_of_term m1; last protocol_failure.
wp_list_match => [sI pkI {m1} ->|_]; last protocol_failure.
wp_is_key_eq kt kI et; last protocol_failure; subst pkI.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Enc)); last protocol_failure.
case: kt => // _.
iDestruct (pterm_msg1E with "[] Hm1")
  as "{Hm1} (s_sI & p_eI & p_sI & started)"; eauto.
wp_pures.
wp_bind (mk_key_share_impl _). iApply (wp_mk_key_share _ kI kR) => //.
iIntros "!> %nR (#s_nR & #p_nR & token)".
iMod (resp_accept with "token [//] [//] [//]")
  as "[waiting #accepted]" => //.
wp_pures. wp_list; wp_term_of_list. wp_tenc. wp_pures.
iAssert (secret_of (mk_key_share nR) kI kR) as "p_sR".
  by iApply mk_key_share_secret_of.
wp_bind (send _ _). iApply wp_send => //.
  iApply pterm_msg2I; eauto.
  by iApply mk_key_share_sterm.
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m3 #p_m3". wp_tdec m3; last protocol_failure.
wp_eq_term e; last protocol_failure; subst m3.
iPoseProof (pterm_msg3E with "[//] [//] [//]") as "finished".
wp_pures.
iMod (resp_finish with "[] [] [] [] waiting") as "?" => //.
wp_bind (mk_session_key_impl _ _ _). iApply wp_mk_session_key => //.
iIntros "!> _". wp_pures.
iApply ("Hpost" $! (Some (TKey Enc kI, mk_session_key Resp nR sI))).
iModIntro. iExists kI. do 3!iSplit => //.
by iApply mk_session_key_sterm => //.
Qed.

End PK.
