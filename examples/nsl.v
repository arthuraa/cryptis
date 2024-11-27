From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSL.

Context `{!heapGS Σ, !spawnG Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).

Definition nslN := nroot.@"nsl".

Definition nsl_session kI kR t : iProp :=
  term_meta t (nroot.@"data") (kI, kR) ∗
  □ (public (TKey Dec kI) → ▷ False) ∗
  □ (public (TKey Dec kR) → ▷ False) ∗
  □ (public t → ▷^2 False).

Lemma nsl_session_agree t kI1 kR1 kI2 kR2 :
  nsl_session kI1 kR1 t -∗
  nsl_session kI2 kR2 t -∗
  ⌜kI1 = kI2 ∧ kR1 = kR2⌝.
Proof.
iIntros "(#meta1 & _) (#meta2 & _)".
iPoseProof (term_meta_agree with "meta1 meta2") as "%e".
by case: e => -> ->.
Qed.

Lemma nsl_session_public_key kI kR t :
  nsl_session kI kR t -∗
  public t -∗
  ▷^2 False.
Proof. iIntros "(_ & _ & _ & #H) #p_t". by iApply "H". Qed.

Lemma nsl_session_alloc kI kR t :
  term_token t (⊤ ∖ ↑nroot.@"resp" ∖ ↑nroot.@"data") -∗
  term_meta t (nroot.@"data") (kI, kR) -∗
  □ (public (TKey Dec kI) → ▷ False) -∗
  □ (public (TKey Dec kR) → ▷ False) -∗
  □ (public t ↔ ▷ □ (public (TKey Dec kI) ∨ public (TKey Dec kR))) ==∗
  term_token t (↑nroot.@"init") ∗
  nsl_session kI kR t.
Proof.
iIntros "token #data #s_dkI #s_dkR #s_t".
iAssert (□ (public t → ▷^2 False))%I as "{s_t} #s_t".
{ iIntros "!> #p_t".
  by iDestruct ("s_t" with "p_t") as "#[#fail|#fail]"; iNext;
  [iApply "s_dkI"|iApply "s_dkR"]. }
iPoseProof (term_token_drop (E1 := ↑nroot.@"init") with "token")
  as "token"; first solve_ndisj.
iFrame. iModIntro. by do !iSplit => //.
Qed.

(*

A --> B: {m1; nA; pkA}@pkB
B --> A: {m2; nA; nB; pkB}@pkA
A --> B: {m3; nB}@pkB

*)

Definition init : val := λ: "c" "skI" "pkI" "pkR",
  let: "nI" := mknonce #() in
  let: "m1" := tenc (nslN.@"m1") "pkR" (term_of_list ["nI"; "pkI"]) in
  send "c" "m1";;
  bind: "m2"   := tdec (nslN.@"m2") "skI" (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nI'"; "nR"; "pkR'"] := "m2" in
  guard: eq_term "nI'" "nI" && eq_term "pkR'" "pkR" in
  let: "m3" := tenc (nslN.@"m3") "pkR" "nR" in
  send "c" "m3";;
  SOME "nR".

Definition resp : val := λ: "c" "skR" "pkR",
  bind: "m1" := tdec (nslN.@"m1") "skR" (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["nI"; "pkI"] := "m1" in
  bind: "kt" := is_key "pkI" in
  guard: "kt" = repr Enc in
  let: "nR" := mknonce #() in
  let: "m2" := tenc (nslN.@"m2") "pkI" (term_of_list ["nI"; "nR"; "pkR"]) in
  send "c" "m2";;
  bind: "m3" := tdec (nslN.@"m3") "skR" (recv "c") in
  guard: eq_term "m3" "nR" in
  SOME ("pkI", "nR").

Definition msg1_pred kR m1 : iProp := ∃ nI kI,
  ⌜m1 = Spec.of_list [nI; TKey Enc kI]⌝ ∧
  public (TKey Enc kI) ∧
  (public nI ↔ ▷ □ (public (TKey Dec kI) ∨ public (TKey Dec kR))).

Definition msg2_pred kI m2 : iProp := ∃ nI nR kR,
  ⌜m2 = Spec.of_list [nI; nR; TKey Enc kR]⌝ ∧
  (public (TKey Dec kR) → ▷ False) ∧
  (public nR ↔ ▷ □ (public (TKey Dec kI) ∨ public (TKey Dec kR))) ∧
  term_meta nR (nroot.@"data") (kI, kR) ∧
  escrow nslN (term_token nI (↑nroot))
    (term_token nR (⊤ ∖ ↑nroot.@"resp" ∖ ↑nroot.@"data")).

Definition msg3_pred kR nR : iProp :=
  ∃ kI, term_meta nR (nroot.@"data") (kI, kR) ∧
        nsl_session kI kR nR.

Definition nsl_ctx : iProp :=
  enc_pred (nslN.@"m1") msg1_pred ∧
  enc_pred (nslN.@"m2") msg2_pred ∧
  enc_pred (nslN.@"m3") msg3_pred.

Lemma nsl_alloc E1 E2 :
  ↑nslN ⊆ E1 →
  enc_pred_token E1 ={E2}=∗
  nsl_ctx ∗
  enc_pred_token (E1 ∖ ↑nslN).
Proof.
iIntros (sub1) "t1".
rewrite (enc_pred_token_difference (↑nslN) E1) //. iDestruct "t1" as "[t1 t1']".
iMod (enc_pred_set (nslN.@"m1") msg1_pred with "t1")
  as "[#H1 t1]"; try solve_ndisj.
iMod (enc_pred_set (nslN.@"m2") msg2_pred with "t1")
  as "[#H2 t1]"; try solve_ndisj.
iMod (enc_pred_set (nslN.@"m3") msg3_pred with "t1")
  as "[#H3 t1]"; try solve_ndisj.
iModIntro; iFrame; do !iSplit => //.
Qed.

Global Instance nsl_ctx_persistent : Persistent nsl_ctx.
Proof. apply _. Qed.

Lemma init_send_1 kI kR nI :
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Enc kI) -∗
  public (TKey Enc kR) -∗
  minted nI -∗
  □ (public nI ↔ ▷ □ (public (TKey Dec kI) ∨ public (TKey Dec kR))) -∗
  public (TEnc (TKey Enc kR) (Spec.tag (nslN.@"m1") (Spec.of_list [nI; TKey Enc kI]))).
Proof.
iIntros "#? (#? & _ & _) #p_ekI #p_ekR #m_nI #p_nI".
iApply public_TEncIS; eauto.
- iModIntro. by iExists _, _; iSplit; eauto.
- by rewrite minted_of_list /=; eauto.
- rewrite public_of_list /=. iIntros "!> #p_dkR".
  do 2?iSplit => //. iApply "p_nI". by eauto.
Qed.

Lemma resp_recv_1_send_2 kI kR nI nR :
  public (TEnc (TKey Enc kR)
            (Spec.tag (nslN.@"m1")
               (Spec.of_list [nI; TKey Enc kI]))) -∗
  term_token nR ⊤ -∗
  cryptis_ctx ∗
  nsl_ctx ∗
  public (TKey Enc kR) ∗
  □ (public (TKey Dec kR) → ▷ False) ∗
  minted nR ∗
  □ (public nR ↔ ▷ □ (public (TKey Dec kI) ∨ public (TKey Dec kR))) ={⊤}▷=∗
  term_token nR (↑nroot.@"resp") ∗
  term_meta nR (nroot.@"data") (kI, kR) ∗
  public (TKey Enc kI) ∗
  public (TEnc (TKey Enc kI)
            (Spec.tag (nslN.@"m2")
               (Spec.of_list [nI; nR; TKey Enc kR]))).
Proof.
iIntros "#p_m1 nR_token (#? & (#? & #? & _) & #p_ekR & #s_dkR & #m_nR & #p_nR)".
rewrite (term_token_difference _ (↑nroot.@"resp")) //.
iDestruct "nR_token" as "[resp nR_token]"; iFrame "resp".
iMod (term_meta_set' (N := nroot.@"data") (kI, kR) with "nR_token")
       as "[#meta nR_token]"; first solve_ndisj.
iMod (escrowI nslN ⊤ _ (term_token nR (⊤ ∖ ↑nroot.@"resp" ∖ ↑nroot.@"data"))
       with "[$] []"
     ) as "#?".
{ iApply (term_token_switch nI nroot). }
set m2 := Spec.of_list [_; _; _].
iAssert (□ msg2_pred kI m2)%I as "#inv_m2".
{ iModIntro. rewrite /msg2_pred. by eauto 13. }
iDestruct (public_TEncE with "p_m1 [//]") as "[[_ fail]|succ]".
- rewrite public_of_list /=. iDestruct "fail" as "(? & ? & _)".
  iIntros "!> !> !>". do !iSplit => //.
  iApply public_TEncIS => //.
  + by iApply public_minted.
  + rewrite minted_of_list /=.
    by do !iSplit => //; iApply public_minted.
  + iIntros "!> #p_dkR". rewrite public_of_list /=.
    do !iSplit => //. iApply "p_nR". by eauto.
- iDestruct "succ" as "(#inv_m1 & m_m1 & _)". iIntros "!> !> !>".
  iDestruct "inv_m1" as "(%nI' & %kI' & %e & p_ekI & p_nI)".
  case/Spec.of_list_inj: e => <- <- {nI' kI'}.
  do 2!iSplitR => //.
  iApply public_TEncIS => //.
  + by iApply public_minted.
  + rewrite !minted_of_list /=. iDestruct "m_m1" as "(? & ? & _)".
    by do !iSplit => //; iApply public_minted.
  + iIntros "!> #p_dkR". rewrite public_of_list /=.
    do !iSplit => //.
    * iApply "p_nI". by eauto.
    * iApply "p_nR". by eauto.
Qed.

Lemma init_recv_2_send_3 kI kR nI nR :
  public (TEnc (TKey Enc kI)
            (Spec.tag (nslN.@"m2")
               (Spec.of_list [nI; nR; TKey Enc kR]))) -∗
  term_token nI ⊤ -∗
  cryptis_ctx ∗
  nsl_ctx ∗
  public (TKey Enc kI) ∗
  public (TKey Enc kR) ∗
  □ (public (TKey Dec kI) → ▷ False) ∗
  □ (public nI ↔ ▷ □ (public (TKey Dec kI) ∨ public (TKey Dec kR))) ={⊤}▷=∗
  minted nR ∗
  public (TEnc (TKey Enc kR) (Spec.tag (nslN.@"m3") nR)) ∗
  (public (TKey Dec kR) ∗ public nR ∨
   nsl_session kI kR nR ∗
   term_token nR (↑nroot.@"init")).
Proof.
iIntros "#p_m2 nI_token".
iIntros "(#? & (_ & #? & #?) & #p_ekI & #p_ekR & #s_dkI & #s_nI)".
iDestruct (public_TEncE with "p_m2 [//]") as "[fail|succ]".
- rewrite !public_of_list /=.
  iDestruct "fail" as "(_ & p_nI & p_nR & _ & _)".
  iSpecialize ("s_nI" with "p_nI").
  iIntros "!> !>". iDestruct "s_nI" as "#[contra|fail]".
  { iDestruct ("s_dkI" with "contra") as ">[]". }
  iFrame. iIntros "!>". iSplit; first by iApply public_minted.
  iSplit; eauto.
  iApply public_TEncIP => //. by rewrite public_tag.
- iDestruct "succ" as "(#inv_m2 & m_m2 & _)".
  rewrite minted_of_list /=. iDestruct "m_m2" as "(_ & m_nR & _)".
  iIntros "!> !>".
  iDestruct "inv_m2"
    as "(%nI' & %nR' & %kR' & %e & s_dkR & s_nR & meta & nR_token)".
  case/Spec.of_list_inj: e => {nI' nR' kR'} <- <- <-.
  rewrite -[in term_token nI ⊤]nclose_nroot.
  iMod (escrowE with "nR_token nI_token") as "{nR_token} >nR_token" => //.
  iMod (nsl_session_alloc with "nR_token [//] [//] [//] [//]")
    as "(nR_token & #key_nR')" => //.
  iFrame. iIntros "!>". iSplit => //.
  iSplit.
  { iApply public_TEncIS => //.
    + by iApply public_minted.
    + iIntros "!>". iExists kI. by eauto.
    + iIntros "!> #p_dkR". iApply "s_nR". by eauto. }
  iRight. by iFrame.
Qed.

Lemma resp_recv_3 kI kR nR :
  public (TEnc (TKey Enc kR) (Spec.tag (nslN.@"m3") nR)) -∗
  cryptis_ctx ∗
  nsl_ctx ∗
  term_meta nR (nroot.@"data") (kI, kR) ∗
  □ (public (TKey Dec kR) → ▷ False) ∗
  □ (public nR ↔ ▷ □ (public (TKey Dec kI) ∨ public (TKey Dec kR))) ={⊤}▷=∗
  public (TKey Dec kI) ∗ public nR ∨ nsl_session kI kR nR.
Proof.
iIntros "#p_m3 (#? & (_ & _ & #?) & #meta & #s_dkR & #s_nR)".
iDestruct (public_TEncE with "p_m3 [//]") as "{p_m3} [[_ p_nR]|p_m3]".
- iSpecialize ("s_nR" with "p_nR"). iIntros "!> !>".
  iDestruct "s_nR" as "[#p_dkI|#p_dkR]"; first by eauto.
  iDestruct ("s_dkR" with "p_dkR") as ">[]".
- iDestruct "p_m3" as "(#inv_m3 & _)". iIntros "!> !>".
  iDestruct "inv_m3" as "(%kI' & meta' & session)".
  iPoseProof (term_meta_agree with "meta meta'") as "%e".
  case: e => {kI'} <-. by eauto.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_init c kI kR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Enc kI) -∗
  □ (public (TKey Dec kI) → ▷ False) -∗
  public (TKey Enc kR) -∗
  {{{ True }}}
    init c (TKey Dec kI) (TKey Enc kI) (TKey Enc kR)
  {{{ ts, RET (repr ts);
      if ts is Some sk then
          minted sk ∗
          (public (TKey Dec kR) ∗ public sk ∨
           nsl_session kI kR sk ∗
           term_token sk (↑nroot.@"init"))
      else True }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_kI #s_kI #p_kR %Ψ !> _ Hpost".
rewrite /init. wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce (λ _, public (TKey Dec kI) ∨ public (TKey Dec kR))%I
          (λ _, False)%I) => //.
iIntros "%nI #m_nI #p_nI _ token".
wp_pures. wp_list. wp_term_of_list. wp_tenc => /=. wp_pures.
wp_bind (send _ _). iApply (wp_send with "[] [#]"); eauto.
  iApply init_send_1; eauto.
wp_pures. wp_bind (recv _). iApply wp_recv; eauto.
iIntros "%m2 #p_m2". wp_tdec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_list_match => [nI' nR pkR' {m2} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nI'.
wp_eq_term e; last protocol_failure; subst pkR'.
iDestruct (init_recv_2_send_3 with "p_m2 [$] []") as ">H"; first by eauto 10.
wp_pure.
iMod "H" as "(#m_nR & #p_m3 & inv)".
wp_tenc. wp_pures. wp_bind (send _ _). iApply wp_send => //.
wp_pures. iApply ("Hpost" $! (Some nR)). by iFrame.
Qed.

Lemma wp_resp c kR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Enc kR) -∗
  □ (public (TKey Dec kR) → ▷ False) -∗
  {{{ True }}}
    resp c (TKey Dec kR) (TKey Enc kR)
  {{{ ts, RET (repr ts);
      if ts is Some (pkI, sk) then ∃ kI,
        ⌜pkI = TKey Enc kI⌝ ∗
        term_token sk (↑nroot.@"resp") ∗
        (public (TKey Dec kI) ∗ public sk ∨ nsl_session kI kR sk)
      else True }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_kR #honR %Ψ !> _ Hpost".
rewrite /resp. wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#p_m1".
wp_tdec m1; last protocol_failure.
wp_list_of_term m1; last protocol_failure.
wp_list_match => [nI pkI {m1} ->|_]; last protocol_failure.
wp_is_key_eq kt kI et; last protocol_failure; subst pkI.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Enc)); last protocol_failure.
case: kt => // _.
wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce (λ _, public (TKey Dec kI) ∨ public (TKey Dec kR))%I
          (λ _, False)%I) => //.
iIntros "%nR #m_nR #p_nR _ nR_token".
iMod (resp_recv_1_send_2 with "p_m1 [$] []" ) as "H"; first eauto 10.
wp_pures. iMod "H" as "(nR_token & #m_nI & #p_pkI & #p_m2)".
wp_bind (term_of_list (nI :: _)%E).
wp_list. wp_term_of_list. wp_list. wp_tenc. wp_pures.
wp_bind (send _ _). iApply wp_send => //.
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m3 #p_m3". wp_tdec m3; last protocol_failure.
wp_eq_term e; last protocol_failure; subst m3.
iPoseProof (resp_recv_3 with "p_m3 []") as ">finished"; first eauto.
wp_pures. iMod "finished".
iApply ("Hpost" $! (Some (TKey Enc kI, nR))).
iModIntro. by iExists kI; eauto.
Qed.

Definition init_loop : val := rec: "loop" "c" "ekI" "dkI" :=
  Fork ("loop" "c" "ekI" "dkI");;
  let: "ekR" := recv "c" in
  bind: "kt" := is_key "ekR" in
  guard: ("kt" = repr Enc) in
  bind: "sk" := init "c" "ekI" "dkI" "ekR" in
  SOME ("ekR", "sk").

Definition resp_loop : val := rec: "loop" "c" "ekR" "dkR" :=
  Fork ("loop" "c" "ekR" "dkR");;
  resp "c" "ekR" "dkR".

Lemma wp_init_loop c kI :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Enc kI) -∗
  □ (public (TKey Dec kI) → ▷ False) -∗
  {{{ True }}}
    init_loop c (TKey Dec kI) (TKey Enc kI)
  {{{ ts, RET (repr ts);
      if ts is Some (pkR, sk) then ∃ kR,
          ⌜pkR = TKey Enc kR⌝ ∗
          minted sk ∗
          (public (TKey Dec kR) ∗ public sk ∨
           nsl_session kI kR sk ∗
           term_token sk (↑nroot.@"init"))
      else True }}}.
Proof.
iIntros "#chan #? #? #p_ekI #s_dkI".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ iApply "IH" => //. by iIntros "!> %?". }
wp_pures. wp_apply wp_recv => //.
iIntros (ekR) "#p_ekR".
wp_pures; wp_bind (is_key _); iApply wp_is_key. wp_pures.
case: Spec.is_keyP => [kt kR eekR|_]; last by protocol_failure.
wp_pures.
case: bool_decide_reflect => [ekt|_]; last by protocol_failure.
case: kt eekR ekt => // -> _.
wp_pures. wp_apply wp_init => //. iIntros "%ts tsP".
case: ts=> [sk|] => /=; last by protocol_failure.
wp_pures. iApply ("Hpost" $! (Some (TKey Enc kR, sk))).
iExists kR. by iFrame.
Qed.

Lemma wp_resp_loop c kR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Enc kR) -∗
  □ (public (TKey Dec kR) → ▷ False) -∗
  {{{ True }}}
    resp_loop c (TKey Dec kR) (TKey Enc kR)
  {{{ ts, RET (repr ts);
      if ts is Some (pkI, sk) then ∃ kI,
        ⌜pkI = TKey Enc kI⌝ ∗
        term_token sk (↑nroot.@"resp") ∗
        (public (TKey Dec kI) ∗ public sk ∨ nsl_session kI kR sk)
      else True }}}.
Proof.
iIntros "#chan #? #? #p_ekR #s_dkR".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ iApply "IH" => //. by iIntros "!> %?". }
wp_pures. by wp_apply wp_resp => //.
Qed.

Definition game : val := λ: "mkchan",
  let: "c"  := "mkchan" #() in
  let: "kI" := mkakey #() in
  let: "kR" := mkakey #() in
  let: "ekI" := Fst "kI" in
  let: "dkI" := Snd "kI" in
  let: "ekR" := Fst "kR" in
  let: "dkR" := Snd "kR" in
  send "c" "ekI";;
  send "c" "ekR";;
  let: "res" := init_loop "c" "dkI" "ekI" ||| resp_loop "c" "dkR" "ekR" in
  bind: "resI"  := Fst "res" in
  bind: "resR" := Snd "res" in
  let: "ekR'"  := Fst "resI" in
  let: "skI"   := Snd "resI" in
  let: "ekI'"  := Fst "resR" in
  let: "skR"   := Snd "resR" in
  if: (eq_term "ekR" "ekR'" || eq_term "ekI" "ekI'")
      && eq_term "skI" "skR" then
    let: "guess" := recv "c" in
    SOME (eq_term "ekR" "ekR'" &&
          eq_term "ekI" "ekI'" &&
          ~ eq_term "skI" "guess")
  else SOME #true.

Lemma wp_game (mkchan : val) :
  {{{ True }}} mkchan #() {{{ v, RET v; channel v }}} -∗
  cryptis_ctx -∗
  enc_pred_token ⊤ -∗
  key_pred_token (⊤ ∖ ↑nroot.@"keys") -∗
  honest 0 ∅ -∗
  ●Ph 0 -∗
  WP game mkchan {{ v, ⌜v = NONEV ∨ v = SOMEV #true⌝ }}.
Proof.
iIntros "wp_mkchan #ctx enc_tok key_tok hon phase"; rewrite /game; wp_pures.
wp_bind (mkchan _); iApply "wp_mkchan" => //.
iIntros "!> %c #cP".
wp_pures; wp_bind (mkakey _).
iApply (wp_mkakey with "[] [hon] phase"); eauto.
iIntros "%kI #p_ekI hon phase tokenI". wp_pures.
wp_bind (mkakey _). iApply (wp_mkakey with "[] [hon] phase"); eauto.
iIntros "%kR #p_ekR hon phase tokenR". wp_pures.
set ekI := TKey Enc kI.
set dkI := TKey Dec kI.
set ekR := TKey Enc kR.
set dkR := TKey Dec kR.
iMod (freeze_honest with "[//] hon phase") as "(hon & phase & sec)" => //.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
iMod "sec" as "sec".
rewrite big_sepS_forall. wp_pures.
iAssert (□ (public dkI ↔ ◇ False))%I as "#s_dkI".
  by iApply "sec"; iPureIntro; set_solver.
iAssert (□ (public dkR ↔ ◇ False))%I as "#s_dkR".
  by iApply "sec"; iPureIntro; set_solver.
iMod (nsl_alloc with "enc_tok") as "[#nsl_ctx _]" => //.
wp_pures; wp_bind (par _ _).
iApply (wp_par (λ v, ∃ a : option (term * term), ⌜v = repr a⌝ ∗ _)%I
               (λ v, ∃ a : option (term * term), ⌜v = repr a⌝ ∗ _)%I
         with "[] []").
- iApply (wp_init_loop with "[//] [//] [//] p_ekI [] [$]") => //.
  { iIntros "!> #p_dkI".
    iDestruct ("s_dkI" with "p_dkI") as ">[]". }
  iIntros "!> %a H". iExists a. iSplit; first done. iApply "H".
- iApply (wp_resp_loop with "[//] [//] [//] p_ekR [] [//]") => //.
  { iIntros "!> #p_dkR".
    iDestruct ("s_dkR" with "p_dkR") as ">[]". }
  iIntros "!> %a H"; iExists a; iSplit; first done. iApply "H".
iIntros (v1 v2) "[H1 H2]".
iDestruct "H1" as (a) "[-> H1]".
iDestruct "H2" as (b) "[-> H2]".
iModIntro.
wp_pure credit:"c1".
case: a => [[ekR' skI]|]; wp_pure credit:"c2"; wp_pures; last by eauto.
case: b => [[ekI' skR]|]; wp_pures; last by eauto.
iDestruct "H1" as (kR') "(-> & #m_skI & sessI)".
iDestruct "H2" as (kI') "(-> & skR_token & sessR)".
pose (b := bool_decide ((ekR = TKey Enc kR' ∨ ekI = TKey Enc kI') ∧ skI = skR)).
wp_bind ((eq_term ekR _ || _) && _)%E.
iApply (wp_wand _ _ _ (λ v, ⌜v = #b⌝)%I with "").
{ wp_eq_term e_ekR; wp_pures.
    iApply wp_eq_term. rewrite /b bool_decide_and bool_decide_or.
    by rewrite (bool_decide_eq_true_2 _ e_ekR) /=.
  wp_eq_term e_ekI; wp_pures.
    iApply wp_eq_term. rewrite /b bool_decide_and bool_decide_or.
    by rewrite (bool_decide_eq_true_2 _ e_ekI) /= Bool.orb_comm /=.
  rewrite /b bool_decide_and bool_decide_or.
  by rewrite (bool_decide_eq_false_2 _ e_ekR) (bool_decide_eq_false_2 _ e_ekI). }
iIntros "% ->".
rewrite /b; case: bool_decide_reflect => [[e_ek e_sk]|_]; wp_pures; eauto.
subst skR.
wp_apply wp_recv => //; iIntros "%guess #p_guess".
iAssert (|={⊤}=> ⌜ekR = TKey Enc kR' ∧ ekI = TKey Enc kI' ∧ skI ≠ guess⌝)%I
  with "[c1 c2 sessI sessR]" as ">%e".
{ case: e_ek => [[<-]|[<-]].
  - iDestruct "sessI" as "[(#fail & _)|(#sessI & _)]".
    { iDestruct ("s_dkR" with "fail") as ">[]". }
    iDestruct "sessR" as "[(_ & #fail) | #sessR]".
    { iPoseProof (nsl_session_public_key with "sessI [//]") as "#contra".
      iMod (lc_fupd_elim_later with "c1 contra") as "{contra} #>[]". }
    iDestruct (nsl_session_agree with "sessI sessR") as "[<- _]".
    case: (decide (skI = guess)) => [->|?].
    { iPoseProof (nsl_session_public_key with "sessI [//]") as "#contra".
      iMod (lc_fupd_elim_later with "c1 contra") as "{contra} #>[]". }
    iModIntro. iPureIntro. by eauto.
  - iDestruct "sessR" as "[(#fail & _)|#sessR]".
    { iDestruct ("s_dkI" with "fail") as ">[]". }
    iDestruct "sessI" as "[(_ & #fail) | (#sessI & _)]".
    { iPoseProof (nsl_session_public_key with "sessR [//]") as "#contra".
      iMod (lc_fupd_elim_later with "c1 contra") as "{contra} #>[]". }
    iDestruct (nsl_session_agree with "sessI sessR") as "[_ <-]".
    case: (decide (skI = guess)) => [->|?].
    { iPoseProof (nsl_session_public_key with "sessI [//]") as "#contra".
      iMod (lc_fupd_elim_later with "c1 contra") as "{contra} #>[]". }
    iModIntro. iPureIntro. by eauto. }
case: e => [[<-] [] [<-] wrong_guess].
wp_pures. wp_apply wp_eq_term. rewrite bool_decide_eq_true_2 //.
wp_pures. wp_apply wp_eq_term. rewrite bool_decide_eq_true_2 //.
wp_pures. wp_apply wp_eq_term. rewrite bool_decide_eq_false_2 //.
wp_pures; eauto.
Qed.

End NSL.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ].

Lemma nsl_secure (mkchan : val) σ₁ σ₂ (v : val) ts :
  (∀ `{!heapGS Σ, !cryptisGS Σ},
     ⊢ {{{ True }}} mkchan #() {{{ c, RET c; channel c}}}) →
  rtc erased_step ([game mkchan], σ₁) (Val v :: ts, σ₂) →
  v = NONEV ∨ v = SOMEV #true.
Proof.
have ? : heapGpreS F by apply _.
move=> wp_mkchan.
apply (adequate_result NotStuck _ _ (λ v _, v = NONEV ∨ v = SOMEV #true)).
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisGS_alloc _) as (?) "(#ctx & enc_tok & key_tok & ? & hon & phase)".
iApply (wp_game with "[] ctx [enc_tok] [key_tok] [hon]") => //.
iApply wp_mkchan.
Qed.
