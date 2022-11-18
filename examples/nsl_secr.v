From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics nown.
From cryptis Require Import role session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSL.

Context `{!heapGS Σ, !spawnG Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).

Variable N : namespace.

(*

A --> B: {nA; pkA}@pkB
B --> A: {nA; nB; pkB}@pkA
A --> B: {nB}@pkB

*)

Definition init : val := λ: "c" "skI" "pkI" "pkR",
  let: "nI" := mknonce #() in
  let: "m1" := tenc (N.@"m1") "pkR" (term_of_list ["nI"; "pkI"]) in
  send "c" "m1";;
  bind: "m2"   := tdec (N.@"m2") "skI" (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nI'"; "nR"; "pkR'"] := "m2" in
  assert: eq_term "nI'" "nI" && eq_term "pkR'" "pkR" in
  let: "m3" := tenc (N.@"m3") "pkR" "nR" in
  send "c" "m3";;
  let: "k" := term_of_list ["nI"; "nR"] in
  SOME "k".

Definition resp : val := λ: "c" "skR" "pkR",
  bind: "m1" := tdec (N.@"m1") "skR" (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["nI"; "pkI"] := "m1" in
  bind: "kt" := is_key "pkI" in
  assert: "kt" = repr Enc in
  let: "nR" := mknonce #() in
  let: "m2" := tenc (N.@"m2") "pkI" (term_of_list ["nI"; "nR"; "pkR"]) in
  send "c" "m2";;
  bind: "m3" := tdec (N.@"m3") "skR" (recv "c") in
  assert: eq_term "m3" "nR" in
  let: "k" := term_of_list ["nI"; "nR"] in
  SOME ("pkI", "k").

Definition corrupt kI kR : iProp :=
  public (TKey Dec kI) ∨ public (TKey Dec kR).

Global Instance corrupt_persistent kI kR :
  Persistent (corrupt kI kR).
Proof. apply _. Qed.

Definition honest k : iProp :=
  □ (public (TKey Dec k) ↔ ◇ False).

Global Instance honest_persistent k : Persistent (honest k).
Proof. apply _. Qed.

Lemma corruptE kI kR :
  corrupt kI kR -∗
  honest kI -∗
  honest kR -∗
  ◇ False.
Proof.
by iIntros "[cor|cor] p_kI p_kR"; [iApply "p_kI"|iApply "p_kR"].
Qed.


Definition msg1_pred kR m1 : iProp :=
  ∃ nI kI,
    ⌜m1 = Spec.of_list [nI; TKey Enc kI]⌝ ∧
    public (TKey Enc kI) ∧
    (public nI ↔ ▷ corrupt kI kR).

Definition msg2_pred kI m2 : iProp :=
  ∃ nI nR kR,
    ⌜m2 = Spec.of_list [nI; nR; TKey Enc kR]⌝ ∧
    (public nR ↔ ▷ corrupt kI kR).

Definition msg3_pred kR nR : iProp := True.

Definition nsl_ctx : iProp :=
  enc_pred (N.@"m1") msg1_pred ∧
  enc_pred (N.@"m2") msg2_pred ∧
  enc_pred (N.@"m3") msg3_pred.

Lemma nsl_alloc E E' :
  ↑N ⊆ E →
  enc_pred_token E ={E'}=∗
  nsl_ctx ∗
  enc_pred_token (E ∖ ↑N).
Proof.
iIntros (sub1) "t1".
rewrite (enc_pred_token_difference (↑N) E) //. iDestruct "t1" as "[t1 t1']".
iMod (enc_pred_set (N.@"m1") msg1_pred with "t1")
  as "[#H1 t1]"; try solve_ndisj.
iMod (enc_pred_set (N.@"m2") msg2_pred with "t1")
  as "[#H2 t1]"; try solve_ndisj.
iMod (enc_pred_set (N.@"m3") msg3_pred with "t1")
  as "[#H3 t1]"; try solve_ndisj.
iModIntro; iFrame; do !iSplit => //.
Qed.

Global Instance nsl_ctx_persistent : Persistent nsl_ctx.
Proof. apply _. Qed.

Lemma public_msg1I kI kR nI :
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Enc kI) -∗
  public (TKey Enc kR) -∗
  minted nI -∗
  □ (public nI ↔ ▷ corrupt kI kR) -∗
  public (TEnc kR (Spec.tag (N.@"m1") (Spec.of_list [nI; TKey Enc kI]))).
Proof.
iIntros "#? (#? & _ & _) #p_ekI #p_ekR #m_nI #p_nI".
iApply public_TEncIS; eauto.
- iModIntro. by iExists _, _; iSplit; eauto.
- by rewrite minted_of_list /=; eauto.
- rewrite public_of_list /=. iIntros "!> #p_dkR".
  do 2?iSplit => //. iApply "p_nI". rewrite /corrupt. by eauto.
Qed.

Lemma public_msg1E kI kR nI :
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TEnc kR (Spec.tag (N.@"m1") (Spec.of_list [nI; TKey Enc kI]))) -∗
  public (TKey Enc kR) -∗
  ▷ (minted nI ∗
     public (TKey Enc kI) ∗
     (▷ corrupt kI kR → public nI)).
Proof.
iIntros "#? (#? & _ & _) #p_m #p_ekR".
iDestruct (public_TEncE with "p_m [//]") as "[fail|succ]".
- rewrite public_of_list /=.
  iDestruct "fail" as "(p_kR & p_nI & p_kI' & _)". by iSplit; eauto.
- iDestruct "succ" as "(#m1P & m_m1 & _)".
  rewrite minted_of_list /=. iDestruct "m_m1" as "(m_nI & _ & _)".
  iModIntro.
  iDestruct "m1P" as "(%nI' & %kI' & %e & #p_ekI & #p_nI)".
  case/Spec.of_list_inj: e => <- <- {nI' kI'}.
  do 2?[iSplit=> //].
  iIntros "#?". by iApply "p_nI".
Qed.

Lemma public_msg2I kI kR nI nR :
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Enc kI) -∗
  minted nI -∗
  □ (▷ corrupt kI kR → public nI) -∗
  public (TKey Enc kR) -∗
  minted nR -∗
  □ (public nR ↔ ▷ corrupt kI kR) -∗
  public (TEnc kI (Spec.tag (N.@"m2") (Spec.of_list [nI; nR; TKey Enc kR]))).
Proof.
iIntros "#? (_ & #? & _) #p_ekI #m_nI #p_nI #p_ekR #m_nR #p_nR".
iApply public_TEncIS; eauto.
- iModIntro. by iExists _, _, _; iSplit; eauto.
- rewrite minted_of_list /=. by eauto.
- iIntros "!> #p_dkI". rewrite public_of_list /corrupt /=.
  do 3?iSplit; eauto.
  + by iApply "p_nI"; eauto.
  + by iApply "p_nR"; eauto.
Qed.

Lemma public_msg2E kI kR nI nR :
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TEnc kI (Spec.tag (N.@"m2") (Spec.of_list [nI; nR; TKey Enc kR]))) -∗
  public (TKey Enc kI) -∗
  □ (public nI ↔ ▷ corrupt kI kR) -∗
  ▷ (minted nR ∗ □ (public nR ↔ ▷ corrupt kI kR)).
Proof.
iIntros "#? (_ & #? & _) #p_m #p_ekI #s_nI".
iDestruct (public_TEncE with "p_m [//]") as "[fail|succ]".
- rewrite public_of_list /=.
  iDestruct "fail" as "(_ & #p_nI & p_nR & _)".
  iPoseProof ("s_nI" with "p_nI") as "fail". iModIntro.
  iSplit; eauto. iModIntro. by iSplit; eauto.
- iDestruct "succ" as "(#m2P & m_m & _)".
  rewrite minted_of_list /=. iDestruct "m_m" as "(? & ? & ? & _)".
  iSplit => //. iModIntro.
  iDestruct "m2P" as "(%nI' & %nR' & %kR' & %e & s_nR)".
  case/Spec.of_list_inj: e => _ <- <- {nI' nR' kR'}.
  by eauto.
Qed.

Lemma public_msg3I kI kR nR :
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Enc kR) -∗
  minted nR -∗
  □ (public nR ↔ ▷ corrupt kI kR) -∗
  public (TEnc kR (Spec.tag (N.@"m3") nR)).
Proof.
iIntros "#? (_ & _ & #?) #p_ekR #m_nR #s_nR".
iApply public_TEncIS; eauto.
iIntros "!> #p_dkR".
iApply "s_nR". rewrite /corrupt. by eauto.
Qed.

Lemma public_msg3E kI kR nR :
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TEnc kR (Spec.tag (N.@"m3") nR)) -∗
  □ (public nR ↔ ▷ corrupt kI kR) -∗
  True.
Proof.
iIntros "#? #(_ & _ & ?) #m3P #p_nR". eauto.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_init c kI kR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Enc kI) -∗
  honest kI -∗
  public (TKey Enc kR) -∗
  {{{ True }}}
    init c (TKey Dec kI) (TKey Enc kI) (TKey Enc kR)
  {{{ okS, RET (repr okS);
      if okS is Some kS then
        minted kS ∗ □ (honest kR → public kS → ▷^2 False)
      else True }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_kI #honI #p_kR".
iIntros "%Ψ !> _ Hpost".
rewrite /init. wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce (λ _, corrupt kI kR) (λ _, False)%I).
iIntros "%nI #m_nI #p_nI _ token".
rewrite bi.intuitionistic_intuitionistically.
wp_pures. wp_list. wp_term_of_list. wp_tenc => /=. wp_pures.
wp_bind (send _ _). iApply (wp_send with "[] [#]"); eauto.
  iApply (public_msg1I kI kR); eauto.
wp_pures. wp_bind (recv _). iApply wp_recv; eauto.
iIntros "%m2 #p_m2". wp_tdec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_list_match => [nI' nR pkR'' {m2} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nI'.
wp_eq_term e; last protocol_failure; subst pkR''.
iPoseProof (public_msg2E with "[//] [//] [//] [//] [//]")
  as "{p_m2} (m_nR & s_nR)".
wp_pures. wp_tenc. wp_pures. wp_bind (send _ _).
iApply wp_send => //.
  by iApply public_msg3I.
wp_pures. wp_list. wp_term_of_list. wp_pures.
iApply ("Hpost" $! (Some (Spec.of_list [nI; nR]))). iModIntro.
rewrite minted_of_list /=. do 3?iSplit => //.
iIntros "!> #honR". rewrite public_of_list /=.
iIntros "(#contra & _)". iSpecialize ("p_nI" with "contra").
iModIntro. iDestruct (corruptE with "p_nI [//] [//]") as ">[]".
Qed.

Lemma wp_resp c kR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Enc kR) -∗
  honest kR -∗
  {{{ True }}}
    resp c (TKey Dec kR) (TKey Enc kR)
  {{{ or, RET (repr or);
      if or is Some (pkI, kS) then ∃ kI,
        ⌜pkI = TKey Enc kI⌝ ∗
        public pkI ∗ minted kS ∗
        □ (honest kI → public kS → ▷^2 False)
      else True }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_kR #honR %Ψ !> _ Hpost".
rewrite /resp. wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#Hm1".
wp_tdec m1; last protocol_failure.
wp_list_of_term m1; last protocol_failure.
wp_list_match => [nI pkI {m1} ->|_]; last protocol_failure.
wp_is_key_eq kt kI et; last protocol_failure; subst pkI.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Enc)); last protocol_failure.
case: kt => // _.
iDestruct (public_msg1E with "[//] [//] Hm1 [//]")
  as "(#m_nI & #p_pkI & #nIP)".
wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce (λ _, corrupt kI kR) (λ _, False)%I).
iIntros "%nR #m_nR #p_nR _ _". rewrite bi.intuitionistic_intuitionistically.
wp_pures. wp_list; wp_term_of_list. wp_tenc. wp_pures.
wp_bind (send _ _). iApply wp_send => //.
  by iApply public_msg2I; eauto.
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m3 #p_m3". wp_tdec m3; last protocol_failure.
wp_eq_term e; last protocol_failure; subst m3.
iPoseProof (public_msg3E with "[//] [//] p_m3 p_nR") as "m3P".
wp_pures. wp_list. wp_term_of_list. wp_pures.
iApply ("Hpost" $! (Some (TKey Enc kI, Spec.of_list [nI; nR]))).
iModIntro. iExists kI. rewrite minted_of_list /=. do 5?[iSplit => //].
rewrite public_of_list /=.
iIntros "!> #honI (_ & #contra & _)".
iSpecialize ("p_nR" with "contra"). iModIntro.
by iDestruct (corruptE with "p_nR honI honR") as ">[]".
Qed.

Definition game : val := λ: "mkchan",
  let: "c"  := "mkchan" #() in
  let: "kI" := mkakey #() in
  let: "kR" := mkakey #() in
  let: "pkI" := Fst "kI" in
  let: "skI" := Snd "kI" in
  let: "pkR" := Fst "kR" in
  let: "skR" := Snd "kR" in
  send "c" "pkI";;
  send "c" "pkR";;
  let: "pkR'" := recv "c" in
  bind: "kt" := is_key "pkR'" in
  assert: ("kt" = repr Enc) in
  let: "res" := init "c" "skI" "pkI" "pkR'" ||| resp "c" "skR" "pkR" in
  bind: "sesskI" := Fst "res" in
  bind: "resR" := Snd "res" in
  let: "pkI'" := Fst "resR" in
  let: "sesskR" := Snd "resR" in
  if: eq_term "pkR" "pkR'" && eq_term "pkI" "pkI'" then
    let: "m" := recv "c" in
    SOME ((~ eq_term "m" "sesskI") && (~ eq_term "m" "sesskR"))
  else SOME #true.

Lemma wp_game (mkchan : val) :
  {{{ True }}} mkchan #() {{{ v, RET v; channel v }}} -∗
  cryptis_ctx -∗
  enc_pred_token ⊤ -∗
  key_pred_token (⊤ ∖ ↑nroot.@"keys") -∗
  ●H{0} ∅ -∗
  WP game mkchan {{ v, ⌜v = NONEV ∨ v = SOMEV #true⌝ }}.
Proof.
iIntros "wp_mkchan #ctx enc_tok key_tok hon"; rewrite /game; wp_pures.
iMod (nsl_alloc with "enc_tok") as "[#nsl_ctx _]" => //.
wp_bind (mkchan _); iApply "wp_mkchan" => //.
iIntros "!> %c #cP".
wp_pures; wp_bind (mkakey _).
iApply (wp_mkakey with "[] [hon]"); eauto.
iIntros "%kI #p_pkI hon". wp_pures.
wp_bind (mkakey _). iApply (wp_mkakey with "[] [hon]"); eauto.
iIntros "%kR #p_pkR hon". wp_pures.
set pkI := TKey Enc kI.
set skI := TKey Dec kI.
set pkR := TKey Enc kR.
set skR := TKey Dec kR.
iMod (freeze_honest with "[//] hon") as "[hon sec]" => //.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
wp_pures; wp_bind (recv _); iApply wp_recv => //.
iIntros (pkR') "#p_pkR'". iMod "sec" as "#sec".
rewrite big_sepS_forall.
iAssert (□ (public skI ↔ ◇ False))%I as "#s_skI".
  by iApply "sec"; iPureIntro; set_solver.
iAssert (□ (public skR ↔ ◇ False))%I as "#s_skR".
  by iApply "sec"; iPureIntro; set_solver.
wp_pures; wp_bind (is_key _); iApply wp_is_key.
case: Spec.is_keyP => [kt kR' epkR'|_]; last by wp_pures; iLeft.
wp_pures.
case: bool_decide_reflect => [ekt|_]; last by wp_pures; iLeft.
wp_pures; wp_bind (par _ _).
case: kt epkR' ekt => // -> _.
iApply (wp_par (λ v, ∃ a : option term, ⌜v = repr a⌝ ∗ _)%I
               (λ v, ∃ a : option (term * term), ⌜v = repr a⌝ ∗ _)%I
          with "[] []").
- iApply (wp_init with "[//] [//] [//] p_pkI [//] p_pkR'") => //.
  iIntros "!> %a H". iExists a. iSplit; first done. iApply "H".
- iApply (wp_resp with "[//] [//] [//] p_pkR [//]") => //.
  iIntros "!> %a H"; iExists a; iSplit; first done. iApply "H".
iIntros (v1 v2) "[H1 H2]".
iDestruct "H1" as (a) "[-> H1]".
iDestruct "H2" as (b) "[-> H2]".
iModIntro.
wp_pures.
case: a => [sI|]; wp_pures; last by eauto.
case: b => [[pkI' sR]|]; wp_pures; last by eauto.
iDestruct "H1" as "(#s_gabI & #p_sI)".
iDestruct "H2" as (kI') "(-> & #p_pkI' & #m_sR & #p_sR)".
pose (b := bool_decide (pkR = TKey Enc kR' ∧ pkI = TKey Enc kI')).
wp_bind (eq_term pkR _ && _)%E.
iApply (wp_wand _ _ _ (λ v, ⌜v = #b⌝)%I with "").
{ wp_eq_term e_pkR; wp_pures.
    iApply wp_eq_term. iPureIntro. congr (# (LitBool _)).
    apply bool_decide_ext. intuition congruence.
  iPureIntro. rewrite /b bool_decide_decide decide_False //.
  tauto. }
iIntros "% ->". rewrite {}/b.
case: (bool_decide_reflect (pkR = _ ∧ _)) => [succ|_]; last by wp_pures; eauto.
case: succ => - [<-] [<-].
iAssert (□ (public sI → ▷ ▷ False))%I as "{p_sI} #p_sI".
  by iModIntro; iApply "p_sI".
iAssert (□ (public sR → ▷ ▷ False))%I as "{p_sR} #p_sR".
  by iModIntro; iApply "p_sR".
wp_pure credit:"c1".
wp_bind (recv _); iApply wp_recv => //; iIntros (m) "#p_m".
wp_pure credit:"c2". wp_pures. wp_bind (eq_term _ _); iApply wp_eq_term.
case: bool_decide_reflect => [->|_].
  iSpecialize ("p_sI" with "p_m").
  iMod (lc_fupd_elim_later with "c1 p_sI") as ">[]".
wp_pures; wp_bind (eq_term _ _); iApply wp_eq_term.
case: bool_decide_reflect => [->|_].
  iSpecialize ("p_sR" with "p_m").
  iMod (lc_fupd_elim_later with "c1 p_sR") as ">[]".
by wp_pures; eauto.
Qed.

End NSL.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ].

Lemma nsl_secure (mkchan : val) σ₁ σ₂ (v : val) ts :
  (∀ `{!heapGS Σ, !cryptisGS Σ},
     ⊢ {{{ True }}} mkchan #() {{{ c, RET c; channel c}}}) →
  rtc erased_step ([game nroot mkchan], σ₁) (Val v :: ts, σ₂) →
  v = NONEV ∨ v = SOMEV #true.
Proof.
have ? : heapGpreS F by apply _.
move=> wp_mkchan.
apply (adequate_result NotStuck _ _ (λ v _, v = NONEV ∨ v = SOMEV #true)).
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisGS_alloc _) as (?) "(#ctx & enc_tok & key_tok & ? & hon)".
iApply (wp_game with "[] ctx [enc_tok] [key_tok] [hon]") => //.
iApply wp_mkchan.
Qed.
