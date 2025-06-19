From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par ticket_lock assert.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.primitives Require Import attacker.
From cryptis.lib Require Import term_set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Section NSL.

Context `{!heapGS Σ, !cryptisGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : aenc_key).

Definition nslN := nroot.@"nsl".

Record sess_info : Type := SessInfo {
  si_init_share : term;
  si_resp_share : term;
}.

Definition si_key skI skR si :=
  SEncKey (Spec.of_list [Spec.pkey skI; Spec.pkey skR;
                         si_init_share si;
                         si_resp_share si]).

Lemma nsl_session_agree skI1 skI2 skR1 skR2 si1 si2 :
  si_key skI1 skR1 si1 = si_key skI2 skR2 si2 →
  (skI1, skR1, si1) = (skI2, skR2, si2).
Proof.
case.
case/Spec.of_list_inj => /Spec.aenc_pkey_inj <- /Spec.aenc_pkey_inj <-.
by case: si1 si2 => [??] [??] /= <- <-.
Qed.

(*

A --> B: {m1; nA; pkA}@pkB
B --> A: {m2; nA; nB; pkB}@pkA
A --> B: {m3; nB}@pkB

*)

Definition init : val := λ: "c" "skI" "pkR",
  let: "pkI" := pkey "skI" in
  let: "nI" := mk_nonce #() in
  let: "m1" := aenc "pkR" (Tag $ nslN.@"m1") (term_of_list ["nI"; "pkI"]) in
  send "c" "m1";;
  bind: "m2"   := adec "skI" (Tag $ nslN.@"m2") (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nI'"; "nR"; "pkR'"] := "m2" in
  guard: eq_term "nI'" "nI" && eq_term "pkR'" "pkR" in
  let: "m3" := aenc "pkR" (Tag $ nslN.@"m3") "nR" in
  send "c" "m3";;
  let: "sess_key" :=
    derive_senc_key (term_of_list ["pkI"; "pkR"; "nI"; "nR"]) in
  SOME "sess_key".

Definition resp : val := λ: "c" "skR",
  let: "pkR" := pkey "skR" in
  bind: "m1" := adec "skR" (Tag $ nslN.@"m1") (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["nI"; "pkI"] := "m1" in
  guard: is_aenc_key "pkI" in
  let: "nR" := mk_nonce #() in
  let: "m2" := aenc "pkI" (Tag $ nslN.@"m2") (term_of_list ["nI"; "nR"; "pkR"]) in
  send "c" "m2";;
  bind: "m3" := adec "skR" (Tag $ nslN.@"m3") (recv "c") in
  guard: eq_term "m3" "nR" in
  let: "sess_key" :=
    derive_senc_key (term_of_list ["pkI"; "pkR"; "nI"; "nR"]) in
  SOME ("pkI", "sess_key").

Definition msg1_pred skR m1 : iProp := ∃ nI skI,
  ⌜m1 = Spec.of_list [nI; Spec.pkey skI]⌝ ∧
  (public nI ↔ ▷ (public skI ∨ public skR)).

Definition msg2_pred skI m2 : iProp := ∃ nI nR skR,
  ⌜m2 = Spec.of_list [nI; nR; Spec.pkey skR]⌝ ∧
  (public nR ↔ ▷ (public skI ∨ public skR)).

Definition msg3_pred skR nR : iProp := True.

Definition nsl_ctx : iProp :=
  aenc_pred (nslN.@"m1") msg1_pred ∧
  aenc_pred (nslN.@"m2") msg2_pred ∧
  aenc_pred (nslN.@"m3") msg3_pred.

Lemma nsl_alloc E1 E2 :
  ↑nslN ⊆ E1 →
  seal_pred_token AENC E1 ={E2}=∗
  nsl_ctx ∗
  seal_pred_token AENC (E1 ∖ ↑nslN).
Proof.
iIntros (sub1) "t1".
rewrite (seal_pred_token_difference _ (↑nslN) E1) //.
iDestruct "t1" as "[t1 t1']". iFrame.
iMod (aenc_pred_set (N := nslN.@"m1") msg1_pred with "t1")
  as "[#H1 t1]"; try solve_ndisj.
iMod (aenc_pred_set (N := nslN.@"m2") msg2_pred with "t1")
  as "[#H2 t1]"; try solve_ndisj.
iMod (aenc_pred_set (N := nslN.@"m3") msg3_pred with "t1")
  as "[#H3 t1]"; try solve_ndisj.
iModIntro; iFrame; do !iSplit => //.
Qed.

Global Instance nsl_ctx_persistent : Persistent nsl_ctx.
Proof. apply _. Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_init c skI skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  minted skI -∗
  minted skR -∗
  {{{ True }}}
    init c skI (Spec.pkey skR)
  {{{ sk, RET (repr sk);
      if sk is Some sk then ∃ si,
        ⌜sk = si_key skI skR si⌝ ∗
        minted sk ∗
        term_token (si_init_share si) (⊤ ∖ ↑nslN) ∗
        □ (public sk ↔ ▷ (public skI ∨ public skR))
      else True }}}.
Proof.
iIntros "#chan_c #ctx #(?&?&?) #m_skI #m_skR %Ψ !> _ Hpost".
iAssert (public (Spec.pkey skI)) as "?". { by iApply public_aenc_key. }
iAssert (public (Spec.pkey skR)) as "?". { by iApply public_aenc_key. }
rewrite /init. wp_pures. wp_apply wp_pkey. wp_pures.
wp_apply (wp_mk_nonce (λ _, public skI ∨ public skR)%I (λ _, False)%I) => //.
iIntros "%nI _ #m_nI #s_nI _ token".
rewrite (term_token_difference _ (↑nslN)) //.
iDestruct "token" as "[_ token]".
rewrite bi.intuitionistic_intuitionistically.
wp_pures. wp_list. wp_term_of_list. wp_apply wp_aenc => /=; eauto.
- by rewrite minted_of_list /= minted_pkey; eauto.
- iRight. iSplit.
  + iModIntro. iExists _. by eauto.
  + iIntros "!> #p_skR". rewrite public_of_list /=. do !iSplit => //.
    iApply "s_nI". by eauto.
iIntros "%m1 #p_m1". wp_pures.
wp_apply wp_send => //.
wp_pures. wp_apply wp_recv => //. iIntros "%m2 #p_m2".
wp_apply wp_adec => //. iSplit; last protocol_failure.
iClear "p_m2" => {m2}. iIntros "%m2 #m_m2 #inv_m2".
wp_list_of_term m2; last protocol_failure.
wp_list_match => [nI' nR pkR' {m2} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nI'.
wp_eq_term e; last protocol_failure; subst pkR'.
rewrite minted_of_list public_of_list /=.
iDestruct "m_m2" as "(_ & m_nR & _)".
iAssert (public nR ↔ ▷ (public skI ∨ public skR))%I as "s_nR".
{ iDestruct "inv_m2" as "[(p_nI & p_nR & _)|[#inv_m2 _]]".
  - iSpecialize ("s_nI" with "p_nI"). by iSplit; eauto.
  - iDestruct "inv_m2" as "(%nI' & %nR' & %skR' & %e & s_nR)".
    by case/Spec.of_list_inj: e => _ <- /Spec.aenc_pkey_inj <-. }
wp_pures. wp_apply wp_aenc; eauto.
{ iRight. iSplit => //. iIntros "!> #p_skR".
  iApply "s_nR". by eauto. }
iIntros "%m3 #p_m3". wp_pures. wp_apply wp_send => //.
wp_pures. wp_list. wp_term_of_list. wp_apply wp_derive_senc_key.
set sess_key := Spec.of_list [Spec.pkey skI; _; _; _].
wp_pures.
iApply ("Hpost" $! (Some (SEncKey sess_key))). iModIntro.
iExists (SessInfo nI nR). iFrame.
rewrite minted_senc minted_of_list /= !minted_pkey.
do !iSplit => //. rewrite public_senc_key public_of_list /=.
iModIntro. iSplit.
- iIntros "(_ & _ & _ & p_nR & _)". by iApply "s_nR".
- iIntros "#fail". by do !iSplit => //; [iApply "s_nI"|iApply "s_nR"].
Qed.

Lemma wp_resp c skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  minted skR -∗
  {{{ True }}}
    resp c skR
  {{{ ts, RET (repr ts);
      if ts is Some (pkI, sk) then ∃ skI si,
        ⌜pkI = Spec.pkey skI⌝ ∗
        ⌜sk = si_key skI skR si⌝ ∗
        term_token (si_resp_share si) (⊤ ∖ ↑nslN) ∗
        □ (public sk ↔ ▷ (public skI ∨ public skR))
      else True }}}.
Proof.
iIntros "#chan_c #ctx #(?&?&?) #aencR %Ψ !> _ Hpost".
iAssert (public (Spec.pkey skR)) as "?". { by iApply public_aenc_key. }
rewrite /resp. wp_pures. wp_apply wp_pkey. wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#p_m1".
wp_apply wp_adec => //. iSplit; last protocol_failure.
iClear "p_m1" => {m1}. iIntros "%m1 #m_m1 #inv_m1".
wp_list_of_term m1; last protocol_failure.
wp_list_match => [nI pkI {m1} ->|_]; last protocol_failure.
rewrite minted_of_list /= public_of_list /=.
iDestruct "m_m1" as "(m_nI & m_pkI & _)".
wp_apply wp_is_aenc_key => //. iSplit; last protocol_failure.
iIntros "%skI -> #m_skI {m_pkI}". wp_pures.
iAssert (▷ (public skI ∨ public skR) → public nI)%I as "s_nI".
{ iDestruct "inv_m1" as "[(? & _)|[#inv_m1 _]]"; eauto.
  iIntros "#fail".
  iDestruct "inv_m1" as "(%nI' & %skI' & %e & s_nI)".
  case/Spec.of_list_inj: e => <- /Spec.aenc_pkey_inj <-.
  by iApply "s_nI". }
wp_apply (wp_mk_nonce_freshN
           ∅
           (λ _, public skI ∨ public skR)%I
           (λ _, False)%I
           (λ nR, {[nR; SEncKey (Spec.of_list [Spec.pkey skI; Spec.pkey skR; nI; nR]) : term]})) => //.
- by iIntros "% %".
- iIntros "%nR".
  rewrite big_sepS_union_pers !big_sepS_singleton minted_senc minted_of_list.
  rewrite /= !minted_pkey.
  iSplit => //; iModIntro; first by iSplit; iIntros "?".
  iSplit; last by iIntros "(_ & _ & _ & ? & _)".
  by iIntros "#m_nR"; do !iSplit => //.
iIntros "%nR _ %nonce #m_nR #s_nR _ tokens".
rewrite bi.intuitionistic_intuitionistically.
set sess_key := SEncKey (Spec.of_list [_; _; _; _]).
have ? : nR ≠ sess_key.
  by move=> e; rewrite e keysE in nonce.
rewrite big_sepS_union; last set_solver.
rewrite !big_sepS_singleton. iDestruct "tokens" as "[nR_token sk_token]".
rewrite (term_token_difference _ (↑nslN)) //.
iDestruct "nR_token" as "[_ nR_token]". wp_pures.
wp_list. wp_term_of_list.
wp_apply wp_aenc; eauto.
- by rewrite minted_of_list /= minted_pkey; eauto.
- iRight. iSplit.
  + iExists nI, nR, skR. by eauto.
  + iIntros "!> #p_skI". rewrite public_of_list /=.
    do !iSplit => //; [iApply "s_nI"|iApply "s_nR"]; eauto.
iIntros "%m2 #p_m2". wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_recv => //.
iIntros "%m3 #p_m3".
wp_apply wp_adec => //. iSplit; last protocol_failure.
iClear "p_m3" => {m3}. iIntros "%m3 _ _". wp_pures.
wp_eq_term e; last protocol_failure; subst m3.
wp_pures. wp_list. wp_term_of_list. wp_apply wp_derive_senc_key.
wp_pures. iApply ("Hpost" $! (Some (Spec.pkey skI, sess_key))).
iModIntro. iExists skI, (SessInfo nI nR). iFrame.
do !iSplit => //.
rewrite public_senc_key public_of_list /=.
iModIntro. iSplit.
- iIntros "(_ & _ & _ & #p_nR & _)". by iApply "s_nR".
- iIntros "#fail". rewrite !public_aenc_key.
  by do !iSplit => //; [iApply "s_nI"|iApply "s_nR"].
Qed.

Definition check_key_secrecy : val := λ: "c" "sk",
  let: "guess" := recv "c" in
  assert: (~ eq_term "sk" "guess").

Definition do_init_loop : val := rec: "loop" "c" "set" "skI" "pkR" :=
  Fork ("loop" "c" "set" "skI" "pkR");;
  let: "pkR'" := recv "c" in
  (guard: is_aenc_key "pkR'" in
   bind: "sk" := init "c" "skI" "pkR'" in
   add_fresh_lock_term_set "sk" "set";;
   if: eq_term "pkR" "pkR'" then check_key_secrecy "c" "sk"
   else #());;
   #().

Definition do_init : val := λ: "c" "skI" "pkR",
  let: "set" := new_lock_term_set #() in
  do_init_loop "c" "set" "skI" "pkR".

Definition si_share_of rl :=
  if rl is Init then si_init_share else si_resp_share.

Definition nsl_game_inv rl t : iProp := ∃ skI skR si,
  ⌜t = si_key skI skR si⌝ ∧
  term_meta (si_share_of rl si) (nroot.@"fresh") ().

Lemma nsl_game_inv_fresh skI skR rl si E :
  ↑nroot.@"fresh" ⊆ E →
  term_token (si_share_of rl si) E -∗
  fresh_term (nsl_game_inv rl) (si_key skI skR si).
Proof.
iIntros "%sub token". iSplit.
- iIntros "(%skI' & %skR' & %si' & %e & #meta)".
  case/term_of_senc_key_inj/nsl_session_agree: e => _ _ <-.
  by iApply (term_meta_token with "token meta").
- iMod (term_meta_set (nroot.@"fresh") () with "token") as "#?" => //.
  iIntros "!> !>". iExists skI, skR, si. by eauto.
Qed.

Lemma wp_check_key_secrecy c k :
  channel c -∗
  cryptis_ctx -∗
  □ (public k → ▷^2 False) -∗
  {{{ True }}}
    check_key_secrecy c k
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #s_k %Φ !> _ post".
wp_lam. wp_pures. wp_apply wp_recv => //. iIntros "%guess #p_guess".
wp_pures. wp_apply wp_assert.
wp_eq_term e.
- rewrite -e. iPoseProof ("s_k" with "p_guess") as "contra".
  wp_pures. by iDestruct "contra" as ">[]".
- wp_pures. iModIntro. iSplit => //. by iApply "post".
Qed.

Lemma wp_do_init_loop c vset skI skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  minted skI -∗
  □ (public skI ↔ ▷ False) -∗
  □ (public skR ↔ ▷ False) -∗
  is_lock_term_set (nsl_game_inv Init) vset -∗
  {{{ True }}}
    do_init_loop c vset skI (Spec.pkey skR)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #m_skI #s_skI #s_skR #set".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ by iApply "IH" => //. }
wp_pures. wp_apply wp_recv => //.
iIntros (pkR') "#p_pkR'".
wp_pures. wp_apply wp_is_aenc_key => //.
{ by iApply public_minted. }
iSplit; last by wp_pures; iApply "Hpost".
iIntros "%skR' -> #m_skR'". wp_pures.
wp_apply wp_init => //. iIntros "%ts tsP".
case: ts=> [sk|] => /=; wp_pures; last by iApply "Hpost".
iDestruct "tsP" as "(%si & -> & _ & token & #s_sk)".
iPoseProof (@nsl_game_inv_fresh skI skR' Init with "token")
  as "fresh" => //; try solve_ndisj.
wp_apply (wp_add_fresh_lock_term_set with "[$]"). iIntros "_".
wp_eq_term e; wp_pures; last by iApply "Hpost".
move: e => /Spec.aenc_pkey_inj <- {skR'}.
wp_apply wp_check_key_secrecy => //.
{ iIntros "!> #fail".
  iPoseProof ("s_sk" with "fail") as "{fail} fail".
  iModIntro. by iDestruct "fail" as "[fail|fail]";
  [iApply "s_skI"|iApply "s_skR"]. }
iIntros "_". wp_pures. by iApply "Hpost".
Qed.

Lemma wp_do_init c skI skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  minted skI -∗
  □ (public skI ↔ ▷ False) -∗
  □ (public skR ↔ ▷ False) -∗
  {{{ True }}}
    do_init c skI (Spec.pkey skR)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #m_skI #s_skI #s_skR %Φ _ !> post".
wp_lam. wp_pures.
wp_apply (wp_new_lock_term_set (nsl_game_inv Init)) => //.
iIntros "%set #set". wp_pures.
wp_apply wp_do_init_loop => //.
Qed.

Definition do_resp_loop : val := rec: "loop" "c" "set" "skR" "pkI" :=
  Fork ("loop" "c" "set" "skR" "pkI");;
  (bind: "res" := resp "c" "skR" in
   let: "pkI'" := Fst "res" in
   let: "sk" := Snd "res" in
   add_fresh_lock_term_set "sk" "set";;
   if: eq_term "pkI" "pkI'" then check_key_secrecy "c" "sk"
   else #());;
  #().

Definition do_resp : val := λ: "c" "skR" "pkI",
  let: "set" := new_lock_term_set #() in
  do_resp_loop "c" "set" "skR" "pkI".

Lemma wp_do_resp_loop c set skI skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  minted skR -∗
  □ (public skR ↔ ▷ False) -∗
  □ (public skI ↔ ▷ False) -∗
  is_lock_term_set (nsl_game_inv Resp) set -∗
  {{{ True }}}
    do_resp_loop c set skR (Spec.pkey skI)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #m_skR #s_skR #s_skI #set".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ iApply "IH" => //. }
wp_pures. wp_apply wp_resp => //.
iIntros "%res res".
case: res => [[ekI' sk]|]; wp_pures; last by iApply "Hpost".
iDestruct "res" as "(%skI' & %si & -> & -> & token & #res)".
iPoseProof (@nsl_game_inv_fresh skI' skR Resp with "token")
  as "fresh" => //; try solve_ndisj.
wp_apply (wp_add_fresh_lock_term_set with "[$]"). iIntros "_".
wp_eq_term e; wp_pures; last by iApply "Hpost".
move: e => /Spec.aenc_pkey_inj <- {skI'}.
wp_apply wp_check_key_secrecy => //.
{ iIntros "!> #fail".
  iPoseProof ("res" with "fail") as "{fail} fail".
  iModIntro. by iDestruct "fail" as "[fail|fail]";
  [iApply "s_skI"|iApply "s_skR"]. }
iIntros "_". wp_pures. by iApply "Hpost".
Qed.

Lemma wp_do_resp c skI skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  minted skR -∗
  □ (public skR ↔ ▷ False) -∗
  □ (public skI ↔ ▷ False) -∗
  {{{ True }}}
    do_resp c skR (Spec.pkey skI)
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #? #? #? #? %Φ _ !> post".
wp_lam. wp_pures.
wp_apply (wp_new_lock_term_set (nsl_game_inv Resp)) => //.
iIntros "%set #set". wp_pures.
by wp_apply wp_do_resp_loop => //.
Qed.

Definition game : val := λ: <>,
  let: "c"   := init_network #() in
  let: "skI" := mk_aenc_key #() in
  let: "skR" := mk_aenc_key #() in
  let: "pkI" := pkey "skI" in
  let: "pkR" := pkey "skR" in
  send "c" "pkI";;
  send "c" "pkR";;
  Fork (do_init "c" "skI" "pkR");;
  Fork (do_resp "c" "skR" "pkI").

Lemma wp_game :
  cryptis_ctx -∗
  seal_pred_token AENC ⊤ -∗
  WP game #() {{ _, True }}.
Proof.
iIntros "#ctx enc_tok"; rewrite /game; wp_pures.
wp_apply wp_init_network => //. iIntros "%c #cP".
wp_pures. wp_apply (wp_mk_aenc_key with "[]"); eauto.
iIntros "%skI #m_skI secI tokenI".
wp_pures. wp_apply (wp_mk_aenc_key with "[]"); eauto.
iIntros "%skR #m_skR secR tokenR".
wp_pures. wp_apply wp_pkey. wp_pures. wp_apply wp_pkey. wp_pures.
iMod (freeze_secret with "secI") as "#?".
iMod (freeze_secret with "secR") as "#?".
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by iApply public_aenc_key.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by iApply public_aenc_key.
wp_pures.
iMod (nsl_alloc with "enc_tok") as "[#nsl_ctx _]" => //.
wp_apply wp_fork.
{ wp_apply wp_do_init => //. }
wp_pures. wp_apply wp_fork => //.
wp_apply wp_do_resp => //.
Qed.

End NSL.

Definition F : gFunctors :=
  #[heapΣ; cryptisΣ; tlockΣ].

Lemma nsl_secure σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([game #()], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisGS_alloc _) as (?) "(#ctx & aenc_tok & _)".
by iApply (wp_game with "ctx [aenc_tok]").
Qed.
