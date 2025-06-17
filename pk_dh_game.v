From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import numbers reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par ticket_lock.
From cryptis Require Import lib cryptis primitives tactics gmeta.
From cryptis Require Import role session pk_auth dh pk_dh.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !sessionGS Σ, !metaGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types rl : role.

Definition N := nroot.@"nsldh".

Definition game : val := λ: <>,
  let: "c"  := init_network #() in
  let: "skI" := mk_aenc_key #() in
  let: "skR" := mk_aenc_key #() in
  let: "pkI" := pkey "skI" in
  let: "pkR" := pkey "skR" in
  send "c" "pkI";;
  send "c" "pkR";;
  let: "pkR'" := recv "c" in
  bind: "kt" := is_key "pkR'" in
  guard: ("kt" = repr Seal) in
  let: "res" := pk_dh_init N "c" "skI" "pkR'" |||
                pk_dh_resp N "c" "skR" in
  bind: "sesskI" := Fst "res" in
  bind: "resR" := Snd "res" in
  let: "pkI'" := Fst "resR" in
  let: "sesskR" := Snd "resR" in
  if: eq_term "pkR" "pkR'" || eq_term "pkI" "pkI'" then
    send "c" (key Open "skI");;
    send "c" (key Open "skR");;
    let: "m" := recv "c" in
    SOME (eq_term "pkR" "pkR'" && eq_term "pkI" "pkI'" &&
          eq_term "sesskI" "sesskR" && ~ eq_term "m" "sesskI")
  else SOME #true.

Lemma wp_game :
  cryptis_ctx -∗
  seal_pred_token ⊤ -∗
  session_token ⊤ -∗
  WP game #() {{ v, ⌜v = NONEV ∨ v = SOMEV #true⌝ }}.
Proof.
iIntros "#ctx seal_tok nown_tok"; rewrite /game; wp_pures.
iMod gmeta_token_alloc as (γI) "tokenI".
iMod gmeta_token_alloc as (γR) "tokenR".
pose (P rl (kI kR kS : term) :=
  gmeta (if rl is Init then γI else γR) nroot (kI, kR, kS)).
iMod (pk_dh_alloc N P with "nown_tok seal_tok") as "[#dh_ctx _]" => //.
wp_apply wp_init_network => //. iIntros "%c #cP".
wp_pures; wp_bind (mk_aenc_key _).
iApply (wp_mk_aenc_key with "[]"); eauto.
iIntros "%kI #p_kI #aenc_kI s_kI _". wp_pures.
wp_bind (mk_aenc_key _). iApply (wp_mk_aenc_key with "[]"); eauto.
iIntros "%kR #p_kR #aenc_kR s_kR _". wp_pures.
wp_apply wp_pkey. wp_pures. set pkI := TKey Seal kI.
set skI := TKey Open kI.
wp_apply wp_pkey. wp_pures. set pkR := TKey Seal kR.
set skR := TKey Open kR.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
wp_pures; wp_bind (recv _); iApply wp_recv => //.
iIntros (pkR') "#p_pkR'".
wp_pures; wp_bind (is_key _); iApply wp_is_key.
case: Spec.is_keyP => [kt kR' epkR'|_]; last by wp_pures; iLeft.
wp_pures.
case: bool_decide_reflect => [ekt|_]; last by wp_pures; iLeft.
wp_pures; wp_bind (par _ _).
case: kt epkR' ekt => // -> _.
iApply (wp_par (λ v, ∃ a : option term, ⌜v = repr a⌝ ∗ _)%I
               (λ v, ∃ a : option (term * term), ⌜v = repr a⌝ ∗ _)%I
          with "[tokenI] [tokenR]").
- iApply (wp_pk_dh_init with "[//] [//] [//] [] [] [tokenI]") => //.
  + iFrame. iIntros "%nI %nR".
    set (kS := mk_session_key _ _ _).
    iMod (own_update with "tokenI") as "ownI".
    apply (namespace_map_alloc_update _ nroot
             (to_agree (encode (kI, kR', kS)))) => //.
    iPoseProof "ownI" as "#ownI".
    by eauto.
  + iIntros "!> %a H". iExists a. iSplit; first done.
    iApply "H".
- iApply (wp_pk_dh_resp with "[//] [//] [//] [] [tokenR]") => //.
  + iFrame. iIntros "%kI' %nI %nR".
    set (kS := mk_session_key _ _ _).
    iMod (own_update with "tokenR") as "ownR".
    apply (namespace_map_alloc_update _ nroot
             (to_agree (encode (kI', kR, kS)))) => //.
    iPoseProof "ownR" as "#ownR".
    eauto.
  + iIntros "!> %a H"; iExists a; iSplit; first done.
    iApply "H".
iIntros (v1 v2) "[H1 H2]".
iDestruct "H1" as (a) "[-> H1]".
iDestruct "H2" as (b) "[-> H2]".
iModIntro.
wp_pures.
case: a => [gabI|]; wp_pures; last by eauto.
case: b => [[pkI' gabR]|]; wp_pures; last by eauto.
iDestruct "H1" as "(#s_gabI & #confI & _ & H1)".
iDestruct "H2" as (kI') "(-> & #p_pkI' & #gabR & #confR & _ & H2)".
pose (b := bool_decide (pkR = TKey Seal kR' ∨ pkI = TKey Seal kI')).
wp_bind (eq_term pkR _ || _)%E.
iApply (wp_wand _ _ _ (λ v, ⌜v = #b⌝)%I with "[] [s_kI s_kR H1 H2]").
{ wp_eq_term e_pkR; wp_pures.
    iPureIntro. by rewrite /b bool_decide_decide decide_True //; eauto.
  iApply wp_eq_term. iPureIntro. congr (# (LitBool _)).
  apply bool_decide_ext. intuition congruence. }
iIntros "% ->". rewrite {}/b.
case: (bool_decide_reflect (pkR = _ ∨ _)) => [succ|_]; last by wp_pures; eauto.
iAssert (▷ (⌜kR' = kR⌝ ∗
            ⌜kI' = kI⌝ ∗
            ⌜gabI = gabR⌝ ∗
            □ (public gabI → ◇ False)))%I as "#finish".
{ case: succ => - [<-].
  - iClear "H2".
    iDestruct "H1" as "[#fail|H1]".
    { iDestruct "fail" as "[fail|fail]".
      + by iDestruct (aenc_secret_not_compromised_key with "s_kI [//] [//]") as ">[]".
      + by iDestruct (aenc_secret_not_compromised_key with "s_kR [//] [//]") as ">[]". }
    iDestruct "H1" as "(#p_gabI & token & #sess)".
    iPoseProof (session_key_confirmation _ Resp with "sess") as "confR'".
    iPoseProof (own_valid_2 with "confR confR'") as "%valid".
    rewrite -reservation_map_data_op reservation_map_data_valid in valid.
    rewrite to_agree_op_valid_L in valid.
    case: (encode_inj _ _ valid) => -> -> {kI' gabR valid}. by eauto.
  - iClear "H1".
    iDestruct "H2" as "[#fail|H2]".
    { iDestruct "fail" as "[fail|fail]".
      + by iDestruct (aenc_secret_not_compromised_key with "s_kI [//] [//]") as ">[]".
      + by iDestruct (aenc_secret_not_compromised_key with "s_kR [//] [//]") as ">[]". }
    iDestruct "H2" as "(#p_gabR & token & #sess)".
    iPoseProof (session_key_confirmation _ Init with "sess") as "confI'".
    iPoseProof (own_valid_2 with "confI confI'") as "%valid".
    rewrite -reservation_map_data_op reservation_map_data_valid in valid.
    rewrite to_agree_op_valid_L in valid.
    case: (encode_inj _ _ valid) => -> -> {kR' gabI valid}. by eauto. }
wp_pure.
iDestruct "finish" as "(-> & -> & <- & #p_gabI) {H1 H2}".
iMod (secret_public with "s_kI") as "#p_kI'".
iMod (secret_public with "s_kR") as "#p_kR'".
wp_apply wp_key.
wp_bind (send _ _). iApply wp_send => //.
  rewrite [public (TKey Open kI)]public_TKey. by eauto.
wp_pures. wp_apply wp_key.
wp_bind (send _ _). iApply wp_send => //.
  rewrite [public (TKey Open kR)]public_TKey. by eauto.
wp_pures. wp_bind (recv _); iApply wp_recv => //; iIntros (m) "#p_m".
wp_pures; wp_bind (eq_term _ _); iApply wp_eq_term.
rewrite bool_decide_decide decide_True //.
wp_pures; wp_bind (eq_term _ _); iApply wp_eq_term.
rewrite bool_decide_decide decide_True //.
wp_pures; wp_bind (eq_term _ _); iApply wp_eq_term.
rewrite bool_decide_decide decide_True //.
case: (decide (m = gabI)) => [->|ne].
  by iDestruct ("p_gabI" with "p_m") as ">[]".
wp_pures; wp_bind (eq_term _ _); iApply wp_eq_term.
rewrite bool_decide_decide decide_False //.
by wp_pures; eauto.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; sessionΣ].

Lemma pk_dh_secure σ₁ σ₂ (v : val) ts :
  rtc erased_step ([game #()], σ₁) (Val v :: ts, σ₂) →
  v = NONEV ∨ v = SOMEV #true.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_result NotStuck _ _ (λ v _, v = NONEV ∨ v = SOMEV #true)).
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisGS_alloc _) as (?) "(#ctx & seal_tok & key_tok & ? & hon & phase)".
iMod (sessionGS_alloc _) as (?) "nown_tok".
iApply (wp_game with "ctx [seal_tok]") => //.
Qed.
