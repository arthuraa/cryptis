From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import numbers reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role session pk_auth dh pk_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types rl : role.

Definition N := nroot.@"nsldh".

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
  let: "res" := pk_dh_init N "c" "skI" "pkI" "pkR'" |||
                pk_dh_resp N "c" "skR" "pkR" in
  bind: "sesskI" := Fst "res" in
  bind: "resR" := Snd "res" in
  let: "pkI'" := Fst "resR" in
  let: "sesskR" := Snd "resR" in
  if: eq_term "pkR" "pkR'" || eq_term "pkI" "pkI'" then
    send "c" "skI";;
    send "c" "skR";;
    let: "m" := recv "c" in
    SOME (eq_term "pkR" "pkR'" && eq_term "pkI" "pkI'" &&
          eq_term "sesskI" "sesskR" && ~ eq_term "m" "sesskI")
  else SOME #true.

(* TODO Avoid exposing these instances *)
Local Existing Instances cryptisGpreS_maps cryptis_inG.

Lemma wp_game (mkchan : val) :
  {{{ True }}} mkchan #() {{{ v, RET v; channel v }}} -∗
  cryptis_ctx -∗
  enc_pred_token ⊤ -∗
  key_pred_token (⊤ ∖ ↑nroot.@"keys") -∗
  session_token ⊤ -∗
  ●H{0} ∅ -∗
  WP game mkchan {{ v, ⌜v = NONEV ∨ v = SOMEV #true⌝ }}.
Proof.
iIntros "wp_mkchan #ctx enc_tok key_tok nown_tok hon"; rewrite /game; wp_pures.
iMod (own_alloc (reservation_map_token ⊤)) as (γI) "tokenI".
  apply reservation_map_token_valid.
iMod (own_alloc (reservation_map_token ⊤)) as (γR) "tokenR".
  apply reservation_map_token_valid.
pose (P rl (kI kR kS : term) :=
  own (if rl is Init then γI else γR)
    (namespace_map_data nroot (to_agree (encode (kI, kR, kS))))).
iMod (pk_dh_alloc N P with "nown_tok enc_tok") as "[#dh_ctx _]" => //.
wp_bind (mkchan _); iApply "wp_mkchan" => //.
iIntros "!> %c #cP".
wp_pures; wp_bind (mkakey _).
iApply (wp_mkakey with "[] [hon]"); eauto.
iIntros "%kI #p_kI hon _". wp_pures.
wp_bind (mkakey _). iApply (wp_mkakey with "[] [hon]"); eauto.
iIntros "%kR #p_kR hon _". wp_pures.
set pkI := TKey Enc kI.
set skI := TKey Dec kI.
set pkR := TKey Enc kR.
set skR := TKey Dec kR.
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
rewrite -Qp.half_half -dfrac_op_own. iDestruct "hon" as "[hon1 hon2]".
iApply (wp_par (λ v, ∃ a : option term, ⌜v = repr a⌝ ∗ _)%I
               (λ v, ∃ a : option (term * term), ⌜v = repr a⌝ ∗ _)%I
          with "[tokenI hon1] [tokenR hon2]").
- iApply (wp_pk_dh_init with "[//] [//] [//] [] [] [tokenI hon1]") => //.
  + iFrame. iIntros "%nI %nR".
    set (kS := mk_session_key _ _ _).
    iMod (own_update with "tokenI") as "ownI".
    * apply (namespace_map_alloc_update _ nroot
               (to_agree (encode (kI, kR', kS)))) => //.
      iPoseProof "ownI" as "#ownI".
      eauto.
    * eauto.
  + iIntros "!> %a H". iExists a. iSplit; first done.
    iApply "H".
- iApply (wp_pk_dh_resp with "[//] [//] [//] [] [tokenR hon2]") => //.
  + iFrame. iIntros "%kI' %nI %nR".
    set (kS := mk_session_key _ _ _).
    iMod (own_update with "tokenR") as "ownR".
    * apply (namespace_map_alloc_update _ nroot
               (to_agree (encode (kI', kR, kS)))) => //.
      iPoseProof "ownR" as "#ownR".
      eauto.
    * eauto.
  + iIntros "!> %a H"; iExists a; iSplit; first done.
    iApply "H".
iIntros (v1 v2) "[H1 H2]".
iDestruct "H1" as (a) "[-> [hon1 H1]]".
iDestruct "H2" as (b) "[-> [hon2 H2]]".
iCombine "hon1 hon2" as "hon". rewrite dfrac_op_own Qp.half_half.
iModIntro.
iMod (compromise_honest with "ctx hon") as "[hon comp]" => //.
wp_pures.
iMod "comp" as "#comp".
case: a => [gabI|]; wp_pures; last by eauto.
case: b => [[pkI' gabR]|]; wp_pures; last by eauto.
iDestruct "H1" as "(#s_gabI & #confI & _ & H1)".
iDestruct "H2" as (kI') "(-> & #p_pkI' & #gabR & #confR & _ & H2)".
pose (b := bool_decide (pkR = TKey Enc kR' ∨ pkI = TKey Enc kI')).
wp_bind (eq_term pkR _ || _)%E.
iApply (wp_wand _ _ _ (λ v, ⌜v = #b⌝)%I with "[] [H1 H2]").
{ wp_eq_term e_pkR; wp_pures.
    iPureIntro. by rewrite /b bool_decide_decide decide_True //; eauto.
  iApply wp_eq_term. iPureIntro. congr (# (LitBool _)).
  apply bool_decide_ext. intuition congruence. }
iIntros "% ->". rewrite {}/b.
case: (bool_decide_reflect (pkR = _ ∨ _)) => [succ|_]; last by wp_pures; eauto.
iAssert (⌜kR' = kR⌝ ∗
         ⌜kI' = kI⌝ ∗
         ⌜gabI = gabR⌝ ∗
         □ (public gabI → ◇ False))%I with "[H1 H2]" as "#finish".
{ case: succ => - [<-].
  - iClear "H2".
    rewrite /in_honest bool_decide_decide decide_True; try set_solver.
    iDestruct "H1" as "(#p_gabI & token & #sess)".
    iPoseProof (session_key_confirmation _ Resp with "sess") as "confR'".
    iPoseProof (own_valid_2 with "confR confR'") as "%valid".
    rewrite -reservation_map_data_op reservation_map_data_valid in valid.
    rewrite to_agree_op_valid_L in valid.
    case: (encode_inj _ _ valid) => -> -> {kI' gabR valid}. by eauto.
  - iClear "H1".
    rewrite /in_honest bool_decide_decide decide_True; try set_solver.
    iDestruct "H2" as "(#p_gabR & token & #sess)".
    iPoseProof (session_key_confirmation _ Init with "sess") as "confI'".
    iPoseProof (own_valid_2 with "confI confI'") as "%valid".
    rewrite -reservation_map_data_op reservation_map_data_valid in valid.
    rewrite to_agree_op_valid_L in valid.
    case: (encode_inj _ _ valid) => -> -> {kR' gabI valid}. by eauto. }
iDestruct "finish" as "(-> & -> & <- & #p_gabI) {H1 H2}".
wp_pures. wp_bind (send _ _). iApply wp_send => //.
  iModIntro. rewrite big_sepS_forall. iApply "comp".
  iPureIntro; set_solver.
wp_pures. wp_bind (send _ _). iApply wp_send => //.
  iModIntro. rewrite big_sepS_forall. iApply "comp".
  iPureIntro; set_solver.
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

Lemma pk_dh_secure (mkchan : val) σ₁ σ₂ (v : val) ts :
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
iMod (cryptisGS_alloc _) as (?) "(#ctx & enc_tok & key_tok & ? & hon)".
iMod (sessionGS_alloc _) as (?) "nown_tok".
iApply (wp_game with "[] ctx [enc_tok] [key_tok] [nown_tok] [hon]") => //.
iApply wp_mkchan.
Qed.
