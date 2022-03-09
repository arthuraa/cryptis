From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import numbers.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role nown session pk_auth dh pk_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisG Σ, !heapGS Σ, !spawnG Σ, !sessionG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types rl : role.

Definition N := nroot.@"nsldh".

Definition game : val := λ: "mkchan",
  let: "c"  := "mkchan" #() in
  let: "nI" := mknonce #() in
  let: "nR" := mknonce #() in
  let: "kI" := mkkey (tag (nroot.@"key") "nI") in
  let: "kR" := mkkey (tag (nroot.@"key") "nR") in
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

Lemma wp_game (mkchan : val) :
  {{{ True }}} mkchan #() {{{ v, RET v; channel v }}} -∗
  enc_pred_token ⊤ -∗
  key_pred_token ⊤ -∗
  nown_token session_name ⊤ -∗
  WP game mkchan {{ v, ⌜v = NONEV ∨ v = SOMEV #true⌝ }}.
Proof.
iIntros "wp_mkchan enc_tok key_tok nown_tok"; rewrite /game; wp_pures.
pose (P rl (kI kR kS : term) :=
  (∃ k, ⌜(if rl is Init then kI else kR) =
         Spec.tag (nroot.@"key") k⌝ ∧
        nonce_meta k (nroot.@"nsl") (kI, kR, kS))%I).
iMod (pk_dh_alloc N P with "nown_tok enc_tok") as "[#ctx _]" => //.
iMod (key_pred_set (nroot.@"key") (λ kt _, ⌜kt = Enc⌝)%I with "key_tok")
  as "[#? _]" => //.
wp_bind (mkchan _); iApply "wp_mkchan" => //.
iIntros "!> %c #cP".
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (λ kI, nonce_meta kI (nroot.@"pub") ()) (λ _, False%I)).
iIntros (kI) "#t_kI #p_kI _ tok_kI".
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (λ _, nonce_meta kI (nroot.@"pub") ()) (λ _, False%I)).
iIntros (kR) "#t_kR #p_kR _ tok_kR".
rewrite (term_meta_token_difference kI (↑nroot.@"pub") ⊤) //.
iDestruct "tok_kI" as "[pub init]".
rewrite (term_meta_token_difference kR (↑nroot.@"pub") ⊤) //.
iDestruct "tok_kR" as "[_ resp]".
wp_pures; wp_tag; wp_bind (mkkey _); iApply wp_mkkey.
set pkI := TKey Enc _.
set skI := TKey Dec _.
wp_pures; wp_tag; wp_bind (mkkey _); iApply wp_mkkey.
set pkR := TKey Enc _.
set skR := TKey Dec _.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  rewrite pterm_TKey sterm_tag; iRight; iSplit => //.
  iExists _, _, _; eauto.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  rewrite pterm_TKey sterm_tag; iRight; iSplit => //.
  iExists _, _, _; eauto.
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
          with "[init] [resp]").
- iApply (wp_pk_dh_init with "[//] [//] [] [] [init]") => //.
  + rewrite [pterm (TKey Enc (Spec.tag _ _))]pterm_TKey sterm_tag.
    iRight; iSplit => //.
    iExists _, _, _; eauto.
  + iIntros "%nI %nR".
    set (kS := mk_session_key _ _ _).
    set (kI' := Spec.tag _ _).
    iMod (term_meta_set _ _ (kI', kR', kS) (nroot.@"nsl") with "init").
      solve_ndisj.
    iModIntro. iExists _. by iFrame.
  + iIntros "!> %a H". iExists a. iSplit; first done.
    iApply "H".
- iApply (wp_pk_dh_resp with "[//] [//] [] [resp]") => //.
  + rewrite [pterm (TKey Enc (Spec.tag _ _))]pterm_TKey sterm_tag.
    iRight; iSplit => //.
    iExists _, _, _; eauto.
  + iIntros "%kI' %nI %nR".
    set (kS := mk_session_key _ _ _).
    set (kR'' := Spec.tag _ _).
    iMod (term_meta_set _ _ (kI', kR'', kS) (nroot.@"nsl") with "resp").
      solve_ndisj.
    iModIntro. iExists _. by iFrame.
  + iIntros "!> %a H"; iExists a; iSplit; first done.
    iApply "H".
iIntros (v1 v2) "[H1 H2]".
iDestruct "H1" as (a) "[-> H1]".
iDestruct "H2" as (b) "[-> H2]".
iModIntro; wp_pures.
case: a => [gabI|]; wp_pures; last by eauto.
case: b => [[pkI' gabR]|]; wp_pures; last by eauto.
iDestruct "H1" as "(#s_gabI & #confI & H1)".
iDestruct "H2" as (kI') "(-> & #p_pkI' & #gabR & #confR & H2)".
iAssert ((nonce_meta kI (nroot.@"pub") () → False) ∧
         |==> nonce_meta kI (nroot.@"pub") ())%I with "[pub]" as "pub"; first iSplit.
- iIntros "#contra".
  by iApply (term_meta_meta_token with "pub contra").
- by iApply (term_meta_set with "pub"); eauto.
wp_eq_term e_pkR; wp_pures.
  case: e_pkR => <- {kR'}.
  iDestruct "H1" as "[#[contra|contra]|H1]".
  - rewrite [pterm (TKey Dec _)]pterm_TKey pterm_tag.
    iDestruct "contra" as "[contra|[_ contra]]".
      iSpecialize ("p_kI" with "contra").
      iAssert (▷ False)%I with "[pub]" as ">[]".
      iModIntro.
      by iDestruct "pub" as "[pub _]"; iApply "pub"; eauto.
    by iMod (wf_key_elim with "contra [//]") as "%".
  - rewrite [pterm (TKey Dec _)]pterm_TKey pterm_tag.
    iDestruct "contra" as "[contra|[_ contra]]".
      iSpecialize ("p_kR" with "contra").
      iAssert (▷ False)%I with "[pub]" as ">[]".
      by iDestruct "pub" as "[pub _]"; iApply "pub"; eauto.
    by iMod (wf_key_elim with "contra [//]") as "%".
  iDestruct "pub" as "[_ >#pub]".
  wp_bind (send _ _); iApply wp_send => //.
    rewrite [pterm skI]pterm_TKey pterm_tag; iModIntro.
    iLeft; iApply "p_kI"; eauto.
  wp_pures; wp_bind (send _ _); iApply wp_send => //.
    rewrite [pterm skR]pterm_TKey pterm_tag; iModIntro.
    iLeft; iApply "p_kR"; eauto.
  iDestruct "H1" as "(#p_gabI & token & #sess)".
  iPoseProof (session_key_confirmation _ Resp with "sess") as "confR'".
  iDestruct "confR" as (k) "[%conf confR]".
  case/Spec.tag_inj: conf => [_ <- {k}].
  iDestruct "confR'" as (k) "[%conf confR']".
  case/Spec.tag_inj: conf => [_ <- {k}] /=.
  iPoseProof (term_meta_agree with "confR confR'") as "%valid".
  case: valid => -> -> {kI' gabR}.
  wp_pures.
  wp_bind (recv _); iApply wp_recv => //; iIntros (m) "#p_m".
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
  wp_pures; eauto.
wp_eq_term e_pkI; wp_pures; last by eauto.
case: e_pkI => <- {kI'}.
iDestruct "H2" as "[[#contra|#contra]|H2]".
- rewrite [pterm (TKey Dec _)]pterm_TKey pterm_tag.
  iDestruct "contra" as "[contra|[_ contra]]".
    iSpecialize ("p_kI" with "contra").
    iAssert (▷ False)%I with "[pub]" as ">[]".
    iModIntro.
    iDestruct "pub" as "[pub _]"; iApply "pub"; eauto.
  by iMod (wf_key_elim with "contra [//]") as "%".
- rewrite [pterm (TKey Dec _)]pterm_TKey pterm_tag.
  iDestruct "contra" as "[contra|[_ contra]]".
    iSpecialize ("p_kR" with "contra").
    iAssert (▷ False)%I with "[pub]" as ">[]".
    by iDestruct "pub" as "[pub _]"; iApply "pub"; eauto.
  by iMod (wf_key_elim with "contra [//]") as "%".
iDestruct "H2" as "(#p_gabR & token & #H2)".
iPoseProof (session_key_confirmation _ Init with "H2") as "confI'".
iDestruct "confI" as (k) "[%conf confI]".
case/Spec.tag_inj: conf => [_ <- {k}].
iDestruct "confI'" as (k) "[%conf confI']".
case/Spec.tag_inj: conf => [_ <- {k}].
iPoseProof (term_meta_agree with "confI confI'") as "%valid".
by case: valid e_pkR => -> _ /(_ eq_refl) [].
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; sessionΣ].

Lemma pk_dh_secure (mkchan : val) σ₁ σ₂ (v : val) ts :
  (∀ `{!heapGS Σ, !cryptisG Σ},
     ⊢ {{{ True }}} mkchan #() {{{ c, RET c; channel c}}}) →
  rtc erased_step ([game mkchan], σ₁) (Val v :: ts, σ₂) →
  v = NONEV ∨ v = SOMEV #true.
Proof.
have ? : heapGpreS F by apply _.
move=> wp_mkchan.
apply (adequate_result NotStuck _ _ (λ v _, v = NONEV ∨ v = SOMEV #true)).
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisG_alloc _) as (?) "(enc_tok & key_tok & _)".
iMod (sessionG_alloc _) as (?) "nown_tok".
iApply (wp_game with "[] [enc_tok] [key_tok]") => //.
iApply wp_mkchan.
Qed.
