From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.algebra Require Import numbers.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par.
From crypto Require Import lib term crypto primitives tactics.
From crypto Require Import session nsl dh nsl_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptoG Σ, !heapG Σ, !spawnG Σ, !sessionG Σ}.
Context `{inG Σ (authR max_natUR)}.
Context `{inG Σ (authR (optionUR (agreeR positiveO)))}.
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
  let: "res" := nsl_dh_init N "c" Spec.zero "skI" "pkI" "pkR'" |||
                nsl_dh_resp N "c" Spec.zero "skR" "pkR" in
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

Lemma own_Some_agree_2 `{Countable X} γ (x y : X) :
  own γ (◯ Some (to_agree (encode x))) -∗
  own γ (◯ Some (to_agree (encode y))) -∗
  ⌜x = y⌝.
Proof.
iIntros "own1 own2".
iPoseProof (own_valid_2 with "own1 own2") as "%valid".
move: valid; rewrite -auth_frag_op -Some_op auth_frag_valid Some_valid.
by move=> /agree_op_invL' /(@encode_inj _ _ _ x y) ->.
Qed.

Lemma wp_game (mkchan : val) :
  {{{ True }}} mkchan #() {{{ v, RET v; channel v }}} -∗
  enc_pred_token ⊤ -∗
  key_pred_token ⊤ -∗
  WP game mkchan {{ v, ⌜v = NONEV ∨ v = SOMEV #true⌝ }}.
Proof.
iIntros "wp_mkchan enc_tok key_tok"; rewrite /game; wp_pures.
iMod (own_alloc (● (MaxNat 0))) as (γk) "own".
  by rewrite auth_auth_valid.
iMod (own_alloc (● None)) as (γ_init) "init" => //.
  by rewrite auth_auth_valid.
iMod (own_alloc (● None)) as (γ_resp) "resp" => //.
  by rewrite auth_auth_valid.
pose (P rl (t1 t2 t3 t4 : term) :=
  if rl is Init then
    own γ_init (◯ (Some (to_agree (encode (t1, t2, t3, t4)))))
  else
    own γ_resp (◯ (Some (to_agree (encode (t1, t2, t3, t4)))))).
iMod (nsl_dh_alloc N P Spec.zero with "enc_tok") as (γdh) "#ctx" => //.
iMod (key_pred_set (nroot.@"key") (λ kt _, ⌜kt = Enc⌝)%I with "key_tok")
  as "#?" => //.
wp_bind (mkchan _); iApply "wp_mkchan" => //.
iIntros "!> %c #cP".
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (own γk (◯ (MaxNat 1))) (λ _, False%I)).
iIntros (kI) "#t_kI #p_kI _ tok_kI".
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (own γk (◯ (MaxNat 1))) (λ _, False%I)).
iIntros (kR) "#t_kR #p_kR _ tok_kR".
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
- iApply (wp_nsl_dh_init P P with "[//] [//] [] [] [//] [init]") => //.
  + by rewrite sterm_TInt.
  + rewrite [pterm (TKey Enc (Spec.tag _ _))]pterm_TKey sterm_tag.
    iRight; iSplit => //.
    iExists _, _, _; eauto.
  + iIntros (ga gb).
    pose (x := Some (to_agree (encode (ga, gb, Spec.tag (nroot.@"key") kI, kR')))).
    iMod (own_update _ _ (● x ⋅ ◯ x) with "init") as "[_ #init]".
      apply: auth_update_alloc.
      apply: alloc_option_local_update => //.
    by iModIntro; iSplit.
  + iIntros (?) "H"; iExists a; iSplit; first done.
    iApply "H".
- iApply (wp_nsl_dh_resp P P with "[//] [//] [] [] [resp]") => //.
  + eauto.
  + by rewrite sterm_TInt.
  + rewrite [pterm (TKey Enc (Spec.tag _ _))]pterm_TKey sterm_tag.
    iRight; iSplit => //.
    iExists _, _, _; eauto.
  + iIntros (ga gb kI').
    pose (x := Some (to_agree (encode (ga, gb, kI', Spec.tag (nroot.@"key") kR)))).
    iMod (own_update _ _ (● x ⋅ ◯ x) with "resp") as "[_ #resp]".
      apply: auth_update_alloc.
      apply: alloc_option_local_update => //.
    by iModIntro; iSplit.
  + iIntros (?) "H"; iExists a; iSplit; first done.
    iApply "H".
iIntros (v1 v2) "[H1 H2]".
iDestruct "H1" as (a) "[-> H1]".
iDestruct "H2" as (b) "[-> H2]".
iModIntro; wp_pures.
case: a => [gabI|]; wp_pures; last by eauto.
case: b => [[pkI' gabR]|]; wp_pures; last by eauto.
iDestruct "H1" as (a gb) "#(-> & s_gabI & init & H1)".
iDestruct "H2" as (kI' b ga) "#(-> & -> & p_pkI' & s_gabR & resp & H2)".
iAssert ((own γk (◯ MaxNat 1) → False) ∧
         |==> own γk (◯ MaxNat 1))%I with "[own]" as "own"; first iSplit.
- iIntros "#contra".
  iPoseProof (own_valid_2 with "own contra") as "%contra".
  move: contra; rewrite auth_both_valid max_nat_included /=.
  by case; lia.
- iMod (own_update _ _ (● MaxNat 1 ⋅ ◯ MaxNat 1) with "own")
    as "[_ #own]"; eauto.
  apply: auth_update_alloc.
  apply: max_nat_local_update; simpl; lia.
wp_eq_term e_pkR; wp_pures.
  case: e_pkR => <- {kR'}.
  iDestruct "H1" as "[[contra|contra]|H1]".
  - rewrite [pterm (TKey Dec _)]pterm_TKey pterm_tag.
    iDestruct "contra" as "[contra|[_ contra]]".
      iSpecialize ("p_kI" with "contra").
      iAssert (▷ False)%I with "[own]" as ">[]".
      iModIntro.
      by iDestruct "own" as "[own _]"; iApply "own"; eauto.
    by iMod (wf_key_elim with "contra [//]") as "%".
  - rewrite [pterm (TKey Dec _)]pterm_TKey pterm_tag.
    iDestruct "contra" as "[contra|[_ contra]]".
      iSpecialize ("p_kR" with "contra").
      iAssert (▷ False)%I with "[own]" as ">[]".
      by iDestruct "own" as "[own _]"; iApply "own"; eauto.
    by iMod (wf_key_elim with "contra [//]") as "%".
  iDestruct "own" as "[_ >#own]".
  wp_bind (send _ _); iApply wp_send => //.
    rewrite [pterm skI]pterm_TKey pterm_tag; iModIntro.
    iLeft; iApply "p_kI"; eauto.
  wp_pures; wp_bind (send _ _); iApply wp_send => //.
    rewrite [pterm skR]pterm_TKey pterm_tag; iModIntro.
    iLeft; iApply "p_kR"; eauto.
  iDestruct "H1" as (b') "# (-> & resp' & sec)".
  iPoseProof (own_Some_agree_2 with "resp resp'") as "%valid".
  case: valid => -> /TExp_inj [_ /(Permutation_singleton_inj b b') <-] ->.
  wp_pures.
  wp_bind (recv _); iApply wp_recv => //; iIntros (m) "#p_m".
  wp_pures; wp_bind (eq_term _ _); iApply wp_eq_term.
  rewrite bool_decide_decide decide_True //.
  wp_pures; wp_bind (eq_term _ _); iApply wp_eq_term.
  rewrite bool_decide_decide decide_True //.
  wp_pures; wp_bind (eq_term _ _); iApply wp_eq_term.
  rewrite !Spec.texpA TExpC2 bool_decide_decide decide_True //.
  case: (decide (m = TExp Spec.zero [b; a])) => [->|ne].
    by iDestruct ("sec" with "p_m") as ">[]".
  wp_pures; wp_bind (eq_term _ _); iApply wp_eq_term.
  rewrite bool_decide_decide decide_False //.
  wp_pures; eauto.
wp_eq_term e_pkI; wp_pures; last by eauto.
case: e_pkI => <- {kI'}.
iDestruct "H2" as "[[contra|contra]|H2]".
- rewrite [pterm (TKey Dec _)]pterm_TKey pterm_tag.
  iDestruct "contra" as "[contra|[_ contra]]".
    iSpecialize ("p_kI" with "contra").
    iAssert (▷ False)%I with "[own]" as ">[]".
    iModIntro.
    by iDestruct "own" as "[own _]"; iApply "own"; eauto.
  by iMod (wf_key_elim with "contra [//]") as "%".
- rewrite [pterm (TKey Dec _)]pterm_TKey pterm_tag.
  iDestruct "contra" as "[contra|[_ contra]]".
    iSpecialize ("p_kR" with "contra").
    iAssert (▷ False)%I with "[own]" as ">[]".
    by iDestruct "own" as "[own _]"; iApply "own"; eauto.
  by iMod (wf_key_elim with "contra [//]") as "%".
iDestruct "H2" as (a') "#(-> & init' & ?)".
iPoseProof (own_Some_agree_2 with "init init'") as "%e".
by case: e e_pkR => _ _ -> /(_ eq_refl) [].
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ;
    spawnΣ;
    cryptoΣ;
    sessionΣ;
    GFunctor (authR max_natUR);
    GFunctor (authR (optionUR (agreeR positiveO)))].

Lemma nsl_dh_secure (mkchan : val) σ₁ σ₂ (v : val) ts :
  (∀ `{!heapG Σ, !cryptoG Σ},
     ⊢ {{{ True }}} mkchan #() {{{ c, RET c; channel c}}}) →
  rtc erased_step ([game mkchan], σ₁) (Val v :: ts, σ₂) →
  v = NONEV ∨ v = SOMEV #true.
Proof.
have ? : heapPreG F by apply _.
move=> wp_mkchan.
apply (adequate_result NotStuck _ _ (λ v _, v = NONEV ∨ v = SOMEV #true)).
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptoG_alloc _) as (?) "(enc_tok & key_tok & _)".
iApply (wp_game with "[] [enc_tok] [key_tok]") => //.
iApply wp_mkchan.
Qed.
