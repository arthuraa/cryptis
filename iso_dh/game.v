From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import numbers reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par assert ticket_lock.
From cryptis Require Import lib cryptis primitives tactics gmeta.
From cryptis Require Import role iso_dh.
From cryptis.lib Require Import term_set.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Existing Instance ticket_lock.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types rl : role.

Definition gameN := nroot.@"game".

Definition compromise_long_term_keys : val :=
  λ: "c" "compromised" "skI" "skR",
    "compromised" <- #true;;
    send "c" "skI";;
    send "c" "skR".

Definition wait_for_compromise : val :=
  rec: "loop" "compromised" :=
    if: !"compromised" then #()
    else "loop" "compromised".

Definition check_key_secrecy : val :=
  λ: "c" "compromised" "sk",
    if: ~ !"compromised" then
      wait_for_compromise "compromised";;
      let: "guess" := recv "c" in
      assert: (~ eq_term "sk" "guess")
    else #().

Definition game_inv lcomp skI skR : iProp :=
  ∃ compromised : bool,
    lcomp ↦ #compromised ∗
    if compromised then public skI ∗ public skR
    else secret skI ∗ secret skR.

Lemma wp_compromise_long_term_keys c lcomp skI skR :
  {{{ cryptis_ctx ∗
      channel c ∗
      inv gameN (game_inv lcomp skI skR) }}}
    compromise_long_term_keys c #lcomp skI skR
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ (#? & #? & #?) post".
wp_lam. wp_pure _ credit:"c1". wp_pures.
wp_bind (_ <- _)%E. iInv gameN as "(%bcomp & >lcomp & inv)". wp_store.
iAssert (|==> (public skI ∗ public skR))%I
  with "[inv]" as ">#[p_skI p_skR]".
{ case: bcomp => //.
  iDestruct "inv" as "[s_skI s_skR]".
  iMod (secret_public with "s_skI") as "#?".
  iMod (secret_public with "s_skR") as "#?".
  by eauto. }
iModIntro. iSplitL "lcomp"; first by iFrame; eauto.
wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_send => //.
by iApply "post".
Qed.

Lemma wp_wait_for_compromise lcomp skI skR :
  {{{ cryptis_ctx ∗
      inv gameN (game_inv lcomp skI skR) }}}
    wait_for_compromise #lcomp
  {{{ RET #(); public skI ∗ public skR }}}.
Proof.
iLöb as "IH". iIntros "%Φ (#? & #?) post".
wp_rec. wp_bind (!_)%E. iInv gameN as "(%bcomp & lcomp & inv)".
wp_load. iModIntro.
iAssert (□ if bcomp then public skI ∗ public skR
           else True)%I as "#?".
{ case: bcomp => //. iPoseProof "inv" as "#inv". by eauto. }
 iSplitL "lcomp inv"; first by iFrame.
case: bcomp; wp_pures; first by iApply "post".
by wp_apply "IH"; eauto.
Qed.

Lemma wp_check_key_secrecy c lcomp si :
  {{{ cryptis_ctx ∗
      channel c ∗
      inv gameN (game_inv lcomp (si_init si) (si_resp si)) ∗
      sign_key (si_init si) ∗ sign_key (si_resp si) ∗
      key_secrecy si ∗ □ (released_session si → False) }}}
    check_key_secrecy c #lcomp (si_key si)
  {{{ RET #(); True }}}.
Proof.
set skI := si_init si. set skR := si_resp si.
iIntros "%Φ (#? & #? & #? & #? & #? & #s_sk & #un) post".
rewrite /check_key_secrecy.
wp_pure _ credit:"c1".
wp_pure _ credit:"c2".
wp_pures.
wp_bind (!_)%E.
iInv gameN as "(%bcomp & >Hcomp & inv)".
wp_load. case: bcomp.
{ iModIntro. iSplitR "post"; first by iExists true; eauto.
  wp_pures. by iApply "post". }
iDestruct "inv" as "[s_skI s_skR]".
iAssert (|={⊤ ∖ ↑gameN}=> secret skI ∗ secret skR ∗
                          □ (public (si_key si) → ▷ False))%I
  with "[c1 s_skI s_skR]" as "{s_sk} >(s_skI & s_skR & #s_sk)".
{ iPoseProof (secret_key_secrecy with "s_skI s_skR [//] [//] [//]")
    as "{s_sk} #>#s_sk".
  iFrame. iIntros "!> !> #p_k". iApply "un". by iApply "s_sk". }
iModIntro. iSplitR "post".
{ iExists false; iFrame. }
wp_pures. wp_apply wp_wait_for_compromise; eauto.
iIntros "#[p_skI p_skR]". wp_pures. wp_apply wp_recv => //.
iIntros "%guess #p_guess". wp_pures.
wp_apply wp_assert. wp_eq_term e.
{ subst guess. iDestruct ("s_sk" with "p_guess") as ">[]". }
wp_pures. iModIntro. iSplit => //. by iApply "post".
Qed.

Definition do_init_loop : val :=
  rec: "loop" "c" "compromised" "set" "skI" "vkR" :=
    Fork ("loop" "c" "compromised" "set" "skI" "vkR");;
    let: "vkR'" := recv "c" in
    (bind: "kt" := is_key "vkR'" in
     guard: ("kt" = repr Open) in
     bind: "sk" := initiator isoN "c" "skI" "vkR'" in
     add_fresh_lock_term_set "sk" "set";;
     if: eq_term "vkR" "vkR'" then check_key_secrecy "c" "compromised" "sk"
     else #());;
     #().

Definition do_init : val := λ: "c" "compromised" "skI" "vkR",
  let: "set" := new_lock_term_set #() in
  do_init_loop "c" "compromised" "set" "skI" "vkR".

Definition iso_dh_game_inv rl x : iProp := ∃ si,
  ⌜si_key si = x⌝ ∧
  term_meta (si_share_of rl si) (isoN.@"fresh") ().

Lemma iso_dh_game_fresh rl si :
  term_token (si_share_of rl si) (↑isoN) -∗
  fresh_term (iso_dh_game_inv rl) (si_key si) ∗
  term_token (si_share_of rl si) (↑isoN ∖ ↑isoN.@"fresh").
Proof.
iIntros "token".
iPoseProof (term_token_difference _ (↑isoN.@"fresh") with "token")
  as "[token ?]" => //; first solve_ndisj. iFrame. iSplit.
- iIntros "# (%si' & %e & #meta)".
  rewrite (session_agree e).
  by iDestruct (term_meta_token with "token meta") as "[]".
- iMod (term_meta_set (isoN.@"fresh") () with "token") as "#meta" => //.
  iIntros "!> !>". iExists si. by eauto.
Qed.

Lemma wp_do_init_loop c lcomp vset kI kR :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx isoN -∗
  sign_key kI -∗
  sign_key kR -∗
  inv gameN (game_inv lcomp kI kR) -∗
  is_lock_term_set (iso_dh_game_inv Init) vset -∗
  {{{ True }}}
    do_init_loop c #lcomp vset kI (TKey Open kR)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #p_vkI #p_vkR #inv #set".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ by iApply "IH" => //. }
wp_pures. wp_apply wp_recv => //.
iIntros (ekR') "#p_ekR'".
wp_pures; wp_bind (is_key _); iApply wp_is_key. wp_pures.
case: Spec.is_keyP => [kt kR' eekR|_]; wp_pures; last by iApply "Hpost".
wp_pures.
case: bool_decide_reflect => [ekt|_]; wp_pures ; last by iApply "Hpost".
case: kt eekR ekt => // -> _.
wp_pures. wp_apply wp_initiator => //. iIntros "%ts tsP".
case: ts=> [sk|] => /=; wp_pures; last by iApply "Hpost".
iDestruct "tsP"
  as "(%si & <- & <- & <- & #m_sk & #s_k & rel & token)".
iPoseProof (iso_dh_game_fresh Init with "token") as "[fresh token]".
iMod (unrelease with "rel") as "#un".
iAssert (□ ¬ released_session si)%I as "#?".
{ iIntros "!> #?". by iApply (unreleased_released_session _ Init). }
wp_apply (wp_add_fresh_lock_term_set with "[$]"). iIntros "_".
wp_pures. wp_eq_term e; wp_pures; last by iApply "Hpost".
case: e => -> {kR}.
wp_pures. wp_apply wp_check_key_secrecy => //.
{ by eauto 10. }
iIntros "_". wp_pures.
by iApply "Hpost".
Qed.

Lemma wp_do_init c lcomp kI kR :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx isoN -∗
  sign_key kI -∗
  sign_key kR -∗
  inv gameN (game_inv lcomp kI kR) -∗
  {{{ True }}}
    do_init c #lcomp kI (TKey Open kR)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #p_pkI #p_pkR #? %Φ _ !> post".
wp_lam. wp_pures.
wp_apply (wp_new_lock_term_set (iso_dh_game_inv Init)) => //.
iIntros "%set #set". wp_pures.
wp_apply wp_do_init_loop => //.
Qed.

Definition do_resp_loop : val :=
  rec: "loop" "c" "compromised" "set" "skR" "vkI" :=
    Fork ("loop" "c" "compromised" "set" "skR" "vkI");;
    (bind: "res" := responder isoN "c" "skR" in
     let: "vkI'" := Fst "res" in
     let: "sk" := Snd "res" in
     add_fresh_lock_term_set "sk" "set";;
     if: eq_term "vkI" "vkI'" then
       check_key_secrecy "c" "compromised" "sk"
     else #());;
    #().

Definition do_resp : val := λ: "c" "compromised" "skR" "vkI",
  let: "set" := new_lock_term_set #() in
  do_resp_loop "c" "compromised" "set" "skR" "vkI".

Lemma wp_do_resp_loop c lcomp set skI skR :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx isoN -∗
  sign_key skI -∗
  sign_key skR -∗
  inv gameN (game_inv lcomp skI skR) -∗
  is_lock_term_set (iso_dh_game_inv Resp) set -∗
  {{{ True }}}
    do_resp_loop c #lcomp set skR (TKey Open skI)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #p_vkI #p_vkR #? #set".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ iApply "IH" => //. }
wp_pures. wp_apply wp_responder; first by eauto.
iIntros "%res res".
case: res => [[vkI' sk]|]; wp_pures; last by iApply "Hpost".
iDestruct "res"
  as "(%si & -> & <- & <- & #p_vkI' & #m_sk & #s_k & rel & token)".
iPoseProof (iso_dh_game_fresh Resp with "token") as "[fresh token]".
iMod (unrelease with "rel") as "#un".
iAssert (¬ released_session si)%I as "?".
{ iIntros "#?". by iApply (unreleased_released_session _ Resp). }
wp_apply (wp_add_fresh_lock_term_set with "[$]"). iIntros "_".
wp_eq_term e; wp_pures; last by iApply "Hpost".
case: e => -> {skI}.
wp_apply (wp_check_key_secrecy _ lcomp) => //; eauto 10.
iIntros "_". wp_pures. by iApply "Hpost".
Qed.

Lemma wp_do_resp c lcomp skI skR :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx isoN -∗
  sign_key skI -∗
  sign_key skR -∗
  inv gameN (game_inv lcomp skI skR) -∗
  {{{ True }}}
    do_resp c #lcomp skR (TKey Open skI)
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #? #? #? #? %Φ _ !> post".
wp_lam. wp_pures.
wp_apply (wp_new_lock_term_set (iso_dh_game_inv Resp)) => //.
iIntros "%set #set". wp_pures.
by wp_apply wp_do_resp_loop => //.
Qed.

Definition game : val := λ: <>,
  let: "c"   := init_network #() in
  let: "skI" := mksigkey #() in
  let: "skR" := mksigkey #() in
  let: "vkI" := vkey "skI" in
  let: "vkR" := vkey "skR" in
  let: "compromised" := ref #false in
  send "c" "vkI";;
  send "c" "vkR";;
  Fork (do_init "c" "compromised" "skI" "vkR");;
  Fork (do_resp "c" "compromised" "skR" "vkI");;
  Fork (compromise_long_term_keys "c" "compromised" "skI" "skR").

Lemma wp_game :
  cryptis_ctx -∗
  seal_pred_token ⊤ -∗
  key_pred_token (⊤ ∖ ↑nroot.@"keys") -∗
  WP game #() {{ _, True }}.
Proof.
iIntros "#ctx enc_tok key_tok"; rewrite /game; wp_pures.
iMod (iso_dh_ctx_alloc isoN with "enc_tok") as "#?" => //.
wp_apply wp_init_network => //. iIntros "%c #cP". wp_pures.
wp_apply (wp_mksigkey with "[]"); eauto.
iIntros "%skI #p_vkI #sign_skI s_skI tokenI". wp_pures.
wp_pures. wp_apply (wp_mksigkey with "[]"); eauto.
iIntros "%skR #p_vkR #sign_skR s_skR tokenR". wp_pures.
wp_apply wp_vkey. wp_pures.
wp_apply wp_vkey. wp_pures.
wp_alloc lcomp as "lcomp".
iMod (inv_alloc gameN _ (game_inv lcomp skI skR)
  with "[s_skI s_skR lcomp]") as "#?".
{ iFrame. }
wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_send => //.
wp_pures.
wp_apply wp_fork; first by wp_apply wp_do_init. wp_pures.
wp_apply wp_fork; first by wp_apply wp_do_resp. wp_pures.
by wp_apply wp_fork; first wp_apply wp_compromise_long_term_keys; eauto.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; tlockΣ].

Lemma iso_dh_secure σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([game #()], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisGS_alloc _) as (?) "(#ctx & enc_tok & key_tok & ? & _ & _)".
by iApply (wp_game with "ctx [enc_tok] [key_tok]") => //.
Qed.
