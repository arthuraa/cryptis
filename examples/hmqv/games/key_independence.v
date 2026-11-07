From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import assert.
From cryptis Require Import lib cryptis primitives tactics role adequacy.
From cryptis.examples Require Import hmqv.
From cryptis.lib Require Import hmqv.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * HMQV: key independence

    The initiator and the responder run sessions with each other in parallel,
    and their long-term keys never leak.  Each time the responder completes a
    session, it checks that the attacker cannot guess the key, and then leaks
    the key.  So the keys of some sessions do not help the attacker guess the
    keys of the others.

*)

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !hmqvGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (p_a p_b : nonce) (si : sess_info).

Definition gameN := nroot.@"game".

(** The responder releases a session once it has checked its key. *)
Definition released si : iProp := term_meta (si_resp_share si) gameN ().

Definition check_key_secrecy : val := λ: "c" "sk",
  let: "guess" := recv "c" in
  assert: (~ eq_term "sk" "guess").

Lemma wp_check_key_secrecy c si :
  {{{ channel c ∗ term_token (si_resp_share si) (↑gameN) ∗
      □ (public (si_key si) → ▷ ▷ □ released si) }}}
    check_key_secrecy c (si_key si)
  {{{ RET #(); term_token (si_resp_share si) (↑gameN) }}}.
Proof.
iIntros "%Φ (#chan & tok & #s_k) post". wp_lam. wp_pure _ credit:"c1".
wp_pures. wp_apply wp_recv => //. iIntros "%guess #p_guess". wp_pures.
wp_apply wp_assert. wp_eq_term e.
- subst guess. iDestruct ("s_k" with "p_guess") as "f".
  iMod (lc_fupd_elim_later with "c1 f") as ">#rel".
  by iDestruct (term_meta_token with "tok rel") as "[]".
- wp_pures. iModIntro. iSplit => //. by iApply "post".
Qed.

Definition do_init : val :=
  rec: "loop" "c" "p_a" "P_a" "P_b" :=
    Fork ("loop" "c" "p_a" "P_a" "P_b");;
    initiator "c" "p_a" "P_a" "P_b" (Tag gameN);;
    #().

Lemma wp_do_init c p_a p_b :
  channel c -∗
  cryptis_ctx -∗
  hmqv_ctx -∗
  hmqv_pred gameN (λ _ _, True)%I released -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  {{{ True }}}
    do_init c p_a (TExp g p_a) (TExp g p_b)
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #? #? #? #key_b".
iLöb as "IH". iIntros "!> %Φ _ post".
wp_rec. wp_pures. wp_apply wp_fork; first by iApply "IH".
wp_pures.
wp_apply (wp_initiator _ _ _ _ _ _ (λ _, True)%I True%I) as "%r _".
- iFrame "#". by iApply hmqv_key_public.
- iSplit => //. iIntros "%x_a %X_b _ !>". by iSplit.
- wp_pures. by iApply "post".
Qed.

Definition do_resp : val :=
  rec: "loop" "c" "p_b" "P_b" "P_a" :=
    Fork ("loop" "c" "p_b" "P_b" "P_a");;
    let: "m1" := responder_listen "c" in
    (guard: eq_term (Snd "m1") "P_a" in
     bind: "sk" :=
       responder_confirm "c" "p_b" "P_b" (Fst "m1") "P_a" (Tag gameN) in
     check_key_secrecy "c" "sk";;
     send "c" "sk");;
    #().

Lemma wp_do_resp c p_a p_b :
  channel c -∗
  cryptis_ctx -∗
  hmqv_ctx -∗
  hmqv_pred gameN (λ _ _, True)%I released -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  □ (public p_a ↔ ▷ False) -∗
  {{{ True }}}
    do_resp c p_b (TExp g p_b) (TExp g p_a)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #? #key_a #key_b #s_pa".
iLöb as "IH". iIntros "!> %Φ _ post".
wp_rec. wp_pures. wp_apply wp_fork; first by iApply "IH".
wp_pures. wp_apply wp_responder_listen; first by iSplit.
iIntros "%X_a %P_a' [#p_Xa #p_Pa']". wp_pures.
wp_eq_term e; wp_pures; last by iApply "post".
subst P_a'.
wp_apply (wp_responder_confirm _ _ _ _ _ _ _
            (λ si, term_token (si_resp_share si) (⊤ ∖ ↑hmqvN))).
{ iFrame "#". iIntros "%x_b tok !>". by iFrame. }
iIntros "%r [->|(%x_b & -> & #sess & tok & _)]"; wp_pures.
  by iApply "post".
set si := resp_si (TExp g p_a) X_a p_b x_b.
iAssert (◇ □ (public (si_key si) → ▷ ▷ □ released si))%I as ">#s_k".
{ iDestruct "sess" as "(_ & _ & [(_ & _ & #l)|(_ & #ok)])".
  - iMod ("l" $! p_a with "[//] key_a") as "#p".
    by iDestruct ("s_pa" with "p") as ">[]".
  - by iIntros "!> !>". }
iPoseProof (term_token_drop (↑gameN) with "tok") as "tok"; first solve_ndisj.
wp_apply (wp_check_key_secrecy with "[tok]"); first by iFrame "∗#".
iIntros "tok". iMod (term_meta_set gameN () with "tok") as "#rel" => //.
iAssert (public (si_key si)) as "#p_k".
{ iApply (session_release with "sess"). by iIntros "!> !>". }
wp_pures. wp_apply wp_send => //. wp_pures. by iApply "post".
Qed.

Definition game : val := λ: "c",
  let: "k_a" := mk_lt_key #() in
  let: "k_b" := mk_lt_key #() in
  let: "p_a" := Fst "k_a" in
  let: "P_a" := Snd "k_a" in
  let: "p_b" := Fst "k_b" in
  let: "P_b" := Snd "k_b" in
  send "c" "P_a";;
  send "c" "P_b";;
  Fork (do_init "c" "p_a" "P_a" "P_b");;
  do_resp "c" "p_b" "P_b" "P_a".

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  hmqv_ctx -∗
  hmqv_pred gameN (λ _ _, True)%I released -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #? #? #?"; rewrite /game; wp_pures.
wp_apply wp_mk_lt_key => //.
iIntros "%p_a (#key_a & s_pa & #p_Pa & _)". wp_pures.
wp_apply wp_mk_lt_key => //.
iIntros "%p_b (#key_b & _ & #p_Pb & _)". wp_pures.
iMod (freeze_secret with "s_pa") as "#s_pa".
wp_apply wp_send => //. wp_pures.
wp_apply wp_send => //. wp_pures.
wp_apply wp_fork; first by wp_apply wp_do_init. wp_pures.
by wp_apply wp_do_resp.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; cryptisΣ; hmqvΣ].

Lemma hmqv_key_independence σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([run_network game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: cryptis_adequacy.
iIntros (? ? c) "#ctx #chan (_ & _ & _ & hash)".
iMod (hmqvGS_alloc with "hash") as (?) "(#? & tok & _)"; eauto.
iMod (hmqv_pred_set gameN (λ _ _, True)%I released with "tok")
  as "[#? _]"; eauto.
by iApply (wp_game with "ctx [//]").
Qed.
