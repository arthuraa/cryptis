From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par assert.
From cryptis Require Import lib cryptis primitives tactics role adequacy.
From cryptis.examples Require Import hmqv.
From cryptis.lib Require Import hmqv.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * HMQV: key-compromise impersonation

    An attacker who learns a party's long-term key can impersonate that party,
    but should not be able to impersonate anybody else to it.  In this game,
    the attacker picks whose long-term key leaks, the initiator's or the
    responder's.  One initiator and one responder session then run in
    parallel, each party accepting only the other as its peer, and the key
    returned by the party whose long-term key leaked must stay unguessable.

*)

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !hmqvGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (p_a p_b : nonce) (rl : role) (si : sess_info).

Definition gameN := nroot.@"game".

(** KCI resistance: nothing is assumed of the party's own long-term key. *)
Lemma kci_key_secrecy rl si (p : nonce) :
  session (λ _, False%I) rl si -∗
  ⌜si_static (swap_role rl) si = TExp g p⌝ -∗
  hmqv_key p -∗
  □ (public (si_key si) → ▷ ▷ ◇ public p).
Proof.
iIntros "#sess %e_p #key !> #p_k".
iDestruct "sess" as "(_ & _ & [(_ & _ & #l)|(_ & #ok)])".
- iNext. iNext. by iApply ("l" $! p with "[//] key").
- iDestruct ("ok" with "p_k") as "f". iNext. iNext.
  by iDestruct "f" as "#[]".
Qed.

Definition kci_res p (v : val) : iProp :=
  ⌜v = NONEV⌝ ∨
  ∃ sk : senc_key, ⌜v = repr (Some sk)⌝ ∗ □ (public sk → ▷ ▷ ◇ public p).

Lemma wp_kci_initiator c p_a p_b :
  channel c -∗
  cryptis_ctx -∗
  hmqv_ctx -∗
  hmqv_pred gameN (λ _ _, True)%I (λ _, False)%I -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  WP initiator c p_a (TExp g p_a) (TExp g p_b) (Tag gameN) {{ kci_res p_b }}.
Proof.
iIntros "#? #? #? #? #? #key_b".
wp_apply (wp_initiator _ _ _ _ _ _ (λ _, True)%I True%I)
  as "%r [[-> _]|(%x_a & %X_b & -> & #sess & _)]".
- iFrame "#". by iApply hmqv_key_public.
- iSplit => //. iIntros "%x_a %X_b _ !>". by iSplit.
- by iLeft.
- iRight. iExists _. iSplit; first done.
  by iApply (kci_key_secrecy with "sess [//] key_b").
Qed.

Definition responder : val := λ: "c" "p_b" "P_b" "P_a" "N",
  let: "m1" := responder_listen "c" in
  guard: eq_term (Snd "m1") "P_a" in
  responder_confirm "c" "p_b" "P_b" (Fst "m1") "P_a" "N".

Lemma wp_kci_responder c p_a p_b :
  channel c -∗
  cryptis_ctx -∗
  hmqv_ctx -∗
  hmqv_pred gameN (λ _ _, True)%I (λ _, False)%I -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  WP responder c p_b (TExp g p_b) (TExp g p_a) (Tag gameN) {{ kci_res p_a }}.
Proof.
iIntros "#? #? #? #? #key_a #?". wp_lam. wp_pures.
wp_apply wp_responder_listen; first by iSplit.
iIntros "%X_a %P_a' [#p_Xa _]".
wp_eq_term e; last by wp_pures; iLeft.
subst P_a'. wp_pures.
wp_apply (wp_responder_confirm _ _ _ _ _ _ _ (λ _, True)%I).
{ iFrame "#". iSplit; first by iApply hmqv_key_public.
  iIntros "%x_b _ !>". by iSplit. }
iIntros "%r [->|(%x_b & -> & #sess & _)]".
- by iLeft.
- iRight. iExists _. iSplit; first done.
  by iApply (kci_key_secrecy with "sess [//] key_a").
Qed.

Definition check_key_secrecy : val := λ: "c" "r",
  bind: "sk" := "r" in
  let: "guess" := recv "c" in
  assert: (~ eq_term "sk" "guess").

Lemma wp_check_key_secrecy c p v :
  channel c -∗
  □ (public p ↔ ▷ False) -∗
  kci_res p v -∗
  WP check_key_secrecy c v {{ _, True }}.
Proof.
iIntros "#? #s_p res". wp_lam. wp_pure _ credit:"c1".
iDestruct "res" as "[->|(%sk & -> & #s_sk)]"; wp_pures => //.
wp_apply wp_recv => //. iIntros "%guess #p_guess".
wp_pure _ credit:"c2". wp_pures.
wp_apply wp_assert. wp_eq_term e.
- subst guess. iDestruct ("s_sk" with "p_guess") as "f".
  iMod (lc_fupd_elim_later with "c1 f") as "f'".
  iMod (lc_fupd_elim_later with "c2 f'") as ">#p_p".
  by iDestruct ("s_p" with "p_p") as ">[]".
- wp_pures. iModIntro. by iSplit.
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
  let: "leak_init" := eq_term (recv "c") (TInt 0) in
  send "c" (if: "leak_init" then "p_a" else "p_b");;
  let: "rs" := initiator "c" "p_a" "P_a" "P_b" (Tag gameN) |||
               responder "c" "p_b" "P_b" "P_a" (Tag gameN) in
  check_key_secrecy "c" (if: "leak_init" then Fst "rs" else Snd "rs").

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  hmqv_ctx -∗
  hmqv_pred gameN (λ _ _, True)%I (λ _, False)%I -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #chan #? #?"; rewrite /game; wp_pures.
wp_apply wp_mk_lt_key => //.
iIntros "%p_a (#key_a & s_pa & #p_Pa & _)". wp_pures.
wp_apply wp_mk_lt_key => //.
iIntros "%p_b (#key_b & s_pb & #p_Pb & _)". wp_pures.
wp_apply wp_send => //. wp_pures.
wp_apply wp_send => //. wp_pures.
wp_apply wp_recv => //. iIntros "%m _".
wp_eq_term e; wp_pures.
- iMod (secret_public with "s_pa") as "#p_pa".
  iMod (freeze_secret with "s_pb") as "#s_pb".
  wp_apply wp_send => //. wp_pures.
  wp_apply (wp_par (kci_res p_b) (kci_res p_a)).
  + by iApply wp_kci_initiator.
  + by iApply wp_kci_responder.
  + iIntros "%v_a %v_b [res _] !>". wp_pures.
    by iApply (wp_check_key_secrecy with "chan s_pb res").
- iMod (secret_public with "s_pb") as "#p_pb".
  iMod (freeze_secret with "s_pa") as "#s_pa".
  wp_apply wp_send => //. wp_pures.
  wp_apply (wp_par (kci_res p_b) (kci_res p_a)).
  + by iApply wp_kci_initiator.
  + by iApply wp_kci_responder.
  + iIntros "%v_a %v_b [_ res] !>". wp_pures.
    by iApply (wp_check_key_secrecy with "chan s_pa res").
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; hmqvΣ].

Lemma hmqv_kci_secure σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([run_network game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: cryptis_adequacy.
iIntros (? ? c) "#ctx #chan (_ & _ & _ & hash)".
iMod (hmqvGS_alloc with "hash") as (?) "(#? & tok & _)"; eauto.
iMod (hmqv_pred_set gameN (λ _ _, True)%I (λ _, False)%I with "tok")
  as "[#? _]"; eauto.
by iApply (wp_game with "ctx [//]").
Qed.
