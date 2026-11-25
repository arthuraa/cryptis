From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par assert.
From cryptis Require Import lib cryptis primitives tactics role adequacy.
From cryptis.lib Require Import hmqv.
From cryptis.examples Require Import alist.
From cryptis.examples.opaque Require Import impl shared client_proofs.
From cryptis.examples.opaque Require Import server_proofs.
From cryptis.examples.opaque.games Require Import base.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * OPAQUE: key-compromise impersonation

    An attacker who steals the server's file can impersonate the server, but
    should not be able to impersonate the client to the server.  In this game,
    the server's file leaks.  One client and one server session then run in
    parallel, and the key returned by the server must stay unguessable.

    Unlike the HMQV game, the attacker does not get to pick whose long-term
    secret leaks: the client's is its password, and whoever knows the password
    can impersonate the server to the client -- by answering with an OPRF key
    and an envelope of its own -- so the client has no KCI resistance to
    test. *)

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !opaqueGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (rl : role) (si : sess_info) (pw : term).

(** KCI resistance: nothing is assumed of the file. *)
Lemma kci_key_secrecy pw si :
  session pw (λ _, False%I) Resp si -∗
  □ (public (si_key si) → ▷ ◇ public pw).
Proof.
iIntros "#sess !> #p_k".
iDestruct "sess" as "(_ & _ & [(_ & _ & [#p_pw|[% _]])|(_ & #ok)])" => //.
iDestruct ("ok" with "p_k") as "f". iNext. by iDestruct "f" as "#[]".
Qed.

Definition kci_res pw (v : val) : iProp :=
  ⌜v = NONEV⌝ ∨
  ∃ si, ⌜v = repr (Some (si_result si))⌝ ∗
        □ (public (si_key si) → ▷ ◇ public pw).

Lemma wp_kci_client c uid pw :
  channel c -∗
  cryptis_ctx -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
  public uid -∗
  minted pw -∗
  WP Client.session uid c pw {{ _, True }}.
Proof.
iIntros "#? #? #? #? #? #?".
iApply (wp_client_session uid pw c (λ _ _, True)%I (λ _, False)%I
          (λ _, True)%I True%I).
- iFrame "#". iSplit => //. by iIntros "%si _ !>".
- by iIntros "!> %r _".
Qed.

Lemma wp_kci_server c db alist pw :
  channel c -∗
  cryptis_ctx -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
  opaque_db (λ _, pw) alist -∗
  AList.is_alist db alist -∗
  opaque_logs (λ _, pw) alist -∗
  WP Server.session db c {{ kci_res pw }}.
Proof.
iIntros "#? #? #? #? #? db logs".
iApply (wp_server_session db c (λ _, pw) alist (λ _ _, True)%I (λ _, False)%I
          (λ _, True)%I with "[$db $logs]").
- iFrame "#". by iIntros "%si _ !>".
- iIntros "!> %r (_ & _ & [->|(%si & -> & _ & _ & _ & #sess & _)])".
  + by iLeft.
  + iRight. iExists si. iSplit => //.
    by iApply kci_key_secrecy.
Qed.

Definition check_key_secrecy : val := λ: "c" "r",
  bind: "r" := "r" in
  let: "guess" := recv "c" in
  assert: (~ eq_term "r" "guess").

Lemma wp_check_key_secrecy c pw v :
  channel c -∗
  □ (public pw ↔ ▷ False) -∗
  kci_res pw v -∗
  WP check_key_secrecy c v {{ _, True }}.
Proof.
iIntros "#? #s_pw res". wp_lam. wp_pure _ credit:"c1".
iDestruct "res" as "[->|(%si & -> & #s_k)]"; wp_pures => //.
wp_apply wp_recv => //. iIntros "%guess #p_guess". wp_pures.
wp_apply wp_assert. wp_eq_term e.
- subst guess. iDestruct (public_si_result with "p_guess") as "[_ p_k]".
  iDestruct ("s_k" with "p_k") as "f".
  iMod (lc_fupd_elim_later with "c1 f") as ">#p_pw".
  by iDestruct ("s_pw" with "p_pw") as ">[]".
- wp_pures. iModIntro. by iSplit.
Qed.

Definition game : val := λ: "c",
  let: "uid" := TInt 0 in
  let: "pw" := mk_password #() in
  let: "db" := AList.new #() in
  let: "file" := register "db" "uid" "pw" in
  send "c" "file";;
  let: "rs" := Client.session "uid" "c" "pw" |||
               Server.session "db" "c" in
  check_key_secrecy "c" (Snd "rs").

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #chan #? #?"; rewrite /game; wp_pures.
iAssert (public (TInt 0)) as "#p_uid"; first by rewrite public_TInt.
wp_apply wp_mk_password => //.
iIntros "%pw (#m_pw & s_pw & s_file & tok)". wp_pures.
iMod (freeze_secret with "s_pw") as "#s_pw".
wp_apply AList.wp_empty => //. iIntros "%db db". wp_pures.
wp_apply (wp_register db (alist := ∅) (pw_of := λ _, TNonce pw)
            (uid := TInt 0) (pw := TNonce pw) with "[$db $tok]") => //.
{ iFrame "#". by rewrite /opaque_logs /opaque_db !big_sepM_empty. }
iIntros "%file (#file & db & logs & #odb)". wp_pures.
(* The file is stolen. *)
iMod (steal_file with "s_file") as "#st".
iDestruct (public_opaque_file with "file st") as "(%t & -> & #p_t)".
wp_apply wp_send => //. wp_pures.
wp_apply (wp_par (λ _, True)%I (kci_res pw) with "[] [db logs]").
- by iApply wp_kci_client.
- by iApply (wp_kci_server with "[//] [//] [//] [//] [//] db logs").
- iIntros "%v_c %v_s [_ res] !>". wp_pures.
  by iApply (wp_check_key_secrecy with "chan s_pw res").
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; opaqueΣ].

Lemma opaque_kci_secure σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([run_network game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: cryptis_adequacy.
iIntros (? ? c) "#ctx #chan (_ & _ & senc & hash)".
iMod (opaqueGS_alloc with "hash senc") as (?) "(#? & tok & _ & _)"; eauto.
iMod (opaque_pred_set (λ _ _, True)%I (λ _, False)%I with "tok") as "#?".
by iApply (wp_game with "ctx chan [//] [//]").
Qed.
