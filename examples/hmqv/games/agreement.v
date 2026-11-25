From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import auth gset.
From iris.algebra.lib Require Import frac_auth.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par assert.
From cryptis Require Import lib cryptis primitives tactics role adequacy.
From cryptis.examples Require Import hmqv agreement_lib.
From cryptis.lib Require Import hmqv.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * HMQV: injective agreement

    Alice, the initiator, and Bob, the responder, run sessions in parallel
    until the attacker tells each of them to stop.  Each talks to whatever peer
    the attacker picks -- Alice connects to the identity that the attacker
    names, Bob answers the identity that the first message claims -- and only
    keeps track of the sessions with the other: Alice records the key of each
    session with Bob, and Bob records the key of each session with Alice as
    soon as he has answered, noting whether Alice confirmed it.  Once all
    sessions are over, every key that Bob saw confirmed must be one of Alice's
    keys, each of Alice's keys must be one that Bob recorded, and no list may
    repeat a key.  So each session that Bob completes with Alice
    matches one of hers, no two of his match the same one, and the keys that
    Alice has but Bob did not see confirmed come from sessions that Bob did run
    with her, but whose last message never reached him.

*)

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !hmqvGS Σ, !commitG Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (p_a p_b : nonce) (rl : role) (si : sess_info).
Implicit Types (k : term) (ks : list term) (rs : list (term * bool)) (q : Qp).

Definition gameN := nroot.@"game".

(* What a party receives from its peer: the peer's commitment to the key.  Each
   party only commits in the sessions that it runs with the other. *)
Definition agree_pred γaw γbw P_a P_b si rl : iProp :=
  (if rl is Resp then ⌜si_resp si = P_b⌝ → committed γaw (si_key si)
   else ⌜si_init si = P_a⌝ → committed γbw (si_key si))%I.

(* A key of a session of role [rl], owned through the session's share. *)
Definition owned rl k : iProp := ∃ si,
  ⌜k = si_key si⌝ ∗ ⌜session_of rl si⌝ ∗
  term_token (si_share_of rl si) (↑gameN).

Lemma owned_excl rl k : owned rl k -∗ owned rl k -∗ False.
Proof.
iIntros "(%si1 & -> & %s1 & tok1) (%si2 & %e & %s2 & tok2)".
move/term_of_senc_key_inj: e => e.
have ? := session_of_key_inj s1 s2 e; subst si2.
iDestruct (term_token_disj with "tok1 tok2") as %dis.
pose proof (nclose_non_empty gameN). set_solver.
Qed.

Lemma owned_NoDup rl ks : ([∗ list] k ∈ ks, owned rl k) -∗ ⌜NoDup ks⌝.
Proof. iApply excl_NoDup. iIntros "!> %k". iApply owned_excl. Qed.


(** Alice contacts whatever identity the attacker names, but only records the
    sessions with Bob. *)
Definition alice_session : val := λ: "c" "p_a" "P_a" "P_b",
  let: "P" := recv "c" in
  if: eq_term "P" "P_b" then
    initiator "c" "p_a" "P_a" "P_b" (Tag gameN)
  else
    initiator "c" "p_a" "P_a" "P" (Tag gameN);;
    NONE.

Lemma wp_alice_session c γa γaw γbw p_a p_b q :
  channel c -∗
  cryptis_ctx -∗
  hmqv_ctx -∗
  hmqv_pred gameN (agree_pred γaw γbw (TExp g p_a) (TExp g p_b))
    (λ _, False)%I -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  □ (public p_a ↔ ▷ False) -∗
  □ (public p_b ↔ ▷ False) -∗
  ledger (gameN.@"alice") γa γaw -∗
  commits γa q ∅ -∗
  WP alice_session c p_a (TExp g p_a) (TExp g p_b)
    {{ session_res (λ ks, commits γa q (list_to_set ks))
         (λ k, owned Init k ∗ committed γbw k) }}.
Proof.
iIntros "#? #? #? #? #key_a #key_b #s_pa #s_pb #led frag". wp_lam. wp_pures.
wp_apply wp_recv => //. iIntros "%P #p_P".
wp_eq_term e; last first.
{ wp_pures.
  wp_apply (wp_initiator _ _ _ _ _ _ (λ _, True)%I True%I with "[] []").
  - by iFrame "#".
  - iSplit => //. iIntros "%x_a %X_b _ !>". iSplit => //.
    rewrite /agree_pred /=. iIntros "%ep". by subst.
  iIntros "%r _". wp_pures. iModIntro. iExists None. by iFrame. }
subst P. wp_pures. iApply wp_fupd.
wp_apply (wp_initiator _ _ _ _ _ _
            (λ si, commits γa q {[si_key si : term]} ∗
                   term_token (si_init_share si) (⊤ ∖ ↑hmqvN))%I
            (commits γa q ∅) with "[] [frag]")
  as "%r [[-> frag]|(%x_a & %X_b & -> & #sess & [frag tok] & gift)]".
- by iFrame "#".
- iSplit; first iExact "frag".
  iIntros "%x_a %X_b tok".
  iMod (commit _ _ _ _ (si_key (init_si p_a x_a (TExp g p_b) X_b))
          with "led frag") as "[frag #w]".
  iModIntro. iFrame "frag tok". by iIntros "_".
- iModIntro. iExists None. by iFrame.
- set si := init_si p_a x_a (TExp g p_b) X_b.
  iAssert (◇ committed γbw (si_key si))%I with "[gift]" as ">#w".
  { iDestruct "gift" as "[#comp|w]"; last by iModIntro; iApply "w".
    iDestruct (session_compromised with "sess comp") as "[_ #l]".
    iMod ("l" $! p_b with "[//] key_b") as "#p".
    iAssert (▷ False)%I as ">[]". by iApply "s_pb". }
  iModIntro.
  iExists (Some (si_key si : term)). iSplit => //=.
  rewrite union_empty_r_L. iFrame "frag w". iExists si. iSplit => //.
  iSplit; first by iPureIntro; exact: init_session_vetted.
  iApply (term_token_drop with "tok"). solve_ndisj.
Qed.

(** Bob answers any identity, but only records the sessions with Alice, along
    with whether she confirmed them. *)
Definition bob_session : val := λ: "c" "p_b" "P_b" "P_a",
  let: "m1" := responder_listen "c" in
  let: "X" := Fst "m1" in
  let: "P" := Snd "m1" in
  if: eq_term "P" "P_a" then
    bind: "σ" := responder_accept "c" "p_b" "P_b" "X" "P_a" (Tag gameN) in
    let: "k" := session_key "σ" in
    let: "r" := responder_finish "c" "σ" (Tag gameN) in
    SOME ("k", match: "r" with NONE => #false | SOME <> => #true end)
  else
    responder_confirm "c" "p_b" "P_b" "X" "P" (Tag gameN);;
    NONE.

Lemma wp_bob_session c γb γaw γbw p_a p_b q :
  channel c -∗
  cryptis_ctx -∗
  hmqv_ctx -∗
  hmqv_pred gameN (agree_pred γaw γbw (TExp g p_a) (TExp g p_b))
    (λ _, False)%I -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  □ (public p_a ↔ ▷ False) -∗
  □ (public p_b ↔ ▷ False) -∗
  ledger (gameN.@"bob") γb γbw -∗
  commits γb q ∅ -∗
  WP bob_session c p_b (TExp g p_b) (TExp g p_a)
    {{ session_res (λ rs, commits γb q (list_to_set (map fst rs)))
         (λ r, owned Resp r.1 ∗ if r.2 then committed γaw r.1 else True) }}.
Proof.
iIntros "#? #? #? #? #key_a #key_b #s_pa #s_pb #led frag". wp_lam. wp_pures.
wp_apply wp_responder_listen; first by iSplit.
iIntros "%X %P [#p_X #p_P]". wp_pures.
wp_eq_term e; last first.
{ wp_pures.
  wp_apply (wp_responder_confirm _ _ _ _ _ _ _ (λ _, True)%I).
  { iFrame "#". iIntros "%x_b _ !>". iSplit => //.
    rewrite /agree_pred /=. iIntros "%ep". by subst. }
  iIntros "%r _". wp_pures. iModIntro. iExists None. by iFrame. }
subst P. wp_pures.
wp_apply (wp_responder_accept _ (TExp g p_a) X p_b _ _ _
            (λ si, commits γb q {[si_key si : term]} ∗
                   term_token (si_resp_share si) (⊤ ∖ ↑hmqvN))%I
            (commits γb q ∅) with "[frag]").
{ iFrame "#". iSplit; first iExact "frag". iIntros "%x_b tok".
  iMod (commit _ _ _ _ (si_key (resp_si (TExp g p_a) X p_b x_b))
          with "led frag") as "[frag #w]".
  iModIntro. iFrame "frag tok". by iIntros "_". }
iIntros "%r [[-> frag]|(%x_b & -> & state & frag & tok)]".
{ wp_pures. iModIntro. iExists None. by iFrame. }
set si := resp_si (TExp g p_a) X p_b x_b.
iAssert (owned Resp (si_key si)) with "[tok]" as "own".
{ iExists si. iSplit => //.
  iSplit; first by iPureIntro; exact: resp_session_vetted.
  iApply (term_token_drop with "tok"). solve_ndisj. }
wp_pures. wp_apply wp_session_key. wp_pures.
wp_apply (wp_responder_finish with "[$state]"); first by iFrame "#".
iIntros "%r [->|(-> & #sess & gift)]".
- wp_pures. iModIntro. iExists (Some (si_key si : term, false)).
  iSplit => //=. rewrite union_empty_r_L. by iFrame.
- iAssert (◇ committed γaw (si_key si))%I with "[gift]" as ">#w".
  { iDestruct "gift" as "[#comp|w]"; last by iModIntro; iApply "w".
    iDestruct (session_compromised with "sess comp") as "[_ #l]".
    iMod ("l" $! p_a with "[//] key_a") as "#p".
    iAssert (▷ False)%I as ">[]". by iApply "s_pa". }
  wp_pures. iModIntro. iExists (Some (si_key si : term, true)).
  iSplit => //=. rewrite union_empty_r_L. by iFrame.
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
  let: "res" :=
    sessions "c" (λ: <>, alice_session "c" "p_a" "P_a" "P_b") |||
    sessions "c" (λ: <>, bob_session "c" "p_b" "P_b" "P_a") in
  let: "ks_a" := Fst "res" in
  let: "ans_b" := answered (Snd "res") in
  let: "conf_b" := confirmed (Snd "res") in
  assert: (all_in "conf_b" "ks_a" && all_in "ks_a" "ans_b" &&
           no_dups "ks_a" && no_dups "ans_b" && no_dups "conf_b").

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  hmqv_ctx -∗
  hmqv_token ⊤ -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #chan #? tok"; rewrite /game; wp_pures.
wp_apply wp_mk_lt_key => //.
iIntros "%p_a (#key_a & s_pa & #p_Pa & _)". wp_pures.
wp_apply wp_mk_lt_key => //.
iIntros "%p_b (#key_b & s_pb & #p_Pb & _)". wp_pures.
iMod (freeze_secret with "s_pa") as "#s_pa".
iMod (freeze_secret with "s_pb") as "#s_pb".
iMod (ledger_alloc (gameN.@"alice")) as (γa γaw) "[#led_a frag_a]".
iMod (ledger_alloc (gameN.@"bob")) as (γb γbw) "[#led_b frag_b]".
iMod (hmqv_pred_set gameN (agree_pred γaw γbw (TExp g p_a) (TExp g p_b))
        (λ _, False)%I with "tok") as "[#? _]"; first solve_ndisj.
wp_apply wp_send => //. wp_pures.
wp_apply wp_send => //. wp_pures.
wp_apply (wp_par
  (λ v, ∃ ks, ⌜v = repr ks⌝ ∗ commits γa 1 (list_to_set ks) ∗
              [∗ list] k ∈ ks, owned Init k ∗ committed γbw k)%I
  (λ v, ∃ rs, ⌜v = repr rs⌝ ∗ commits γb 1 (list_to_set (map fst rs)) ∗
              [∗ list] r ∈ rs, owned Resp r.1 ∗
                  if (r : term * bool).2 then committed γaw r.1 else True)%I
  with "[frag_a] [frag_b]").
- wp_pures.
  iApply (wp_sessions _ _ (λ q ks, commits γa q (list_to_set ks))
            with "chan [] [] [] frag_a").
  + iIntros "!> %q frag". by iApply commits_split.
  + iIntros "!> %q %ks1 %ks2 f1 f2". rewrite list_to_set_app_L.
    by iApply (commits_join with "f1 f2").
  + iIntros "!> %q frag". wp_pures. by iApply wp_alice_session.
- wp_pures.
  iApply (wp_sessions _ _ (λ q rs, commits γb q (list_to_set (map fst rs)))
            with "chan [] [] [] frag_b").
  + iIntros "!> %q frag". by iApply commits_split.
  + iIntros "!> %q %rs1 %rs2 f1 f2". rewrite map_app list_to_set_app_L.
    by iApply (commits_join with "f1 f2").
  + iIntros "!> %q frag". wp_pures. by iApply wp_bob_session.
- iIntros "%v1 %v2 [(%ks_a & -> & frag_a & owns_a) (%rs & -> & frag_b & owns_b)]
           !>".
  rewrite !big_sepL_sep.
  iDestruct "owns_a" as "[owns_a ws_a]". iDestruct "owns_b" as "[owns_b ws_b]".
  iDestruct (owned_NoDup with "owns_a") as %nd_a.
  iDestruct (big_sepL_answered with "owns_b") as "owns_b".
  iDestruct (owned_NoDup with "owns_b") as %nd_b.
  iDestruct (big_sepL_confirmed with "ws_b") as "ws_b".
  iMod (commits_full with "led_a frag_a ws_b") as %sub_a.
  iMod (commits_full with "led_b frag_b ws_a") as %sub_b.
  wp_pures. wp_apply wp_answered => //. iIntros "_".
  wp_pures. wp_apply wp_confirmed => //. iIntros "_".
  wp_pures. wp_apply wp_assert.
  wp_apply wp_all_in => //.
  { apply: (Forall_impl _ _ _ sub_a) => k. by rewrite elem_of_list_to_set. }
  iIntros "_". wp_pures.
  wp_apply wp_all_in => //.
  { apply: (Forall_impl _ _ _ sub_b) => k. by rewrite elem_of_list_to_set. }
  iIntros "_". wp_pures.
  wp_apply wp_no_dups => //. iIntros "_". wp_pures.
  wp_apply wp_no_dups => //. iIntros "_". wp_pures.
  by wp_apply wp_no_dups; first exact: NoDup_confirmed.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; hmqvΣ; commitΣ].

Lemma hmqv_agreement σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([run_network game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: cryptis_adequacy.
iIntros (? ? c) "#ctx #chan (_ & _ & _ & hash)".
iMod (hmqvGS_alloc with "hash") as (?) "(#? & tok & _)"; eauto.
by iApply (wp_game with "ctx chan [//] tok").
Qed.
