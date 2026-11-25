From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par assert ticket_lock.
From cryptis Require Import lib cryptis primitives tactics role adequacy.
From cryptis.lib Require Import hmqv.
From cryptis.examples Require Import alist agreement_lib.
From cryptis.examples.opaque Require Import impl shared client_proofs.
From cryptis.examples.opaque Require Import server_proofs.
From cryptis.examples.opaque.games Require Import base.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * OPAQUE: injective agreement

    Alice, the client, and Bob, the server, run sessions in parallel until the
    attacker tells each of them to stop.  Bob serves two users: Alice, and one
    whose password the attacker knows.  He answers whichever user the first
    message claims, but only keeps track of the sessions with Alice: he
    records the result of each as soon as he has answered, noting whether
    Alice confirmed it.  Alice records the result of each of her sessions; the
    client does not name its peer, but learns the server's key from its
    envelope.  Once all sessions are over, every result that Bob saw confirmed
    must be one of Alice's, each of Alice's results must be one that Bob
    recorded, and no list may repeat a result.  So each session that Bob
    completes with Alice matches one of hers, no two of his match the same
    one, and the results that Alice has but Bob did not see confirmed come
    from sessions that Bob did run with her, but whose last message never
    reached him.

*)

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !opaqueGS Σ, !tlockG Σ,
          !commitG Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (rl : role) (si : sess_info) (r : term) (ks : list term).
Implicit Types (rs : list (term * bool)).
Implicit Types (q : Qp).

Definition gameN := nroot.@"game".

(** Alice's user name is [TInt 0], and the attacker's is [TInt 1]. *)
Definition pw_of (pw_a pw_e : term) (uid : term) : term :=
  if bool_decide (uid = TInt 0) then pw_a else pw_e.

(* What a party receives from its peer: the peer's commitment to the result.
   Bob only commits in the sessions that he runs with Alice. *)
Definition agree_pred γaw γbw si rl : iProp :=
  if rl is Resp then committed γaw (si_result si)
  else ⌜si_uid si = TInt 0⌝ → committed γbw (si_result si).

(* A result of a session of role [rl], owned through the session's share. *)
Definition owned rl r : iProp := ∃ si,
  ⌜r = si_result si⌝ ∗ ⌜session_of rl si⌝ ∗
  term_token (share_of rl si) (↑gameN).

Lemma owned_excl rl r : owned rl r -∗ owned rl r -∗ False.
Proof.
iIntros "(%si1 & -> & %s1 & tok1) (%si2 & %e & %s2 & tok2)".
have ek : si_key si1 = si_key si2.
{ by move: e => /Spec.of_list_inj /(f_equal (λ l, nth 1 l (TInt 0))) /=. }
iEval (rewrite (share_of_key_inj s1 s2 ek)) in "tok1".
iDestruct (term_token_disj with "tok1 tok2") as %dis.
pose proof (nclose_non_empty gameN). set_solver.
Qed.

Lemma owned_NoDup rl ks : ([∗ list] r ∈ ks, owned rl r) -∗ ⌜NoDup ks⌝.
Proof. iApply excl_NoDup. iIntros "!> %r". iApply owned_excl. Qed.

(** Alice records all of her sessions. *)
Definition alice_session : val := λ: "c" "pw",
  Client.session (TInt 0) "c" "pw".

Lemma wp_alice_session c γa γaw γbw pw_a q :
  channel c -∗
  cryptis_ctx -∗
  opaque_ctx -∗
  opaque_pred (agree_pred γaw γbw) (λ _, False)%I -∗
  minted pw_a -∗
  □ (public pw_a ↔ ▷ False) -∗
  inv (gameN.@"file") (file_secret pw_a) -∗
  ledger (gameN.@"alice") γa γaw -∗
  commits γa q ∅ -∗
  WP alice_session c pw_a
    {{ session_res (λ ks, commits γa q (list_to_set ks))
         (λ r, owned Init r ∗ committed γbw r) }}.
Proof.
iIntros "#? #? #? #? #? #s_pa #inv_f #led frag". wp_lam. wp_pures.
iAssert (public (TInt 0)) as "#p_uid"; first by rewrite public_TInt.
iApply wp_fupd.
wp_apply (wp_client_session (TInt 0) pw_a c (agree_pred γaw γbw)
            (λ _, False)%I
            (λ si, commits γa q {[si_result si]} ∗
                   term_token (si_blind si) (⊤ ∖ ↑opN))%I
            (commits γa q ∅) with "[frag]")
  as "%r [[-> frag]|(%si & -> & (%e_uid & _) & #sess & [frag tok] & gift)]".
- iFrame "#". iSplit; first iExact "frag".
  iIntros "%si tok".
  iMod (commit _ _ _ _ (si_result si) with "led frag") as "[frag #w]".
  by iFrame "frag tok w".
- iModIntro. iExists None. by iFrame.
- iAssert (|={⊤}=> committed γbw (si_result si))%I with "[gift]" as ">#w".
  { iDestruct "gift" as "[#comp|w]"; last by iModIntro; iApply "w".
    iDestruct (session_compromised with "sess comp") as "[_ [#p|[_ #st]]]".
    - by iDestruct ("s_pa" with "p") as ">[]".
    - iInv "inv_f" as ">s_file".
      by iDestruct (file_secret_stolen with "s_file st") as "[]". }
  iModIntro. iExists (Some (si_result si)). iSplit => //=.
  rewrite union_empty_r_L. iFrame "frag w". iExists si. iSplit => //.
  iSplit => //. iApply (term_token_drop with "tok"). solve_ndisj.
Qed.

(** The user name of a session result. *)
Definition result_uid : val := λ: "r",
  bind: "l" := list_of_term "r" in
  list_match: ["uid"; "sk"] := "l" in
  SOME "uid".

Lemma wp_result_uid si :
  {{{ True }}}
    result_uid (si_result si)
  {{{ RET (repr (Some (si_uid si))); True }}}.
Proof.
iIntros "%Φ _ post". wp_lam.
wp_apply wp_list_of_term. rewrite Spec.of_listK. wp_pures.
rewrite subst_list_match /=.
wp_list_match => [uid sk e | ]; last by [].
case: e => <- _. wp_pures. by iApply "post".
Qed.

(** Bob answers any user, but only records the sessions with Alice, along
    with whether she confirmed them. *)
Definition bob_session : val := λ: "c" "lk" "db",
  bind: "st" := locked_accept "lk" "db" "c" in
  let: "r" := Server.result "st" in
  bind: "uid" := result_uid "r" in
  if: eq_term "uid" (TInt 0) then
    let: "fin" := Server.finish "c" "st" in
    SOME ("r", match: "fin" with NONE => #false | SOME <> => #true end)
  else
    Server.finish "c" "st";;
    NONE.

Lemma wp_bob_session c γb γaw γbw lk db alist (pw_a pw_e : term) q :
  channel c -∗
  cryptis_ctx -∗
  opaque_ctx -∗
  opaque_pred (agree_pred γaw γbw) (λ _, False)%I -∗
  server_lock lk db (pw_of pw_a pw_e) alist -∗
  opaque_db (pw_of pw_a pw_e) alist -∗
  □ (public pw_a ↔ ▷ False) -∗
  ledger (gameN.@"bob") γb γbw -∗
  commits γb q ∅ -∗
  WP bob_session c lk db
    {{ session_res (λ rs, commits γb q (list_to_set (map fst rs)))
         (λ x : term * bool, owned Resp x.1 ∗ if x.2 then committed γaw x.1 else True) }}.
Proof.
iIntros "#? #? #? #? #lock #odb #s_pa #led frag". wp_lam. wp_pures.
wp_apply (wp_locked_accept lk db c (pw_of pw_a pw_e) alist
            (agree_pred γaw γbw) (λ _, False)%I
            (λ si, (if bool_decide (si_uid si = TInt 0) then
                      commits γb q {[si_result si]}
                    else commits γb q ∅) ∗
                   term_token (si_sshare si) (⊤ ∖ ↑opN))%I
            (commits γb q ∅) with "[frag]").
{ iFrame "#". iSplit; first iExact "frag". iIntros "%si tok".
  case: bool_decide_reflect => e_uid.
  - iMod (commit _ _ _ _ (si_result si) with "led frag") as "[frag #w]".
    iModIntro. iFrame "frag tok". by iIntros "_".
  - iModIntro. iFrame "frag tok". by iIntros "%". }
iIntros "%v [[-> frag]|(%si & -> & %ss & _ & st & [frag tok])]".
{ wp_pures. iModIntro. iExists None. by iFrame. }
wp_pures. wp_apply wp_server_result => //. iIntros "_". wp_pures.
wp_apply wp_result_uid => //. iIntros "_". wp_pures.
wp_eq_term e; wp_pures; last first.
{ rewrite bool_decide_eq_false_2 //.
  wp_apply (wp_server_finish with "[$st]"); first by iFrame "#".
  iIntros "%r _". wp_pures. iModIntro. iExists None. by iFrame. }
rewrite bool_decide_eq_true_2 //.
iAssert (owned Resp (si_result si)) with "[tok]" as "own".
{ iExists si. do 2!iSplit => //.
  iApply (term_token_drop with "tok"). solve_ndisj. }
wp_apply (wp_server_finish with "[$st]"); first by iFrame "#".
iIntros "%r [->|(-> & #sess & gift)]".
- wp_pures. iModIntro. iExists (Some (si_result si, false)).
  iSplit => //=. rewrite union_empty_r_L. by iFrame.
- rewrite /pw_of e bool_decide_eq_true_2 //.
  iAssert (◇ committed γaw (si_result si))%I with "[gift]" as ">#w".
  { iDestruct "gift" as "[#comp|w]"; last by iModIntro; iApply "w".
    iDestruct (session_compromised with "sess comp") as "[_ [#p|[% _]]]" => //.
    by iDestruct ("s_pa" with "p") as ">[]". }
  wp_pures. iModIntro. iExists (Some (si_result si, true)).
  iSplit => //=. rewrite union_empty_r_L. by iFrame.
Qed.

Definition game : val := λ: "c",
  let: "pw_a" := mk_password #() in
  let: "pw_e" := mk_password #() in
  send "c" "pw_e";;
  let: "db" := AList.new #() in
  register "db" (TInt 0) "pw_a";;
  register "db" (TInt 1) "pw_e";;
  let: "lk" := new_server_lock #() in
  let: "res" :=
    sessions "c" (λ: <>, alice_session "c" "pw_a") |||
    sessions "c" (λ: <>, bob_session "c" "lk" "db") in
  let: "ks_a" := Fst "res" in
  let: "ans_b" := answered (Snd "res") in
  let: "conf_b" := confirmed (Snd "res") in
  assert: (all_in "conf_b" "ks_a" && all_in "ks_a" "ans_b" &&
           no_dups "ks_a" && no_dups "ans_b" && no_dups "conf_b").

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_token -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #chan #? tok"; rewrite /game; wp_pures.
wp_apply wp_mk_password => //.
iIntros "%pw_a (#m_pa & s_pa & s_fa & tok_a)". wp_pures.
wp_apply wp_mk_password => //.
iIntros "%pw_e (#m_pe & s_pe & _ & tok_e)". wp_pures.
iMod (freeze_secret with "s_pa") as "#s_pa".
iMod (inv_alloc (gameN.@"file") _ (file_secret pw_a) with "s_fa")
  as "#inv_f".
iMod (secret_public with "s_pe") as "#p_pe".
wp_apply wp_send => //. wp_pures.
iMod (ledger_alloc (gameN.@"alice")) as (γa γaw) "[#led_a frag_a]".
iMod (ledger_alloc (gameN.@"bob")) as (γb γbw) "[#led_b frag_b]".
iMod (opaque_pred_set (agree_pred γaw γbw) (λ _, False)%I with "tok") as "#?".
set pw := pw_of pw_a pw_e.
wp_apply AList.wp_empty => //. iIntros "%db db". wp_pures.
wp_apply (wp_register db (alist := ∅) (pw_of := pw)
            (uid := TInt 0) (pw := TNonce pw_a) with "[$db $tok_a]") => //.
{ iFrame "#". rewrite public_TInt.
  by rewrite /opaque_logs /opaque_db !big_sepM_empty. }
iIntros "%file_a (_ & db & logs & #odb)". wp_pures.
wp_apply (wp_register db (pw_of := pw) (uid := TInt 1) (pw := TNonce pw_e)
            with "[$db $tok_e $logs]").
- by rewrite lookup_insert_ne // lookup_empty.
- by rewrite /pw /pw_of bool_decide_eq_false_2.
- iFrame "#". by rewrite public_TInt.
iIntros "%file_e (_ & db & logs & #odb')". wp_pures.
wp_apply (wp_new_server_lock with "[$db $logs]"). iIntros "%lk #lock".
wp_pures.
wp_apply (wp_par
  (λ v, ∃ ks, ⌜v = repr ks⌝ ∗ commits γa 1 (list_to_set ks) ∗
              [∗ list] r ∈ ks, owned Init r ∗ committed γbw r)%I
  (λ v, ∃ rs, ⌜v = repr rs⌝ ∗ commits γb 1 (list_to_set (map fst rs)) ∗
              [∗ list] x ∈ rs, owned Resp x.1 ∗
                  if (x : term * bool).2 then committed γaw x.1 else True)%I
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
  { apply: (Forall_impl _ _ _ sub_a) => r. by rewrite elem_of_list_to_set. }
  iIntros "_". wp_pures.
  wp_apply wp_all_in => //.
  { apply: (Forall_impl _ _ _ sub_b) => r. by rewrite elem_of_list_to_set. }
  iIntros "_". wp_pures.
  wp_apply wp_no_dups => //. iIntros "_". wp_pures.
  wp_apply wp_no_dups => //. iIntros "_". wp_pures.
  by wp_apply wp_no_dups; first exact: NoDup_confirmed.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; tlockΣ; opaqueΣ; commitΣ].

Lemma opaque_agreement σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([run_network game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: cryptis_adequacy.
iIntros (? ? c) "#ctx #chan (_ & _ & senc & hash)".
iMod (opaqueGS_alloc with "hash senc") as (?) "(#? & tok & _ & _)"; eauto.
by iApply (wp_game with "ctx chan [//] tok").
Qed.
