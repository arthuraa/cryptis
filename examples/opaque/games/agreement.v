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
    attacker tells each of them to stop.  Bob serves two users: Alice, whose
    password is secret, and one whose password the attacker knows.  He answers
    whichever user the first message claims, but only records the result of
    each session with Alice.  Alice records the result of each of her
    sessions; the client does not name its peer, but learns the server's key
    from its envelope.  Once all sessions are over, every result that Bob
    recorded must be one of Alice's, and no list may repeat a result.  So each
    session that Bob completes with Alice matches one of hers, and no two of
    his match the same one.

    Unlike the HMQV game, Bob cannot record a session as soon as he has
    answered: [Server.session] only returns once the client has confirmed.
    So the game cannot check the converse, that each of Alice's results comes
    from a session that Bob answered.

*)

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !opaqueGS Σ, !tlockG Σ,
          !commitG Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (rl : role) (si : sess_info) (r : term) (rs : list term).
Implicit Types (q : Qp).

Definition gameN := nroot.@"game".

(** Alice's user name is [TInt 0], and the attacker's is [TInt 1]. *)
Definition pw_of (pw_a pw_e : term) (uid : term) : term :=
  if bool_decide (uid = TInt 0) then pw_a else pw_e.

(* What a party receives from its peer: Bob receives Alice's commitment to the
   result of the session, and Alice receives nothing. *)
Definition agree_pred γaw si rl : iProp :=
  if rl is Resp then committed γaw (si_result si) else True.

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

Lemma owned_NoDup rl rs : ([∗ list] r ∈ rs, owned rl r) -∗ ⌜NoDup rs⌝.
Proof. iApply excl_NoDup. iIntros "!> %r". iApply owned_excl. Qed.

(** Alice records all of her sessions. *)
Definition alice_session : val := λ: "c" "pw",
  Client.session (TInt 0) "c" "pw".

Lemma wp_alice_session c γa γaw pw_a q :
  channel c -∗
  cryptis_ctx -∗
  opaque_ctx -∗
  opaque_pred (agree_pred γaw) (λ _, False)%I -∗
  minted pw_a -∗
  ledger (gameN.@"alice") γa γaw -∗
  commits γa q ∅ -∗
  WP alice_session c pw_a
    {{ session_res (λ rs, commits γa q (list_to_set rs)) (owned Init) }}.
Proof.
iIntros "#? #? #? #? #? #led frag". wp_lam. wp_pures.
iAssert (public (TInt 0)) as "#p_uid"; first by rewrite public_TInt.
iApply wp_fupd.
wp_apply (wp_client_session (TInt 0) pw_a c (agree_pred γaw) (λ _, False)%I
            (λ si, commits γa q {[si_result si]} ∗
                   term_token (si_blind si) (⊤ ∖ ↑opN))%I
            (commits γa q ∅) with "[frag]")
  as "%r [[-> frag]|(%si & -> & _ & _ & [frag tok] & _)]".
- iFrame "#". iSplit; first iExact "frag".
  iIntros "%si tok".
  iMod (commit _ _ _ _ (si_result si) with "led frag") as "[frag #w]".
  by iFrame "frag tok w".
- iModIntro. iExists None. by iFrame.
- iModIntro. iExists (Some (si_result si)). iSplit => //=.
  rewrite union_empty_r_L. iFrame "frag". iExists si. iSplit => //.
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

(** Bob answers any user, but only records the sessions with Alice. *)
Definition bob_session : val := λ: "c" "lk" "db",
  bind: "r" := locked_server "lk" "db" "c" in
  bind: "uid" := result_uid "r" in
  guard: eq_term "uid" (TInt 0) in
  SOME "r".

Lemma wp_bob_session c γaw lk db alist (pw_a pw_e : term) :
  channel c -∗
  cryptis_ctx -∗
  opaque_ctx -∗
  opaque_pred (agree_pred γaw) (λ _, False)%I -∗
  server_lock lk db (pw_of pw_a pw_e) alist -∗
  opaque_db (pw_of pw_a pw_e) alist -∗
  □ (public pw_a ↔ ▷ False) -∗
  WP bob_session c lk db
    {{ session_res (λ _, True)%I (λ r, owned Resp r ∗ committed γaw r) }}.
Proof.
iIntros "#? #? #? #? #lock #odb #s_pa". wp_lam. wp_pures.
wp_apply (wp_locked_server lk db c (pw_of pw_a pw_e) alist (agree_pred γaw)
            (λ _, False)%I
            (λ si, term_token (si_sshare si) (⊤ ∖ ↑opN))%I).
{ iFrame "#". by iIntros "%si tok !>"; iFrame. }
iIntros "%r [->|(%si & -> & %ss & _ & #sess & tok & gift)]"; wp_pures.
  by iModIntro; iExists None.
wp_apply wp_result_uid => //. iIntros "_". wp_pures.
wp_eq_term e; wp_pures; last by iModIntro; iExists None.
rewrite /pw_of e bool_decide_eq_true_2 // in ss *.
iAssert (◇ committed γaw (si_result si))%I with "[gift]" as ">#w".
{ iDestruct "gift" as "[#comp|w]"; last by iModIntro; iApply "w".
  iDestruct (session_compromised with "sess comp") as "[_ [#p|[% _]]]" => //.
  by iDestruct ("s_pa" with "p") as ">[]". }
iModIntro. iExists (Some (si_result si)). iSplit => //=.
iSplit => //. iFrame "w". iExists si. do 2!iSplit => //.
iApply (term_token_drop with "tok"). solve_ndisj.
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
  let: "rs_a" := Fst "res" in
  let: "rs_b" := Snd "res" in
  assert: (all_in "rs_b" "rs_a" && no_dups "rs_a" && no_dups "rs_b").

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_token -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #chan #? tok"; rewrite /game; wp_pures.
wp_apply wp_mk_password => //.
iIntros "%pw_a (#m_pa & s_pa & _ & tok_a)". wp_pures.
wp_apply wp_mk_password => //.
iIntros "%pw_e (#m_pe & s_pe & _ & tok_e)". wp_pures.
iMod (freeze_secret with "s_pa") as "#s_pa".
iMod (secret_public with "s_pe") as "#p_pe".
wp_apply wp_send => //. wp_pures.
iMod (ledger_alloc (gameN.@"alice")) as (γa γaw) "[#led frag]".
iMod (opaque_pred_set (agree_pred γaw) (λ _, False)%I with "tok") as "#?".
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
  (λ v, ∃ rs, ⌜v = repr rs⌝ ∗ commits γa 1 (list_to_set rs) ∗
              [∗ list] r ∈ rs, owned Init r)%I
  (λ v, ∃ rs, ⌜v = repr rs⌝ ∗ True ∗
              [∗ list] r ∈ rs, owned Resp r ∗ committed γaw r)%I
  with "[frag] []").
- wp_pures.
  iApply (wp_sessions _ _ (λ q rs, commits γa q (list_to_set rs))
            with "chan [] [] [] frag").
  + iIntros "!> %q frag". by iApply commits_split.
  + iIntros "!> %q %rs1 %rs2 f1 f2". rewrite list_to_set_app_L.
    by iApply (commits_join with "f1 f2").
  + iIntros "!> %q frag". wp_pures. by iApply wp_alice_session.
- wp_pures.
  iApply (wp_sessions (A := term) _ _ (λ _ _, True)%I
            (λ r, owned Resp r ∗ committed γaw r)%I 1 with "chan [] [] [] [//]").
  + by iIntros "!> %q _".
  + by iIntros "!> %q %rs1 %rs2 _ _".
  + iIntros "!> %q _". wp_pures. by iApply wp_bob_session.
- iIntros "%v1 %v2 [(%rs_a & -> & frag & owns_a) (%rs_b & -> & _ & owns_b)]
           !>".
  rewrite big_sepL_sep.
  iDestruct "owns_b" as "[owns_b ws_b]".
  iDestruct (owned_NoDup with "owns_a") as %nd_a.
  iDestruct (owned_NoDup with "owns_b") as %nd_b.
  iMod (commits_full with "led frag ws_b") as %sub.
  wp_pures. wp_apply wp_assert.
  wp_apply wp_all_in => //.
  { apply: (Forall_impl _ _ _ sub) => r. by rewrite elem_of_list_to_set. }
  iIntros "_". wp_pures.
  wp_apply wp_no_dups => //. iIntros "_". wp_pures.
  by wp_apply wp_no_dups.
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
