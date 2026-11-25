From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import assert ticket_lock.
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

(** * OPAQUE: key independence

    The client and the server run sessions in parallel, and neither the
    password nor the file ever leaks.  Each time the server completes a
    session, it checks that the attacker cannot guess the key, and then leaks
    the key.  So the keys of some sessions do not help the attacker guess the
    keys of the others.

*)

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !opaqueGS Σ, !tlockG Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (si : sess_info) (pw : term).

Definition gameN := nroot.@"game".

(** The server releases a session once it has checked its key. *)
Definition released si : iProp := term_meta (si_sshare si) gameN ().

Definition check_key_secrecy : val := λ: "c" "r",
  let: "guess" := recv "c" in
  assert: (~ eq_term "r" "guess").

Lemma wp_check_key_secrecy c si :
  {{{ channel c ∗ term_token (si_sshare si) (↑gameN) ∗
      □ (public (si_key si) → ▷ □ released si) }}}
    check_key_secrecy c (si_result si)
  {{{ RET #(); term_token (si_sshare si) (↑gameN) }}}.
Proof.
iIntros "%Φ (#chan & tok & #s_k) post". wp_lam. wp_pure _ credit:"c1".
wp_pures. wp_apply wp_recv => //. iIntros "%guess #p_guess". wp_pures.
wp_apply wp_assert. wp_eq_term e.
- subst guess. iDestruct (public_si_result with "p_guess") as "[_ p_k]".
  iDestruct ("s_k" with "p_k") as "f".
  iMod (lc_fupd_elim_later with "c1 f") as "#rel".
  by iDestruct (term_meta_token with "tok rel") as "[]".
- wp_pures. iModIntro. iSplit => //. by iApply "post".
Qed.

Definition do_client : val :=
  rec: "loop" "c" "uid" "pw" :=
    Fork ("loop" "c" "uid" "pw");;
    Client.session "uid" "c" "pw";;
    #().

Lemma wp_do_client c uid pw :
  channel c -∗
  cryptis_ctx -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I released -∗
  public uid -∗
  minted pw -∗
  {{{ True }}}
    do_client c uid pw
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #? #? #? #?".
iLöb as "IH". iIntros "!> %Φ _ post".
wp_rec. wp_pures. wp_apply wp_fork; first by iApply "IH".
wp_pures.
wp_apply (wp_client_session uid pw c (λ _ _, True)%I released
            (λ _, True)%I True%I).
{ iFrame "#". iSplit => //. by iIntros "%si _ !>". }
iIntros "%r _". wp_pures. by iApply "post".
Qed.

Definition do_server : val :=
  rec: "loop" "c" "lk" "db" :=
    Fork ("loop" "c" "lk" "db");;
    (bind: "r" := locked_server "lk" "db" "c" in
     check_key_secrecy "c" "r";;
     send "c" "r");;
    #().

Lemma wp_do_server c lk db alist pw :
  channel c -∗
  cryptis_ctx -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I released -∗
  server_lock lk db (λ _, pw) alist -∗
  opaque_db (λ _, pw) alist -∗
  □ (public pw ↔ ▷ False) -∗
  {{{ True }}}
    do_server c lk db
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #? #lock #odb #s_pw".
iLöb as "IH". iIntros "!> %Φ _ post".
wp_rec. wp_pures. wp_apply wp_fork; first by iApply "IH".
wp_pures.
wp_apply (wp_locked_server lk db c (λ _, pw) alist (λ _ _, True)%I released
            (λ si, term_token (si_sshare si) (⊤ ∖ ↑opN))).
{ iFrame "#". iIntros "%si tok !>". by iFrame. }
iIntros "%r [->|(%si & -> & _ & (_ & #p_uid & _) & #sess & tok & _)]";
  wp_pures.
  by iApply "post".
iAssert (◇ □ (public (si_key si) → ▷ □ released si))%I as ">#s_k".
{ iDestruct "sess" as "(_ & _ & [(_ & _ & [#p_pw|[% _]])|(_ & #ok)])" => //.
  by iDestruct ("s_pw" with "p_pw") as ">[]". }
iPoseProof (term_token_drop (↑gameN) with "tok") as "tok"; first solve_ndisj.
wp_apply (wp_check_key_secrecy with "[tok]"); first by iFrame "∗#".
iIntros "tok". iMod (term_meta_set gameN () with "tok") as "#rel" => //.
iAssert (public (si_result si)) as "#p_r".
{ rewrite public_si_result. iSplit => //.
  iApply (session_release with "sess"). by iIntros "!> !>". }
wp_pures. wp_apply wp_send => //. wp_pures. by iApply "post".
Qed.

Definition game : val := λ: "c",
  let: "uid" := TInt 0 in
  let: "pw" := mk_password #() in
  let: "db" := AList.new #() in
  register "db" "uid" "pw";;
  let: "lk" := new_server_lock #() in
  Fork (do_client "c" "uid" "pw");;
  do_server "c" "lk" "db".

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I released -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #chan #? #?"; rewrite /game; wp_pures.
iAssert (public (TInt 0)) as "#p_uid"; first by rewrite public_TInt.
wp_apply wp_mk_password => //.
iIntros "%pw (#m_pw & s_pw & _ & tok)". wp_pures.
iMod (freeze_secret with "s_pw") as "#s_pw".
wp_apply AList.wp_empty => //. iIntros "%db db". wp_pures.
wp_apply (wp_register db (alist := ∅) (pw_of := λ _, TNonce pw)
            (uid := TInt 0) (pw := TNonce pw) with "[$db $tok]") => //.
{ iFrame "#". by rewrite /opaque_logs /opaque_db !big_sepM_empty. }
iIntros "%file (_ & db & logs & #odb)". wp_pures.
wp_apply (wp_new_server_lock with "[$db $logs]"). iIntros "%lk #lock".
wp_pures.
wp_apply wp_fork; first by wp_apply wp_do_client. wp_pures.
by wp_apply wp_do_server.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; cryptisΣ; tlockΣ; opaqueΣ].

Lemma opaque_key_independence σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([run_network game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: cryptis_adequacy.
iIntros (? ? c) "#ctx #chan (_ & _ & senc & hash)".
iMod (opaqueGS_alloc with "hash senc") as (?) "(#? & tok & _ & _)"; eauto.
iMod (opaque_pred_set (λ _ _, True)%I released with "tok") as "#?".
by iApply (wp_game with "ctx chan [//] [//]").
Qed.
