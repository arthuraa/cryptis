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

(** * OPAQUE: forward secrecy

    The client and the server run sessions in parallel, while the attacker may
    compromise both parties' long-term secrets at any time: the game then
    leaks the password and the server's file.  A session completed before the
    compromise must keep its key unguessable afterwards.  The game never
    releases a session.

*)

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !opaqueGS Σ, !tlockG Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (rl : role) (si : sess_info) (pw : term).

Definition gameN := nroot.@"game".

Definition compromise_long_term_keys : val :=
  λ: "c" "compromised" "pw" "file",
    "compromised" <- #true;;
    send "c" "pw";;
    send "c" "file".

Definition wait_for_compromise : val :=
  rec: "loop" "compromised" :=
    if: !"compromised" then #()
    else "loop" "compromised".

Definition check_key_secrecy : val :=
  λ: "c" "compromised" "r",
    if: ~ !"compromised" then
      wait_for_compromise "compromised";;
      let: "guess" := recv "c" in
      assert: (~ eq_term "r" "guess")
    else #().

Definition game_inv lcomp pw : iProp :=
  ∃ compromised : bool,
    lcomp ↦ #compromised ∗
    if compromised then public pw ∗ stolen pw
    else secret pw ∗ file_secret pw.

Lemma wp_compromise_long_term_keys c lcomp pw file :
  {{{ cryptis_ctx ∗
      channel c ∗
      opaque_file pw file ∗
      inv gameN (game_inv lcomp pw) }}}
    compromise_long_term_keys c #lcomp pw file
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ (#? & #? & #file & #?) post".
wp_lam. wp_pures.
wp_bind (_ <- _)%E. iInv gameN as "(%bcomp & >lcomp & inv)". wp_store.
iAssert (|==> (public pw ∗ stolen pw))%I
  with "[inv]" as ">#[p_pw st]".
{ case: bcomp; first by iDestruct "inv" as "#[? ?]"; eauto.
  iDestruct "inv" as "[s_pw s_file]".
  iMod (secret_public with "s_pw") as "#?".
  iMod (steal_file with "s_file") as "#?".
  by eauto. }
iModIntro. iSplitL "lcomp"; first by iFrame; eauto.
iDestruct (public_opaque_file with "file st") as "(%t & -> & #p_t)".
wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_send => //.
by iApply "post".
Qed.

Lemma wp_wait_for_compromise lcomp pw :
  {{{ cryptis_ctx ∗
      inv gameN (game_inv lcomp pw) }}}
    wait_for_compromise #lcomp
  {{{ RET #(); public pw ∗ stolen pw }}}.
Proof.
iLöb as "IH". iIntros "%Φ (#? & #?) post".
wp_rec. wp_bind (!_)%E. iInv gameN as "(%bcomp & lcomp & inv)".
wp_load. iModIntro.
iAssert (□ if bcomp then public pw ∗ stolen pw else True)%I as "#?".
{ case: bcomp => //. iPoseProof "inv" as "#inv". by eauto. }
iSplitL "lcomp inv"; first by iFrame.
case: bcomp; wp_pures; first by iApply "post".
by wp_apply "IH"; eauto.
Qed.

(** Ephemerals never leak and the game never releases a session, so a session
    completed while the password and the file were secret keeps its key
    secret. *)
Lemma wp_check_key_secrecy c lcomp pw rl si :
  {{{ cryptis_ctx ∗
      channel c ∗
      inv gameN (game_inv lcomp pw) ∗
      session pw (λ _, False%I) rl si }}}
    check_key_secrecy c #lcomp (si_result si)
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ (#? & #? & #? & #sess) post".
rewrite /check_key_secrecy.
wp_pure _ credit:"c1". wp_pures.
wp_bind (!_)%E.
iInv gameN as "(%bcomp & >Hcomp & inv)".
wp_load. case: bcomp.
{ iModIntro. iSplitR "post c1"; first by iExists true; eauto.
  wp_pures. by iApply "post". }
iDestruct "inv" as "[s_pw s_file]".
iAssert (◇ (secret pw ∗ file_secret pw ∗
            □ (public (si_key si) ↔ ▷ □ False)))%I
  with "[s_pw s_file]" as ">(s_pw & s_file & #s_sk)".
{ case: rl.
  - by iApply (secret_session_ok _ _ Init with "s_pw s_file sess").
  - iMod (secret_session_ok _ _ Resp with "s_pw [//] sess")
      as "($ & _ & $)".
    by iFrame. }
iModIntro. iSplitR "post c1".
{ iExists false; iFrame. }
wp_pures. wp_apply wp_wait_for_compromise; eauto.
iIntros "_". wp_pures. wp_apply wp_recv => //.
iIntros "%guess #p_guess". wp_pures.
wp_apply wp_assert. wp_eq_term e.
{ subst guess. iDestruct (public_si_result with "p_guess") as "[_ p_k]".
  iDestruct ("s_sk" with "p_k") as "f".
  by iMod (lc_fupd_elim_later with "c1 f") as "#[]". }
wp_pures. iModIntro. iSplit => //. by iApply "post".
Qed.

Definition do_client : val :=
  rec: "loop" "c" "compromised" "uid" "pw" :=
    Fork ("loop" "c" "compromised" "uid" "pw");;
    (bind: "r" := Client.session "uid" "c" "pw" in
     check_key_secrecy "c" "compromised" "r");;
    #().

Lemma wp_do_client c lcomp uid pw :
  channel c -∗
  cryptis_ctx -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
  public uid -∗
  minted pw -∗
  inv gameN (game_inv lcomp pw) -∗
  {{{ True }}}
    do_client c #lcomp uid pw
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #? #p_uid #m_pw #inv".
iLöb as "IH". iIntros "!> %Φ _ post".
wp_rec; wp_pures; wp_apply wp_fork; first by iApply "IH".
wp_pures.
wp_apply (wp_client_session uid pw c (λ _ _, True)%I (λ _, False)%I
            (λ _, True)%I True%I).
{ iFrame "#". iSplit => //. by iIntros "%si _ !>". }
iIntros "%r [[-> _]|(%si & -> & _ & #sess & _)]"; wp_pures.
  by iApply "post".
wp_apply (wp_check_key_secrecy _ lcomp pw Init si); first by iFrame "#".
iIntros "_". wp_pures. by iApply "post".
Qed.

(* The server has a single user, so every session it completes is a session
   with the client. *)
Definition do_server : val :=
  rec: "loop" "c" "compromised" "lk" "db" :=
    Fork ("loop" "c" "compromised" "lk" "db");;
    (bind: "r" := locked_server "lk" "db" "c" in
     check_key_secrecy "c" "compromised" "r");;
    #().

Lemma wp_do_server c lcomp lk db alist pw :
  channel c -∗
  cryptis_ctx -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
  server_lock lk db (λ _, pw) alist -∗
  opaque_db (λ _, pw) alist -∗
  inv gameN (game_inv lcomp pw) -∗
  {{{ True }}}
    do_server c #lcomp lk db
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #? #lock #db #inv".
iLöb as "IH". iIntros "!> %Φ _ post".
wp_rec; wp_pures; wp_apply wp_fork; first by iApply "IH".
wp_pures.
wp_apply (wp_locked_server lk db c (λ _, pw) alist (λ _ _, True)%I
            (λ _, False)%I (λ _, True)%I).
{ iFrame "#". by iIntros "%si _ !>". }
iIntros "%r [->|(%si & -> & _ & _ & #sess & _)]"; wp_pures.
  by iApply "post".
wp_apply (wp_check_key_secrecy _ lcomp pw Resp si); first by iFrame "#".
iIntros "_". wp_pures. by iApply "post".
Qed.

Definition game : val := λ: "c",
  let: "uid" := TInt 0 in
  let: "pw" := mk_password #() in
  let: "db" := AList.new #() in
  let: "file" := register "db" "uid" "pw" in
  let: "lk" := new_server_lock #() in
  let: "compromised" := ref #false in
  Fork (do_client "c" "compromised" "uid" "pw");;
  Fork (do_server "c" "compromised" "lk" "db");;
  Fork (compromise_long_term_keys "c" "compromised" "pw" "file").

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
wp_apply AList.wp_empty => //. iIntros "%db db". wp_pures.
wp_apply (wp_register db (alist := ∅) (pw_of := λ _, TNonce pw)
            (uid := TInt 0) (pw := TNonce pw) with "[$db $tok]") => //.
{ iFrame "#". by rewrite /opaque_logs /opaque_db !big_sepM_empty. }
iIntros "%file (#file & db & logs & #odb)". wp_pures.
wp_apply (wp_new_server_lock with "[$db $logs]"). iIntros "%lk #lock".
wp_pures. wp_alloc lcomp as "lcomp".
iMod (inv_alloc gameN _ (game_inv lcomp pw)
  with "[s_pw s_file lcomp]") as "#inv".
{ iFrame. }
wp_pures.
wp_apply wp_fork; first by wp_apply wp_do_client. wp_pures.
wp_apply wp_fork; first by wp_apply wp_do_server. wp_pures.
by wp_apply wp_fork; first wp_apply wp_compromise_long_term_keys; eauto.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; cryptisΣ; tlockΣ; opaqueΣ].

Lemma opaque_forward_secrecy σ₁ σ₂ (v : val) t₂ e₂ :
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
