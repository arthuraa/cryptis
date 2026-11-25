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

(** * OPAQUE: resistance against offline guessing

    The symbolic model cannot represent guessing directly, since a fresh term
    differs from every other term.  Instead, the client and the server run as
    many sessions as the attacker wants, while the attacker may also query an
    OPRF oracle.  The oracle has a dictionary of passwords, made of the
    client's password and of any terms the attacker chooses; given a key [k],
    it outputs [F_k(p)] for every password [p] of the dictionary.  At some
    point the server's file leaks, and the attacker may not query the oracle
    anymore.  Even then, the attacker cannot guess the envelope key derived
    from the password, [F_{k_s}(pw)].

    The oracle's outputs at the password are as good as a successful guess of
    the password for impersonating the server to the client, which the
    protocol's specifications account for (cf. [impersonable] in
    [shared.v]); the game does not check the session keys. *)

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !opaqueGS Σ, !tlockG Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (pw k : term) (ps : list term).

(** The OPRF output at [p] under [k]. *)
Definition oprf k p : term :=
  hash_result "H" (Spec.of_list [p; TExp (hash_result "H" p) k]).

(** Answers a query for the passwords [ps] under [k]. *)
Definition oracle_answer : val := rec: "loop" "c" "k" "ps" :=
  match: "ps" with
    NONE => #()
  | SOME "p" =>
      send "c" (OPRF "k" (Fst "p"));;
      "loop" "c" "k" (Snd "p")
  end.

Lemma wp_oracle_answer c pw k ps :
  {{{ channel c ∗ hash_pred (opN.@"H") H_pred ∗
      public k ∗ minted pw ∗ □ oracle_ok pw k ∗
      □ (∀ p, ⌜p ∈ ps⌝ → public p ∨ ⌜p = pw⌝) }}}
    oracle_answer c k (repr ps)
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ (#chan & #HpredH & #p_k & #m_pw & #ok & #ps) post".
iInduction ps as [|p ps] "IH".
{ rewrite [repr (@nil term)]repr_listE. wp_rec. wp_pures. by iApply "post". }
rewrite [repr (p :: ps)]repr_listE. wp_rec. wp_pures.
iAssert (public p ∨ ⌜p = pw⌝)%I as "p_p".
{ iApply "ps". iPureIntro. by apply elem_of_cons; left. }
rewrite /OPRF. wp_pures.
wp_apply wp_H'; wp_apply wp_texp; wp_list; wp_apply wp_H.
wp_apply wp_send => //.
{ iDestruct "p_p" as "[#p_p | ->]".
  - iApply public_THash; iLeft; iApply public_tag.
    rewrite public_of_list /=. do !iSplit => //.
    iApply public_TExp => //.
    iApply public_THash; iLeft. by iApply public_tag.
  - iApply (public_THashIS with "HpredH").
    + rewrite minted_of_list /=. do !iSplit => //.
      iApply minted_TExp => //. iSplit; last by iApply public_minted.
      by rewrite minted_hash_result.
    + iIntros "!> !>". iExists pw, k. by iSplit. }
wp_pures. iApply ("IH" with "[] post").
iIntros "!> %p' %p'_ps". iApply "ps". iPureIntro. by apply elem_of_cons; right.
Qed.

(** One query: the attacker picks a key and a dictionary, to which the oracle
    adds the password. *)
Definition oracle_query : val := λ: "c" "pw",
  let: "k" := recv "c" in
  bind: "dict" := list_of_term (recv "c") in
  oracle_answer "c" "k" (SOME ("pw", "dict")).

(** The oracle may be queried as long as the file is secret: then the server's
    key is secret too, so the attacker's key is not it. *)
Lemma wp_oracle_query c pw file :
  {{{ cryptis_ctx ∗ channel c ∗ opaque_ctx ∗ minted pw ∗
      opaque_file pw file ∗ oracle_used pw ∗
      term_token pw (↑opN.@"stolen") }}}
    oracle_query c pw
  {{{ v, RET v; term_token pw (↑opN.@"stolen") }}}.
Proof.
iIntros "%Φ (#? & #chan & #(HpredH & _) & #m_pw & #file & #used & tok) post".
iDestruct "file" as "(%k_s & %p_s & %p_u & %envelope & -> & _ & #key & #s_k
                      & _)".
wp_lam. wp_pure _ credit:"c1". wp_pures.
wp_apply wp_recv => //. iIntros "%k #p_k". wp_pures.
iAssert (|={⊤}=> ⌜k ≠ TNonce k_s⌝ ∗ term_token pw (↑opN.@"stolen"))%I
  with "[tok c1]" as ">[%ne tok]".
{ case: (decide (k = TNonce k_s)) => [->|ne]; last by iFrame.
  iDestruct ("s_k" with "p_k") as "st".
  iMod (lc_fupd_elim_later with "c1 st") as "#st'".
  by iDestruct (term_meta_token with "tok st'") as "[]". }
wp_apply wp_recv => //. iIntros "%dict #p_dict".
wp_list_of_term dict; wp_pures; last by iApply ("post" with "tok").
have -> : InjRV (pw, repr_list dict) = repr (pw :: dict).
  by rewrite [repr (pw :: dict)]repr_listE.
wp_apply (wp_oracle_answer _ pw k (pw :: dict)).
{ iFrame "#". iSplit.
  - iModIntro. iFrame "#". by iPureIntro.
  - rewrite public_of_list. iIntros "!> %p %p_in".
    case/elem_of_cons: p_in => [->|p_in]; first by iRight.
    iLeft. by iApply (big_sepL_elem_of with "p_dict"). }
iIntros "_". by iApply "post".
Qed.

(** The oracle answers queries until the attacker stops it. *)
Definition oracle_phase : val := rec: "loop" "c" "pw" :=
  if: eq_term (recv "c") (TInt 0) then #()
  else oracle_query "c" "pw";; "loop" "c" "pw".

Lemma wp_oracle_phase c pw file :
  {{{ cryptis_ctx ∗ channel c ∗ opaque_ctx ∗ minted pw ∗
      opaque_file pw file ∗ oracle_used pw ∗
      term_token pw (↑opN.@"stolen") }}}
    oracle_phase c pw
  {{{ RET #(); term_token pw (↑opN.@"stolen") }}}.
Proof.
iIntros "%Φ (#? & #chan & #? & #? & #? & #? & tok) post".
iLöb as "IH".
wp_rec. wp_pures. wp_apply wp_recv => //. iIntros "%m _".
wp_eq_term e; wp_pures; first by iApply "post".
wp_apply (wp_oracle_query with "[$tok]"); first by iFrame "#".
iIntros "%v tok". wp_pures. by iApply ("IH" with "tok post").
Qed.

(** The envelope key, which the game computes from the password and the
    file. *)
Definition envelope_key : val := λ: "pw" "file",
  bind: "l" := list_of_term "file" in
  list_match: [ "k_s"; "p_s"; "P_s"; "P_u"; "envelope" ] := "l" in
  SOME (derive_senc_key (OPRF "k_s" "pw")).

Lemma wp_envelope_key pw file :
  {{{ opaque_file pw file }}}
    envelope_key pw file
  {{{ (k_s : nonce), RET (repr (Some (SEncKey (oprf k_s pw))));
      oprf_key pw k_s }}}.
Proof.
iIntros "%Φ (%k_s & %p_s & %p_u & %envelope & -> & _ & #key & _) post".
wp_lam. wp_pures.
wp_apply wp_list_of_term. rewrite Spec.of_listK. wp_pures.
rewrite subst_list_match /=.
wp_list_match => [k_s' p_s' P_s' P_u' envelope' e | ]; last by [].
symmetry in e; inversion e; subst; clear e.
rewrite /OPRF. wp_pures.
wp_apply wp_H'; wp_apply wp_texp; wp_list; wp_apply wp_H.
wp_apply wp_derive_senc_key. wp_pures.
by iApply "post".
Qed.

(** Sessions, which the game does not check. *)
Definition do_client : val :=
  rec: "loop" "c" "uid" "pw" :=
    Fork ("loop" "c" "uid" "pw");;
    Client.session "uid" "c" "pw";;
    #().

Lemma wp_do_client c uid pw :
  channel c -∗
  cryptis_ctx -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
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
wp_apply (wp_client_session uid pw c (λ _ _, True)%I (λ _, False)%I
            (λ _, True)%I True%I).
{ iFrame "#". iSplit => //. by iIntros "%si _ !>". }
iIntros "%r _". wp_pures. by iApply "post".
Qed.

Definition do_server : val :=
  rec: "loop" "c" "lk" "db" :=
    Fork ("loop" "c" "lk" "db");;
    locked_server "lk" "db" "c";;
    #().

Lemma wp_do_server c lk db alist pw :
  channel c -∗
  cryptis_ctx -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
  server_lock lk db (λ _, pw) alist -∗
  opaque_db (λ _, pw) alist -∗
  {{{ True }}}
    do_server c lk db
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #? #? #? #?".
iLöb as "IH". iIntros "!> %Φ _ post".
wp_rec. wp_pures. wp_apply wp_fork; first by iApply "IH".
wp_pures.
wp_apply (wp_locked_server lk db c (λ _, pw) alist (λ _ _, True)%I
            (λ _, False)%I (λ _, True)%I).
{ iFrame "#". by iIntros "%si _ !>". }
iIntros "%r _". wp_pures. by iApply "post".
Qed.

Definition game : val := λ: "c",
  let: "uid" := TInt 0 in
  let: "pw" := mk_password #() in
  let: "db" := AList.new #() in
  let: "file" := register "db" "uid" "pw" in
  let: "lk" := new_server_lock #() in
  Fork (do_client "c" "uid" "pw");;
  Fork (do_server "c" "lk" "db");;
  oracle_phase "c" "pw";;
  send "c" "file";;
  bind: "rw" := envelope_key "pw" "file" in
  let: "guess" := recv "c" in
  assert: (~ eq_term "rw" "guess").

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #chan #octx #?"; rewrite /game; wp_pures.
iAssert (public (TInt 0)) as "#p_uid"; first by rewrite public_TInt.
wp_apply wp_mk_password => //.
iIntros "%pw (#m_pw & s_pw & s_file & tok)". wp_pures.
iMod (freeze_secret with "s_pw") as "#s_pw".
wp_apply AList.wp_empty => //. iIntros "%db db". wp_pures.
wp_apply (wp_register db (alist := ∅) (pw_of := λ _, TNonce pw)
            (uid := TInt 0) (pw := TNonce pw) with "[$db $tok]") => //.
{ iFrame "#". by rewrite /opaque_logs /opaque_db !big_sepM_empty. }
iIntros "%file (#file & db & logs & #odb)". wp_pures.
wp_apply (wp_new_server_lock with "[$db $logs]"). iIntros "%lk #lock".
wp_pures.
wp_apply wp_fork; first by wp_apply wp_do_client. wp_pures.
wp_apply wp_fork; first by wp_apply wp_do_server. wp_pures.
iMod (use_oracle with "s_file") as "[#used tok]".
wp_apply (wp_oracle_phase with "[$tok]"); first by iFrame "#".
iIntros "tok". wp_pures.
(* The file leaks; the oracle is closed. *)
iMod (term_meta_set (opN.@"stolen") true with "tok") as "#st"; first done.
iDestruct (public_opaque_file with "file st") as "(%t & -> & #p_t)".
wp_apply wp_send => //. wp_pures.
wp_apply wp_envelope_key => //. iIntros "%k_s #key". wp_pures.
wp_apply wp_recv => //. iIntros "%guess #p_guess".
wp_pure _ credit:"c1". wp_pures.
wp_apply wp_assert. wp_eq_term e.
- subst guess.
  iDestruct "octx" as "(HpredH & _)".
  iEval (rewrite public_senc_key /oprf) in "p_guess".
  iDestruct (public_THashE with "HpredH p_guess") as "[p | [_ pred]]".
  + rewrite public_of_list /=. iDestruct "p" as "[p_pw _]".
    iDestruct ("s_pw" with "p_pw") as "f".
    by iMod (lc_fupd_elim_later with "c1 f") as "[]".
  + iMod (lc_fupd_elim_later with "c1 pred") as "#pred'".
    by iDestruct (H_pred_oprf_key with "key pred'") as "[]".
- wp_pures. iModIntro. by iSplit.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; cryptisΣ; tlockΣ; opaqueΣ].

Lemma opaque_offline_guessing σ₁ σ₂ (v : val) t₂ e₂ :
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
