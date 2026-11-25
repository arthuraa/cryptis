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

(** * OPAQUE: the attacker cannot evaluate the server's OPRF

    The client and the server run as many rounds of OPAQUE as the attacker
    wants, each round a client and a server session in parallel.  Once they
    stop, the game hands a fresh value [p] to the attacker, which must guess
    [F_{k_s}(p)] without interacting with the server or seeing the file.  The
    guess is wrong because the exponent predicate of [k_s] only lets
    [F_{k_s}(p)] be public if the server received a request with base
    [H'(p)] (cf. [public_oprf]). *)

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !opaqueGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (pw : term).

Definition round : val := λ: "c" "db" "uid" "pw",
  Server.session "db" "c" ||| Client.session "uid" "c" "pw".

Definition rounds : val := rec: "loop" "c" "db" "uid" "pw" :=
  if: eq_term (recv "c") (TInt 0) then #()
  else round "c" "db" "uid" "pw";; "loop" "c" "db" "uid" "pw".

Lemma wp_rounds c db alist pw_of uid pw :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
  opaque_db pw_of alist -∗
  public uid -∗
  minted pw -∗
  {{{ AList.is_alist db alist ∗ opaque_logs pw_of alist }}}
    rounds c db uid pw
  {{{ RET #(); AList.is_alist db alist ∗ opaque_logs pw_of alist }}}.
Proof.
iIntros "#? #chan #? #? #? #? #?".
iLöb as "IH". iIntros "%Φ !> [db logs] post".
wp_rec. wp_pures. wp_apply wp_recv => //. iIntros "%m _".
wp_eq_term e; wp_pures; first by iApply "post"; iFrame.
rewrite /round. wp_pures.
wp_apply (wp_par (λ _, AList.is_alist db alist ∗ opaque_logs pw_of alist)%I
                 (λ _, True)%I with "[db logs] []").
- iApply (wp_server_session db c pw_of alist (λ _ _, True)%I (λ _, False)%I
            (λ _, True)%I with "[$db $logs]").
  + iFrame "#". by iIntros "%si _ !>".
  + by iIntros "!> %r (db & logs & _)"; iFrame.
- iApply (wp_client_session uid pw c (λ _ _, True)%I (λ _, False)%I
            (λ _, True)%I True%I).
  + iFrame "#". iSplit => //. by iIntros "%si _ !>".
  + by iIntros "!> %r _".
- iIntros "%v1 %v2 [[db logs] _] !>". wp_pures.
  by iApply ("IH" with "[$db $logs] post").
Qed.

(** The attacker gets a fresh value and must evaluate the OPRF of the file at
    it. *)
Definition oprf_challenge : val := λ: "c" "file",
  bind: "file_l" := list_of_term "file" in
  list_match: [ "k_s"; "p_s"; "P_s"; "P_u"; "envelope" ] := "file_l" in
  let: "p" := mk_nonce #() in
  send "c" "p" ;;
  assert: (~ eq_term (recv "c") (OPRF "k_s" "p")).

Lemma wp_oprf_challenge c pw file B :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_file pw file -∗
  {{{ oprf_log pw B ∗ file_secret pw }}}
    oprf_challenge c file
  {{{ v, RET v; True }}}.
Proof.
iIntros "#? #chan #(HpredH & _) #file %Φ !> [[auth #m_B] s_file] post".
iDestruct "file"
  as "(%k_s & %p_s & %p_u & %envelope & -> & _ & _ & #s_k & #e_k & _)".
wp_lam. wp_pures.
wp_apply wp_list_of_term. rewrite Spec.of_listK. wp_pures.
rewrite subst_list_match /=.
wp_list_match => [k_s' p_s' P_s' P_u' envelope' e' | ]; last by [].
symmetry in e'; inversion e'; subst; clear e'.
(* The value is fresh with respect to the bases the server evaluated. *)
wp_apply (wp_mk_nonce_freshN B (λ _, True)%I (λ _, False)%I
            (λ t, {[TNonce t]})) => //.
- iIntros "%t %t_B". by iApply (big_sepS_elem_of with "m_B").
- iIntros "%t". rewrite big_sepS_singleton. iIntros "!>"; iSplit; by iIntros "?".
iIntros "%p %fresh #m_p #p_p _ _ tok_p".
rewrite big_sepS_singleton.
wp_pures. wp_apply wp_send => //.
  by iApply "p_p"; iIntros "!> !>".
wp_pures. wp_apply wp_assert.
rewrite /OPRF. wp_pures.
wp_apply wp_H'; wp_apply wp_texp; wp_list; wp_apply wp_H.
wp_apply wp_recv => //. iIntros "%y #p_y".
wp_eq_term Hy.
- subst y.
  iDestruct (public_THashE with "HpredH p_y") as "[p | [_ contra]]"; last first.
  { (* The oracle of [offline_guessing.v] was never used at [p]. *)
    iAssert (▷ False)%I with "[tok_p]" as ">[]".
    iNext. iDestruct (H_pred_oracle_used with "contra") as "used".
    iApply (term_meta_token with "tok_p used"). solve_ndisj. }
  iEval (rewrite public_of_list /=) in "p".
  iDestruct "p" as "(_ & p & _)".
  have Nx : negb (is_exp (hash_result "H" p)) by [].
  have Nm : negb (is_gmul (hash_result "H" p)) by [].
  (* [k_s] only consents to the bases the server logged. *)
  iPoseProof (public_oprf pw _ Nx Nm with "s_k e_k p") as "q".
  wp_pures.
  iDestruct "q" as "[st | q]".
  + by iDestruct (file_secret_stolen with "s_file st") as "[]".
  + iDestruct (oprf_log_queried with "[$auth $m_B] q") as %p_B.
    case: (fresh _ p_B). apply: STHash. exact: subterm_tag.
- wp_pures. iModIntro. iSplit => //. by iApply "post".
Qed.

Definition game : val := λ: "c",
  let: "uid" := TInt 0 in
  let: "pw" := mk_password #() in
  let: "db" := AList.new #() in
  let: "file" := register "db" "uid" "pw" in
  rounds "c" "db" "uid" "pw";;
  oprf_challenge "c" "file".

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #chan #? #?"; rewrite /game; wp_pures.
iAssert (public (TInt 0)) as "#p_uid"; first by rewrite public_TInt.
wp_apply (wp_mk_password with "ctx").
iIntros "%pw (#m_pw & _ & s_file & tok)". wp_pures.
wp_apply AList.wp_empty => //. iIntros "%db db". wp_pures.
wp_apply (wp_register db (alist := ∅) (pw_of := λ _, TNonce pw)
            (uid := TInt 0) (pw := TNonce pw) with "[$db $tok]") => //.
{ iFrame "#". by rewrite /opaque_logs /opaque_db !big_sepM_empty. }
iIntros "%file (#file & db & logs & #odb)". wp_pures.
wp_apply (wp_rounds with "ctx chan [//] [//] odb p_uid m_pw [$db $logs]").
iIntros "[_ logs]". wp_pures.
iDestruct (big_sepM_insert with "logs") as "[[%B log] _]"; first done.
by wp_apply (wp_oprf_challenge with "ctx chan [//] file [$log $s_file]").
Qed.

End Game.

Definition F : gFunctors := #[heapΣ; spawnΣ; cryptisΣ; opaqueΣ].

Lemma opaque_oprf_secure σ₁ σ₂ (v : val) t₂ e₂ :
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
