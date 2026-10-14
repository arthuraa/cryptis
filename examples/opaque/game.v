From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang.lib Require Import assert.

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par lock ticket_lock.
From cryptis.examples Require Import alist.

From cryptis.examples.opaque Require Import impl server_proofs client_proofs shared.
From cryptis Require Import lib term cryptis primitives tactics role adequacy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !opaqueGS Σ}.
Abbreviation iProp := (iProp Σ).

Definition gameN := nroot.@"game".

(** Postcondition after a party completes a handshake. *)
Definition session_res (rl : role) (r : option term) : iProp :=
  match r with
  | None => True
  | Some t =>
      ∃ si, ⌜t = si_result si⌝ ∗
            ⌜session_of rl si⌝ ∗
            public (si_uid si) ∗
            □ (public (si_key si) ↔ ▷ □ False) ∗
            term_token (share_of rl si) (↑gameN)
  end.

Definition session_secret (r : option term) : iProp :=
  match r with
  | None => True
  | Some t => ∃ si, ⌜t = si_result si⌝ ∗ □ (public (si_key si) ↔ ▷ □ False)
  end.

#[global] Instance session_secret_persistent r : Persistent (session_secret r).
Proof. by case: r => [t|] /=; apply _. Qed.

Lemma session_res_secret rl r : session_res rl r -∗ session_secret r.
Proof.
case: r => [t|] /=; last by iIntros "_".
iIntros "(%si & -> & _ & _ & #s & _)". iExists si. by iSplit.
Qed.

Definition unguessable_option : val :=
  λ: "x" "c",
    bind: "x'" := "x" in
      assert: (~ eq_term "x'" (recv "c")).

Lemma wp_unguessable_option (x : option term) (c : val) :
  channel c -∗
  session_secret x -∗
  WP unguessable_option (repr x) c {{ _, True }}.
Proof.
iIntros "#? #Hx".
wp_lam. wp_pures.
destruct x as [x|]; wp_pures => //.
iDestruct "Hx" as "(%si & -> & #s)".
wp_apply wp_assert.
wp_apply wp_recv => //.
iIntros "%guess #pubguess".
wp_bind (eq_term _ _).
wp_eq_term H.
- subst guess.
  rewrite /si_result public_of_list /=.
  iDestruct "pubguess" as "(_ & p_key & _)".
  iDestruct ("s" with "p_key") as "contra".
  wp_pures. by iDestruct "contra" as "[]".
- wp_pures. iModIntro. by iSplit.
Qed.

Definition neq_options : val :=
λ: "x1" "x2",
bind: "x1'" := "x1" in
bind: "x2'" := "x2" in
assert: (~ eq_term "x1'" "x2'").

Lemma wp_neq_options rl (x1 x2 : option term) :
  session_res rl x1 -∗
  session_res rl x2 -∗
  WP neq_options (repr x1) (repr x2) {{ _, True }}.
Proof.
iIntros "H1 H2".
wp_lam.
destruct x1 as [x1|]; wp_pures => //.
destruct x2 as [x2|]; wp_pures => //.
wp_apply wp_assert.
iDestruct "H1" as "(%si1 & -> & %sh1 & #p_uid1 & #s1 & tok1)".
iDestruct "H2" as "(%si2 & -> & %sh2 & #p_uid2 & #s2 & tok2)".
wp_bind (eq_term _ _).
wp_eq_term H.
- (* Both results are the same term, hence the same key, hence the same share,
     which then carries two overlapping tokens. *)
  move: (H) => /Spec.of_list_inj /(f_equal (λ l, nth 1 l (TInt 0))) /= ekey.
  iEval (rewrite -(share_of_key_inj sh1 sh2 ekey)) in "tok2".
  iDestruct (term_token_disj with "tok1 tok2") as %dis.
  pose proof (nclose_non_empty gameN). set_solver.
- wp_pures. iModIntro. by iSplit.
Qed.

Definition game_round : val := λ: "c" "db" "uid" "pw",
  let: "SKs" := Server.session "db" "c" ||| Client.session "uid" "c" "pw" in
  unguessable_option (Fst "SKs") "c";;
  unguessable_option (Snd "SKs") "c";;
  "SKs".

Definition game : val := λ: "c",
  let: "uid" := mk_nonce #() in
  let: "pw" := mk_nonce #() in
  let: "db" := AList.new #() in
  AList.insert "db" "uid" (Server.make_file "pw") ;;
  let: "SK1s" := game_round "c" "db" "uid" "pw" in
  let: "SK2s" := game_round "c" "db" "uid" "pw" in
  assert: (~ eq_term "pw" (recv "c")) ;;
  neq_options (Fst "SK1s") (Fst "SK2s") ;;
  neq_options (Snd "SK1s") (Snd "SK2s") ;;
  #().

Definition session_res' rl (x : val) : iProp :=
  ∃ r : option term, ⌜x = repr r⌝ ∗ session_res rl r.

(** One round of the game: both roles run in parallel, and both results are
    tested against the attacker.  Each role's result is converted to
    [session_res], carrying the role's token on its own share, which is what
    [neq_options] needs to compare two rounds. *)
Lemma wp_game_round c db alist uid pw :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I -∗
  public uid -∗
  minted pw -∗
  □ (public pw ↔ ▷ □ False) -∗
  opaque_db alist -∗
  {{{ AList.is_alist db alist }}}
    game_round c db uid pw
  {{{ (rs rc : option term), RET (repr rs, repr rc)%V;
      AList.is_alist db alist ∗
      session_res Resp rs ∗
      session_res Init rc }}}.
Proof.
iIntros "#? #Hchannel #ctx #N_φ #p_uid #m_pw #s_pw #Hdb %Φ !> Halist Hpost".
wp_lam. wp_pures.
wp_apply (wp_par (λ x, session_res' Resp x ∗ AList.is_alist db alist)%I
                 (λ x, session_res' Init x)%I with "[Halist]").
- iApply (wp_server_session db c alist (λ _ _, True)%I with "[Halist]") => //.
  { iFrame "Halist"; do !iSplit => //. by iIntros "%si _ !>". }
  iNext. iIntros "%r [Halist Hres]". iFrame "Halist".
  iExists r. iSplit; first by [].
  iDestruct "Hres" as "[-> | (%si & -> & %ss & (_ & #p_uid' & _ & _ & _)
                                 & _ & #sec & tok & _)]" => //=.
  iExists si. iSplit; first by []. iSplit; first by [].
  iSplit => //. iSplit => //.
  rewrite /share_of /=.
  iApply (term_token_drop with "tok"); solve_ndisj.
- iApply (wp_client_session uid pw c (λ _ _, True)%I) => //.
  { by do !iSplit => //. }
  iNext. iIntros "%r Hres".
  iExists r. iSplit; first by [].
  iDestruct "Hres" as "[-> | (%si & -> & (_ & #p_uid' & _ & _ & _)
                                 & #sec & tok & _)]" => //=.
  iExists si. iSplit; first by []. iSplit; first by [].
  iSplit => //. iSplit => //.
  rewrite /share_of /=.
  iApply (term_token_drop with "tok"); solve_ndisj.
- iIntros "%vs %vc [[(%rs & -> & Hs) Halist] (%rc & -> & Hc)]".
  iNext. wp_pures.
  iDestruct (session_res_secret with "Hs") as "#sec_s".
  iDestruct (session_res_secret with "Hc") as "#sec_c".
  wp_bind (unguessable_option _ _).
  iApply wp_wand; first by iApply (wp_unguessable_option with "Hchannel sec_s").
  iIntros "% _". wp_pures.
  wp_bind (unguessable_option _ _).
  iApply wp_wand; first by iApply (wp_unguessable_option with "Hchannel sec_c").
  iIntros "% _". wp_pures.
  iModIntro. iApply "Hpost". iFrame.
Qed.

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#Hcryptis #Hchannel #ctx #N_φ".
wp_lam.
wp_apply (wp_mk_nonce (fun _ => True)%I (fun _ => False)%I) => //.
iIntros "%uid #Hminuid #Hpubuid #Hdhuid _ _".
iAssert (public uid) as "Hpubuid'".
by iApply "Hpubuid".
iClear "Hpubuid".
wp_pures.
wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I) => //.
iIntros "%pw #Hminpw #Hprivpw #Hdhpw _ _".
wp_pures.
wp_bind (AList.new #()).
iApply AList.wp_empty => //.
iNext.
iIntros "%db Halist".
wp_pures.
wp_apply (wp_make_file pw).
do !iSplit => //.
iIntros "%file #Hopaquefile" => /=.
wp_bind (AList.insert db uid file).
iApply (AList.wp_insert with "Halist").
iNext.
iIntros "Halist".
wp_pures.
iAssert (opaque_db (<[TNonce uid:=file]> ∅ : gmap term val)) as "#Hdb".
  iApply big_sepM_insert => //.
  by do !iSplit => //.
wp_apply (wp_game_round
            with "Hcryptis Hchannel ctx N_φ Hpubuid' Hminpw Hprivpw Hdb Halist").
iIntros "%SKs1 %SKc1 (Halist & Hs1 & Hc1)".
wp_pures.
wp_apply (wp_game_round
            with "Hcryptis Hchannel ctx N_φ Hpubuid' Hminpw Hprivpw Hdb Halist").
iIntros "%SKs2 %SKc2 (Halist & Hs2 & Hc2)".
wp_pures.
wp_apply wp_assert.
wp_apply wp_recv => //.
iIntros "%attack #Hpubattack".
wp_bind (eq_term _ _).
wp_eq_term H.
  rewrite H.
  iDestruct "Hprivpw" as "[Hprivpw _]".
  iDestruct ("Hprivpw" with "Hpubattack") as "Hcontra".
  wp_pures.
  by iDestruct "Hcontra" as "%Hcontra".
wp_pures.
iModIntro.
iSplit => //.
iNext.
wp_pures.
wp_bind (neq_options _ _).
iApply (wp_wand with "[Hs1 Hs2]"); first by iApply (wp_neq_options with "Hs1 Hs2").
iIntros "% _". wp_pures.
wp_bind (neq_options _ _).
iApply (wp_wand with "[Hc1 Hc2]"); first by iApply (wp_neq_options with "Hc1 Hc2").
iIntros "% _". by wp_pures.
Qed.

End Game.

Definition F : gFunctors := #[heapΣ; spawnΣ; cryptisΣ; opaqueΣ].

Lemma opaque_secure σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([run_network game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: cryptis_adequacy.
iIntros (? ? c) "#ctx #chan (_ & _ & senc & hash)".
iMod (opaqueGS_alloc with "hash senc") as (?) "(#? & tok & _ & _)"; eauto.
iMod (opaque_pred_set (λ _ _, True)%I with "tok") as "[#? _]"; eauto.
by iApply (wp_game with "ctx chan [//] [//]").
Qed.
