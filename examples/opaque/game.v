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
From cryptis.lib Require Import hmqv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !opaqueGS Σ}.
Abbreviation iProp := (iProp Σ).

Definition gameN := nroot.@"game".

(** What a role's specification gives the game when it completes. *)
Definition raw_res pw (rl : role) (r : option term) : iProp :=
  match r with
  | None => True
  | Some t =>
      ∃ si, ⌜t = si_result si⌝ ∗
            ⌜session_of rl si⌝ ∗
            public (si_uid si) ∗
            session pw (λ _, False)%I rl si ∗
            term_token (share_of rl si) (↑gameN)
  end.

Definition raw_res' pw rl (x : val) : iProp :=
  ∃ r : option term, ⌜x = repr r⌝ ∗ raw_res pw rl r.

(** What the game keeps: the key stays secret, even after the password leaks,
    because the game never releases a session. *)
Definition session_res (rl : role) (r : option term) : iProp :=
  match r with
  | None => True
  | Some t =>
      ∃ si, ⌜t = si_result si⌝ ∗
            ⌜session_of rl si⌝ ∗
            public (si_uid si) ∗
            □ (public (si_key si) → ▷ False) ∗
            term_token (share_of rl si) (↑gameN)
  end.

Definition session_secret (r : option term) : iProp :=
  match r with
  | None => True
  | Some t => ∃ si, ⌜t = si_result si⌝ ∗ □ (public (si_key si) → ▷ False)
  end.

(* The conversion needs the password, and for the client the file, to be
   secret at the time. *)
Lemma raw_res_session_res pw rl r :
  secret pw -∗
  (if rl is Init then file_secret pw else True) -∗
  raw_res pw rl r -∗
  secret pw ∗ (if rl is Init then file_secret pw else True) ∗
  ◇ session_res rl r.
Proof.
case: r => [t|] /=; iIntros "s_pw s_file Hr"; last by iFrame "s_pw s_file".
iDestruct "Hr" as "(%si & -> & %sh & #p_uid & #sess & tok)".
iPoseProof (secret_session with "s_pw s_file sess") as "#nc".
iFrame "s_pw s_file". iMod "nc" as "#nc".
iPoseProof (session_ok with "sess nc") as "#ok".
iModIntro. iExists si. iFrame "tok".
do 3!(iSplit; first done).
iIntros "!> #p". iDestruct ("ok" with "p") as "f". iNext.
by iDestruct "f" as "#[]".
Qed.

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

(** A round after the file is stolen.  The attacker may now impersonate the
    server to the client, but not the client to the server, so only the
    server's key is tested. *)
Definition stolen_round : val := λ: "c" "db" "uid" "pw",
  let: "SKs" := Server.session "db" "c" ||| Client.session "uid" "c" "pw" in
  unguessable_option (Fst "SKs") "c";;
  Fst "SKs".

(** The attacker gets a fresh candidate password and must evaluate the OPRF
    of the file at it, without querying the server again. *)
Definition oprf_challenge : val := λ: "c" "file",
  bind: "file_l" := list_of_term "file" in
  list_match: [ "k_s"; "p_s"; "P_s"; "P_u"; "envelope" ] := "file_l" in
  let: "w" := mk_nonce #() in
  send "c" "w" ;;
  assert: (~ eq_term (recv "c") (OPRF "k_s" "w")).

(** The game: two rounds, each tested while the password and the file are
    secret; then the OPRF challenge, which must fail; then the file is stolen,
    and a third round follows; then a password guess, which must fail; then
    the password leaks, and the keys of the last two rounds must still be
    unguessable. *)
Definition game : val := λ: "c",
  let: "uid" := mk_nonce #() in
  let: "pw" := mk_nonce #() in
  let: "db" := AList.new #() in
  let: "file" := Server.make_file "pw" in
  AList.insert "db" "uid" "file" ;;
  let: "SK1s" := game_round "c" "db" "uid" "pw" in
  let: "SK2s" := game_round "c" "db" "uid" "pw" in
  oprf_challenge "c" "file" ;;
  send "c" "file" ;;
  let: "SK3" := stolen_round "c" "db" "uid" "pw" in
  assert: (~ eq_term "pw" (recv "c")) ;;
  neq_options (Fst "SK1s") (Fst "SK2s") ;;
  neq_options (Snd "SK1s") (Snd "SK2s") ;;
  send "c" "pw" ;;
  unguessable_option (Fst "SK2s") "c" ;;
  unguessable_option (Snd "SK2s") "c" ;;
  unguessable_option "SK3" "c" ;;
  #().

(** One round of the game: both roles run in parallel, and both results are
    tested against the attacker.  Each role's result is converted to
    [session_res], carrying the role's token on its own share, which is what
    [neq_options] needs to compare two rounds. *)
Lemma wp_game_round c db alist uid pw :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
  public uid -∗
  minted pw -∗
  opaque_db (λ _, pw) alist -∗
  {{{ AList.is_alist db alist ∗ opaque_logs (λ _, pw) alist ∗ secret pw ∗
      file_secret pw }}}
    game_round c db uid pw
  {{{ (rs rc : option term), RET (repr rs, repr rc)%V;
      AList.is_alist db alist ∗ opaque_logs (λ _, pw) alist ∗
      secret pw ∗ file_secret pw ∗
      session_res Resp rs ∗
      session_res Init rc }}}.
Proof.
iIntros "#? #Hchannel #ctx #N_φ #p_uid #m_pw #Hdb %Φ !>
         (Halist & Hlogs & s_pw & s_file) Hpost".
wp_lam. wp_pures.
wp_apply (wp_par (λ x, raw_res' pw Resp x ∗ AList.is_alist db alist ∗
                       opaque_logs (λ _, pw) alist)%I
                 (λ x, raw_res' pw Init x)%I with "[Halist Hlogs]").
- iApply (wp_server_session db c (λ _, pw) alist (λ _ _, True)%I
            (λ _, False)%I (λ si, term_token (si_sshare si) (↑gameN))
            with "[Halist Hlogs]") => //.
  { iFrame "Halist Hlogs"; do !iSplit => //.
    iIntros "%si tok !>". iSplit => //.
    iApply (term_token_drop with "tok"). solve_ndisj. }
  iNext. iIntros "%r (Halist & Hlogs & Hres)". iFrame "Halist Hlogs".
  iExists r. iSplit; first by [].
  iDestruct "Hres"
    as "[-> | (%si & -> & %ss & (_ & #p_uid' & _ & _ & _) & _ & #sess & tok
               & _)]" => //=.
  iExists si. by iFrame "p_uid' sess tok".
- iApply (wp_client_session uid pw c (λ _ _, True)%I (λ _, False)%I
            (λ si, term_token (si_blind si) (↑gameN)) True%I) => //.
  { do !iSplit => //.
    iIntros "%si tok !>". iSplit => //.
    iApply (term_token_drop with "tok"). solve_ndisj. }
  iNext. iIntros "%r Hres".
  iExists r. iSplit; first by [].
  iDestruct "Hres" as "[[-> _] | (%si & -> & (_ & #p_uid' & _ & _ & _)
                                    & #sess & tok & _)]" => //=.
  iExists si. by iFrame "p_uid' sess tok".
- iIntros "%vs %vc [((%rs & -> & Hs) & Halist & Hlogs) (%rc & -> & Hc)]".
  iNext.
  iDestruct (raw_res_session_res pw Resp with "s_pw [//] Hs")
    as "(s_pw & _ & Hs)".
  iDestruct (raw_res_session_res pw Init with "s_pw s_file Hc")
    as "(s_pw & s_file & Hc)".
  wp_pures.
  iMod "Hs" as "Hs". iMod "Hc" as "Hc".
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

Lemma wp_stolen_round c db alist uid pw :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
  public uid -∗
  minted pw -∗
  opaque_db (λ _, pw) alist -∗
  {{{ AList.is_alist db alist ∗ opaque_logs (λ _, pw) alist ∗ secret pw }}}
    stolen_round c db uid pw
  {{{ (rs : option term), RET (repr rs);
      AList.is_alist db alist ∗ opaque_logs (λ _, pw) alist ∗
      secret pw ∗ session_secret rs }}}.
Proof.
iIntros "#? #Hchannel #ctx #N_φ #p_uid #m_pw #Hdb %Φ !>
         (Halist & Hlogs & s_pw) Hpost".
wp_lam. wp_pures.
wp_apply (wp_par (λ x, raw_res' pw Resp x ∗ AList.is_alist db alist ∗
                       opaque_logs (λ _, pw) alist)%I
                 (λ _, True)%I with "[Halist Hlogs]").
- iApply (wp_server_session db c (λ _, pw) alist (λ _ _, True)%I
            (λ _, False)%I (λ si, term_token (si_sshare si) (↑gameN))
            with "[Halist Hlogs]") => //.
  { iFrame "Halist Hlogs"; do !iSplit => //.
    iIntros "%si tok !>". iSplit => //.
    iApply (term_token_drop with "tok"). solve_ndisj. }
  iNext. iIntros "%r (Halist & Hlogs & Hres)". iFrame "Halist Hlogs".
  iExists r. iSplit; first by [].
  iDestruct "Hres"
    as "[-> | (%si & -> & %ss & (_ & #p_uid' & _ & _ & _) & _ & #sess & tok
               & _)]" => //=.
  iExists si. by iFrame "p_uid' sess tok".
- iApply (wp_client_session uid pw c (λ _ _, True)%I (λ _, False)%I
            (λ _, True)%I True%I) => //.
  { do !iSplit => //. by iIntros "%si _ !>". }
  by iIntros "!> %r _".
- iIntros "%vs %vc [((%rs & -> & Hs) & Halist & Hlogs) _]".
  iNext.
  iDestruct (raw_res_session_res pw Resp with "s_pw [//] Hs")
    as "(s_pw & _ & Hs)".
  wp_pures.
  iMod "Hs" as "Hs".
  iDestruct (session_res_secret with "Hs") as "#sec_s".
  wp_bind (unguessable_option _ _).
  iApply wp_wand; first by iApply (wp_unguessable_option with "Hchannel sec_s").
  iIntros "% _". wp_pures.
  iModIntro. iApply "Hpost". by iFrame.
Qed.

Lemma wp_oprf_challenge c pw file B :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_file pw file -∗
  {{{ oprf_log pw B ∗ file_secret pw }}}
    oprf_challenge c file
  {{{ v, RET v; oprf_log pw B ∗ file_secret pw }}}.
Proof.
iIntros "#? #Hchannel #(HpredH & _) #Hfile %Φ !> [[auth #m_B] s_file] Hpost".
iDestruct "Hfile"
  as "(%k_s & %p_s & %p_u & %envelope & -> & _ & #s_k & #e_k & _)".
wp_lam. wp_pures.
wp_apply wp_list_of_term. rewrite Spec.of_listK. wp_pures.
rewrite subst_list_match /=.
wp_list_match => [k_s' p_s' P_s' P_u' envelope' e' | ]; last by [].
symmetry in e'; inversion e'; subst; clear e'.
(* The candidate is fresh with respect to the bases the server evaluated. *)
wp_apply (wp_mk_nonce_freshN B (λ _, True)%I (λ _, False)%I (λ _, ∅)) => //.
- iIntros "%t %t_B". by iApply (big_sepS_elem_of with "m_B").
- by iIntros "%t"; rewrite big_sepS_empty.
iIntros "%w %fresh #m_w #p_w _ _ _".
wp_pures. wp_apply wp_send => //.
  by iApply "p_w"; iIntros "!> !>".
wp_pures. wp_apply wp_assert.
rewrite /OPRF. wp_pures.
wp_apply wp_H'; wp_apply wp_texp; wp_list; wp_apply wp_H.
wp_apply wp_recv => //. iIntros "%y #p_y".
wp_eq_term Hy.
- subst y.
  iDestruct (public_THashE with "HpredH p_y") as "[p | [_ contra]]";
    last by wp_pures; iDestruct "contra" as "[]".
  iEval (rewrite public_of_list /=) in "p".
  iDestruct "p" as "(_ & p & _)".
  have Nx : negb (is_exp (hash_result "H" w)) by [].
  have Nm : negb (is_gmul (hash_result "H" w)) by [].
  iPoseProof (public_oprf pw _ Nx Nm with "s_k e_k p") as "q".
  wp_pures.
  iDestruct "q" as "[st | q]".
  + by iDestruct (file_secret_stolen with "s_file st") as "[]".
  + iDestruct (oprf_log_queried with "[$auth $m_B] q") as %w_B.
    case: (fresh _ w_B). apply: STHash. exact: subterm_tag.
- wp_pures. iModIntro. iSplit => //. iApply "Hpost". by iFrame.
Qed.

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  opaque_ctx -∗
  opaque_pred (λ _ _, True)%I (λ _, False)%I -∗
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
(* The password is a secret that the game itself leaks later. *)
iMod pending_alloc as (γ) "pend".
wp_apply (wp_mk_nonce (fun _ => shot γ 1)%I (fun _ => False)%I) => //.
iIntros "%pw #Hminpw #Hpw_shot #Hdhpw _ tok_pw".
iDestruct (term_token_difference pw (↑opN.@"log") with "tok_pw")
  as "[tok_log tok_pw]"; first solve_ndisj.
iDestruct (term_token_drop (↑opN.@"stolen") with "tok_pw") as "s_file";
  first solve_ndisj.
iAssert (□ (public pw ↔ ▷ shot γ 1))%I as "#Hpw_shot'".
{ iModIntro; iSplit.
  - iIntros "#p". iDestruct ("Hpw_shot" with "p") as "#s". iNext.
    by iDestruct "s" as "#s".
  - iIntros "#s". iApply "Hpw_shot". iNext. by iModIntro. }
iPoseProof (secret_alloc with "Hpw_shot' pend") as "s_pw".
wp_pures.
wp_bind (AList.new #()).
iApply AList.wp_empty => //.
iNext.
iIntros "%db Halist".
wp_pures.
wp_apply (wp_make_file pw with "[$tok_log]"); first by iFrame "#".
iIntros "%file [#Hopaquefile log]" => /=.
wp_pures.
wp_bind (AList.insert db uid file).
iApply (AList.wp_insert with "Halist").
iNext.
iIntros "Halist".
wp_pures.
iAssert (opaque_db (λ _, pw) (<[TNonce uid:=file]> ∅ : gmap term val)) as "#Hdb".
  iApply big_sepM_insert => //.
  by do !iSplit => //.
iAssert (opaque_logs (λ _, pw) (<[TNonce uid:=file]> ∅ : gmap term val))
  with "[log]" as "Hlogs".
{ iApply big_sepM_insert => //. iSplitL "log"; last done. by iExists ∅. }
wp_apply (wp_game_round
            with "Hcryptis Hchannel ctx N_φ Hpubuid' Hminpw Hdb
                  [$Halist $Hlogs $s_pw $s_file]").
iIntros "%SKs1 %SKc1 (Halist & Hlogs & s_pw & s_file & Hs1 & Hc1)".
wp_pures.
wp_apply (wp_game_round
            with "Hcryptis Hchannel ctx N_φ Hpubuid' Hminpw Hdb
                  [$Halist $Hlogs $s_pw $s_file]").
iIntros "%SKs2 %SKc2 (Halist & Hlogs & s_pw & s_file & Hs2 & Hc2)".
iDestruct (session_res_secret with "Hs2") as "#sec_s".
iDestruct (session_res_secret with "Hc2") as "#sec_c".
wp_pures.
iDestruct (big_sepM_insert with "Hlogs") as "[[%B log] Hlogs]"; first done.
wp_apply (wp_oprf_challenge with "Hcryptis Hchannel ctx Hopaquefile
                                  [$log $s_file]").
iIntros "%v [log s_file]".
iAssert (opaque_logs (λ _, pw) (<[TNonce uid:=file]> ∅ : gmap term val))
  with "[log Hlogs]" as "Hlogs".
{ iApply big_sepM_insert => //. iFrame "Hlogs". by iExists B. }
wp_pures.
(* The file is stolen. *)
iMod (steal_file with "s_file") as "#stolen".
iDestruct (public_opaque_file with "Hopaquefile stolen") as "(%t & -> & #p_t)".
wp_apply wp_send => //.
wp_pures.
wp_apply (wp_stolen_round
            with "Hcryptis Hchannel ctx N_φ Hpubuid' Hminpw Hdb
                  [$Halist $Hlogs $s_pw]").
iIntros "%SK3 (Halist & Hlogs & s_pw & #sec_3)".
wp_pures.
wp_apply wp_assert.
wp_apply wp_recv => //.
iIntros "%attack #Hpubattack".
wp_bind (eq_term _ _).
wp_eq_term H.
  rewrite H.
  iDestruct (secret_not_public with "s_pw Hpubattack") as "Hcontra".
  wp_pures.
  by iDestruct "Hcontra" as "[]".
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
iIntros "% _". wp_pures.
(* The leak.  The keys established before it stay secret. *)
iMod (secret_public with "s_pw") as "#p_pw".
wp_apply wp_send => //.
wp_pures.
wp_bind (unguessable_option _ _).
iApply wp_wand; first by iApply (wp_unguessable_option with "Hchannel sec_s").
iIntros "% _". wp_pures.
wp_bind (unguessable_option _ _).
iApply wp_wand; first by iApply (wp_unguessable_option with "Hchannel sec_c").
iIntros "% _". wp_pures.
wp_bind (unguessable_option _ _).
iApply wp_wand; first by iApply (wp_unguessable_option with "Hchannel sec_3").
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
iMod (opaque_pred_set (λ _ _, True)%I (λ _, False)%I with "tok") as "#?".

by iApply (wp_game with "ctx chan [//] [//]").
Qed.
