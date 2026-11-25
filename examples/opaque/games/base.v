From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib term cryptis primitives tactics role.
From cryptis.lib Require Import hmqv.
From cryptis.examples Require Import alist.
From cryptis.examples.opaque Require Import impl shared client_proofs.
From cryptis.examples.opaque Require Import server_proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * OPAQUE games: shared definitions

    The OPAQUE games mirror those of [examples/hmqv/games]; the parties' long-term
    secrets are the password, for the client, and the password file, for the
    server.  This file sets up the passwords and the server's database.

    [Server.accept] owns the database and the OPRF logs, so the games that run
    server sessions in parallel take a lock around it ([locked_accept]).  The
    rest of a session, [Server.finish], runs concurrently with the others. *)

#[local] Existing Instance ticket_lock.

Definition mk_password : val := λ: <>, mk_nonce #().

Definition register : val := λ: "db" "uid" "pw",
  let: "file" := Server.make_file "pw" in
  AList.insert "db" "uid" "file";;
  "file".

Definition new_server_lock : val := λ: <>, newlock #().

Definition locked_accept : val := λ: "lk" "db" "c",
  acquire "lk";;
  let: "r" := Server.accept "db" "c" in
  release "lk";;
  "r".

Definition locked_server : val := λ: "lk" "db" "c",
  bind: "st" := locked_accept "lk" "db" "c" in
  Server.finish "c" "st".

Section Base.

Context `{!cryptisGS Σ, !heapGS Σ, !opaqueGS Σ, !tlockG Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (si : sess_info) (φ : sess_info → role → iProp).
Implicit Types (ρ : sess_info → iProp).
Implicit Types (pw_of : term → term) (alist : gmap term val).

(** A fresh password: whoever owns [secret pw] decides when it leaks, and
    whoever owns [file_secret pw] decides when the file is stolen. *)
Lemma wp_mk_password :
  {{{ cryptis_ctx }}}
    mk_password #()
  {{{ (pw : nonce), RET (TNonce pw : val);
      minted pw ∗ secret pw ∗ file_secret pw ∗ term_token pw (↑opN.@"log" ∪ ↑opN.@"key") }}}.
Proof.
iIntros "%Φ #ctx post". wp_lam.
iMod pending_alloc as (γ) "pend".
wp_apply (wp_mk_nonce (λ _, shot γ 1)%I (λ _, False)%I) => //.
iIntros "%pw #m_pw #s_pw _ _ tok".
iDestruct (term_token_difference pw (↑opN.@"log" ∪ ↑opN.@"key") with "tok")
  as "[tok_log tok]"; first solve_ndisj.
iDestruct (term_token_drop (↑opN.@"stolen" ∪ ↑opN.@"oracle") with "tok") as "s_file";
  first solve_ndisj.
iAssert (□ (public pw ↔ ▷ shot γ 1))%I as "#s_pw'".
{ iModIntro; iSplit.
  - iIntros "#p". iDestruct ("s_pw" with "p") as "#s". iNext.
    by iDestruct "s" as "#s".
  - iIntros "#s". iApply "s_pw". iNext. by iModIntro. }
iPoseProof (secret_alloc with "s_pw' pend") as "sec".
iApply "post". by iFrame.
Qed.

(** Registers [uid] with password [pw], which [pw_of] must already assign to
    it. *)
Lemma wp_register db alist pw_of (uid pw : term) :
  alist !! uid = None →
  pw_of uid = pw →
  {{{ cryptis_ctx ∗ opaque_ctx ∗ public uid ∗ minted pw ∗
      term_token pw (↑opN.@"log" ∪ ↑opN.@"key") ∗
      AList.is_alist db alist ∗ opaque_logs pw_of alist ∗
      opaque_db pw_of alist }}}
    register db uid pw
  {{{ file, RET file;
      opaque_file pw file ∗
      AList.is_alist db (<[uid := file]> alist) ∗
      opaque_logs pw_of (<[uid := file]> alist) ∗
      opaque_db pw_of (<[uid := file]> alist) }}}.
Proof.
move=> uid_fresh e_pw.
iIntros "%Φ (#ctx & #octx & #p_uid & #m_pw & tok & db & logs & #odb) post".
wp_lam. wp_pures.
wp_apply (wp_make_file pw with "[$tok]"); first by iFrame "#".
iIntros "%file [#file log]". wp_pures.
wp_apply (AList.wp_insert with "db"). iIntros "db". wp_pures.
iApply "post". iFrame "file db". iModIntro. iSplitL.
- iApply big_sepM_insert => //. iFrame "logs". iExists ∅. by rewrite e_pw.
- iApply big_sepM_insert => //. iFrame "odb". rewrite e_pw. by iSplit.
Qed.

Definition server_lock lk db pw_of alist : iProp :=
  ∃ γ, is_lock γ lk (AList.is_alist db alist ∗ opaque_logs pw_of alist).

#[global] Instance server_lock_persistent lk db pw_of alist :
  Persistent (server_lock lk db pw_of alist).
Proof. apply _. Qed.

Lemma wp_new_server_lock db pw_of alist :
  {{{ AList.is_alist db alist ∗ opaque_logs pw_of alist }}}
    new_server_lock #()
  {{{ lk, RET lk; server_lock lk db pw_of alist }}}.
Proof.
iIntros "%Φ res post". wp_lam.
wp_apply (newlock_spec with "res"). iIntros "%lk %γ #lock".
iApply "post". by iExists γ.
Qed.

(** [wp_server_accept], with the database behind the lock. *)
Lemma wp_locked_accept lk db c pw_of alist φ ρ ψ R :
  {{{ cryptis_ctx ∗ opaque_ctx ∗ opaque_pred φ ρ ∗ channel c ∗
      server_lock lk db pw_of alist ∗ opaque_db pw_of alist ∗
      (R ∧ ∀ si, term_token (si_sshare si) (⊤ ∖ ↑opN) ={⊤}=∗
                 φ si Init ∗ ψ si) }}}
    locked_accept lk db c
  {{{ v, RET v;
      ⌜v = NONEV⌝ ∗ R ∨ ∃ si,
        ⌜v = SOMEV (server_state_val si)⌝ ∗
        ⌜server_session si⌝ ∗
        opaque_session_for (si_uid si) si ∗
        server_state pw_of si ∗ ψ si }}}.
Proof.
iIntros "%Φ (#ctx & #octx & #N_φ & #chan & (%γ & #lock) & #odb & hook) post".
wp_lam. wp_pures.
wp_apply (acquire_spec with "lock"). iIntros "(locked & db & logs)".
wp_pures.
wp_apply (wp_server_accept db c pw_of alist φ ρ ψ R
            with "[$db $logs $hook]"); first by iFrame "#".
iIntros "%v (db & logs & res)". wp_pures.
wp_apply (release_spec with "[$lock $locked $db $logs]"). iIntros "_".
wp_pures. iApply "post". iModIntro.
iDestruct "res" as "[res|(%si & -> & %ss & #sess_for & _ & res)]";
  first by iLeft.
iRight. iExists si. by iFrame "sess_for res".
Qed.

(** [wp_server_session], with the database behind the lock. *)
Lemma wp_locked_server lk db c pw_of alist φ ρ ψ :
  {{{ cryptis_ctx ∗ opaque_ctx ∗ opaque_pred φ ρ ∗ channel c ∗
      server_lock lk db pw_of alist ∗ opaque_db pw_of alist ∗
      (∀ si, term_token (si_sshare si) (⊤ ∖ ↑opN) ={⊤}=∗ φ si Init ∗ ψ si) }}}
    locked_server lk db c
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_result si)⌝ ∗
        ⌜server_session si⌝ ∗
        opaque_session_for (si_uid si) si ∗
        session (pw_of (si_uid si)) ρ Resp si ∗ ψ si ∗
        (compromised Resp si ∨ φ si Resp) }}}.
Proof.
iIntros "%Φ (#ctx & #octx & #N_φ & #chan & #lock & #odb & hook) post".
wp_lam. wp_pures.
wp_apply (wp_locked_accept lk db c pw_of alist φ ρ ψ True%I with "[hook]").
{ iFrame "#". by iSplit. }
iIntros "%v [[-> _]|(%si & -> & %ss & #sf & st & ψ)]"; wp_pures.
  by iApply ("post" $! None); iLeft.
wp_apply (wp_server_finish with "[$st]"); first by iFrame "#".
iIntros "%r [->|(-> & #sess & res)]".
- iApply ("post" $! None). by iLeft.
- iApply "post". iRight. iExists si. by iFrame "∗ #".
Qed.

(** The key of a session is public if its result is. *)
Lemma public_si_result si :
  public (si_result si) ⊣⊢ public (si_uid si) ∗ public (si_key si).
Proof. by rewrite /si_result public_of_list /= right_id. Qed.

(** As [secret_session], but keeping the secrets: a session completed while the
    password -- and, for the client, the file -- are secret was not
    compromised, so its key is public exactly when released. *)
Lemma secret_session_ok pw ρ rl si :
  secret pw -∗
  (if rl is Init then file_secret pw else True) -∗
  session pw ρ rl si -∗
  ◇ (secret pw ∗ (if rl is Init then file_secret pw else True) ∗
     □ (public (si_key si) ↔ ▷ □ ρ si)).
Proof.
iIntros "s_pw s_file #sess".
iPoseProof "sess" as "(_ & _ & [(_ & _ & [#p_pw|[-> #st]])|(_ & #ok)])".
- by iDestruct (secret_not_public with "s_pw p_pw") as ">[]".
- by iDestruct (file_secret_impersonable with "s_file st") as "[]".
- iModIntro. iFrame. iModIntro. iSplit; first done.
  by iApply (session_release with "sess").
Qed.

End Base.
