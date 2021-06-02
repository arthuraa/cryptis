From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib guarded term crypto primitives tactics.
From crypto Require Import session nsl dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSLDH.

Context `{!cryptoG Σ, !heapG Σ, !network Σ, !nslG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types rl : role.

Variable N : namespace.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition nsl_dh_init : val := λ: "g" "skA" "pkA" "pkB",
  let: "a" := mknonce #() in
  let: "ga" := texp (tgroup "g") "a" in
  bind: "gb" := nsl_init (N.@"nsl") "skA" "pkA" "pkB" "ga" in
  SOME (texp "gb" "a").

Definition nsl_dh_resp : val := λ: "g" "skB" "pkB",
  let: "b" := mknonce #() in
  let: "gb" := texp (tgroup "g") "b" in
  bind: "res" := nsl_resp (N.@"nsl") "skB" "pkB" "gb" in
  let: "pkA" := Fst "res" in
  let: "ga" := Snd "res" in
  SOME ("pkA", texp "ga" "b").

Implicit Types Ψ : val → iProp.
Implicit Types kA kB : term.

Definition nsl_dh_inv g rl kA kB ga gb : iProp :=
  match rl with
  | Init =>
    ∃ a, ⌜ga = TExp g [a]⌝ ∧
    □ ∀ b, (pterm (TExp g [a; b]) → ◇ pterm b)
  | Resp =>
    ∃ b, ⌜gb = TExp g [b]⌝ ∧
    □ ∀ a, (pterm (TExp g [a; b]) → ◇ pterm a)
  end%I.

Definition nsl_dh_fail (k : term) a : iProp :=
  ∃ k', meta a (N.@"peer") k' ∧ corruption k k'.

Lemma pterm_nsl_dh1 g a k k' :
  dh_gen g -∗
  dh_nonce (nsl_dh_fail k) a -∗
  meta a (N.@"peer") k' -∗
  pterm (TExp g [TNonce a])  ↔ ▷ corruption k k'.
Proof.
iIntros "#gP #a_pred #meta"; iSplit.
- iIntros "#p_e".
  iDestruct (dh_nonce_elim1 with "a_pred p_e") as (k'') "[meta' corr]".
  iModIntro.
  by iPoseProof (meta_agree with "meta meta'") as "<-".
- iIntros "#corr".
  iApply dh_pterm_TExp; eauto.
  by iExists k'; iModIntro; iModIntro; iSplit; eauto.
Qed.

Lemma pterm_nsl_dh2 g a k t :
  dh_nonce (nsl_dh_fail k) a -∗
  pterm (TExp g [TNonce a; t]) -∗ ◇ pterm t.
Proof.
iIntros "#a_pred #p_e".
by iPoseProof (dh_nonce_elim2 with "a_pred p_e") as ">[??]".
Qed.

Lemma wp_nsl_dh_init g kA kB E Ψ :
  ↑N ⊆ E →
  N ## cryptoN.@"nonce" →
  nonces_of_term g = ∅ →
  nsl_ctx (N.@"nsl") (nsl_dh_inv g) -∗
  pterm (TKey Enc kA) -∗
  pterm (TKey Enc kB) -∗
  (∀ ogab : option term,
      (if ogab is Some gab then
         sterm gab ∧
         (corruption kA kB ∨ □ (pterm gab → ▷ False))
       else True) -∗
      Ψ (repr ogab)) -∗
  WP nsl_dh_init g (TKey Dec kA) (TKey Enc kA) (TKey Enc kB) @ E {{ Ψ }}.
Proof.
iIntros (?? g0) "#ctx #p_e_kA #p_e_kB Hpost".
rewrite /nsl_dh_init; wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (dh_pred (nsl_dh_fail kA))).
iIntros (a) "#s_a #a_pred token".
rewrite (meta_token_difference _ (↑N.@"peer")); last solve_ndisj.
iDestruct "token" as "[dh token]".
iMod (meta_set _ _ kB with "dh") as "#dh"; eauto.
wp_pures; wp_bind (tgroup _); iApply wp_tgroup.
wp_pures; wp_bind (texp _ _); iApply wp_texp.
rewrite Spec.texpA; wp_pures; wp_bind (nsl_init _ _ _ _ _).
iApply (wp_nsl_init with "ctx p_e_kA p_e_kB [] [] [] [token]") => //.
- solve_ndisj.
- rewrite sterm_TExp /=; iSplit.
    by iApply dh_gen_sterm; iApply nonces_of_term_dh_gen.
  by rewrite /=; iSplit.
- by iModIntro; iApply pterm_nsl_dh1; eauto; iApply nonces_of_term_dh_gen.
- iIntros (nB); rewrite /=.
  iExists (TNonce a); iSplit => //.
  iModIntro; iIntros (b) "p_b".
  by iApply pterm_nsl_dh2.
- rewrite /crypto_meta_token nonces_of_term_TExp /=.
  rewrite g0 nonces_of_term_eq right_id_L left_id_L /=.
  iSplit; first by iPureIntro; set_solver.
  rewrite big_sepS_singleton.
  rewrite (meta_token_difference _ (↑N.@"nsl")).
    by iDestruct "token" as "[??]".
  by solve_ndisj.
iIntros (onB) "pub"; case: onB=> [nB|]; last by protocol_failure.
iDestruct "pub" as "# [s_nB [fail | succ]]".
  wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
  iApply ("Hpost" $! (Some (Spec.texp nB (TNonce a)))).
  iSplit; first by iApply sterm_texp => //.
  by eauto.
iDestruct "succ" as (b) "[-> #succ]".
wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
iApply ("Hpost" $! (Some (Spec.texp (TExp g [b]) (TNonce a)))).
iSplit; first by iApply sterm_texp => //.
iRight; iModIntro.
rewrite Spec.texpA.
iIntros "#contra".
iDestruct ("succ" with "contra") as "{succ} >succ".
by iApply dh_nonce_elim0.
Qed.

Lemma wp_dh_responder g kB E Ψ :
  ↑N ⊆ E →
  N ## cryptoN.@"nonce" →
  nonces_of_term g = ∅ →
  nsl_ctx (N.@"nsl") (nsl_dh_inv g) -∗
  pterm (TKey Enc kB) -∗
  (∀ oresp : option (term * term),
      (if oresp is Some (pkA, gab) then
         ∃ kA,
           ⌜pkA = TKey Enc kA⌝ ∧
           pterm pkA ∧
           sterm gab ∧
           (corruption kA kB ∨ □ (pterm gab → ▷ False))
       else True) -∗
      Ψ (repr oresp)) -∗
  WP nsl_dh_resp g (TKey Dec kB) (TKey Enc kB) @ E {{ Ψ }}.
Proof.
iIntros (?? g0) "#ctx #p_e_kB Hpost".
rewrite /nsl_dh_resp; wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (dh_pred (nsl_dh_fail kB))).
iIntros (b) "#s_b #b_pred token".
rewrite (meta_token_difference _ (↑N.@"peer")); last solve_ndisj.
iDestruct "token" as "[dh token]".
wp_pures; wp_bind (tgroup _); iApply wp_tgroup.
wp_pures; wp_bind (texp _ _); iApply wp_texp.
rewrite Spec.texpA; wp_pures; wp_bind (nsl_resp _ _ _ _).
iApply (wp_nsl_resp with "ctx p_e_kB [token] [] [dh]") => //.
- solve_ndisj.
- rewrite /crypto_meta_token nonces_of_term_TExp /=.
  rewrite g0 nonces_of_term_eq right_id_L left_id_L /=.
  iSplit; first by iPureIntro; set_solver.
  rewrite big_sepS_singleton.
  rewrite (meta_token_difference _ (↑N.@"nsl")).
    by iDestruct "token" as "[??]".
  by solve_ndisj.
- rewrite sterm_TExp /=; iSplit; eauto.
  by iApply dh_gen_sterm; iApply nonces_of_term_dh_gen.
- iIntros (kA nA).
  iMod (meta_set _ b kA with "dh") as "#meta"; eauto.
  iModIntro; iSplit.
  + iModIntro; rewrite [corruption _ _]comm.
    by iApply pterm_nsl_dh1 => //; iApply nonces_of_term_dh_gen.
  + iExists (TNonce b); iSplit => //.
    iIntros "!> %".
    rewrite -[ [a; TNonce b]]/(seq.cat [a] [TNonce b]) TExpC /=.
    by iIntros "#?"; iApply pterm_nsl_dh2.
iIntros ([[pkA nA]|]) "resp"; last by protocol_failure.
iDestruct "resp" as (kA) "# (-> & p_e_kA & s_nA & p_nA & inv)".
wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
iApply ("Hpost" $! (Some (TKey Enc kA, Spec.texp nA (TNonce b)))).
iExists _; do 3!iSplit => //; eauto.
  by iApply sterm_texp.
iDestruct "inv" as "[inv|inv]"; eauto.
iDestruct "inv" as (t) "[-> #inv]".
rewrite Spec.texpA.
rewrite -[ [TNonce b; t]]/(seq.cat [TNonce b] [t]) TExpC /=.
iRight; iIntros "!> #contra".
iSpecialize ("inv" with "contra").
iDestruct "inv" as ">inv".
by iApply dh_nonce_elim0.
Qed.

End NSLDH.
