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

Context `{!cryptoG Σ, !heapG Σ, !network Σ, !inG Σ sessionR}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types rl : role.

Variable γ : gname.
Variable N : namespace.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition nsl_dh_init : val := λ: "g" "skA" "pkA" "pkB",
  let: "a" := mkdh #() in
  let: "ga" := texp (tgroup "g") "a" in
  bind: "gb" := nsl_init (N.@"nsl") "skA" "pkA" "pkB" "ga" in
  SOME (texp "gb" "a").

Definition nsl_dh_resp : val := λ: "g" "skB" "pkB",
  let: "b" := mkdh #() in
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
  ∃ k', term_meta a (N.@"peer") k' ∧ corruption k k'.

Lemma pterm_nsl_dh1 g a k k' :
  sterm g -∗
  dh_seed (nsl_dh_fail k) a -∗
  term_meta a (N.@"peer") k' -∗
  pterm (TExp g [a])  ↔ ▷ corruption k k'.
Proof.
iIntros "#gP #a_pred #meta"; iSplit.
- iIntros "#p_e".
  iDestruct (dh_seed_elim1 with "a_pred p_e") as (k'') "[meta' corr]".
  iModIntro.
  by iPoseProof (term_meta_agree with "meta meta'") as "<-".
- iIntros "#corr".
  iApply dh_pterm_TExp; eauto.
  by iExists k'; iModIntro; iModIntro; iSplit; eauto.
Qed.

Lemma pterm_nsl_dh2 g a k t :
  dh_seed (nsl_dh_fail k) a -∗
  pterm (TExp g [a; t]) -∗ ◇ pterm t.
Proof.
iIntros "#a_pred #p_e".
by iPoseProof (dh_seed_elim2 with "a_pred p_e") as ">[??]".
Qed.

Existing Instance dh_fresh.

Lemma wp_nsl_dh_init g kA kB E Ψ :
  ↑N ⊆ E →
  nsl_ctx γ (N.@"nsl") (nsl_dh_inv g) -∗
  sterm g -∗
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
iIntros (?) "#ctx #s_g #p_e_kA #p_e_kB Hpost".
rewrite /nsl_dh_init; wp_pures; wp_bind (mknonce _).
iApply (wp_mkdh (nsl_dh_fail kA)).
iIntros (a) "#s_a #a_pred token".
rewrite (term_meta_token_difference _ (↑N.@"peer")); last solve_ndisj.
iDestruct "token" as "[dh token]".
iMod (term_meta_set _ _ _ kB with "dh") as "#dh"; eauto.
wp_pures; wp_bind (tgroup _); iApply wp_tgroup.
wp_pures; wp_bind (texp _ _); iApply wp_texp.
rewrite Spec.texpA; wp_pures; wp_bind (nsl_init _ _ _ _ _).
iApply (wp_nsl_init with "ctx p_e_kA p_e_kB [] [] [] [token]") => //.
- solve_ndisj.
- rewrite sterm_TExp /=; iSplit => //.
  by rewrite /=; iSplit.
- by iModIntro; iApply pterm_nsl_dh1.
- iIntros (nB); rewrite /=.
  iExists a; iSplit => //.
  iModIntro; iIntros (b) "p_b".
  by iApply pterm_nsl_dh2.
- rewrite (term_meta_token_difference _ (↑N.@"nsl")); last solve_ndisj.
  iDestruct "token" as "[token _]".
  by iExists _, _; eauto.
iIntros (onB) "pub"; case: onB=> [nB|]; last by protocol_failure.
iDestruct "pub" as "# [s_nB [fail | succ]]".
  wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
  iApply ("Hpost" $! (Some (Spec.texp nB a))).
  iSplit; first by iApply sterm_texp => //.
  by eauto.
iDestruct "succ" as (b) "[-> #succ]".
wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
iApply ("Hpost" $! (Some (Spec.texp (TExp g [b]) a))).
iSplit; first by iApply sterm_texp => //.
iRight; iModIntro.
rewrite Spec.texpA.
iIntros "#contra".
iDestruct ("succ" with "contra") as "{succ} >succ".
by iApply dh_seed_elim0.
Qed.

Lemma wp_dh_responder g kB E Ψ :
  ↑N ⊆ E →
  nsl_ctx γ (N.@"nsl") (nsl_dh_inv g) -∗
  sterm g -∗
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
iIntros (?) "#ctx #s_g #p_e_kB Hpost".
rewrite /nsl_dh_resp; wp_pures; wp_bind (mkdh _).
iApply (wp_mkdh (nsl_dh_fail kB)).
iIntros (b) "#s_b #b_pred token".
rewrite (term_meta_token_difference _ (↑N.@"peer")); last solve_ndisj.
iDestruct "token" as "[dh token]".
wp_pures; wp_bind (tgroup _); iApply wp_tgroup.
wp_pures; wp_bind (texp _ _); iApply wp_texp.
rewrite Spec.texpA; wp_pures; wp_bind (nsl_resp _ _ _ _).
iApply (wp_nsl_resp with "ctx p_e_kB [token] [] [dh]") => //.
- solve_ndisj.
- rewrite (term_meta_token_difference _ (↑N.@"nsl")); last solve_ndisj.
  iDestruct "token" as "[token _]".
  by iExists _, _; eauto.
- by rewrite sterm_TExp /=; iSplit; eauto.
- iIntros (kA nA).
  iMod (term_meta_set _ _ _ kA with "dh") as "#meta"; eauto.
  iModIntro; iSplit.
  + iModIntro; rewrite [corruption _ _]comm; by iApply pterm_nsl_dh1.
  + iExists b; iSplit => //.
    iIntros "!> %".
    rewrite -[ [a; b]]/(seq.cat [a] [b]) TExpC /=.
    by iIntros "#?"; iApply pterm_nsl_dh2.
iIntros ([[pkA nA]|]) "resp"; last by protocol_failure.
iDestruct "resp" as (kA) "# (-> & p_e_kA & s_nA & p_nA & inv)".
wp_pures; wp_bind (texp _ _); iApply wp_texp; wp_pures.
iApply ("Hpost" $! (Some (TKey Enc kA, Spec.texp nA b))).
iExists _; do 3!iSplit => //; eauto.
  by iApply sterm_texp.
iDestruct "inv" as "[inv|inv]"; eauto.
iDestruct "inv" as (t) "[-> #inv]".
rewrite Spec.texpA.
rewrite -[ [b; t]]/(seq.cat [b] [t]) TExpC /=.
iRight; iIntros "!> #contra".
iSpecialize ("inv" with "contra").
iDestruct "inv" as ">inv".
by iApply dh_seed_elim0.
Qed.

End NSLDH.
