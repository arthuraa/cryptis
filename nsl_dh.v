From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib guarded term crypto primitives tactics session nsl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSLDH.

Context `{!cryptoG Σ, !heapG Σ, !nslG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types rl : role.

Variable send recv : val.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition dh_initiator : val := λ: "skA" "pkA" "pkB",
  let: "a" := mknonce #() in
  let: "ga" := texp (tgroup (tint #0)) "a" in
  bind: "gb" := initiator send recv "skA" "pkA" "pkB" "ga" in
  SOME (texp "gb" "a").

Definition dh_responder : val := λ: "skB" "pkB",
  let: "b" := mknonce #() in
  let: "gb" := texp (tgroup (tint #0)) "b" in
  bind: "res" := responder send recv "skB" "pkB" "gb" in
  let: "pkA" := Fst "res" in
  let: "ga" := Snd "res" in
  SOME ("pkA", texp "ga" "b").

Implicit Types Ψ : val → iProp.

Hypothesis wp_send : forall E t Ψ,
  ▷ pterm t -∗
  Ψ #() -∗
  WP send t @ E {{ Ψ }}.

Hypothesis wp_recv : forall E Ψ,
  (∀ t, pterm t -∗ Ψ t) -∗
  WP recv #() @ E {{ Ψ }}.

Implicit Types kA kB : term.

Definition nsl_dh_inv rl kA kB ga gb : iProp :=
  match rl with
  | Init =>
    ∃ a, ⌜ga = TExp (TInt 0) [a]⌝ ∧
    □ ∀ b, (pterm (TExp (TInt 0) [a; b]) → ▷ pterm b)
  | Resp =>
    ∃ b, ⌜gb = TExp (TInt 0) [b]⌝ ∧
    □ ∀ a, (pterm (TExp (TInt 0) [a; b]) → ▷ pterm a)
  end%I.

Definition nsl_dh_pred k t : iProp :=
  ∃ a k',
    meta a (cryptoN.@"dh") k' ∧
    (pterm (TKey Dec k) ∨ pterm (TKey Dec k')) ∧
    ⌜t = TExp (TInt 0) [TNonce a]⌝.

Lemma nsl_dh_predN k t : negb (is_exp t) → nsl_dh_pred k t -∗ False.
Proof.
iIntros (nexp); iDestruct 1 as (a k') "# (_ & _ & %contra)".
by move: nexp contra; rewrite unlock; case: t.
Qed.

Lemma nsl_dh_predX1 a k k' :
  meta a (cryptoN.@"dh") k' -∗
  nsl_dh_pred k (TExp (TInt 0) [TNonce a]) -∗
  pterm (TKey Dec k) ∨ pterm (TKey Dec k').
Proof.
iIntros "#meta"; iDestruct 1 as (a' k'') "# (meta' & pub & %e)".
case/TExp_inj: e => _ /Permutation_singleton [] <-.
by iPoseProof (meta_agree with "meta meta'") as "<-".
Qed.

Lemma nsl_dh_predX2 a k t :
  nsl_dh_pred k (TExp (TInt 0) [TNonce a; t]) -∗
  False.
Proof.
iDestruct 1 as (??) "# (_ & _ & %contra)".
by case/TExp_inj: contra => _ /Permutation_length.
Qed.

Lemma pterm_dh1 a k k' :
  nonce_pred a (nsl_dh_pred k) -∗
  meta a (cryptoN.@"dh") k' -∗
  pterm (TExp (TInt 0) [TNonce a])  ↔
  ▷ (pterm (TKey Dec k) ∨ pterm (TKey Dec k')).
Proof.
iIntros "#a_pred #meta"; iSplit.
- rewrite pterm_TExp1.
  iDestruct 1 as "[[_ #contra] | #pub]".
    rewrite pterm_TNonce.
    iPoseProof (publishedE with "a_pred contra") as "{contra} contra".
    iModIntro.
    by iDestruct (nsl_dh_predN with "contra") as "[]".
  rewrite nonces_of_term_eq /= left_id_L big_sepS_singleton.
  iPoseProof (publishedE with "a_pred pub") as "{pub} pub".
  by iModIntro; iApply nsl_dh_predX1; eauto.
- iIntros "#pub".
  rewrite pterm_TExp1 nonces_of_term_eq /= left_id_L; iRight.
  rewrite big_sepS_singleton.
  iApply (publishedE with "a_pred").
  do 2!iModIntro.
  by iExists a, k'; do 2!iSplit => //.
Qed.

Lemma pterm_dh2 a k t :
  nonce_pred a (nsl_dh_pred k) -∗
  pterm (TExp (TInt 0) [TNonce a; t]) -∗
  ▷ pterm t.
Proof.
iIntros "#a_pred"; rewrite pterm_TExp2.
iDestruct 1 as "# [[_ ?] | [ [_ contra] | pub]]"; eauto.
- rewrite pterm_TNonce.
  iPoseProof (publishedE with "a_pred contra") as "{contra} contra".
  iModIntro.
  by iDestruct (nsl_dh_predN with "contra") as "[]".
- rewrite nonces_of_term_eq /= left_id_L big_sepS_union_pers.
  rewrite big_sepS_singleton; iDestruct "pub" as "[pub _]".
  iPoseProof (publishedE with "a_pred pub") as "{pub} pub".
  iModIntro.
  iDestruct (nsl_dh_predX2 with "pub") as "[]".
Qed.

Lemma wp_dh_initiator kA kB E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx nsl_dh_inv -∗
  crypto_enc (nroot.@"m1") msg1_pred -∗
  crypto_enc (nroot.@"m2") msg2_pred -∗
  crypto_enc (nroot.@"m3") msg3_pred -∗
  pterm (TKey Enc kA) -∗
  pterm (TKey Enc kB) -∗
  (∀ ogab : option term,
      (if ogab is Some gab then
         sterm gab ∧
         ((pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) ∨
           □ (pterm gab → ▷ ▷ False))
       else True) -∗
      Ψ (repr ogab)) -∗
  WP dh_initiator (TKey Dec kA) (TKey Enc kA) (TKey Enc kB) @ E {{ Ψ }}.
Proof.
iIntros (?) "#ctx #? #? #? #p_e_kA #p_e_kB Hpost".
rewrite /dh_initiator; wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (nsl_dh_pred kA)).
iIntros (a) "#s_a #a_pred token".
rewrite (meta_token_difference _ (↑cryptoN.@"dh")); last solve_ndisj.
iDestruct "token" as "[dh token]".
iMod (meta_set _ _ kB with "dh") as "#dh"; eauto.
wp_pures; wp_bind (tint _); iApply wp_tint.
wp_pures; wp_bind (tgroup _); iApply wp_tgroup.
wp_pures; wp_bind (texp _ _); iApply wp_texp.
rewrite Spec.texpA; wp_pures; wp_bind (initiator _ _ _ _ _ _).
iApply (wp_initiator with "ctx [] [] [] p_e_kA p_e_kB [] [] [] [token]") => //.
- rewrite sterm_TExp sterm_TInt /=; eauto.
- by iModIntro; iApply pterm_dh1; eauto.
- iIntros (nB); iRight; rewrite /=.
  iExists (TNonce a); iSplit => //.
  iModIntro; iIntros (b) "p_b".
  by iApply pterm_dh2.
- rewrite /crypto_meta_token nonces_of_term_TExp /=.
  rewrite nonces_of_term_eq right_id_L left_id_L /=.
  iSplit; first by iPureIntro; set_solver.
  rewrite big_sepS_singleton.
  rewrite (meta_token_difference _ (↑cryptoN.@"nsl".@TExp (TInt 0) [TNonce a])).
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
iApply ("Hpost" $! (Some (Spec.texp (TExp (TInt 0) [b]) (TNonce a)))).
iSplit; first by iApply sterm_texp => //.
iRight; iModIntro.
rewrite Spec.texpA.
iIntros "#contra".
iSpecialize ("succ" with "contra").
iModIntro.
rewrite pterm_TNonce.
iPoseProof (publishedE with "a_pred succ") as "{contra} contra".
iModIntro.
by iPoseProof (nsl_dh_predN with "contra") as "[]".
Qed.

Lemma wp_dh_responder kB E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx nsl_dh_inv -∗
  crypto_enc (nroot.@"m1") msg1_pred -∗
  crypto_enc (nroot.@"m2") msg2_pred -∗
  crypto_enc (nroot.@"m3") msg3_pred -∗
  pterm (TKey Enc kB) -∗
  (∀ oresp : option (term * term),
      (if oresp is Some (pkA, gab) then
         ∃ kA,
           ⌜pkA = TKey Enc kA⌝ ∧
           pterm pkA ∧
           sterm gab ∧
           ((pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) ∨
             □ (pterm gab → ▷ ▷ False))
       else True) -∗
      Ψ (repr oresp)) -∗
  WP dh_responder (TKey Dec kB) (TKey Enc kB) @ E {{ Ψ }}.
Proof.
iIntros (?) "#ctx #? #? #? #p_e_kB Hpost".
rewrite /dh_responder; wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (nsl_dh_pred kB)).
iIntros (b) "#s_b #b_pred token".
rewrite (meta_token_difference _ (↑cryptoN.@"dh")); last solve_ndisj.
iDestruct "token" as "[dh token]".
wp_pures; wp_bind (tint _); iApply wp_tint.
wp_pures; wp_bind (tgroup _); iApply wp_tgroup.
wp_pures; wp_bind (texp _ _); iApply wp_texp.
rewrite Spec.texpA; wp_pures; wp_bind (responder _ _ _ _ _).
iApply (wp_responder with "ctx [] [] [] p_e_kB [token] [] [dh]") => //.
- rewrite /crypto_meta_token nonces_of_term_TExp /=.
  rewrite nonces_of_term_eq right_id_L left_id_L /=.
  iSplit; first by iPureIntro; set_solver.
  rewrite big_sepS_singleton.
  rewrite (meta_token_difference _ (↑cryptoN.@"nsl".@TExp (TInt 0) [TNonce b])).
    by iDestruct "token" as "[??]".
  by solve_ndisj.
- rewrite sterm_TExp sterm_TInt /=; eauto.
- iIntros (kA nA).
  iMod (meta_set _ b kA with "dh") as "#meta"; eauto.
  iModIntro; iSplit.
  + by iModIntro; rewrite [(_ ∨ _)%I]comm; by iApply pterm_dh1.
  + iExists (TNonce b); iSplit => //.
    iIntros "!> %".
    rewrite -[ [a; TNonce b]]/(seq.cat [a] [TNonce b]) TExpC /=.
    by iIntros "#?"; iApply pterm_dh2.
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
iModIntro.
rewrite pterm_TNonce.
iPoseProof (publishedE with "b_pred inv") as "{inv} inv".
iModIntro.
by iDestruct (nsl_dh_predN with "inv") as "[]".
Qed.

End NSLDH.