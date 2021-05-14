From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
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
  let: "gb" := texp (tgroup (tint #0)) in
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
  WP dh_initiator (TKey Dec kA) (TKey Enc kA) (TKey Enc kB) @ E
     {{ Ψ }}.
Proof.
iIntros (?) "#ctx #? #? #? #p_e_kA #p_e_kB Hpost".
rewrite /dh_initiator; wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (λ t, (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) ∧
                           ∃ t', ⌜t = TExp (TInt 0) [t']⌝)%I).
iIntros (a) "#s_a #a_pred token".
wp_pures; wp_bind (tint _); iApply wp_tint.
wp_pures; wp_bind (tgroup _); iApply wp_tgroup.
wp_pures; wp_bind (texp _ _); iApply wp_texp.
rewrite Spec.texpA; wp_pures; wp_bind (initiator _ _ _ _ _ _).
iApply (wp_initiator with "ctx [] [] [] p_e_kA p_e_kB [] [] [] [token]") => //.
- rewrite sterm_TExp sterm_TInt /=; eauto.
- rewrite pterm_TExp1 pterm_TNonce; iModIntro; iSplit; last first.
    iIntros "#pub"; iRight.
    rewrite /= nonces_of_term_eq /= left_id_L.
    by rewrite big_sepS_singleton; iApply publishedE; eauto.
  iDestruct 1 as "[[_ pub] | pub]" => //.
    by iPoseProof (publishedE with "a_pred pub") as "[??]"; eauto.
  rewrite nonces_of_term_eq /= left_id_L big_sepS_singleton.
  by iPoseProof (publishedE with "a_pred pub") as "{pub} #[pub ?]"; eauto.
- iIntros (nB); iRight; rewrite /=.
  iExists (TNonce a); iSplit => //.
  iModIntro; iIntros (b).
  rewrite pterm_TExp2.
  iDestruct 1 as "# [[_ ?] | [[_ pub] | pub]]" => //.
    rewrite pterm_TNonce.
    iPoseProof (publishedE with "a_pred pub") as "{pub} pub"; iModIntro.
    iDestruct "pub" as "[_ #pub]".
    iDestruct "pub" as (t') "%e".
    by rewrite unlock in e.
  rewrite nonces_of_term_eq /= left_id_L big_sepS_union_pers.
  iDestruct "pub" as "[pub _]".
  rewrite big_sepS_singleton.
  iPoseProof (publishedE with "a_pred pub") as "{pub} [? pub]"; iModIntro.
  iDestruct "pub" as (t') "%e".
  by case/TExp_inj: e => ? /Permutation_length.
- rewrite /crypto_meta_token nonces_of_term_TExp /=.
  rewrite nonces_of_term_eq right_id_L left_id_L /=.
  iSplit; first by iPureIntro; set_solver.
  rewrite big_sepS_singleton.
  rewrite (meta_token_difference _ (↑cryptoN.@"nsl".@TExp (TInt 0) [TNonce a])).
    by iDestruct "token" as "[??]".
  admit. (* TODO: Reason about namespace disjointness *)
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
iDestruct "contra" as "#[_ contra]".
iDestruct "contra" as (?) "%e".
by rewrite unlock in e.
Admitted.

End NSL.
