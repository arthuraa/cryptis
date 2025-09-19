From iris.algebra Require Import gmap auth agree gset coPset list.
From iris.bi Require Import big_op fixpoint.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import total_weakestpre adequacy.
From iris.prelude Require Import options.
Import uPred.

Section adequacy.
Context `{!irisGS_gen HasNoLc Λ Σ}.
Implicit Types (e : expr Λ) (v : val Λ) (es : list (expr Λ)).
Implicit Types (Φ : val Λ → iProp Σ).

Definition runs_until e Φ : iProp Σ :=
  ∀ es1 es2 σ ns ks nt, state_interp σ ns ks nt ={⊤}=∗ ∃ v es' σ' ns' ks' nt',
    ⌜rtc erased_step
      (es1 ++ e :: es2, σ)
      (es1 ++ (of_val v) :: es2 ++ es', σ')⌝ ∗
    state_interp σ' ns' ks' nt' ∗
    Φ v.

Local Instance runs_until_proper n e :
  Proper (pointwise_relation (val Λ) (dist n) ==> dist n) (runs_until e).
Proof. solve_proper. Qed.

Lemma twp_runs_until Φ e : WP e [{ Φ }] -∗ runs_until e Φ.
Proof.
  iIntros "He". remember (⊤ : coPset) as E eqn:HE.
  iRevert (HE). iRevert (e E Φ) "He". iApply twp_ind.
  { solve_proper. }
  iIntros "!>" (e E Φ); iIntros "IH" (->).
  rewrite /twp_pre. iIntros (es1 es2 σ ns ks nt) "state".
  case val_e: (to_val e) => [v|].
  { iExists v, [], σ, ns, ks, nt. iMod "IH". iFrame.
    rewrite app_nil_r -(of_to_val _ _ val_e). eauto. }
  iMod ("IH" with "state") as (red_e) "IH".
  case: red_e => e' [] σ' [] es' Hstep.
  iMod ("IH" with "[//]") as "(_ & state & [IH _] & _)".
  iSpecialize ("IH" with "[//]").
  iMod ("IH" $! es1 (es2 ++ es') with "state")
    as (v es'' σ'' ns' ks' nt' Hexec) "state".
  have {}Hstep : erased_step (es1 ++ e :: es2, σ) (es1 ++ e' :: es2 ++ es', σ').
  { exists []. econstructor; eauto. }
  iModIntro. iExists v, (es' ++ es''), σ'', ns', ks', nt'. iFrame.
  iPureIntro. rewrite -app_assoc in Hexec. by eapply rtc_l; eauto.
Qed.
End adequacy.

Theorem twp_rtc Σ Λ `{!invGpreS Σ} e es1 es2 σ P n :
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → nat → list (observation Λ) → nat → iProp Σ)
         (** We abstract over any instance of [irisG], and thus any value of
             the field [num_laters_per_step]. This is needed because instances
             of [irisG] (e.g., the one of HeapLang) are shared between WP and
             TWP, where TWP simply ignores [num_laters_per_step]. *)
         (num_laters_per_step : nat → nat)
         (fork_post : val Λ → iProp Σ)
         state_interp_mono,
       let _ : irisGS_gen HasNoLc Λ Σ :=
           IrisG Hinv stateI fork_post num_laters_per_step state_interp_mono
       in
       stateI σ n [] 0 ∗ WP e [{ v, ⌜ P v ⌝ }]) →
  ∃ v es' σ',
  rtc erased_step (es1 ++ e :: es2, σ) (es1 ++ of_val v :: es2 ++ es', σ') ∧
  P v.
Proof.
  intros Hwp. eapply pure_soundness.
  apply (fupd_soundness_no_lc ⊤ ⊤ _ 0)=> Hinv. iIntros "_".
  iMod (Hwp) as (stateI num_laters_per_step fork_post stateI_mono) "[Hσ H]".
  set (iG := IrisG Hinv stateI fork_post num_laters_per_step stateI_mono).
  iPoseProof (twp_runs_until with "H") as "H".
  iMod ("H" $! es1 es2 with "Hσ") as (v es' σ' ns' ks' nt' Hexec) "[_ %post]".
  iModIntro. iPureIntro. by eauto.
Qed.
