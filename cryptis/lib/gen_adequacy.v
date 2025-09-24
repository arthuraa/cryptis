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

Definition thread_step (p1 p2 : expr Λ * state Λ) : Prop :=
  ∃ efs, prim_step p1.1 p1.2 [] p2.1 p2.2 efs.

Definition runs_until e Φ : iProp Σ :=
  ∀ σ ns ks nt, state_interp σ ns ks nt ={⊤}=∗ ∃ v σ' ns' ks' nt',
    ⌜rtc thread_step (e, σ) (of_val v, σ')⌝ ∗
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
  rewrite /twp_pre. iIntros (σ ns ks nt) "state".
  case val_e: (to_val e) => [v|].
  { iExists v, σ, ns, ks, nt. iMod "IH". iFrame.
    rewrite -(of_to_val _ _ val_e). by eauto. }
  iMod ("IH" with "state") as (red_e) "IH".
  case: red_e => e' [] σ' [] es' Hstep.
  iMod ("IH" with "[//]") as "(_ & state & [IH _] & _)".
  iSpecialize ("IH" with "[//]").
  iMod ("IH" with "state") as (v σ'' ns' ks' nt' Hexec) "state".
  have {}Hstep : thread_step (e, σ) (e', σ').
  { by exists es' => /=. }
  iModIntro. iExists v, σ'', ns', ks', nt'. iFrame.
  iPureIntro. by eapply rtc_l; eauto.
Qed.
End adequacy.

Theorem twp_rtc Σ Λ `{!invGpreS Σ} e σ P n :
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
  ∃ v σ', rtc thread_step (e, σ) (of_val v, σ') ∧ P v.
Proof.
  intros Hwp. eapply pure_soundness.
  apply (fupd_soundness_no_lc ⊤ ⊤ _ 0)=> Hinv. iIntros "_".
  iMod (Hwp) as (stateI num_laters_per_step fork_post stateI_mono) "[Hσ H]".
  set (iG := IrisG Hinv stateI fork_post num_laters_per_step stateI_mono).
  iPoseProof (twp_runs_until with "H") as "H".
  iMod ("H" with "Hσ") as (v σ' ns' ks' nt' Hexec) "[_ %post]".
  iModIntro. iPureIntro. by eauto.
Qed.
