From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map excl.
From iris.algebra Require Import functions dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib gmeta nown.
From cryptis.core Require Import term comp_map minted.

Definition savedPredR Σ A :=
  dfrac_agreeR (oFunctor_apply (A -d> ▶ ∙) (iPropO Σ)).
Definition savedPropR Σ :=
  dfrac_agreeR (oFunctor_apply (▶ ∙) (iPropO Σ)).

Class savedPredG Σ A := savedPred_inG : inG Σ (savedPredR Σ A).
Class savedPropG Σ := savedProp_inG : inG Σ (savedPropR Σ).

Definition savedPredΣ A :=
  #[GFunctor (dfrac_agreeRF (A -d> ▶ ∙))].
Definition savedPropΣ :=
  #[GFunctor (dfrac_agreeRF (▶ ∙))].

Global Existing Instance savedPred_inG.
Global Existing Instance savedProp_inG.

Global Instance subG_savedPredG Σ A : subG (savedPredΣ A) Σ → savedPredG Σ A.
Proof. solve_inG. Qed.
Global Instance subG_savedPropG Σ : subG savedPropΣ Σ → savedPropG Σ.
Proof. solve_inG. Qed.

Section SavedProp.

Context `{Σ : gFunctors}.

Implicit Types (dq : dfrac) (P Q : iProp Σ).

Definition saved_prop (dq : dfrac) (P : iProp Σ) : savedPropR Σ :=
  to_dfrac_agree dq (Next P).

Lemma saved_prop_valid dq P : ✓ saved_prop dq P ↔ ✓ dq.
Proof.
rewrite /saved_prop /to_dfrac_agree pair_valid.
by split=> [[] //|?]; split.
Qed.

Lemma saved_prop_validI dq P : ✓ saved_prop dq P ⊣⊢ (⌜✓ dq⌝ : iProp Σ).
Proof. by rewrite /saved_prop dfrac_agree_validI. Qed.

Lemma saved_prop_op_validI dq1 dq2 P Q :
  ✓ (saved_prop dq1 P ⋅ saved_prop dq2 Q)
  ⊣⊢ (⌜✓ (dq1 ⋅ dq2)⌝ ∧ ▷ (P ≡ Q) : iProp Σ).
Proof.
by rewrite /saved_prop dfrac_agree_validI_2 later_equivI.
Qed.

Lemma saved_prop_op d1 d2 P :
  saved_prop (d1 ⋅ d2) P ≡ saved_prop d1 P ⋅ saved_prop d2 P.
Proof. exact: dfrac_agree_op. Qed.

Lemma saved_prop_persist d P :
  saved_prop d P ~~> saved_prop DfracDiscarded P.
Proof. exact: dfrac_agree_persist. Qed.

Lemma saved_prop_update_2 d1 d2 P1 P2 P' :
  d1 ⋅ d2 = DfracOwn 1 →
  saved_prop d1 P1 ⋅ saved_prop d2 P2 ~~> saved_prop d1 P' ⋅ saved_prop d2 P'.
Proof. exact: dfrac_agree_update_2. Qed.

Context `{A : Type}.

Implicit Types (φ ψ : A → iProp Σ).

Definition saved_pred dq φ : savedPredR Σ A :=
  to_dfrac_agree dq (Next ∘ φ : A -d> later (iProp Σ)).

Lemma saved_pred_valid dq φ : ✓ saved_pred dq φ ↔ ✓ dq.
Proof.
rewrite /saved_pred /to_dfrac_agree pair_valid.
by split=> [[] //|?]; split.
Qed.

Lemma saved_pred_validI dq φ : ✓ saved_pred dq φ ⊣⊢ (⌜✓ dq⌝ : iProp Σ).
Proof. by rewrite /saved_pred dfrac_agree_validI. Qed.

Lemma saved_pred_op_validI dq1 dq2 φ ψ :
  ✓ (saved_pred dq1 φ ⋅ saved_pred dq2 ψ)
  ⊣⊢ (⌜✓ (dq1 ⋅ dq2)⌝ ∧ □ (∀ x, ▷ (φ x ≡ ψ x)) : iProp Σ).
Proof.
rewrite /saved_pred dfrac_agree_validI_2.
iSplit.
- iIntros "[% #e]". iSplit => //.
  iIntros "!> %x".
  rewrite discrete_fun_equivI.
  iSpecialize ("e" $! x).
  by rewrite /= later_equivI.
- iIntros "[% #e]". iSplit => //.
  rewrite discrete_fun_equivI. iIntros "%x".
  rewrite /= later_equivI. iApply "e".
Qed.

Lemma saved_pred_op d1 d2 φ :
  saved_pred (d1 ⋅ d2) φ ≡ saved_pred d1 φ ⋅ saved_pred d2 φ.
Proof. exact: dfrac_agree_op. Qed.

Lemma saved_pred_persist d φ :
  saved_pred d φ ~~> saved_pred DfracDiscarded φ.
Proof. exact: dfrac_agree_persist. Qed.

Lemma saved_pred_update_2 d1 d2 φ1 φ2 φ' :
  d1 ⋅ d2 = DfracOwn 1 →
  saved_pred d1 φ1 ⋅ saved_pred d2 φ2 ~~> saved_pred d1 φ' ⋅ saved_pred d2 φ'.
Proof. exact: dfrac_agree_update_2. Qed.

End SavedProp.
