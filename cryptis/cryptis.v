From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib gmeta nown.
From cryptis.core Require Export term term_meta minted public phase.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation cryptisN := (nroot.@"cryptis").

Class cryptisGpreS Σ := CryptisGPreS {
  cryptisGpreS_term_meta : term_metaGpreS Σ;
  cryptisGpreS_public : publicGpreS Σ;
  cryptisGpreS_phase : phaseGpreS Σ;
  cryptisGpreS_tlock : tlockG Σ;
}.

Local Existing Instance cryptisGpreS_term_meta.
Local Existing Instance cryptisGpreS_public.
Local Existing Instance cryptisGpreS_phase.
Local Existing Instance cryptisGpreS_tlock.

Class cryptisGS Σ := CryptisGS {
  cryptisGS_term_meta : term_metaGS Σ;
  cryptisGS_public : publicGS Σ;
  cryptisGS_phase : phaseGS Σ;
  cryptisGS_tlock : tlockG Σ;
}.

Global Existing Instance cryptisGS_term_meta.
Global Existing Instance cryptisGS_public.
Global Existing Instance cryptisGS_phase.
Local Existing Instance cryptisGS_tlock.

Definition cryptisΣ : gFunctors :=
  #[term_metaΣ; publicΣ; phaseΣ; tlockΣ].

Global Instance subG_cryptisGpreS Σ : subG cryptisΣ Σ → cryptisGpreS Σ.
Proof. solve_inG. Qed.

Section Cryptis.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Definition cryptis_ctx : iProp :=
  term_meta_ctx ∧ phase_ctx.

#[global]
Instance cryptis_ctx_persistent : Persistent cryptis_ctx.
Proof. apply _. Qed.

#[global]
Instance cryptis_ctx_has_term_meta_ctx : HasTermMetaCtx cryptis_ctx.
Proof.
split; last apply _. by iIntros "(? & ?)".
Qed.

#[global]
Instance cryptis_ctx_has_phase_ctx : HasPhaseCtx cryptis_ctx.
Proof.
split; last apply _. by iIntros "(? & ?)".
Qed.

End Cryptis.

Arguments cryptis_ctx {Σ _ _}.

Lemma cryptisGS_alloc `{!heapGS Σ} E :
  cryptisGpreS Σ →
  ⊢ |={E}=> ∃ (H : cryptisGS Σ),
             cryptis_ctx ∗
             seal_pred_token AENC ⊤ ∗
             seal_pred_token SIGN ⊤ ∗
             seal_pred_token SENC ⊤ ∗
             hash_pred_token ⊤ ∗
             honest 0 ∅ ∗
             ●Ph 0.
Proof.
move=> ?; iStartProof.
iMod term_metaGS_alloc as "[% #?]".
iMod publicGS_alloc as "(% & ? & ? & ? & ?)".
iMod phaseGS_alloc as "(% & #? & ? & ?)".
iExists (CryptisGS _ _ _ _). iFrame. iModIntro.
by do !iSplit => //.
Qed.
