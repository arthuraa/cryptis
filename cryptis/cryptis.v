From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib.
From cryptis.core Require Export term term_meta minted public.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation cryptisN := (nroot.@"cryptis").

Class cryptisGpreS Σ := CryptisGPreS {
  #[local] cryptisGpreS_term_meta :: term_metaGpreS Σ;
  #[local] cryptisGpreS_public :: publicGpreS Σ;
  #[local] cryptisGpreS_tlock :: tlockG Σ;
}.

Class cryptisGS Σ := CryptisGS {
  #[global] cryptisGS_term_meta :: term_metaGS Σ;
  #[global] cryptisGS_public :: publicGS Σ;
  #[local] cryptisGS_tlock :: tlockG Σ;
}.

Definition cryptisΣ : gFunctors :=
  #[term_metaΣ; publicΣ; tlockΣ].

#[global] Instance subG_cryptisGpreS Σ : subG cryptisΣ Σ → cryptisGpreS Σ.
Proof. solve_inG. Qed.

Section Cryptis.

Context `{!heapGS Σ, !cryptisGS Σ}.
Abbreviation iProp := (iProp Σ).
Abbreviation iPropO := (iPropO Σ).
Abbreviation iPropI := (iPropI Σ).

Definition cryptis_ctx : iProp :=
  term_meta_ctx.

#[global]
Instance cryptis_ctx_persistent : Persistent cryptis_ctx.
Proof. apply _. Qed.

#[global]
Instance cryptis_ctx_has_term_meta_ctx : HasTermMetaCtx cryptis_ctx.
Proof. split; last apply _. by []. Qed.

End Cryptis.

Arguments cryptis_ctx {Σ _ _}.

Lemma cryptisGS_alloc `{!heapGS Σ} E :
  cryptisGpreS Σ →
  ⊢ |={E}=> ∃ (H : cryptisGS Σ),
             cryptis_ctx ∗
             seal_pred_token AENC ⊤ ∗
             seal_pred_token SIGN ⊤ ∗
             seal_pred_token SENC ⊤ ∗
             hash_pred_token ⊤.
Proof.
move=> ?; iStartProof.
iMod term_metaGS_alloc as "[% #?]".
iMod publicGS_alloc as "(% & ? & ? & ? & ?)".
iExists (CryptisGS _ _ _). iFrame. by iModIntro.
Qed.
