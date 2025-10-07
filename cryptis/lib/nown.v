(* A global map from namespaces to ghost names. *)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NOwn.

Context `{!metaGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types γ : gname.

Section NOwnLaws.

Context `{!inG Σ A}.

Definition nown γ N (a : A) : iProp :=
  ∃ γ', gmeta γ N γ' ∧ own γ' a.

Lemma nown_alloc γ N E (a : A) :
  ↑N ⊆ E → ✓ a → gmeta_token γ E ==∗ nown γ N a ∗ gmeta_token γ (E ∖ ↑N).
Proof.
intros sub valid_a. iIntros "token".
iMod (own_alloc a) as "(%γ' & own)"; auto.
rewrite (gmeta_token_difference _ (↑N)) //.
iDestruct "token" as "[tok1 tok2]". iFrame.
by iApply (gmeta_set with "tok1").
Qed.

Lemma nown_token γ N E (a : A) :
  ↑N ⊆ E → gmeta_token γ E -∗ nown γ N a -∗ False.
Proof.
iIntros "%sub token (%γ' & #meta & _)".
by iApply (gmeta_gmeta_token with "token meta").
Qed.

Lemma nown_valid γ N (a : A) : nown γ N a -∗ ✓ a.
Proof.
iIntros "(%γ' & #own_γ & own)". iApply (own_valid with "own").
Qed.

Lemma nown_valid_2 γ N (a1 a2 : A) :
  nown γ N a1 -∗ nown γ N a2 -∗ ✓ (a1 ⋅ a2).
Proof.
iIntros "(%γ1 & #own_γ1 & own1) (%γ2 & #own_γ2 & own2)".
iPoseProof (gmeta_agree with "own_γ1 own_γ2") as "<-".
by iApply (own_valid_2 with "own1 own2").
Qed.

Lemma nown_update γ N (a a' : A) :
  a ~~> a' → nown γ N a ==∗ nown γ N a'.
Proof.
iIntros (?) "(%γ' & #? & own)".
iMod (own_update with "own") as "own"; eauto.
iModIntro. iExists γ'. eauto.
Qed.

#[global]
Instance nown_core_persistent γ N (a : A) :
  CoreId a → Persistent (nown γ N a).
Proof. apply _. Qed.

#[global]
Instance nown_timeless γ N (a : A) :
  Discrete a → Timeless (nown γ N a).
Proof. apply _. Qed.

#[global]
Instance nown_ne γ N : NonExpansive (nown γ N).
Proof. solve_proper. Qed.

#[global]
Instance nown_proper γ N : Proper ((≡) ==> (≡)) (nown γ N).
Proof. solve_proper. Qed.

Lemma nown_op γ N (a1 a2 : A) :
  nown γ N (a1 ⋅ a2) ⊣⊢ nown γ N a1 ∗ nown γ N a2.
Proof.
iSplit.
- iIntros "(%γ' & #? & [own1 own2])".
  by iSplitL "own1"; iExists γ'; iSplit.
- iIntros "[(%γ1 & #own_γ1 & own1) (%γ2 & #own_γ2 & own2)]".
  iPoseProof (gmeta_agree with "own_γ1 own_γ2") as "<-".
  iExists γ1. iSplit => //. by iSplitL "own1".
Qed.

#[global]
Instance from_sep_nown γ N (a b1 b2 : A) :
  IsOp a b1 b2 → FromSep (nown γ N a) (nown γ N b1) (nown γ N b2).
Proof.
by rewrite /IsOp /FromSep => ->; rewrite nown_op.
Qed.

#[global]
Instance combine_sep_as_nown γ N (a b1 b2 : A) :
  IsOp a b1 b2 → CombineSepAs (nown γ N b1) (nown γ N b2) (nown γ N a).
Proof. exact: from_sep_nown. Qed.

#[global]
Instance into_sep_nown γ N (a b1 b2 : A) :
  IsOp a b1 b2 → IntoSep (nown γ N a) (nown γ N b1) (nown γ N b2).
Proof.
by rewrite /IsOp /IntoSep => ->; rewrite nown_op.
Qed.

Lemma nown_mono γ N (a1 a2 : A) : a1 ≼ a2 → nown γ N a2 -∗ nown γ N a1.
Proof.
case => ? ->.
rewrite nown_op.
by iIntros "[??]".
Qed.

Lemma nown_update_2 γ N (a1 a2 a' : A) :
  a1 ⋅ a2 ~~> a' →
  nown γ N a1 -∗
  nown γ N a2 ==∗
  nown γ N a'.
Proof.
iIntros "% H1 H2".
iMod (nown_update with "[H1 H2]") as "H" => //.
by iSplitL "H1".
Qed.

End NOwnLaws.

End NOwn.

#[global] Typeclasses Opaque nown.
Arguments nown_alloc {Σ _ A _ γ} N {_} a.
