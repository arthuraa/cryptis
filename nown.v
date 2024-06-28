(* A global map from namespaces to ghost names. *)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib gmeta.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NOwn.

Context `{!metaGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types γ : gname.

Definition nown_token γ E : iProp :=
  gmeta_token γ E.

Lemma nown_token_alloc : ⊢ |==> ∃ γ, nown_token γ ⊤.
Proof. exact: gmeta_token_alloc. Qed.

Definition nown_ptr γ N γ' : iProp :=
  gmeta γ N γ'.

#[global]
Instance nown_ptr_timeless γ N γ' : Timeless (nown_ptr γ N γ').
Proof. apply _. Qed.

#[global]
Instance nown_ptr_persistent γ N γ' : Persistent (nown_ptr γ N γ').
Proof. apply _. Qed.

Lemma nown_ptr_set γ E N γ' :
  ↑N ⊆ E →
  nown_token γ E ==∗ nown_ptr γ N γ'.
Proof. exact: gmeta_set. Qed.

Lemma nown_ptr_agree γ N γ1 γ2 :
  nown_ptr γ N γ1 -∗
  nown_ptr γ N γ2 -∗
  ⌜γ1 = γ2⌝.
Proof. exact: gmeta_agree. Qed.

Lemma nown_token_difference E1 E2 γ :
  E1 ⊆ E2 →
  nown_token γ E2 ⊣⊢ nown_token γ E1 ∗ nown_token γ (E2 ∖ E1).
Proof.
move=> ?.
by rewrite /nown_token -own_op -reservation_map_token_difference.
Qed.

Arguments nown_token_difference E1 E2 γ : clear implicits.

Lemma nown_token_drop E1 E2 γ :
  E1 ⊆ E2 →
  nown_token γ E2 -∗
  nown_token γ E1.
Proof.
iIntros (sub) "t".
rewrite nown_token_difference //.
by iDestruct "t" as "[t _]".
Qed.

Definition nown `{!inG Σ A} γ N (a : A) : iProp :=
  ∃ γ', nown_ptr γ N γ' ∧ own γ' a.

Lemma nown_alloc `{!inG Σ A} γ N E (a : A) :
  ↑N ⊆ E → ✓ a → nown_token γ E ==∗ nown γ N a ∗ nown_token γ (E ∖ ↑N).
Proof.
intros sub valid_a. iIntros "token".
iMod (own_alloc a) as "(%γ' & own)"; auto.
rewrite (nown_token_difference (↑N)) //.
iDestruct "token" as "[tok1 tok2]". iFrame. iExists γ'. iFrame.
by iApply (gmeta_set with "tok1").
Qed.

Lemma nown_valid `{!inG Σ A} γ N (a : A) : nown γ N a -∗ ✓ a.
Proof.
iIntros "(%γ' & #own_γ & own)". iApply (own_valid with "own").
Qed.

Lemma nown_valid_2 `{!inG Σ A} γ N (a1 a2 : A) :
  nown γ N a1 -∗ nown γ N a2 -∗ ✓ (a1 ⋅ a2).
Proof.
iIntros "(%γ1 & #own_γ1 & own1) (%γ2 & #own_γ2 & own2)".
iPoseProof (nown_ptr_agree with "own_γ1 own_γ2") as "<-".
by iApply (own_valid_2 with "own1 own2").
Qed.

Lemma nown_update `{!inG Σ A} γ N (a a' : A) :
  a ~~> a' → nown γ N a ==∗ nown γ N a'.
Proof.
iIntros (?) "(%γ' & #? & own)".
iMod (own_update with "own") as "own"; eauto.
iModIntro. iExists γ'. eauto.
Qed.

#[global]
Instance nown_core_persistent `{!inG Σ A} γ N (a : A) :
  CoreId a → Persistent (nown γ N a).
Proof. apply _. Qed.

#[global]
Instance nown_timeless `{!inG Σ A} γ N (a : A) :
  Discrete a → Timeless (nown γ N a).
Proof. apply _. Qed.

Lemma nown_op `{!inG Σ A} γ N (a1 a2 : A) :
  nown γ N (a1 ⋅ a2) ⊣⊢ nown γ N a1 ∗ nown γ N a2.
Proof.
iSplit.
- iIntros "(%γ' & #? & [own1 own2])".
  by iSplitL "own1"; iExists γ'; iSplit.
- iIntros "[(%γ1 & #own_γ1 & own1) (%γ2 & #own_γ2 & own2)]".
  iPoseProof (nown_ptr_agree with "own_γ1 own_γ2") as "<-".
  iExists γ1. iSplit => //. by iSplitL "own1".
Qed.

End NOwn.

Arguments nown_alloc {Σ _ A _ γ} N {_} a.
Arguments nown_token_difference {Σ _} E1 E2 γ.
