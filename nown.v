(* A global map from namespaces to ghost names. *)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NOwn.

Context `{!heapGS Σ}.
Notation iProp := (iProp Σ).

Definition nown_token γ E : iProp :=
  own γ (reservation_map_token E).

Definition nown_name γ N (γ' : gname) : iProp :=
  own γ (namespace_map_data N (to_agree γ')).

#[global]
Instance nown_name_timeless γ N γ' : Timeless (nown_name γ N γ').
Proof. apply _. Qed.

#[global]
Instance nown_name_persistent γ N γ' : Persistent (nown_name γ N γ').
Proof. apply _. Qed.

Lemma nown_name_set E γ N γ' :
  ↑N ⊆ E →
  nown_token γ E ==∗ nown_name γ N γ'.
Proof.
iIntros (?) "token".
iMod (own_update with "token") as "data".
  by apply (namespace_map_alloc_update _ N (to_agree γ')).
by eauto.
Qed.

Lemma nown_name_agree γ N γ1 γ2 :
  nown_name γ N γ1 -∗
  nown_name γ N γ2 -∗
  ⌜γ1 = γ2⌝.
Proof.
iIntros "own1 own2".
iPoseProof (own_valid_2 with "own1 own2") as "%valid".
move: valid; rewrite -reservation_map_data_op reservation_map_data_valid.
by move=> /to_agree_op_inv_L ->.
Qed.

Lemma nown_token_difference γ E1 E2 :
  E1 ⊆ E2 →
  nown_token γ E2 ⊣⊢ nown_token γ E1 ∗ nown_token γ (E2 ∖ E1).
Proof.
move=> ?.
by rewrite /nown_token -own_op -reservation_map_token_difference.
Qed.

Definition nown `{!inG Σ A} γ N (a : A) : iProp :=
  ∃ γ', nown_name γ N γ' ∧ own γ' a.

Lemma nown_alloc `{!inG Σ A} γ N E (a : A) :
  ↑N ⊆ E → ✓ a → nown_token γ E ==∗ nown γ N a.
Proof.
intros sub valid_a. iIntros "token".
iMod (own_alloc a) as "(%γ' & own)"; auto.
iMod (nown_name_set _ γ' with "token") as "name"; eauto.
iModIntro. iExists γ'. eauto.
Qed.

Lemma nown_valid `{!inG Σ A} γ N (a : A) : nown γ N a -∗ ✓ a.
Proof.
iIntros "(%γ' & #own_γ' & own)". iApply (own_valid with "own").
Qed.

Lemma nown_valid_2 `{!inG Σ A} γ N (a1 a2 : A) :
  nown γ N a1 -∗ nown γ N a2 -∗ ✓ (a1 ⋅ a2).
Proof.
iIntros "(%γ1 & #own_γ1 & own1) (%γ2 & own_γ2 & own2)".
iPoseProof (nown_name_agree with "own_γ1 own_γ2") as "<-".
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
  iPoseProof (nown_name_agree with "own_γ1 own_γ2") as "<-".
  iExists γ1. iSplit => //. by iSplitL "own1".
Qed.

End NOwn.

Lemma nownGS_alloc `{!heapGS Σ} : ⊢ |==> ∃ γ , nown_token γ ⊤.
Proof.
iApply (own_alloc (reservation_map_token ⊤)).
apply reservation_map_token_valid.
Qed.

Arguments nown_alloc {Σ _ A _} γ N {_} a.
