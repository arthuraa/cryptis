(* A global map from namespaces to ghost names. *)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class nownGS Σ := NOwnGS {
  nown_inG  : inG Σ (reservation_mapUR (agreeR positiveO));
  nown_name : gname;
}.

Local Existing Instance nown_inG.

Definition nownΣ : gFunctors :=
  #[GFunctor (reservation_mapUR (agreeR positiveO))].

Class nownGpreS Σ := NOwnPreG {
  nown_preG :> inG Σ (reservation_mapUR (agreeR positiveO));
}.

Global Instance subG_nownGpreS Σ : subG nownΣ Σ → nownGpreS Σ.
Proof. solve_inG. Qed.

Local Existing Instance nown_preG.

Section NOwn.

Context `{!nownGS Σ}.
Notation iProp := (iProp Σ).

Definition nown_token E : iProp :=
  own nown_name (reservation_map_token E).

Definition nown_ptr N (γ : gname) : iProp :=
  own nown_name (namespace_map_data N (to_agree γ)).

#[global]
Instance nown_ptr_timeless N γ : Timeless (nown_ptr N γ).
Proof. apply _. Qed.

#[global]
Instance nown_ptr_persistent N γ : Persistent (nown_ptr N γ).
Proof. apply _. Qed.

Lemma nown_ptr_set E N γ :
  ↑N ⊆ E →
  nown_token E ==∗ nown_ptr N γ.
Proof.
iIntros (?) "token".
iMod (own_update with "token") as "data".
  by apply (namespace_map_alloc_update _ N (to_agree γ)).
by eauto.
Qed.

Lemma nown_ptr_agree N γ1 γ2 :
  nown_ptr N γ1 -∗
  nown_ptr N γ2 -∗
  ⌜γ1 = γ2⌝.
Proof.
iIntros "own1 own2".
iPoseProof (own_valid_2 with "own1 own2") as "%valid".
move: valid; rewrite -reservation_map_data_op reservation_map_data_valid.
by move=> /to_agree_op_inv_L ->.
Qed.

Lemma nown_token_difference E1 E2 :
  E1 ⊆ E2 →
  nown_token E2 ⊣⊢ nown_token E1 ∗ nown_token (E2 ∖ E1).
Proof.
move=> ?.
by rewrite /nown_token -own_op -reservation_map_token_difference.
Qed.

Arguments nown_token_difference E1 E2 : clear implicits.

Lemma nown_token_drop E1 E2 :
  E1 ⊆ E2 →
  nown_token E2 -∗
  nown_token E1.
Proof.
iIntros (sub) "t".
rewrite nown_token_difference //.
by iDestruct "t" as "[t _]".
Qed.

Definition nown `{!inG Σ A} N (a : A) : iProp :=
  ∃ γ, nown_ptr N γ ∧ own γ a.

Lemma nown_alloc `{!inG Σ A} N E (a : A) :
  ↑N ⊆ E → ✓ a → nown_token E ==∗ nown N a ∗ nown_token (E ∖ ↑N).
Proof.
intros sub valid_a. iIntros "token".
iMod (own_alloc a) as "(%γ & own)"; auto.
rewrite (nown_token_difference (↑N)) //.
iDestruct "token" as "[tok1 tok2]". iFrame. iExists γ. iFrame.
iApply (own_update with "tok1").
exact: namespace_map_alloc_update.
Qed.

Lemma nown_valid `{!inG Σ A} N (a : A) : nown N a -∗ ✓ a.
Proof.
iIntros "(%γ & #own_γ & own)". iApply (own_valid with "own").
Qed.

Lemma nown_valid_2 `{!inG Σ A} N (a1 a2 : A) :
  nown N a1 -∗ nown N a2 -∗ ✓ (a1 ⋅ a2).
Proof.
iIntros "(%γ1 & #own_γ1 & own1) (%γ2 & #own_γ2 & own2)".
iPoseProof (nown_ptr_agree with "own_γ1 own_γ2") as "<-".
by iApply (own_valid_2 with "own1 own2").
Qed.

Lemma nown_update `{!inG Σ A} N (a a' : A) : a ~~> a' → nown N a ==∗ nown N a'.
Proof.
iIntros (?) "(%γ & #? & own)".
iMod (own_update with "own") as "own"; eauto.
iModIntro. iExists γ. eauto.
Qed.

#[global]
Instance nown_core_persistent `{!inG Σ A} N (a : A) :
  CoreId a → Persistent (nown N a).
Proof. apply _. Qed.

#[global]
Instance nown_timeless `{!inG Σ A} N (a : A) :
  Discrete a → Timeless (nown N a).
Proof. apply _. Qed.

Lemma nown_op `{!inG Σ A} N (a1 a2 : A) :
  nown N (a1 ⋅ a2) ⊣⊢ nown N a1 ∗ nown N a2.
Proof.
iSplit.
- iIntros "(%γ & #? & [own1 own2])".
  by iSplitL "own1"; iExists γ; iSplit.
- iIntros "[(%γ1 & #own_γ1 & own1) (%γ2 & #own_γ2 & own2)]".
  iPoseProof (nown_ptr_agree with "own_γ1 own_γ2") as "<-".
  iExists γ1. iSplit => //. by iSplitL "own1".
Qed.

End NOwn.

Lemma nown_token_alloc `{!nownGpreS Σ} :
  ⊢ |==> ∃ _ : nownGS Σ, nown_token ⊤.
Proof.
iMod (own_alloc (reservation_map_token ⊤)) as "(%γ & ?)".
  apply reservation_map_token_valid.
iExists (NOwnGS _ γ). by iFrame.
Qed.

Arguments nown_alloc {Σ _ A _} N {_} a.
Arguments nown_token_difference {Σ _} E1 E2.
