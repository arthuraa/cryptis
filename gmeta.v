From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import reservation_map.
From iris.base_logic Require Import proofmode invariants.
From iris.heap_lang Require Import proofmode.
From cryptis Require Import lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class metaGS Σ := {
  metaG_inG : inG Σ (reservation_mapR (agreeR positiveO));
}.

Local Existing Instance metaG_inG.

Definition metaΣ := GFunctor (reservation_mapR (agreeR positiveO)).

Global Instance subG_metaGS Σ : subG metaΣ Σ → metaGS Σ.
Proof. solve_inG. Qed.

Section Laws.

Implicit Types (N : namespace) (γ : gname) (E : coPset).

Context `{!metaGS Σ}.

Definition gmeta `{Countable L} γ N (x : L) :=
  own γ (namespace_map_data N (to_agree (encode x))).

Definition gmeta_token γ E :=
  own γ (reservation_map_token E).

Global Instance gmeta_timeless `{Countable L} γ N (x : L) :
  Timeless (gmeta γ N x).
Proof. apply _. Qed.

Global Instance gmeta_token_timeless γ E :
  Timeless (gmeta_token γ E).
Proof. apply _. Qed.

Global Instance gmeta_persistent `{Countable L} γ N (x : L) :
  Persistent (gmeta γ N x).
Proof. apply _. Qed.

Lemma gmeta_token_alloc : ⊢ |==> ∃ γ, gmeta_token γ ⊤.
Proof. apply: own_alloc. exact: reservation_map_token_valid. Qed.

Lemma gmeta_set `{Countable L} E γ N (x : L) :
  ↑N ⊆ E →
  gmeta_token γ E ==∗ gmeta γ N x.
Proof.
iIntros "%sub H". iApply own_update; eauto.
exact: namespace_map_alloc_update.
Qed.

Lemma gmeta_gmeta_token `{Countable L} γ (x : L) N E :
  ↑N ⊆ E →
  gmeta_token γ E -∗ gmeta γ N x -∗ False.
Proof.
iIntros "%sub token #meta".
iPoseProof (own_valid_2 with "token meta") as "%contra".
iPureIntro.
exact: namespace_map_disj.
Qed.

Lemma gmeta_agree `{Countable L} γ N (x1 x2 : L) :
  gmeta γ N x1 -∗
  gmeta γ N x2 -∗
  ⌜x1 = x2⌝.
Proof.
iIntros "#meta1 #meta2".
iPoseProof (own_valid_2 with "meta1 meta2") as "%valid".
rewrite /namespace_map_data -reservation_map_data_op in valid.
rewrite reservation_map_data_valid in valid.
by move/to_agree_op_inv/leibniz_equiv_iff/(encode_inj _ _): valid.
Qed.

Lemma gmeta_token_difference γ E1 E2 :
  E1 ⊆ E2 →
  gmeta_token γ E2 ⊣⊢
  gmeta_token γ E1 ∗ gmeta_token γ (E2 ∖ E1).
Proof.
rewrite /gmeta_token -own_op => sub.
by rewrite -reservation_map_token_difference.
Qed.

End Laws.

Arguments gmeta_set {Σ _ _ _ _} E γ N x.
