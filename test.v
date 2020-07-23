From mathcomp Require Import ssreflect.
From iris.algebra Require Import gmap auth gset numbers.
From iris.heap_lang Require Import notation proofmode metatheory.
From iris.base_logic.lib Require Import invariants.

Class symbolG Σ := { symbol_inG :> inG Σ (authR max_natUR) }.
Definition symbolΣ : gFunctors := #[GFunctor (authR max_natUR)].

Section Symbol.

Context `{!symbolG Σ, heapG Σ}.

Implicit Types (γ : gname) (l : loc) (n : nat).

Definition counterN := nroot .@ "counter".

Definition symbol γ v :=
  (∃ n : nat, ⌜v = #n⌝ ∗ own γ (◯ (MaxNat (S n))))%I.
Definition counter γ v :=
  (∃ l : loc, ⌜v = #l⌝ ∗
     inv (counterN .@ l)
       (∃ n : nat, (l ↦ #n) ∗ own γ (● (MaxNat n))))%I.

Definition symbol_init : val := λ: <>, ref #0.

Lemma wp_symbol_init :
  ⊢ WP symbol_init #() {{v, ∃ γ, counter γ v}}.
Proof.
iIntros; iApply wp_fupd.
rewrite /symbol_init; wp_alloc l as "Hl".
iPoseProof (own_alloc (● (MaxNat 0))) as "H".
  by apply/auth_auth_valid.
iMod "H"; iDestruct "H" as (γ) "Hγ".
pose (has n := own γ (● (MaxNat n))).
iMod (inv_alloc (counterN.@l) _ (∃ n : nat, (l ↦ #n) ∗ has n) with "[Hl Hγ]").
  iNext; iExists 0; iFrame.
iModIntro; iExists γ. iExists l. iFrame. eauto.
Qed.

Definition symbol_new : val := λ: "l", FAA "l" #1.

Lemma wp_symbol_new γ v :
  counter γ v -∗
  WP symbol_new v {{w, symbol γ w}}.
Proof.
iDestruct 1 as (l) "[-> #?]".
rewrite /symbol_new; wp_pures.
iInv (counterN.@l) as (n) "[> Hl > Hn]"; wp_faa.
pose m := MaxNat (S n).
iPoseProof (own_update _ _ (● m ⋅ ◯ m) with "Hn") as "> Hn".
  apply auth_update_alloc.
  apply max_nat_local_update.
  rewrite /=; lia.
rewrite own_op; iDestruct "Hn" as "[Hn1 Hn2]"; iModIntro.
iSplit.
- iNext. iExists (S n).
  rewrite Nat2Z.inj_succ -Z.add_1_r; by iFrame.
- by iExists n; iSplit.
Qed.

End Symbol.
