From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib guarded term crypto primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DH.

Context `{!cryptoG Σ, !heapG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Variable N : namespace.

Implicit Types Ψ : val → iProp.
Implicit Types kA kB : term.

Variable P : loc → iProp.

Definition dh_pred t : iProp :=
  ∃ g a, ⌜t = TExp g [TNonce a]⌝ ∧ □ P a.

Definition dh_nonce a : iProp := nonce_pred a dh_pred.

Fact dh_gen_key : unit. Proof. exact: tt. Qed.

Definition dh_gen g : iProp :=
  locked_with dh_gen_key (
    ∀ ts, [∗ set] a ∈ nonces_of_term g, published a (TExp g ts))%I.

Canonical dh_gen_unlockable g := [unlockable of dh_gen g].

Global Instance Persistent_dh_gen g : Persistent (dh_gen g).
Proof. rewrite unlock; apply _. Qed.

Lemma dh_gen_sterm g : dh_gen g -∗ sterm g.
Proof.
rewrite unlock; iIntros "H"; iSpecialize ("H" $! []).
rewrite [in sterm _]unlock.
iApply (big_sepS_mono with "H") => ??.
iApply published_declared_nonce.
Qed.

Lemma nonces_of_term_dh_gen g :
  nonces_of_term g = ∅ →
  ⊢ dh_gen g.
Proof.
rewrite unlock => ->.
by iIntros (ts); rewrite big_sepS_empty.
Qed.

Lemma dh_nonce_elim0 a :
  dh_nonce a -∗
  pterm (TNonce a) -∗
  ▷ False.
Proof.
iIntros "#aP #p_t".
rewrite pterm_TNonce.
iPoseProof (publishedE with "aP p_t") as "{p_t} p_t".
iIntros "!>".
iDestruct "p_t" as (g' a') "# [%e p_t]".
by move/(f_equal is_exp): e; rewrite is_exp_TExp.
Qed.

Lemma dh_nonce_elim1 g a :
  dh_nonce a -∗
  pterm (TExp g [TNonce a]) -∗
  ▷ P a.
Proof.
iIntros "#aP #p_t".
rewrite pterm_TExp1 big_sepS_union_pers.
iDestruct "p_t" as "[[? contra]|[_ p_t]]".
  by iPoseProof (dh_nonce_elim0 with "aP contra") as ">[]".
rewrite nonces_of_term_eq /= big_sepS_singleton.
iPoseProof (publishedE with "aP p_t") as "{p_t} p_t".
iIntros "!>".
iDestruct "p_t" as (g' a') "# [%e p_t]".
by case/TExp_inj: e => _ /Permutation_singleton [] ->; eauto.
Qed.

Lemma dh_nonce_elim2 g a t :
  dh_nonce a -∗
  pterm (TExp g [TNonce a; t]) -∗
  ◇ (pterm (TExp g [TNonce a]) ∧ pterm t).
Proof.
iIntros "#aP #p_t".
rewrite pterm_TExp2 !big_sepS_union_pers.
iDestruct "p_t" as "[[??] | [[? contra] | p_t]]"; eauto.
  by iPoseProof (dh_nonce_elim0 with "aP contra") as ">[]".
iDestruct "p_t" as "([_ p_t] & _)".
rewrite nonces_of_term_eq /= big_sepS_singleton.
iPoseProof (publishedE with "aP p_t") as "{p_t} p_t".
iAssert (▷ False)%I as ">[]".
iModIntro.
iDestruct "p_t" as (g' a') "(%e & _)".
by case/TExp_inj: e => _ /Permutation_length.
Qed.

Lemma dh_pterm_TExp g a :
  dh_gen g -∗
  dh_nonce a -∗
  ▷ □ P a -∗
  pterm (TExp g [TNonce a]).
Proof.
rewrite unlock; iIntros "#gP #aP #P_a".
rewrite pterm_TExp1; iRight.
rewrite big_sepS_union_pers; iSplit; first by iApply "gP".
rewrite nonces_of_term_eq /= big_sepS_singleton.
iExists _; iSplit; eauto.
by iExists g, a; eauto.
Qed.

End DH.
