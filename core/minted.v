From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib gmeta nown.
From cryptis.core Require Import term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Minted.

Context `{heapGS Σ}.

Notation iProp := (iProp Σ).

Fact minted_key : unit. Proof. exact: tt. Qed.

Definition minted : term → iProp :=
  locked_with minted_key (
    λ t, [∗ set] a ∈ nonces_of_term t,
      meta a (nroot.@"minted") ()
  )%I.

Canonical minted_unlock := [unlockable of minted].

Global Instance Persistent_minted t : Persistent (minted t).
Proof. rewrite unlock; apply _. Qed.

Global Instance Timeless_minted t : Timeless (minted t).
Proof. rewrite unlock; apply _. Qed.

Lemma subterm_minted t1 t2 :
  subterm t1 t2 → minted t2 -∗ minted t1.
Proof.
rewrite unlock !big_sepS_forall; iIntros "%sub m_t2 %t %t_t1".
move/subterm_nonces_of_term in sub.
iApply "m_t2". iPureIntro. set_solver.
Qed.

Lemma minted_TInt n : minted (TInt n) ⊣⊢ True.
Proof. by rewrite unlock nonces_of_term_unseal /= big_sepS_empty. Qed.

Lemma minted_TPair t1 t2 : minted (TPair t1 t2) ⊣⊢ minted t1 ∧ minted t2.
Proof.
by rewrite unlock nonces_of_term_unseal /= !big_sepS_union_pers.
Qed.

Lemma minted_TNonce a : minted (TNonce a) ⊣⊢ meta a (nroot.@"minted") ().
Proof.
by rewrite unlock nonces_of_term_unseal /= big_sepS_singleton.
Qed.

Lemma minted_TKey kt t : minted (TKey kt t) ⊣⊢ minted t.
Proof. by rewrite unlock nonces_of_term_unseal /=. Qed.

Lemma minted_TSeal k t : minted (TSeal k t) ⊣⊢ minted k ∧ minted t.
Proof.
by rewrite unlock nonces_of_term_unseal /= !big_sepS_union_pers.
Qed.

Lemma minted_THash t : minted (THash t) ⊣⊢ minted t.
Proof. by rewrite unlock nonces_of_term_unseal /=. Qed.

Lemma minted_TExpN t ts :
  minted (TExpN t ts) ⊣⊢ minted t ∧ [∗ list] t' ∈ ts, minted t'.
Proof.
rewrite unlock nonces_of_term_TExpN big_sepS_union_pers.
by rewrite big_sepS_union_list_pers big_sepL_fmap.
Qed.

Lemma minted_TExp t1 t2 :
  minted (TExp t1 t2) ⊣⊢ minted t1 ∧ minted t2.
Proof.
rewrite unlock nonces_of_term_TExpN big_sepS_union_pers.
by rewrite /= union_empty_r_L.
Qed.

Lemma minted_nonces_of_term t :
  minted t ⊣⊢ [∗ set] a ∈ nonces_of_term t, minted (TNonce a).
Proof.
rewrite {1}unlock !big_sepS_forall; iSplit; iIntros "#H %a %a_t".
- by rewrite minted_TNonce; iApply "H".
- by rewrite -minted_TNonce; iApply "H".
Qed.

Lemma minted_to_list t ts :
  Spec.to_list t = Some ts →
  minted t -∗ [∗ list] t' ∈ ts, minted t'.
Proof.
elim/term_ind': t ts => //=.
  by case=> // ts [<-] /=; iIntros "?".
move=> t _ tl IH ts.
case e: (Spec.to_list tl) => [ts'|] // [<-] /=.
rewrite minted_TPair /=; iIntros "[??]"; iFrame.
by iApply IH.
Qed.

Lemma minted_of_list ts :
  minted (Spec.of_list ts) ⊣⊢
  [∗ list] t ∈ ts, minted t.
Proof.
rewrite Spec.of_list_unseal.
elim: ts => [|t ts IH]; first by rewrite minted_TInt.
by rewrite minted_TPair /= IH bi.persistent_and_sep.
Qed.

Lemma minted_tag N t : minted (Spec.tag N t) ⊣⊢ minted t.
Proof.
by rewrite Spec.tag_unseal minted_TPair minted_TInt bi.emp_and.
Qed.

Lemma minted_derive_key t : minted (Spec.derive_key t) ⊣⊢ minted t.
Proof. exact: minted_tag. Qed.

End Minted.
