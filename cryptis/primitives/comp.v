(* These proofs take much longer to check than the rest of the
development. Since they don't have many dependencies, they are left in their own
file to avoid slowing down the compilation process. *)

From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis.core Require Import term.
From cryptis.primitives Require Import notations pre_term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition tmul : val := λ: "t1" "t2", hl_mul "t1" "t2".

Definition tinv : val := λ: "t", hl_inv "t".

Definition tone : val := λ: <>, hl_mul_aux (NILV, NILV).

(* The Diffie-Hellman group operations. *)
Definition tgmul : val := λ: "t1" "t2", hl_gmul "t1" "t2".

Definition tginv : val := λ: "t", hl_ginv "t".

Definition tgone : val := λ: <>, hl_gmul_aux (NILV, NILV).

Section Proofs.

Context `{!heapGS Σ}.

Implicit Types E : coPset.
Implicit Types a : loc.
Implicit Types t : term.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.
Implicit Types N : namespace.

Lemma twp_eq_term E t1 t2 Ψ :
  Ψ #(bool_decide (t1 = t2)) ⊢
  WP (eq_term t1 t2) @ E [{ Ψ }].
Proof.
iIntros "H".
rewrite -!val_of_pre_term_unfold.
iApply twp_wand; first iApply twp_eq_pre_term_aux.
iIntros (?) "->".
rewrite (_ : bool_decide (t1 = t2) =
             bool_decide (unfold_term t1 = unfold_term t2)) //.
by apply: bool_decide_ext; split => [->|/unfold_term_inj] //.
Qed.

Lemma wp_eq_term E t1 t2 Ψ :
  Ψ #(bool_decide (t1 = t2)) ⊢
  WP (eq_term t1 t2) @ E {{ Ψ }}.
Proof.
by iIntros "H"; iApply twp_wp; iApply twp_eq_term.
Qed.

Lemma twp_texp E t1 t2 Ψ :
  Ψ (TExp t1 t2) ⊢
  WP texp t1 t2 @ E [{ Ψ }].
Proof.
    iIntros "HΨ".
    rewrite /texp; wp_lam; wp_pures.
    rewrite -[val_of_term t1]val_of_pre_term_unfold.
    rewrite -[val_of_term t2]val_of_pre_term_unfold.
    wp_apply (twp_hl_exp _ _ _ _ (wf_unfold_term _) (wf_unfold_term _)).
    rewrite -unfold_TExp; rewrite [repr _]val_of_pre_term_unfold; iApply "HΨ".
Qed.

Lemma wp_texp E t1 t2 Ψ :
  Ψ (TExp t1 t2) ⊢
  WP texp t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_texp. Qed.


Lemma twp_tmul E t1 t2 Ψ :
  Ψ (TMul {[+ t1; t2 +]}) ⊢
  WP tmul t1 t2 @ E [{ Ψ }].
Proof.
iIntros "HΨ". rewrite /tmul; wp_lam; wp_pures.
rewrite -[val_of_term t1]val_of_pre_term_unfold.
rewrite -[val_of_term t2]val_of_pre_term_unfold.
wp_apply (twp_hl_mul _ _ _ _ (wf_unfold_term _) (wf_unfold_term _)).
rewrite (_ : PreTerm.mul _ = unfold_term (TMul {[+ t1; t2 +]})); last first.
  by rewrite !SMS.singleton_make SMS.disj_union_make unfold_TMul_make.
rewrite [repr _]val_of_pre_term_unfold.
by iApply "HΨ".
Qed.

Lemma wp_tmul E t1 t2 Ψ :
  Ψ (TMul {[+ t1; t2 +]}) ⊢
  WP tmul t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_tmul. Qed.

Lemma twp_tinv E t Ψ :
  Ψ (TInv t) ⊢
  WP tinv t @ E [{ Ψ }].
Proof.
iIntros "HΨ". rewrite /tinv; wp_lam; wp_pures.
rewrite -[val_of_term t]val_of_pre_term_unfold.
wp_apply (twp_hl_inv _ _ _ (wf_unfold_term _)).
rewrite (_ : PreTerm.mul _ = unfold_term (TInv t)); last first.
  by rewrite /TInv SMS.singleton_make SMS.inv_make unfold_TMul_make.
rewrite [repr _]val_of_pre_term_unfold.
by iApply "HΨ".
Qed.

Lemma wp_tinv E t Ψ :
  Ψ (TInv t) ⊢
  WP tinv t @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_tinv. Qed.

Lemma twp_tone E Ψ :
  Ψ (TMul ∅) ⊢
  WP tone #() @ E [{ Ψ }].
Proof.
iIntros "HΨ". rewrite /tone; wp_pures.
rewrite (_ : (NILV, NILV)%V =
             repr ([] : list PreTerm.pre_term, [] : list PreTerm.pre_term));
  last by rewrite /= [@repr_list]unlock.
wp_apply (twp_hl_mul_aux E ∅).
rewrite (_ : PreTerm.mul_aux ∅ = unfold_term (TMul ∅));
  last by rewrite unfold_TMul SMS.map_empty /PreTerm.mul SMS.bind_empty.
rewrite [repr _]val_of_pre_term_unfold.
by iApply "HΨ".
Qed.

Lemma wp_tone E Ψ :
  Ψ (TMul ∅) ⊢
  WP tone #() @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_tone. Qed.

Lemma twp_tgmul E t1 t2 Ψ :
  Ψ (TGMul {[+ t1; t2 +]}) ⊢
  WP tgmul t1 t2 @ E [{ Ψ }].
Proof.
iIntros "HΨ". rewrite /tgmul; wp_lam; wp_pures.
rewrite -[val_of_term t1]val_of_pre_term_unfold.
rewrite -[val_of_term t2]val_of_pre_term_unfold.
wp_apply (twp_hl_gmul _ _ _ _ (wf_unfold_term _) (wf_unfold_term _)).
rewrite (_ : PreTerm.gmul _ = unfold_term (TGMul {[+ t1; t2 +]})); last first.
  by rewrite !SMS.singleton_make SMS.disj_union_make unfold_TGMul_make.
rewrite [repr _]val_of_pre_term_unfold.
by iApply "HΨ".
Qed.

Lemma wp_tgmul E t1 t2 Ψ :
  Ψ (TGMul {[+ t1; t2 +]}) ⊢
  WP tgmul t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_tgmul. Qed.

Lemma twp_tginv E t Ψ :
  Ψ (TGInv t) ⊢
  WP tginv t @ E [{ Ψ }].
Proof.
iIntros "HΨ". rewrite /tginv; wp_lam; wp_pures.
rewrite -[val_of_term t]val_of_pre_term_unfold.
wp_apply (twp_hl_ginv _ _ _ (wf_unfold_term _)).
rewrite (_ : PreTerm.gmul _ = unfold_term (TGInv t)); last first.
  by rewrite /TGInv SMS.singleton_make SMS.inv_make unfold_TGMul_make.
rewrite [repr _]val_of_pre_term_unfold.
by iApply "HΨ".
Qed.

Lemma wp_tginv E t Ψ :
  Ψ (TGInv t) ⊢
  WP tginv t @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_tginv. Qed.

Lemma twp_tgone E Ψ :
  Ψ (TGMul ∅) ⊢
  WP tgone #() @ E [{ Ψ }].
Proof.
iIntros "HΨ". rewrite /tgone; wp_pures.
rewrite (_ : (NILV, NILV)%V =
             repr ([] : list PreTerm.pre_term, [] : list PreTerm.pre_term));
  last by rewrite /= [@repr_list]unlock.
wp_apply (twp_hl_gmul_aux E ∅).
rewrite (_ : PreTerm.gmul_aux ∅ = unfold_term (TGMul ∅));
  last by rewrite unfold_TGMul SMS.map_empty /PreTerm.gmul SMS.bind_empty.
rewrite [repr _]val_of_pre_term_unfold.
by iApply "HΨ".
Qed.

Lemma wp_tgone E Ψ :
  Ψ (TGMul ∅) ⊢
  WP tgone #() @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_tgone. Qed.

End Proofs.
