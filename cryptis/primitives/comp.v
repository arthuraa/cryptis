(* These proofs take much longer to check than the rest of the
development. Since they don't have many dependencies, they are left in their own
file to avoid slowing down the compilation process. *)

From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From mathcomp Require all_order ssrbool seq path eqtype.
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

Definition tinv : val := λ: "t", hl_inv_distr "t".

Definition tone : val := λ: <>, hl_mk_mul NILV.

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

#[warnings="-ambiguous-paths"]
Import all_order ssrbool seq path boot.eqtype.

Lemma twp_texp E t1 t2 Ψ :
  Ψ (TExp t1 t2) ⊢
  WP texp t1 t2 @ E [{ Ψ }].
Proof.
    iIntros "HΨ".
    rewrite /texp; wp_lam; wp_pures.
    rewrite -[val_of_term t1]val_of_pre_term_unfold.
    rewrite -[val_of_term t2]val_of_pre_term_unfold.
    wp_apply twp_hl_exp.
    rewrite -unfold_TExp; rewrite [repr _]val_of_pre_term_unfold; iApply "HΨ".
Qed.

Lemma wp_texp E t1 t2 Ψ :
  Ψ (TExp t1 t2) ⊢
  WP texp t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_texp. Qed.


Lemma wp_hl_inv_term E (t : term) Ψ :
    is_true (~~ is_mul t) ->
    Ψ (TInv t) ⊢
    WP hl_inv t @ E {{ Ψ }}.
Proof.
    move=> Nm; iIntros "post".
    rewrite -!val_of_pre_term_unfold (unfold_TInv_Nmul Nm).
    by iApply wp_hl_inv.
Qed.

Lemma twp_tmul E t1 t2 Ψ :
  Ψ (TMulN [:: t1; t2]) ⊢
  WP tmul t1 t2 @ E [{ Ψ }].
Proof.
iIntros "HΨ". rewrite /tmul; wp_lam; wp_pures.
rewrite -[val_of_term t1]val_of_pre_term_unfold.
rewrite -[val_of_term t2]val_of_pre_term_unfold.
wp_apply twp_hl_mul.
rewrite -(unfold_TMulN [:: t1; t2]) [repr _]val_of_pre_term_unfold.
by iApply "HΨ".
Qed.

Lemma wp_tmul E t1 t2 Ψ :
  Ψ (TMulN [:: t1; t2]) ⊢
  WP tmul t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_tmul. Qed.

Lemma twp_tinv E t Ψ :
  Ψ (TInv t) ⊢
  WP tinv t @ E [{ Ψ }].
Proof.
iIntros "HΨ". rewrite /tinv; wp_lam; wp_pures.
rewrite -[val_of_term t]val_of_pre_term_unfold.
wp_apply (twp_hl_inv_distr _ _ (wf_unfold_term t)).
rewrite -unfold_TInv [repr _]val_of_pre_term_unfold.
by iApply "HΨ".
Qed.

Lemma wp_tinv E t Ψ :
  Ψ (TInv t) ⊢
  WP tinv t @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_tinv. Qed.

Lemma twp_tone E Ψ :
  Ψ (TMulN [::]) ⊢
  WP tone #() @ E [{ Ψ }].
Proof.
iIntros "HΨ". rewrite /tone; wp_pures.
rewrite (_ : NILV = repr ([::] : seq PreTerm.pre_term));
  last by rewrite repr_list_unseal.
wp_apply (twp_hl_mk_mul E [::]).
rewrite (_ : PreTerm.PTMul [::] = unfold_term (TMulN [::]));
  last by rewrite (unfold_TMulN [::]).
rewrite [repr _]val_of_pre_term_unfold.
by iApply "HΨ".
Qed.

Lemma wp_tone E Ψ :
  Ψ (TMulN [::]) ⊢
  WP tone #() @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_tone. Qed.

End Proofs.
