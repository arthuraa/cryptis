(* These proofs take much longer to check than the rest of the
development. Since they don't have many dependencies, they are left in their own
file to avoid slowing down the compilation process. *)

From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis.core Require Import term.
From cryptis.primitives Require Import notations pre_term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!heapGS Σ}.
Notation nonce := loc.

Implicit Types E : coPset.
Implicit Types a : nonce.
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

Import ssrbool seq path ssreflect.eqtype ssreflect.order.

Lemma twp_texp E t1 t2 Ψ :
  Ψ (TExp t1 t2) ⊢
  WP texp t1 t2 @ E [{ Ψ }].
Proof.
iIntros "post"; rewrite /texp /=; wp_pures; wp_bind (Fst _ = _)%E.
iApply (twp_wand _ _ _ (λ v, ⌜v = #(is_exp t1)⌝)%I).
  rewrite -val_of_pre_term_unfold.
  rewrite is_exp_unfold val_of_pre_term_unseal.
  by case: (unfold_term t1) =>> //=; wp_pures.
iIntros "% ->"; case: (boolP (is_exp t1)) => [t1X|t1NX].
- rewrite -!val_of_pre_term_unfold unfold_TExpN /=.
  rewrite /PreTerm.exp /=.
  wp_pures. rewrite is_exp_unfold in t1X.
  rewrite val_of_pre_term_unseal /=.
  case: (unfold_term t1) (wf_unfold_term t1) t1X => //= pt pts.
  case/and5P=> ???? sorted_pts _. wp_pures.
  wp_bind (insert_sorted _ _ _).
  rewrite -val_of_pre_term_unseal -!repr_list_val.
  iApply (@twp_insert_sorted _
            (Order.Total.Pack (Order.Total.on PreTerm.pre_term))) => //.
    move=> * /=; iIntros "_ post".
    by iApply twp_leq_pre_term; iApply "post".
  iIntros "_"; wp_pures.
  have -> : sort Order.le (pts ++ [:: unfold_term t2])
            = sort Order.le (unfold_term t2 :: pts).
    by apply/perm_sort_leP; rewrite perm_catC.
  by [].
- wp_pures.
  rewrite -!val_of_pre_term_unfold unfold_TExpN /PreTerm.exp /=.
  rewrite is_exp_unfold in t1NX.
  rewrite PreTerm.base_expN // PreTerm.exps_expN //= sortE /=.
  rewrite val_of_pre_term_unseal /=.
  rewrite /CONS. wp_pures.
  by rewrite repr_list_unseal /=.
Qed.

Lemma wp_texp E t1 t2 Ψ :
  Ψ (TExp t1 t2) ⊢
  WP texp t1 t2 @ E {{ Ψ }}.
Proof. by iIntros "post"; iApply twp_wp; iApply twp_texp. Qed.

End Proofs.
