From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import term crypto1.

Definition mknonce : val := (λ: <>, ref #()).

Definition eq_term : val := (rec: "eq" "x" "y" :=
  if: (Fst "x" = #0) && (Fst "y" = #0) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #1) && (Fst "y" = #1) then
    ("eq" (Fst (Snd "x")) (Fst (Snd "y"))) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else if: (Fst "x" = #2) && (Fst "y" = #2) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #3) && (Fst "y" = #3) then
    (Fst (Snd "x") = Fst (Snd "y")) &&
    (Snd (Snd "x") = Snd (Snd "y"))
  else if: (Fst "x" = #4) && (Fst "y" = #4) then
    (Fst (Snd "x") = Fst (Snd "y")) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else if: (Fst "x" = #5) && (Fst "y" = #5) then
    Snd "x" = Snd "y"
  else if: (Fst "x" = #6) && (Fst "y" = #6) then
    (Fst (Snd "x") = Fst (Snd "y")) &&
    ("eq" (Snd (Snd "x")) (Snd (Snd "y")))
  else #false)%V.

Definition resN := nroot .@ "res".

Section Proofs.

Context `{!heapG Σ, !resG Σ}.

Implicit Types E : coPset.
Implicit Types rs : readers.

Definition res_ctx : iProp Σ :=
  inv resN res_inv.

Global Instance persistent_res_ctx : Persistent res_ctx.
Proof. apply _. Qed.

Lemma twp_eq_term t1 t2 :
  ⊢ WP (eq_term (val_of_term t1) (val_of_term t2))
       [{ v, ⌜v = #(bool_decide (t1 = t2))⌝ }].
Proof.
elim: t1 t2=> [n1|t11 IH1 t12 IH2|l1|l1 b1|l1 t1 IH1|l1|l1 t1 IH1];
case=> [n2|t21 t22|l2|l2 b2|l2 t2|l2|l2 t2] /=;
wp_rec; wp_pures=> //.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- wp_bind (eq_term _ _).
  iPoseProof (IH1 t21) as "IH1"; iPoseProof (IH2 t22) as "IH2".
  iApply (twp_wand with "IH1"); iIntros (?) "->".
  case: bool_decide_reflect=> e1.
  + wp_pures; iApply (twp_wand with "IH2"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- case: bool_decide_reflect=> e1.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- case: bool_decide_reflect=> e1.
  + wp_pures.
    iPoseProof (IH1 t2) as "IH1".
    iApply (twp_wand with "IH1"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- case: bool_decide_reflect=> e1.
  + wp_pures.
    iPoseProof (IH1 t2) as "IH1".
    iApply (twp_wand with "IH1"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
Qed.

End Proofs.
