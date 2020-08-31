From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gmap.
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

Section Proofs.

Context `{!heapG Σ, !resG Σ}.

Lemma wp_eq_term t1 t2 :
  ⊢ WP (eq_term (val_of_term t1) (val_of_term t2)) {{ v,
      ⌜v = #(bool_decide (t1 = t2))⌝ }}.
Proof.
iLöb as "IH" forall (t1 t2).
case: t1=> [n1|t11 t12|l1|l1 b1|l1 t1|l1|l1 t1];
case: t2=> [n2|t21 t22|l2|l2 b2|l2 t2|l2|l2 t2] /=;
wp_rec; wp_pures=> //.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- wp_bind (eq_term _ _).
  iApply (wp_wand with "IH"); iIntros (?) "->".
  case: bool_decide_reflect=> e1.
  + wp_pures; iApply (wp_wand with "IH"); iIntros (?) "->".
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
  + wp_pures; iApply (wp_wand with "IH"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
- iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_iff; intuition congruence.
- case: bool_decide_reflect=> e1.
  + wp_pures; iApply (wp_wand with "IH"); iIntros (?) "->".
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_iff; intuition congruence.
  + wp_pures; iPureIntro; congr (# (LitBool _)).
    rewrite bool_decide_false; congruence.
Qed.

End Proofs.
