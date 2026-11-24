(* HeapLang implementation of the canonical form [SMS.Internal.to] of
   [cryptis.lib.sms] on pairs of lists, parameterised by HeapLang closures for
   the element operations: an equality test [eq] and an order test [le] for
   [MSet.le].  It sorts both sides into multisets and takes their differences
   with the primitives of [primitives/mset.v].

   Its spec is continuation-style, like the [twp_hl_*] specs in [pre_term.v].
   A wrapped [SMS.sms] is represented by its underlying pair ([repr_sms]). *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import repr list mset sms.
From cryptis.primitives Require Import mset.

Unset Printing Implicit Defensive.

#[global] Instance repr_prod {A B} `{!Repr A, !Repr B} : Repr (A * B) :=
  λ p, (repr p.1, repr p.2)%V.

#[global] Instance repr_sms {T} `{!Repr T, EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)} :
  Repr (SMS.sms T) := λ s, repr (SMS.car s).

Lemma repr_smsE {T} `{!Repr T, EqDecision T, Lexico T}
    `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)} (s : SMS.sms T) :
  repr s = repr (SMS.car s).
Proof. done. Qed.

(** ** Implementation *)

Definition sms_to : val := λ: "le" "eq" "A",
  let: "X" := mset_of_list "le" (Fst "A") in
  let: "Y" := mset_of_list "le" (Snd "A") in
  (mset_difference "eq" "X" "Y", mset_difference "eq" "Y" "X").

Section Proofs.

Context `{!heapGS Σ}.
Context {T : Type} `{!Repr T, EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context (eqv lev : val).
Hypothesis eqvP : ∀ (x y : T) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqv (repr x) (repr y) @ E [{ Ψ }].
Hypothesis levP : ∀ (x y : T) E Ψ,
  Ψ #(bool_decide (MSet.le x y)) ⊢ WP lev (repr x) (repr y) @ E [{ Ψ }].

Lemma twp_sms_to (A : list T * list T) E Ψ :
  Ψ (repr (SMS.Internal.to A)) ⊢ WP sms_to lev eqv (repr A) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_mset_of_list lev levP); wp_pures.
wp_apply (twp_mset_of_list lev levP); wp_pures.
wp_apply (twp_mset_difference eqv eqvP).
wp_apply (twp_mset_difference eqv eqvP).
wp_pures; by iApply "HΨ".
Qed.

End Proofs.
