(* HeapLang implementation of [SMS.to] of [cryptis.lib.sms], parameterised by
   a HeapLang closure [eq] that tests elements for equality.  It takes two
   multisets and returns their differences, with the primitives of
   [primitives/mset.v].  Its spec is continuation-style, like the [twp_hl_*]
   specs in [pre_term.v].  A signed multiset is represented by the pair of its
   sides ([repr_sms]). *)

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
  Repr (SMS.sms T) := λ s, repr (SMS.pos s, SMS.neg s).

Lemma repr_smsE {T} `{!Repr T, EqDecision T, Lexico T}
    `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)} (s : SMS.sms T) :
  repr s = repr (SMS.pos s, SMS.neg s).
Proof. done. Qed.

(** ** Implementation *)

Definition sms_to : val := λ: "eq" "X" "Y",
  (mset_difference "eq" "X" "Y", mset_difference "eq" "Y" "X").

Section Proofs.

Context `{!heapGS Σ}.
Context {T : Type} `{!Repr T, EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context (eqv : val).
Hypothesis eqvP : ∀ (x y : T) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqv (repr x) (repr y) @ E [{ Ψ }].

Lemma twp_sms_to (X Y : MSet.mset T) E Ψ :
  Ψ (repr (SMS.to X Y)) ⊢ WP sms_to eqv (repr X) (repr Y) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_mset_difference eqv eqvP).
wp_apply (twp_mset_difference eqv eqvP).
wp_pures; by iApply "HΨ".
Qed.

End Proofs.
