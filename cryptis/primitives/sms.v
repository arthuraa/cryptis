(* HeapLang implementations of the signed-multiset operations of
   [cryptis.lib.sms] on pairs of lists, parameterised by HeapLang closures for
   the element operations: an equality test [eq] and (for [to]) an order
   comparison [le].  [to] reuses the shared [insertion_sort] of [lib/list.v].

   Each implementation gets a continuation-style spec relating it to the pure
   [SMS.Internal.*] model (same shape as the [twp_hl_*] specs in
   [pre_term.v]).  A wrapped [SMS.sms] is represented by its underlying pair
   ([repr_sms]). *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import repr list sms.

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

(** ** Implementations *)

Definition sms_cancel_step : val := λ: "eq" "x" "A",
  if: mem_list "eq" "x" (Snd "A") then (Fst "A", rem_list "eq" "x" (Snd "A"))
  else ("x" :: Fst "A", Snd "A").

Definition sms_cancel : val := λ: "eq" "A",
  foldr_list (λ: "x" "acc", sms_cancel_step "eq" "x" "acc") ([], Snd "A")
    (Fst "A").

Definition sms_to : val := λ: "le" "eq" "A",
  let: "B" := sms_cancel "eq" "A" in
  (insertion_sort "le" (Fst "B"), insertion_sort "le" (Snd "B")).

Section Proofs.

Context `{!heapGS Σ}.
Context {T : Type} `{!Repr T, !EqDecision T}.
Context (R : relation T)
  `{!RelDecision R, !Transitive R, !Total R, !AntiSymm (=@{T}) R}.
Context (eqv lev : val).

Hypothesis eqvP : forall (x y : T) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqv (repr x) (repr y) @ E [{ Ψ }].
Hypothesis levP : forall (x y : T) E Ψ,
  Ψ #(bool_decide (R x y)) ⊢ WP lev (repr x) (repr y) @ E [{ Ψ }].

Implicit Types (x : T) (A : list T * list T).

Lemma twp_sms_cancel_step x A E Ψ :
  Ψ (repr (SMS.Internal.cancel_step x A)) ⊢
  WP sms_cancel_step eqv (repr x) (repr A) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; rewrite /SMS.Internal.cancel_step; wp_lam; wp_pures.
wp_apply twp_mem_list => //.
  by iIntros "%y %z %Φ _ HΦ"; wp_apply eqvP; iApply "HΦ".
iIntros "_".
case: (bool_decide (x ∈ A.2)); wp_pures.
- wp_apply twp_rem_list => //.
    by iIntros "%y %z %Φ _ HΦ"; wp_apply eqvP; iApply "HΦ".
  iIntros "_"; wp_pures; by iApply "HΨ".
- wp_apply twp_cons; wp_pures; by iApply "HΨ".
Qed.

Lemma twp_sms_cancel A E Ψ :
  Ψ (repr (SMS.Internal.cancel A)) ⊢ WP sms_cancel eqv (repr A) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
rewrite (_ : InjLV #() = repr (@nil T)); last by rewrite [@repr_list]unlock.
wp_apply (twp_foldr_list SMS.Internal.cancel_step _ A.1 ([], A.2)) => //.
  iIntros "%b %a %Φ _ HΦ"; wp_pures.
  by wp_apply twp_sms_cancel_step; iApply "HΦ".
iIntros "_"; by iApply "HΨ".
Qed.

Lemma twp_sms_to A E Ψ :
  Ψ (repr (SMS.Internal.to R A)) ⊢ WP sms_to lev eqv (repr A) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_sms_cancel; wp_pures.
wp_apply (twp_insertion_sort R lev) => //.
  by iIntros "%x %y %Φ _ HΦ"; wp_apply levP; iApply "HΦ".
iIntros "_"; wp_pures.
wp_apply (twp_insertion_sort R lev) => //.
  by iIntros "%x %y %Φ _ HΦ"; wp_apply levP; iApply "HΦ".
iIntros "_"; wp_pures; by iApply "HΨ".
Qed.

End Proofs.
