(* HeapLang implementations of the signed-multiset operations from
   [cryptis.lib.sms], parameterised by HeapLang closures for the element
   operations: an equality test [eq], the involution [inv], and (for [to]) an
   order comparison [le].  They mirror the pre-term counterparts in
   [primitives/pre_term.v] ([hl_insert_exp], [hl_cancel_invs], and the
   [insertion_sort]-of-[hl_cancel_invs] pattern in [hl_mul]/[hl_exp]) and reuse
   the shared [insertion_sort] of [lib/list.v] for [to].

   Each implementation gets a continuation-style spec relating it to the pure
   [SMS.*] model (same shape as the [twp_hl_*] specs in [pre_term.v]). *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import repr list sms.

Unset Printing Implicit Defensive.

(** ** Implementations *)

Definition sms_insert : val := λ: "eq" "inv" "x" "xs",
  if: mem_list "eq" ("inv" "x") "xs" then rem_list "eq" ("inv" "x") "xs"
  else "x" :: "xs".

Definition sms_cancel : val := λ: "eq" "inv" "xs",
  foldr_list (λ: "x" "acc", sms_insert "eq" "inv" "x" "acc") [] "xs".

(* Drop the involution's fixed points, matching [SMS.prune]: keep [x] unless
   [inv x = x]. *)
Definition sms_prune : val := λ: "eq" "inv" "xs",
  foldr_list (λ: "x" "acc", if: "eq" ("inv" "x") "x" then "acc" else "x" :: "acc")
    [] "xs".

Definition sms_to : val := λ: "le" "eq" "inv" "xs",
  insertion_sort "le" (sms_cancel "eq" "inv" (sms_prune "eq" "inv" "xs")).

Section Proofs.

Context `{!heapGS Σ}.
Context {T : Type} `{!Repr T, !EqDecision T}.
Context (R : relation T)
  `{!RelDecision R, !Transitive R, !Total R, !AntiSymm (=@{T}) R}.
Context (i : T -> T) (eqv invv lev : val).

Hypothesis eqvP : forall (x y : T) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqv (repr x) (repr y) @ E [{ Ψ }].
Hypothesis invvP : forall (x : T) E Ψ,
  Ψ (repr (i x)) ⊢ WP invv (repr x) @ E [{ Ψ }].
Hypothesis levP : forall (x y : T) E Ψ,
  Ψ #(bool_decide (R x y)) ⊢ WP lev (repr x) (repr y) @ E [{ Ψ }].

Implicit Types (x y z : T) (xs ys : list T).

(** ** [insert] and [cancel] *)

Lemma twp_sms_insert x xs E Ψ :
  Ψ (repr (SMS.insert i x xs)) ⊢ WP sms_insert eqv invv (repr x) (repr xs) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; rewrite /SMS.insert; wp_lam; wp_pures.
wp_apply invvP; wp_apply twp_mem_list => //.
  by iIntros "%y %z %Φ _ HΦ"; wp_apply eqvP; iApply "HΦ".
iIntros "_".
case: (bool_decide (i x ∈ xs)); wp_pures.
- wp_apply invvP; wp_apply twp_rem_list => //.
    by iIntros "%y %z %Φ _ HΦ"; wp_apply eqvP; iApply "HΦ".
  iIntros "_"; by iApply "HΨ".
- wp_apply twp_cons; by iApply "HΨ".
Qed.

Lemma twp_sms_cancel xs E Ψ :
  Ψ (repr (SMS.cancel i xs)) ⊢ WP sms_cancel eqv invv (repr xs) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_nil.
wp_apply twp_foldr_list => //.
iIntros "%b %a %Φ _ HΦ"; wp_pures; wp_apply twp_sms_insert; by iApply "HΦ".
iIntros "_"; by iApply "HΨ".
Qed.

(* The foldr the [sms_prune] closure runs is exactly [SMS.prune] (= [filter]). *)
Lemma sms_prune_foldr xs :
  foldr (fun b a => if bool_decide (i b = b) then a else b :: a) [] xs = SMS.prune i xs.
Proof.
elim: xs => [//|x xs IH] /=.
rewrite SMS.prune_cons IH.
case: (bool_decide_reflect (i x = x)) => [e|ne].
- by rewrite (bool_decide_eq_false_2 (i x ≠ x) (fun h => h e)).
- by rewrite (bool_decide_eq_true_2 (i x ≠ x) ne).
Qed.

Lemma twp_sms_prune xs E Ψ :
  Ψ (repr (SMS.prune i xs)) ⊢ WP sms_prune eqv invv (repr xs) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_nil.
wp_apply (twp_foldr_list (fun b a => if bool_decide (i b = b) then a else b :: a)) => //.
iIntros "%b %a %Φ _ HΦ"; wp_pures.
wp_apply invvP; wp_apply eqvP.
case: (bool_decide (i b = b)); wp_pures.
- by iApply "HΦ".
- wp_apply twp_cons; by iApply "HΦ".
iIntros "_"; rewrite sms_prune_foldr; by iApply "HΨ".
Qed.

(** ** [to]: prune the involution's fixed points, cancel inverse pairs, then
    sort with the shared [insertion_sort] of [lib/list.v]. *)

Lemma twp_sms_to xs E Ψ :
  Ψ (repr (SMS.to R i xs)) ⊢ WP sms_to lev eqv invv (repr xs) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_sms_prune.
wp_apply twp_sms_cancel.
wp_apply (twp_insertion_sort R lev) => //.
  by iIntros "%x %y %Φ _ HΦ"; wp_apply levP; iApply "HΦ".
iIntros "_"; rewrite /SMS.to; by iApply "HΨ".
Qed.

End Proofs.
