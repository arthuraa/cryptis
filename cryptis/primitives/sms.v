(* HeapLang implementations of the signed-multiset operations from
   [cryptis.lib.sms], parameterised by HeapLang closures for the element
   operations: an equality test [eq], the involution [inv], and (for [to]) an
   order comparison [le].  They mirror the pre-term counterparts in
   [primitives/pre_term.v] ([hl_insert_exp], [hl_cancel_invs], and the
   [insertion_sort]-of-[hl_cancel_invs] pattern in [hl_mul]/[hl_exp]) and reuse
   the shared [insertion_sort] of [lib/list.v] for [to].

   Each implementation gets a continuation-style spec relating it to the pure
   [SMS.*] model (same shape as the [twp_hl_*] specs in [pre_term.v]). *)

From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From stdpp Require Import sorting list.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import list_sort sms.
From cryptis.primitives Require Import notations.

Set Implicit Arguments.
Unset Strict Implicit.
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
Context (i : T -> T) (eqv invv : val).

Hypothesis eqvP : forall (x y : T) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqv (repr x) (repr y) @ E [{ Ψ }].
Hypothesis invvP : forall (x : T) E Ψ,
  Ψ (repr (i x)) ⊢ WP invv (repr x) @ E [{ Ψ }].

Implicit Types (x y z : T) (xs ys : list T).

(** ** Membership and removal, stdpp-flavoured *)

Lemma find_mem x xs :
  bool_decide (x ∈ xs)
  = match find (fun y => bool_decide (x = y)) xs with Some _ => true | None => false end.
Proof.
elim: xs => [|y xs IH].
- done.
- rewrite /=; case: (bool_decide_reflect (x = y)) => [->|ne].
  + by rewrite bool_decide_eq_true_2 //; exact: list_elem_of_here.
  + rewrite -IH; apply: bool_decide_ext; rewrite elem_of_cons; naive_solver.
Qed.

Lemma twp_sms_mem x xs E :
  [[{ True }]] mem_list eqv (repr x) (repr xs) @ E [[{ RET #(bool_decide (x ∈ xs)); True }]].
Proof.
iIntros "%Φ _ HΦ"; wp_lam; wp_pures.
wp_apply twp_find_list => //.
{ by iIntros "%y %Ψ _ HΨ"; wp_pures; wp_apply eqvP; iApply "HΨ". }
iIntros "_"; rewrite find_mem.
by case: (find (fun y => bool_decide (x = y)) xs) => [y|]; wp_pures; iApply "HΦ".
Qed.

Lemma twp_sms_rem x xs E :
  [[{ True }]] rem_list eqv (repr x) (repr xs) @ E [[{ RET repr (rem x xs); True }]].
Proof.
rewrite repr_list_unseal /=.
iIntros "%Φ _ HΦ".
iStopProof; elim: xs Φ => [| y xs IH] Φ /=; iIntros "HΦ"; wp_rec; wp_pures.
  by iApply "HΦ".
wp_apply eqvP.
rewrite (_ : bool_decide (x = y) = bool_decide (y = x)); last first.
  by apply: bool_decide_ext; split; congruence.
case: (bool_decide (y = x)) => /=; wp_pures; first by iApply "HΦ".
wp_apply IH; iIntros "_".
wp_pures; by iApply "HΦ".
Qed.

(** ** [insert] and [cancel] *)

Lemma twp_sms_insert x xs E Ψ :
  Ψ (repr (SMS.insert i x xs)) ⊢ WP sms_insert eqv invv (repr x) (repr xs) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; rewrite /SMS.insert; wp_lam; wp_pures.
wp_apply invvP; wp_apply twp_sms_mem => //; iIntros "_".
case: (bool_decide (i x ∈ xs)); wp_pures.
- wp_apply invvP; wp_apply twp_sms_rem => //; iIntros "_"; by iApply "HΨ".
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

End Proofs.

(** ** [to]: cancel, then sort with the shared [insertion_sort]

    [lib/list.v] proves [insertion_sort] correct only in mathcomp terms
    ([twp_insertion_sort], phrased with [path.sort] over an [orderType]).  We
    restate that correctness in stdpp terms — [insertion_sort] computes
    [merge_sort ole] for the total decidable order [ole] induced by the
    [orderType] — via the bridge [sort_merge_sort_ole], and use it for [to].
    Once [twp_insertion_sort] itself is restated over a stdpp order, this
    [orderType] scaffolding (and the [ole] instances) should be removed. *)

Section Ordered.

Context `{!heapGS Σ}.
Hypothesis eqvP : forall (x y : A) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqv (repr x) (repr y) @ E [{ Ψ }].
Hypothesis invvP : forall (x : A) E Ψ,
  Ψ (repr (i x)) ⊢ WP invv (repr x) @ E [{ Ψ }].

(* Stdpp packaging of the mathcomp order [<=%O] (cf. [pt_order] in
   [core/pre_term/with_stdpp.v]). *)
Definition ole : relation A := fun x y => is_true (x <= y).

Global Instance ole_dec : RelDecision ole.
Proof. rewrite /ole /RelDecision => x y; case: (x <= y); [by left | by right]. Qed.
Global Instance ole_refl : Reflexive ole.
Proof. move=> x; exact: lexx. Qed.
Global Instance ole_trans : Transitive ole.
Proof. move=> x y z; exact: le_trans. Qed.
Global Instance ole_total : Total ole.
Proof. by move=> x y; case/orP: (le_total x y); [left | right]. Qed.
Global Instance ole_antisymm : AntiSymm eq ole.
Proof. move=> x y Hxy Hyx; apply: le_anti; apply/andP; by split. Qed.

Lemma sorted_StronglySorted_ole (l : list A) :
  is_true (path.sorted <=%O l) -> StronglySorted ole l.
Proof.
elim: l => [_|x l IH]; first by constructor.
move=> Hs.
have Hl : is_true (path.sorted <=%O l) := path.path_sorted Hs.
have Ha : is_true (seq.all (<=%O x) l) := path.order_path_min le_trans Hs.
constructor; first exact: IH Hl.
by elim: l Ha {IH Hl Hs} => [//|y l IH] /ssrbool.andP [xy /IH ?]; constructor.
Qed.

(* Bridge: mathcomp's [path.sort <=%O] and stdpp's [merge_sort ole] are both
   *the* sorted permutation of the input, so they coincide. *)
Lemma sort_merge_sort_ole (l : list A) :
  path.sort <=%O l = merge_sort ole l.
Proof.
have Hss : StronglySorted ole (path.sort <=%O l).
  apply: sorted_StronglySorted_ole; exact: (path.sort_sorted le_total).
rewrite -{1}(merge_sort_id _ _ Hss).
apply: merge_sort_Permutation_eq.
apply/perm_Perm; rewrite path.perm_sort; exact: seq.perm_refl.
Qed.

(* The order-comparison closure still speaks mathcomp's [<=%O] (bool); this is
   the last mathcomp-flavoured bit of the interface, to be replaced by a stdpp
   [bool_decide (ole _ _)] once [twp_insertion_sort] is restated. *)
Hypothesis levP : forall (x y : A) E Ψ,
  Ψ #((x <= y)%O) ⊢ WP lev (repr x) (repr y) @ E [{ Ψ }].

(* Correctness of [insertion_sort], restated in stdpp terms. *)
Lemma twp_insertion_sort_merge (l : list A) E Ψ :
  Ψ (repr (merge_sort ole l)) ⊢ WP insertion_sort lev (repr l) @ E [{ Ψ }].
Proof.
iIntros "HΨ".
wp_apply (twp_insertion_sort d A lev l) => //.
{ by iIntros "%x %y %Φ _ HΦ"; wp_apply levP; iApply "HΦ". }
iIntros "_"; rewrite sort_merge_sort_ole; by iApply "HΨ".
Qed.

Lemma twp_sms_to xs E Ψ :
  Ψ (repr (SMS.to ole i xs)) ⊢ WP sms_to lev eqv invv (repr xs) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_sms_prune (i := i)); try exact: eqvP; try exact: invvP.
wp_apply (twp_sms_cancel (i := i)); try exact: eqvP; try exact: invvP.
wp_apply twp_insertion_sort_merge.
rewrite /SMS.to; by iApply "HΨ".
Qed.

End Ordered.
