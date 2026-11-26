(* HeapLang implementations of the multiset operations of [cryptis.lib.mset]
   on sorted lists, parameterised by HeapLang closures for the element
   operations: an equality test [eq] and, where sorting is needed, a test
   [le] for [MSet.le].  Each implementation gets a continuation-style spec
   relating it to the pure [MSet] model.  A multiset is represented by its
   sorted list ([repr_mset]).  [mset_eq] and [mset_le] compare multisets
   themselves, so that multisets can be elements of other multisets, as the
   monomials of [primitives/poly.v] are. *)
From mathcomp Require Import ssreflect.
From stdpp Require Import sorting list.
From iris.heap_lang Require Import notation proofmode.
From cryptis.lib Require Import repr list list_sort mset.

Unset Printing Implicit Defensive.

#[global] Instance repr_mset {T} `{!Repr T, EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)} :
  Repr (MSet.mset T) := λ X, repr (elements X).

Lemma repr_msetE {T} `{!Repr T, EqDecision T, Lexico T}
    `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}
    (X : MSet.mset T) :
  repr X = repr (elements X).
Proof. done. Qed.

(** ** Implementations *)

Definition mset_of_list : val := λ: "le" "l", insertion_sort "le" "l".

Definition mset_disj_union : val := λ: "le" "X" "Y",
  insertion_sort "le" (append_lists "X" "Y").

(* Removing elements keeps a list sorted, so the result needs no sorting. *)
Definition mset_difference : val := λ: "eq" "X" "Y",
  foldr_list (λ: "y" "acc", rem_list "eq" "y" "acc") "X" "Y".

Definition mset_elem_of : val := λ: "eq" "x" "X", mem_list "eq" "x" "X".

Definition mset_count : val := λ: "eq" "x" "X",
  foldr_list (λ: "y" "n", if: "eq" "x" "y" then "n" + #1 else "n") #0 "X".

Definition mset_eq : val := λ: "eq" "X" "Y", eq_list "eq" "X" "Y".

Definition mset_le : val := λ: "eq" "le" "X" "Y", leq_list "eq" "le" "X" "Y".

(* [MSet.grlex_lt] and its least element ([MSet.grlex_min]). *)
Definition mset_size : val := λ: "X",
  foldr_list (λ: <> "n", "n" + #1) #0 "X".

Definition mset_grlex_lt : val := λ: "eq" "le" "X" "Y",
  let: "sX" := mset_size "X" in
  let: "sY" := mset_size "Y" in
  if: "sX" < "sY" then #true
  else if: "sX" = "sY" then
    if: mset_eq "eq" "X" "Y" then #false else mset_le "eq" "le" "X" "Y"
  else #false.

Definition mset_grlex_min : val := λ: "eq" "le" "Xs",
  foldr_list (λ: "X" "acc",
    match: "acc" with
      NONE => SOME "X"
    | SOME "Y" => if: mset_grlex_lt "eq" "le" "Y" "X" then SOME "Y" else SOME
      "X"
    end) NONE "Xs".

(** ** Specifications *)

Section Proofs.

Context `{!heapGS Σ}.
Context {T : Type} `{!Repr T, EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context (eqv lev : val).
Hypothesis eqvP : ∀ (x y : T) E Ψ,
  Ψ #(bool_decide (x = y)) ⊢ WP eqv (repr x) (repr y) @ E [{ Ψ }].
Hypothesis levP : ∀ (x y : T) E Ψ,
  Ψ #(bool_decide (MSet.le x y)) ⊢ WP lev (repr x) (repr y) @ E [{ Ψ }].

Implicit Types (x : T) (l : list T) (X Y : MSet.mset T).

#[local] Lemma sorted_rem x l :
  StronglySorted MSet.le l → StronglySorted MSet.le (rem x l).
Proof.
elim: l => [|y l IH] //= /StronglySorted_cons [yl sl].
case_bool_decide; first done.
apply/StronglySorted_cons; split; last exact: IH.
by apply/Forall_forall => z /elem_of_rem; move/Forall_forall: yl; apply.
Qed.

#[local] Lemma elements_difference X Y :
  elements (X ∖ Y) = foldr rem (elements X) (elements Y).
Proof.
rewrite (_ : X ∖ Y = MSet.of_list (foldr rem (elements X) (elements Y))) //.
rewrite MSet.elements_of_list_sort; apply: (merge_sort_id MSet.le).
elim: (elements Y) => [|y l IH] /=; first exact: MSet.elements_sorted.
exact: sorted_rem.
Qed.

Lemma twp_mset_of_list l E Ψ :
  Ψ (repr (MSet.of_list l)) ⊢ WP mset_of_list lev (repr l) @ E [{ Ψ }].
Proof.
rewrite repr_msetE MSet.elements_of_list_sort; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_insertion_sort MSet.le lev) => //.
  by iIntros "%x %y %Φ _ HΦ"; wp_apply levP; iApply "HΦ".
iIntros "_"; by iApply "HΨ".
Qed.

Lemma twp_mset_disj_union X Y E Ψ :
  Ψ (repr (X ⊎ Y)) ⊢ WP mset_disj_union lev (repr X) (repr Y) @ E [{ Ψ }].
Proof.
rewrite !repr_msetE (_ : X ⊎ Y = MSet.of_list (elements X ++ elements Y)) //.
rewrite MSet.elements_of_list_sort; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_append_lists.
wp_apply (twp_insertion_sort MSet.le lev) => //.
  by iIntros "%x %y %Φ _ HΦ"; wp_apply levP; iApply "HΦ".
iIntros "_"; by iApply "HΨ".
Qed.

Lemma twp_mset_difference X Y E Ψ :
  Ψ (repr (X ∖ Y)) ⊢ WP mset_difference eqv (repr X) (repr Y) @ E [{ Ψ }].
Proof.
rewrite !repr_msetE elements_difference; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_foldr_list rem) => //.
  iIntros "%y %l %Φ _ HΦ"; wp_pures.
  wp_apply twp_rem_list => //.
  by iIntros "%a %b %Φ' _ HΦ'"; wp_apply eqvP; iApply "HΦ'".
iIntros "_"; by iApply "HΨ".
Qed.

Lemma twp_mset_elem_of x X E Ψ :
  Ψ #(bool_decide (x ∈ X)) ⊢ WP mset_elem_of eqv (repr x) (repr X) @ E [{ Ψ }].
Proof.
rewrite repr_msetE; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_mem_list => //.
  by iIntros "%a %b %Φ _ HΦ"; wp_apply eqvP; iApply "HΦ".
iIntros "_"; by iApply "HΨ".
Qed.

#[local] Lemma foldr_count_mem x l :
  foldr (λ y n, if bool_decide (x = y) then n + 1 else n)%Z 0%Z l =
  Z.of_nat (count_mem x l).
Proof. elim: l => [|y l IH] //=; rewrite IH; case_bool_decide; lia. Qed.

Lemma twp_mset_count x X E Ψ :
  Ψ #(MSet.count x X) ⊢ WP mset_count eqv (repr x) (repr X) @ E [{ Ψ }].
Proof.
rewrite repr_msetE -MSet.count_mem_elements -foldr_count_mem.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_foldr_list (λ y n, if bool_decide (x = y) then n + 1 else n)%Z
            _ _ 0%Z) => //.
  iIntros "%y %n %Φ _ HΦ"; wp_pures; wp_apply eqvP.
  by case_bool_decide; wp_pures; iApply "HΦ".
iIntros "_"; by iApply "HΨ".
Qed.

Lemma twp_mset_eq X Y E Ψ :
  Ψ #(bool_decide (X = Y)) ⊢ WP mset_eq eqv (repr X) (repr Y) @ E [{ Ψ }].
Proof.
have -> : bool_decide (X = Y) = bool_decide (elements X = elements Y).
  by apply: bool_decide_ext; split=> [->|/MSet.car_inj].
rewrite !repr_msetE; iIntros "HΨ"; wp_lam; wp_pures.
iApply (twp_eq_list eqv with "HΨ") => x y Φ _.
iIntros "HΦ"; iApply (eqvP with "HΦ").
Qed.

Lemma twp_mset_le X Y E Ψ :
  Ψ #(bool_decide (MSet.le X Y)) ⊢
  WP mset_le eqv lev (repr X) (repr Y) @ E [{ Ψ }].
Proof.
rewrite !repr_msetE; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_leq_list eqv lev) => //.
  by iIntros "%x %y %Φ _ HΦ"; wp_apply eqvP; iApply "HΦ".
  move=> x y _; iIntros "%Φ _ HΦ"; wp_apply levP; by iApply "HΦ".
iIntros "_".
rewrite [bool_decide (_ ∨ _)](bool_decide_ext _ (MSet.le X Y)).
  by iApply "HΨ".
rewrite /MSet.le; split=> -[e|l]; [left; exact: MSet.car_inj|right; exact l|
                                  left; congruence|right; exact l].
Qed.

Lemma twp_mset_size X E Ψ :
  Ψ #(Z.of_nat (size X)) ⊢ WP mset_size (repr X) @ E [{ Ψ }].
Proof.
rewrite repr_msetE; iIntros "HΨ"; wp_lam; wp_pures.
wp_apply (twp_foldr_list (λ (_ : T) (n : Z), (n + 1)%Z) _ (elements X) 0%Z)
  => //.
  by move=> b a; iIntros "%Φ _ HΦ"; wp_pures; iApply "HΦ".
iIntros "_".
have -> : foldr (λ (_ : T) (n : Z), (n + 1)%Z) 0%Z (elements X) =
          Z.of_nat (size X).
  by rewrite MSet.size_elements; elim: (elements X) => //= ? l ->; lia.
by iApply "HΨ".
Qed.

Lemma twp_mset_grlex_lt X Y E Ψ :
  Ψ #(bool_decide (MSet.grlex_lt X Y)) ⊢
  WP mset_grlex_lt eqv lev (repr X) (repr Y) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
wp_apply twp_mset_size; wp_pures; wp_apply twp_mset_size; wp_pures.
case: (bool_decide_reflect (Z.of_nat (size X) < Z.of_nat (size Y))%Z) => lt.
  rewrite bool_decide_eq_true_2; last by left; lia.
  by wp_pures; iApply "HΨ".
wp_pures.
case: (bool_decide_reflect (#(Z.of_nat (size X)) = #(Z.of_nat (size Y)))).
- move=> [e]; wp_pures; wp_apply twp_mset_eq.
  case: (bool_decide_reflect (X = Y)) => [->|nXY]; wp_pures.
    by rewrite bool_decide_eq_false_2;
      [iApply "HΨ"|exact: MSet.grlex_lt_irrefl].
  wp_apply twp_mset_le.
  rewrite (bool_decide_ext (MSet.le X Y) (MSet.grlex_lt X Y));
    first by iApply "HΨ".
  rewrite /MSet.le /MSet.grlex_lt; split.
  + by case=> // l; right; split=> //; lia.
  + by case=> [|[_ l]]; [lia|right].
- move=> ne; wp_pures.
  rewrite bool_decide_eq_false_2; first by iApply "HΨ".
  by case=> [|[e _]]; [lia|apply: ne; rewrite e].
Qed.

Definition grlex_min_step (X : MSet.mset T) (acc : option (MSet.mset T)) :
    option (MSet.mset T) :=
  match acc with
  | None => Some X
  | Some Y => if bool_decide (MSet.grlex_lt Y X) then Some Y else Some X
  end.

Lemma twp_mset_grlex_min (Xs : list (MSet.mset T)) E Ψ :
  Ψ (repr (MSet.grlex_min Xs)) ⊢
  WP mset_grlex_min eqv lev (repr Xs) @ E [{ Ψ }].
Proof.
iIntros "HΨ"; wp_lam; wp_pures.
set f := grlex_min_step.
wp_apply (twp_foldr_list f _ Xs None) => //.
  move=> b [a|]; rewrite /f /grlex_min_step; iIntros "%Φ _ HΦ"; wp_pures.
    wp_apply twp_mset_grlex_lt.
    by case: bool_decide; wp_pures; iApply "HΦ".
  by iApply "HΦ".
iIntros "_".
have -> : foldr f None Xs = MSet.grlex_min Xs.
  rewrite /f; elim: Xs => //= X Xs ->; rewrite /grlex_min_step.
  by case: (MSet.grlex_min Xs) => [Y|] //; case: bool_decide.
by iApply "HΨ".
Qed.

End Proofs.
