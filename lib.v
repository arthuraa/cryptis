From stdpp Require Import base countable gmap.
From iris.heap_lang Require Import lang notation proofmode.

Definition perm `{!EqDecision T, !Countable T} (X : gset (T * T)) :=
  forall p1 p2, p1 ∈ X → p2 ∈ X → (p1.1 = p2.1 ↔ p1.2 = p2.2).

Definition flipb {T S} (b : bool) (f : T → T → S) x y :=
  f (if b then x else y) (if b then y else x).

Class Repr A := repr : A -> val.

Instance repr_Z : Repr Z := λ x, #x.

Instance repr_option `{Repr A} : Repr (option A) := λ x,
  match x with
  | Some x => SOMEV (repr x)
  | None => NONEV
  end.

Instance repr_list `{Repr A} : Repr (list A) :=
  fold_right (fun x v => (repr x, v)%V) #0.

Definition get_list : val := rec: "loop" "l" "n" :=
  if: "l" = #0 then NONE
  else if: "n" = #0 then SOME (Fst "l")
  else "loop" (Snd "l") ("n" - #1).

Lemma twp_get_list `{!Repr A, !heapG Σ} (l : list A) (n : nat) :
  ⊢ WP get_list (repr l) #n
       [{v, ⌜v = repr (nth_error l n)⌝}].
Proof.
rewrite /repr; elim: n l=> [|n IH] [|x l] /=; wp_rec; wp_pures; eauto.
rewrite (_ : (S n - 1)%Z = n); try lia.
by iApply IH.
Qed.

Instance prod_repr `{Repr A, Repr B} : Repr (A * B) :=
  λ p, (repr p.1, repr p.2)%V.
