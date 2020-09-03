From stdpp Require Import base countable gmap.
From iris.heap_lang Require Import lang notation.

Definition perm `{!EqDecision T, !Countable T} (X : gset (T * T)) :=
  forall p1 p2, p1 ∈ X → p2 ∈ X → (p1.1 = p2.1 ↔ p1.2 = p2.2).

Definition flipb {T S} (b : bool) (f : T → T → S) x y :=
  f (if b then x else y) (if b then y else x).

Class AsVal A := as_val : A -> val.

Instance as_val_option `{AsVal A} : AsVal (option A) := λ x,
  match x with
  | Some x => SOMEV (as_val x)
  | None => NONEV
  end.
