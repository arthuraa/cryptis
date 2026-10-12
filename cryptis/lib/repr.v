From iris.heap_lang Require Import lang notation proofmode.
From elpi.apps Require Import locker.

Class Repr A := repr : A -> val.
Arguments repr / .
#[global] Hint Mode Repr ! : typeclass_instances.

#[global]
Instance repr_val : Repr val := λ x, x.
Arguments repr_val / .

#[global]
Instance repr_Z : Repr Z := λ x, #x.
Arguments repr_Z / .

#[global] Instance repr_bool : Repr bool := λ b, #b.
Arguments repr_bool / .

#[global]
Instance repr_option `{Repr A} : Repr (option A) := λ x,
  match x with
  | Some x => SOMEV (repr x)
  | None => NONEV
  end.
Arguments repr_option {A} {_} !_.

lock Definition repr_list `{Repr A} : Repr (list A) :=
  foldr (fun (x : A) v => SOMEV (repr x, v)%V) NONEV.
#[global] Existing Instance repr_list.
Arguments repr_list {A} {_} _ : simpl never.

Lemma repr_list_val `{Repr A} (xs : list A) :
  repr_list xs = repr_list (map repr xs).
Proof.
rewrite ![@repr_list]unlock; by elim: xs => //= x xs ->.
Qed.

Lemma repr_listE `{Repr A} (l : list A) :
  repr l =
  match l with
  | [] => NONEV
  | x :: xs => SOMEV (repr x, repr xs)
  end.
Proof.
rewrite /= [@repr_list]unlock. by case: l.
Qed.
