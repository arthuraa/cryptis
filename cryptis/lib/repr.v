From iris.heap_lang Require Import lang notation proofmode.

Class Repr A := repr : A -> val.
Arguments repr / .
Global Hint Mode Repr ! : typeclass_instances.

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

Definition repr_list_aux `{Repr A} :
  seal (foldr (fun (x : A) v => SOMEV (repr x, v)%V) NONEV).
  by eexists.
Qed.
#[global]
Instance repr_list `{Repr A} : Repr (list A) := unseal repr_list_aux.
Arguments repr_list {A} {_} _ : simpl never.

Lemma repr_list_unseal `{Repr A} :
  repr_list = foldr (fun (x : A) v => SOMEV (repr x, v)%V) NONEV.
Proof. exact: seal_eq. Qed.

Lemma repr_list_val `{Repr A} (xs : list A) :
  repr_list xs = repr_list (map repr xs).
Proof.
rewrite !repr_list_unseal; by elim: xs => //= x xs ->.
Qed.

Lemma repr_listE `{Repr A} (l : list A) :
  repr l =
  match l with
  | [] => NONEV
  | x :: xs => SOMEV (repr x, repr xs)
  end.
Proof.
rewrite /= repr_list_unseal. by case: l.
Qed.
