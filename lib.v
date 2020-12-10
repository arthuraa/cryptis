From stdpp Require Import base countable gmap.
From iris.heap_lang Require Import lang notation proofmode.

Definition perm `{!EqDecision T, !Countable T} (X : gset (T * T)) :=
  forall p1 p2, p1 ∈ X → p2 ∈ X → (p1.1 = p2.1 ↔ p1.2 = p2.2).

Definition flipb {T S} (b : bool) (f : T → T → S) x y :=
  f (if b then x else y) (if b then y else x).

Class Repr A := repr : A -> val.
Arguments repr / .

Instance repr_Z : Repr Z := λ x, #x.
Arguments repr_Z / .

Instance repr_option `{Repr A} : Repr (option A) := λ x,
  match x with
  | Some x => SOMEV (repr x)
  | None => NONEV
  end.
Arguments repr_option {A} {_} !_.

Definition repr_list_aux `{Repr A} :
  seal (foldr (fun x v => SOMEV (repr x, v)%V) NONEV).
  by eexists.
Qed.
Instance repr_list `{Repr A} : Repr (list A) := unseal repr_list_aux.
Arguments repr_list {A} {_} _ : simpl never.

Lemma repr_list_eq `{Repr A} :
  repr_list = foldr (fun x v => SOMEV (repr x, v)%V) NONEV.
Proof. exact: seal_eq. Qed.

Existing Instance repr_list.

Definition get_list : val := rec: "loop" "l" "n" :=
  match: "l" with NONE => NONE
  | SOME "p" =>
    if: "n" = #0 then SOME (Fst "p")
    else "loop" (Snd "p") ("n" - #1)
  end.

Notation "l !! n" := (get_list l n) : expr_scope.

Definition NILV : val := NONEV.
Definition CONSV hd tl : val := SOMEV (hd, tl).
Notation "hd :: tl" := (CONSV hd%V tl%V) : val_scope.
Notation "[ ]" := (NILV) : val_scope.
Notation "[ x ]" := (CONSV x%V NILV) : val_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (CONSV x%V (CONSV y%V .. (CONSV z%V NILV) ..)) : val_scope.

Definition NIL : expr := NONE.
Definition CONS : val := λ: "hd" "tl", SOME ("hd", "tl").
Notation "hd :: tl" := (CONS hd%E tl%E) : expr_scope.
Notation "[ ]" := (NIL) : expr_scope.
Notation "[ x ]" := (CONS x%V NIL) : expr_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (CONS x%E (CONS y%E .. (CONS z%E NIL) ..)) : expr_scope.

Section ListLemmas.

Context `{!Repr A, !heapG Σ}.

Lemma twp_get_list E (l : list A) (n : nat) Ψ :
  Ψ (repr (l !! n)) -∗
  WP repr l !! #n @ E [{ Ψ }].
Proof.
rewrite /= repr_list_eq.
elim: n l Ψ => [|n IH] [|x l] /= Ψ; iIntros "post";
wp_rec; wp_pures; eauto.
rewrite (_ : (S n - 1)%Z = n); try lia.
by iApply IH.
Qed.

Lemma wp_get_list E (l : list A) (n : nat) Ψ :
  Ψ (repr (l !! n)) -∗
  WP repr l !! #n @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_get_list. Qed.

Lemma twp_nil E Ψ :
  Ψ (repr (@nil A)) -∗
  WP []%V @ E [{ Ψ }].
Proof.
rewrite /NILV /= repr_list_eq; iIntros "?"; wp_pures.
by iApply twp_value. (* FIXME *)
Qed.

Lemma wp_nil E Ψ :
  Ψ (repr (@nil A)) -∗
  WP []%V @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_nil. Qed.

Lemma twp_cons E x xs Ψ :
  Ψ (repr (x :: xs)) -∗
  WP repr x :: repr xs @ E [{ Ψ }].
Proof.
rewrite /= repr_list_eq; iIntros "post"; by rewrite /CONS; wp_pures.
Qed.

Lemma wp_cons E x xs Ψ :
  Ψ (repr (x :: xs)) -∗
  WP repr x :: repr xs @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_cons. Qed.

Definition list_to_expr :=
  foldr (fun (x : A) e => CONS (repr x) e) NILV.

End ListLemmas.

Instance repr_prod `{Repr A, Repr B} : Repr (A * B) :=
  λ p, (repr p.1, repr p.2)%V.
Arguments repr_prod {_ _ _ _} !_.
