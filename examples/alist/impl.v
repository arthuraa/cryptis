From cryptis Require Import lib.
From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import term cryptis primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Pure.

Definition empty : val := λ: <>, []%V.

Definition find : val := λ: "kvs" "k",
  let: "res" := find_list (λ: "kv", eq_term (Fst "kv") "k") "kvs" in
  match: "res" with
    SOME "res" => SOME (Snd "res")
  | NONE => NONE
  end.

Definition insert : val := λ: "kvs" "k" "v",
  ("k", "v") :: "kvs".

Definition delete : val := λ: "kvs" "k",
  filter_list (λ: "p", ~ eq_term "k" (Fst "p")) "kvs".

End Pure.

Module Impure.

Definition new : val := λ: <>,
  ref (Pure.empty #()).

Definition find : val := λ: "l" "k",
  Pure.find !"l" "k".

Definition insert : val := λ: "l" "k" "v",
  "l" <- Pure.insert !"l" "k" "v".

Definition delete : val := λ: "l" "k",
  "l" <- Pure.delete !"l" "k".

End Impure.
