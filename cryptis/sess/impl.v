From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role iso_dh conn.
From actris Require Import proto.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation sessN := (nroot.@"sess").

Module Impl.

Section Impl.

Definition connect : val := λ: "c" "skA" "pkB",
  let: "conn" := Conn.connect "c" "skA" "pkB" in
  (#true, "conn").

Definition listen : val := λ: "c", Conn.listen "c".

Definition confirm : val := λ: "c" "skB" "req",
  let: "conn" := Conn.confirm "c" "skB" "req" in
  (#false, "conn").

Definition send : val := λ: "cs" "ts",
  let: "is_init" := Fst "cs" in
  let: "conn" := Snd "cs" in
  let: "N" := if: "is_init" then Tag (sessN.@"init") else
              Tag (sessN.@"resp") in
  Conn.send "conn" "N" "ts".

Definition recv : val := λ: "cs",
  let: "is_init" := Fst "cs" in
  let: "conn" := Snd "cs" in
  let: "N" := if: "is_init" then Tag (sessN.@"resp") else
              Tag (sessN.@"init") in
  Conn.recv "conn" "N".

End Impl.

End Impl.
