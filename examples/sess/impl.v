From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role iso_dh gen_conn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition connect : val := λ: "c" "skA" "pkB" "N",
  GenConn.connect "c" "skA" "pkB" "N".

Definition listen : val := λ: "c", GenConn.listen "c".

Definition confirm : val := λ: "c" "skB" "N" "req",
  GenConn.confirm "c" "skB" "N" "req".

Definition send : val := λ: "c" "m",
  GenConn.send "c" "m".

Definition recv : val := λ: "c",
  (* FIXME: This step is used to add an extra later credit during the proof, but
     it should be possible to remove it.  *)
  let: <> := #() in
  GenConn.recv "c".
