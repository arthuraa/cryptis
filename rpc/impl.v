From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role iso_dh conn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation rpcN := (nroot.@"rpc").

Module Impl.

Section Impl.

Definition connect : val := λ: "c" "skA" "vkB",
  Conn.connect "c" "skA" "vkB".

Definition listen : val := λ: "c", Conn.listen "c".

Definition confirm : val := λ: "c" "skB" "req",
  Conn.confirm "c" "skB" "req".

Definition call : val := λ: "c" "cs" "N" "ts",
  Conn.write "c" "cs" "N" "ts";;
  Conn.read "c" "cs" (Tag $ rpcN.@"resp").

Definition handle : val := λ: "c" "N" "f",
  Conn.handle "N"
    (λ: "cs" "ts",
      match: "f" "ts" with
        SOME "res" => Conn.write "c" "cs" (Tag (rpcN.@"resp")) "res"
      | NONE => Conn.write "c" "cs" (Tag (rpcN.@"error")) [TInt 0]
      end;;
      #true).

Definition close : val := λ: "c" "cs",
  Conn.write "c" "cs" (Tag $ rpcN.@"close") [TInt 0];;
  Conn.read  "c" "cs" (Tag $ rpcN.@"resp");;
  Conn.free "c" "cs".

Definition handle_close : val := λ: "c",
  Conn.handle (Tag $ rpcN.@"close")
    (λ: "cs" "ts",
      Conn.write "c" "cs" (Tag (rpcN.@"resp")) [TInt 0];;
      Conn.free "c" "cs";;
      #false).

Definition server : val := rec: "loop" "c" "cs" "handlers" :=
  let: "cont" := Conn.select "c" "cs" (handle_close "c" :: "handlers") in
  if: "cont" then "loop" "c" "cs" "handlers"
  else #().

End Impl.

End Impl.
