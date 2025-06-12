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

Definition call N (s : string) : val := λ: "c" "cs" "ts",
  Conn.write "c" "cs" (Tag $ N.@s.@"call") "ts";;
  Conn.read "c" "cs" (Tag $ N.@s.@"resp").

Definition handle N (s : string) : val := λ: "c" "f",
  Conn.handle (Tag $ N.@s.@"call")
    (λ: "cs" "ts",
      match: "f" "ts" with
        SOME "res" => Conn.write "c" "cs" (Tag (N.@s.@"resp")) "res"
      | NONE => Conn.write "c" "cs" (Tag (rpcN.@"error")) [TInt 0]
      end;;
      #true).

Definition close : val := λ: "c" "cs",
  Conn.write "c" "cs" (Tag $ rpcN.@"close".@"call") [TInt 0];;
  Conn.read  "c" "cs" (Tag $ rpcN.@"close".@"resp");;
  Conn.free "c" "cs".

Definition handle_close : val := λ: "c",
  Conn.handle (Tag $ rpcN.@"close".@"call")
    (λ: "cs" "ts",
      Conn.write "c" "cs" (Tag (rpcN.@"close".@"resp")) [TInt 0];;
      Conn.free "c" "cs";;
      #false).

Definition server : val := rec: "loop" "c" "cs" "handlers" :=
  let: "cont" := Conn.select "c" "cs" (handle_close "c" :: "handlers") in
  if: "cont" then "loop" "c" "cs" "handlers"
  else #().

End Impl.

End Impl.
