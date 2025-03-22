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

Module Impl.

Section Impl.

Variable N : namespace.

Definition connect : val := λ: "c" "skA" "vkB",
  Conn.connect (N.@"rpc".@"auth") "c" "skA" "vkB".

Definition listen : val := λ: "c", Conn.listen "c".

Definition confirm : val := λ: "c" "skB" "req",
  Conn.confirm (N.@"rpc".@"auth") "c" "skB" "req".

Definition call (s : string) : val := λ: "c" "cs" "ts",
  Conn.write (Tag $ N.@s.@"call") "c" "cs" "ts";;
  Conn.read  (Tag $ N.@s.@"resp") "c" "cs".

Definition handle (s : string) : val := λ: "c" "f",
  Conn.handle (Tag $ N.@s.@"call")
    (λ: "cs" "ts",
      match: "f" "ts" with
        SOME "res" => Conn.write (Tag (N.@s.@"resp")) "c" "cs" "res"
      | NONE => Conn.write (Tag (N.@"rpc".@"error")) "c" "cs" [TInt 0]
      end;;
      #true).

Definition close : val := λ: "c" "cs",
  Conn.write (Tag $ N.@"rpc".@"close".@"call") "c" "cs" [TInt 0];;
  Conn.read  (Tag $ N.@"rpc".@"close".@"resp") "c" "cs";;
  Conn.free "c" "cs".

Definition handle_close : val := λ: "c",
  Conn.handle (Tag $ N.@"rpc".@"close".@"call")
    (λ: "cs" "ts",
      Conn.write (Tag (N.@"rpc".@"close".@"resp")) "c" "cs" [TInt 0];;
      Conn.free "c" "cs";;
      #false).

Definition server : val := rec: "loop" "c" "cs" "handlers" :=
  let: "cont" := Conn.select "c" "cs" (handle_close "c" :: "handlers") in
  if: "cont" then "loop" "c" "cs" "handlers"
  else #().

End Impl.

End Impl.
