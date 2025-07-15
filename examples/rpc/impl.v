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

Definition connect : val := λ: "c" "skA" "pkB",
  Conn.connect "c" "skA" "pkB" (Tag rpcN) (TInt 0).

Definition listen : val := λ: "c", Conn.listen "c".

Definition confirm : val := λ: "c" "skB" "req",
  Fst (Conn.confirm "c" "skB" (Tag rpcN) "req").

Definition call : val := λ: "cs" "N" "ts",
  Conn.send "cs" "N" "ts";;
  Conn.recv "cs" (Tag $ rpcN.@"resp").

Definition handle : val := λ: "N" "f",
  Conn.handle "N"
    (λ: "cs" "ts",
      match: "f" "ts" with
        SOME "res" => Conn.send "cs" (Tag (rpcN.@"resp")) "res"
      | NONE => Conn.send "cs" (Tag (rpcN.@"error")) [TInt 0]
      end;;
      #true).

Definition close : val := λ: "cs",
  Conn.send "cs" (Tag $ rpcN.@"close") [TInt 0];;
  Conn.recv  "cs" (Tag $ rpcN.@"resp");;
  Conn.free "cs".

Definition handle_close : expr :=
  Conn.handle (Tag $ rpcN.@"close")
    (λ: "cs" "ts",
      Conn.send "cs" (Tag (rpcN.@"resp")) [TInt 0];;
      Conn.free "cs";;
      #false)%V.

Definition server : val := rec: "loop" "cs" "handlers" :=
  let: "cont" := Conn.select "cs" (handle_close :: "handlers") in
  if: "cont" then "loop" "cs" "handlers"
  else #().
