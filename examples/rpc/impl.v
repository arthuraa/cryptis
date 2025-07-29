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
  Conn.connect "c" "skA" "pkB" (Tag rpcN).

Definition listen : val := λ: "c", Conn.listen "c".

Definition confirm : val := λ: "c" "skB" "req",
  Conn.confirm "c" "skB" (Tag rpcN) "req".

Definition call : val := λ: "cs" "N" "t",
  Conn.send "cs" (tag "N" "t");;
  Conn.recv "cs".

Definition handle_gen : val := λ: "N" "f" "cs" "t",
  bind: "t" := untag "N" "t" in
  match: "f" "t" with
    SOME "res" =>
      let: "cont" := Fst "res" in
      let: "res" := Snd "res" in
      Conn.send "cs" "res";;
      (if: "cont" then #() else Conn.free "cs");;
      SOME "cont"
  | NONE => SOME #true
  end.

Definition handle : val := λ: "N" "f",
  handle_gen "N" (λ: "t",
    match: "f" "t" with
      SOME "res" => SOME (#true, "res")
    | NONE => NONE
    end
  ).

Definition close : val := λ: "cs",
  call "cs" (Tag $ rpcN.@"close") (TInt 0);;
  Conn.free "cs".

Definition handle_close : expr :=
  handle_gen (Tag (rpcN.@"close")) (λ: "t", SOME (#false, TInt 0))%V.

Definition select : val := λ: "cs" "handlers",
  let: "m" := Conn.recv "cs" in
  let: "handlers" := handle_close :: "handlers" in
  scan_list (λ: "handler", "handler" "cs" "m") "handlers".

Definition server : val := rec: "loop" "cs" "handlers" :=
  let: "res" := select "cs" "handlers" in
  match: "res" with
    SOME "cont" => if: "cont" then "loop" "cs" "handlers" else #()
  | NONE => "loop" "cs" "handlers"
  end.
