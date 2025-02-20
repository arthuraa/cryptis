From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib version term cryptis primitives tactics conn.
From cryptis.store Require Import alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Module Client.

Section Client.

Variable N : namespace.

Definition connect : val := λ: "c" "skA" "vkB",
  Conn.connect N "c" "skA" "vkB".

Definition store : val := λ: "c" "cs" "k" "v",
  Conn.write (N.@"store") "c" "cs" ["k"; "v"];;
  Conn.read (N.@"ack_store") "c" "cs";;
  Conn.tick "cs".

Definition load : val := λ: "c" "cs" "k",
  Conn.write (N.@"load") "c" "cs" ["k"];;
  let: "ts" := Conn.read (N.@"ack_load") "c" "cs" in
  Conn.tick "cs";;
  match: "ts" with
    NONE => TInt 0
  | SOME "ts" => Fst "ts"
  end.

Definition create : val := λ: "c" "cs" "k" "v",
  Conn.write (N.@"create") "c" "cs" ["k"; "v"];;
  Conn.read (N.@"ack_create") "c" "cs";;
  Conn.tick "cs".

Definition close : val := λ: "c" "cs",
  Conn.close N "c" "cs".

End Client.

End Client.

Module Server.

Implicit Types N : namespace.

Definition start : val := λ: "k",
  let: "accounts" := SAList.new #() in
  ("k", "accounts").

Definition handle_store N : val :=
λ: "c" "cs" "db" "req",
  list_match: ["k"; "v"] := "req" in
  SAList.insert "db" "k" "v";;
  Conn.write (N.@"ack_store") "c" "cs" [];;
  Conn.tick "cs";;
  SOME #true.

(* FIXME: Should return an error when the key is not present *)
Definition handle_load N : val :=
λ: "c" "cs" "db" "req",
  list_match: ["k"] := "req" in
  bind: "data" := SAList.find "db" "k" in
  Conn.write (N.@"ack_load") "c" "cs" ["data"];;
  Conn.tick "cs";;
  SOME #true.

Definition handle_create N : val :=
λ: "c" "cs" "db" "req",
  list_match: ["k"; "v"] := "req" in
  let: "success" :=
    match: SAList.find "db" "k" with
      SOME <> => #0
    | NONE =>
      SAList.insert "db" "k" "v";;
      #1
    end in
  let: "m" := ["k"; "v"; tint "success"] in
  Conn.write (N.@"ack_create") "c" "cs" "m";;
  Conn.tick "cs";;
  SOME #true.

Definition conn_handler N : val :=
  let handlers := [
    (N.@"store", handle_store N "c" "cs" "db");
    (N.@"load", handle_load N "c" "cs" "db");
    (N.@"create", handle_create N "c" "cs" "db")
  ] in λ: "c" "cs" "db" "lock",
     Conn.handle N "c" "cs" handlers;;
     lock.release "lock".

Definition find_client : val := λ: "ss" "client_key",
  let: "clients" := Snd "ss" in
  match: SAList.find "clients" "client_key" with
    NONE =>
    let: "db"   := SAList.new #() in
    let: "lock" := newlock #()    in
    SAList.insert "clients" "client_key" ("db", "lock");;
    ("db", "lock")
  | SOME "account" => "account"
  end.

Definition listen N : val := λ: "c" "ss",
  let: "secret_key" := Fst "ss" in
  let: "clients" := Snd "ss" in
  let: "res" := Conn.listen N "c" "secret_key" in
  let: "client_key" := Fst "res" in
  let: "cs" := Snd "res" in
  let: "account" := find_client "ss" "client_key" in
  let: "db" := Fst "account" in
  let: "lock" := Snd "account" in
  acquire "lock";;
  Conn.confirm N "c" "cs";;
  Fork (conn_handler N "c" "cs" "db" "lock").

End Server.
