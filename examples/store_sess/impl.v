From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib term cryptis primitives tactics sess gen_conn.
From cryptis.examples Require Import alist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Notation dbN := (nroot.@"db_sess").

Module Client.

Section Client.

Definition connect : val := λ: "c" "skA" "pkB",
  Sess.connect "c" "skA" "pkB" (Tag dbN).

Definition store : val := λ: "cs" "k" "v",
  Sess.send "cs" (tag (Tag $ dbN.@"store") (term_of_list ["k"; "v"]));; #().

Definition load : val := λ: "cs" "k",
  Sess.send "cs" (tag (Tag $ dbN.@"load") "k");;
  Sess.recv "cs".

Definition create : val := λ: "cs" "k" "v",
  Sess.send "cs" (tag (Tag $ dbN.@"create") (term_of_list ["k"; "v"]));; #().

Definition close : val := λ: "cs",
  Sess.send "cs" (tag (Tag $ dbN.@"close") (TInt 0));;
  Sess.recv "cs";;
  GenConn.free "cs".

End Client.

End Client.

Module Server.

Implicit Types N : namespace.

Definition start : val := λ: "k",
  let: "accounts" := AList.new #() in
  ("k", "accounts").

Definition handle_store : val :=
λ: "db" "req",
  bind: "req" := list_of_term "req" in
  list_match: ["k"; "v"] := "req" in
  AList.insert "db" "k" "v";;
  SOME (TInt 0).

Definition handle_load : val :=
λ: "db" "k",
  bind: "data" := AList.find "db" "k" in
  SOME "data".

Definition handle_create : val :=
λ: "db" "req",
  bind: "req" := list_of_term "req" in
  list_match: ["k"; "v"] := "req" in
  match: AList.find "db" "k" with
    SOME <> => NONE
  | NONE =>
    AList.insert "db" "k" "v";;
    SOME (TInt 0)
  end.

Definition conn_handler : val := λ: "cs" "db" "lock",
  let: "handlers" := [
    Sess.handle (Tag $ dbN.@"store") (λ: "req",
      handle_store "db" "req";; #true);
    Sess.handle (Tag $ dbN.@"load") (λ: "k",
      (match: handle_load "db" "k" with
         SOME "v" => Sess.send "cs" "v"
       | NONE => #()
       end);; #true);
    Sess.handle (Tag $ dbN.@"create") (λ: "req",
      handle_create "db" "req";; #true);
    Sess.handle (Tag $ dbN.@"close") (λ: <>,
      Sess.send "cs" (TInt 0);;
      GenConn.free "cs";;
      #false)
  ] in
  (rec: "loop" <> :=
    match: Sess.select "cs" "handlers" with
      SOME "cont" => if: "cont" then "loop" #() else #()
    | NONE => "loop" #()
    end) #();;
  lock.release "lock".

Definition find_client : val := λ: "ss" "client_key",
  let: "clients" := Snd "ss" in
  match: AList.find "clients" "client_key" with
    NONE =>
    let: "db"   := AList.new #() in
    let: "lock" := newlock #()    in
    AList.insert "clients" "client_key" ("db", "lock");;
    ("db", "lock")
  | SOME "account" => "account"
  end.

Definition listen : val := λ: "c" "ss",
  let: "secret_key" := Fst "ss" in
  let: "clients" := Snd "ss" in
  let: "res" := Sess.listen "c" in
  let: "client_key" := Snd "res" in
  let: "account" := find_client "ss" "client_key" in
  let: "db" := Fst "account" in
  let: "lock" := Snd "account" in
  acquire "lock";;
  let: "cs" := Sess.confirm "c" "secret_key" (Tag dbN) "res" in
  Fork (conn_handler "cs" "db" "lock").

End Server.
