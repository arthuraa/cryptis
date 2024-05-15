From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.
From cryptis.store Require Import alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record cst := {
  cst_ts   : loc;
  cst_key  : term;
  cst_name : gname;
  cst_ok   : bool;
}.

#[global]
Instance cst_repr : Repr cst := λ s, (#(cst_ts s), Spec.mkskey (cst_key s))%V.

Record sst := {
  sst_ts  : loc;
  sst_key : term;
  sst_db  : loc;
  sst_ok  : bool;
}.

#[global]
Instance sst_repr : Repr sst :=
  λ s, (#(sst_ts s), Spec.mkskey (sst_key s), #(sst_db s))%V.

(* FIXME: Maybe generalize this *)
Definition sess_recv N : val := λ: "c" "k" "f",
  do_until (λ: <>,
    let: "m" := recv "c" in
    bind: "m" := tsdec N "k" "m" in
    "f" "m"
  ).

Module Client.

Section Client.

Variable N : namespace.

Definition connect : val := λ: "c" "skA" "pkA" "pkB",
  do_until (λ: <>,
    bind: "session_key" := pk_dh_init N "c" "skA" "pkA" "pkB" in
    let: "timestamp"  := ref #0 in
    let: "session_key" := mkskey (tag (nroot.@"keys".@"sym") "session_key") in
    send "c" (tsenc (N.@"init") "session_key" (TInt 0));;
    SOME ("timestamp", "session_key")
  ).

Definition get_timestamp : val := λ: "cs",
  let: "timestamp" := Fst "cs" in
  !"timestamp".

Definition incr_timestamp : val := λ: "cs",
  let: "timestamp" := Fst "cs" in
  "timestamp" <- (!"timestamp" + #1).

Definition get_session_key : val := λ: "cs",
  Snd "cs".

Definition send_store : val := λ: "c" "cs" "k" "v",
  let: "ts" := get_timestamp "cs" in
  incr_timestamp "cs";;
  let: "sk" := get_session_key "cs" in
  let: "m" := tsenc (N.@"store") "sk" (term_of_list [tint "ts"; "k"; "v"]) in
  send "c" "m".

Definition ack_store : val := λ: "c" "cs",
  let: "ts" := get_timestamp "cs" in
  let: "sk" := get_session_key "cs" in
  sess_recv (N.@"ack_store") "c" "sk" (λ: "m",
    assert: eq_term "m" (tint "ts") in
    SOME #()
  ).

Definition store : val := λ: "c" "cs" "k" "v",
  send_store "c" "cs" "k" "v";;
  ack_store "c" "cs".

Definition load : val := λ: "c" "cs" "k",
  let: "ts" := tint (get_timestamp "cs") in
  let: "sk" := get_session_key "cs" in
  send "c" (tsenc (N.@"load") "sk" (term_of_list ["ts"; "k"]));;
  sess_recv (N.@"ack_load") "c" "sk" (λ: "resp",
    bind: "resp" := list_of_term "resp" in
    list_match: ["ts'"; "k'"; "t"] := "resp" in
    assert: eq_term "ts'" "ts" in
    assert: eq_term "k'" "k" in
    SOME "t"
  ).

End Client.

End Client.

Module Server.

Implicit Types N : namespace.

Definition handle_store N : val :=
λ: "c" "ss" "req",
  let: "timestamp" := Fst (Fst "ss") in
  let: "session_key" := Snd (Fst "ss") in
  let: "db" := Snd "ss" in
  bind: "req" := tsdec (N.@"store") "session_key" "req" in
  bind: "req" := list_of_term "req" in
  list_match: ["timestamp'"; "k"; "v"] := "req" in
  bind: "timestamp'" := to_int "timestamp'" in
  assert: !"timestamp" = "timestamp'" in
  "timestamp" <- !"timestamp" + #1;;
  "db" <- AList.insert !"db" "k" "v";;
  send "c" (tsenc (N.@"ack_store") "session_key" (tint "timestamp'"));;
  SOME #().

Definition handle_load N : val :=
λ: "c" "ss" "req",
  let: "timestamp" := ! (Fst (Fst "ss")) in
  let: "session_key" := Snd (Fst "ss") in
  let: "db" := ! (Snd "ss") in
  bind: "req" := tsdec (N.@"load") "session_key" "req" in
  bind: "req" := list_of_term "req" in
  list_match: ["timestamp'"; "k"] := "req" in
  bind: "timestamp'" := to_int "timestamp'" in
  assert: "timestamp" = "timestamp'" in
  bind: "data" := AList.find "db" "k" in
  let: "m" := term_of_list [ tint "timestamp"; "k"; "data"] in
  send "c" (tsenc (N.@"ack_load") "session_key" "m");;
  SOME #().

Definition conn_handler_body N : val :=
λ: "c" "ss",
  let: "m" := recv "c" in
  match: handle_store N "c" "ss" "m" with
    SOME <> => #()
  | NONE => match: handle_load N "c" "ss" "m" with
    SOME <> => #()
  | NONE => #()
  end end.

Definition conn_handler N : val :=
rec: "loop" "c" "ss" :=
  conn_handler_body N "c" "ss";;
  "loop" "c" "ss".

Definition wait_init N : val :=
  λ: "c" "session_key",
  sess_recv (N.@"init") "c" "session_key" (λ: <>,
    let: "db" := ref (AList.empty #()) in
    conn_handler N "c" (ref #0, "session_key", "db")
  ).

Definition listen N : val :=
rec: "loop" "c" "secret_key" "public_key" :=
  match: pk_dh_resp N "c" "secret_key" "public_key" with
    NONE =>
    "loop" "c" "secret_key" "public_key"
  | SOME "res" =>
    (* Unused for now *)
    let: "client_key" := Fst "res" in
    let: "session_key"  := mkskey (tag (nroot.@"keys".@"sym") (Snd "res")) in
    Fork (wait_init N "c" "session_key");;
    "loop" "c" "secret_key" "public_key"
  end.

End Server.
