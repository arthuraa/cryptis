From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record cst := {
  cst_ts   : loc;
  cst_key  : term;
  cst_ok   : bool;
}.

#[global]
Instance cst_repr : Repr cst := λ s, (#(cst_ts s), Spec.mkskey (cst_key s))%V.

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
    bind: "kS" := pk_dh_init N "c" "skA" "pkA" "pkB" in
    let: "l"  := ref #0 in
    let: "kS" := mkskey (tag (N.@"key") "kS") in
    send "c" (tsenc (N.@"init") "kS" (TInt 0));;
    SOME ("l", "kS")
  ).

Definition get_ts : val := λ: "cs",
  let: "l" := Fst "cs" in
  !"l".

Definition next_ts : val := λ: "cs",
  let: "l" := Fst "cs" in
  "l" <- (!"l" + #1).

Definition get_sk : val := λ: "cs",
  Snd "cs".

Definition send_store : val := λ: "c" "cs" "v",
  next_ts "cs";;
  let: "n" := get_ts "cs" in
  let: "sk" := get_sk "cs" in
  let: "m" := tsenc (N.@"store") "sk" (term_of_list [tint "n"; "v"]) in
  send "c" "m".

Definition ack_store : val := λ: "c" "cs",
  let: "n" := get_ts "cs" in
  let: "sk" := get_sk "cs" in
  sess_recv (N.@"ack_store") "c" "sk" (λ: "m",
    assert: eq_term "m" (tint "n") in
    SOME #()
  ).

Definition store : val := λ: "c" "cs" "t",
  send_store "c" "cs" "t";;
  ack_store "c" "cs".

Definition load : val := λ: "c" "cs",
  let: "n" := tint (get_ts "cs") in
  let: "sk" := get_sk "cs" in
  send "c" (tsenc (N.@"load") "sk" "n");;
  sess_recv (N.@"ack_load") "c" "sk" (λ: "resp",
    bind: "resp" := list_of_term "resp" in
    list_match: ["n'"; "t"] := "resp" in
    assert: eq_term "n'" "n" in
    SOME "t"
  ).

End Client.

End Client.

Record sst := {
  sst_ts   : loc;
  sst_val  : loc;
  sst_key  : term;
  sst_ok   : bool;
}.

#[global]
Instance sst_repr : Repr sst :=
  λ ss, (#(sst_ts ss), #(sst_val ss), Spec.mkskey (sst_key ss))%V.

Module Server.

Implicit Types N : namespace.

Definition get_ts : val := λ: "ss",
  !(Fst (Fst "ss")).

Definition get_val : val := λ: "ss",
  !(Snd (Fst "ss")).

Definition upd_val : val := λ: "ss" "ts" "v",
  Fst (Fst "ss") <- "ts" ;;
  Snd (Fst "ss") <- "v".

Definition get_key : val := λ: "ss",
  Snd "ss".

Definition handle_store N : val := λ: "c" "ss" "m",
  bind: "m" := list_of_term "m" in
  list_match: ["n"; "x"] := "m" in
  bind: "n'" := to_int "n" in
  assert: get_ts "ss" ≤ "n'" in
  upd_val "ss" "n'" "x";;
  send "c" (tsenc (N.@"ack_store") (get_key "ss") "n").

Definition handle_load N : val := λ: "c" "ss" "m",
  bind: "n" := to_int "m" in
  assert: get_ts "ss" = "n" in
  let: "v" := get_val "ss" in
  send "c" (tsenc (N.@"ack_load") (get_key "ss") (term_of_list ["m"; "v"])).

Definition conn_handler_body N : val := λ: "c" "ss",
  let: "sk" := get_key "ss" in
  let: "m" := recv "c" in
  match: tsdec (N.@"store") "sk" "m" with
    SOME "m" => handle_store N "c" "ss" "m"
  | NONE => match: tsdec (N.@"load") "sk" "m" with
    SOME "m" => handle_load N "c" "ss" "m"
  | NONE => #()
  end end.

Definition conn_handler N : val := rec: "loop" "c" "ss" :=
  conn_handler_body N "c" "ss";;
  "loop" "c" "ss".

Definition wait_init N : val := λ: "c" "kS",
  sess_recv (N.@"init") "c" "kS" (λ: <>,
    let: "ss" := (ref #0, ref #0, "kS") in
    conn_handler N "c" "ss"
  ).

Definition listen N : val := rec: "loop" "c" "skB" "pkB" :=
  match: pk_dh_resp N "c" "skB" "pkB" with
    NONE =>
    "loop" "c" "skB" "pkB"
  | SOME "res" =>
    let: "pkA" := Fst "res" in (* Unused for now *)
    let: "kS"  := mkskey (tag (N.@"key") (Snd "res")) in
    Fork (wait_init N "c" "kS");;
    "loop" "c" "skB" "pkB"
  end.

End Server.
