From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation connN := (nroot.@"conn").

Definition channel : val := λ: "cs",
  Snd (Fst "cs").

Definition sent     : val := λ: "cs", Fst (Fst (Fst "cs")) +ₗ #0%nat.
Definition received : val := λ: "cs", Fst (Fst (Fst "cs")) +ₗ #1%nat.

Definition session_key : val := λ: "cs",
  Snd (Fst (Fst "cs")).

Definition role : val := λ: "cs",
  Snd "cs".

Definition connect : val := λ: "c" "skA" "pkB" "N",
  let: "session_key" :=
    do_until (λ: <>, initiator "c" "skA" "pkB" "N") in
  let: "counters" := AllocN #2 #0%nat in
  ("counters", "session_key", "c", #1).

Definition listen : val := λ: "c",
  responder_wait "c".

Definition confirm : val := λ: "c" "skB" "N" "req",
  let: "ga" := Fst "req" in
  let: "pkA" := Snd "req" in
  let: "sk" := do_until
    (λ: <>, responder_accept "c" "skB" "ga" "pkA" "N") in
  let: "counters" := AllocN #2 #0%nat in
  let: "conn" := ("counters", "sk", "c", #0) in
  "conn".

Definition send : val := λ: "cs" "t",
  let: "c"  := channel "cs" in
  let: "n"  := sent "cs" in
  let: "sk" := session_key "cs" in
  let: "m"  := term_of_list [tint (role "cs"); tint !"n"; "t"] in
  let: "m"  := senc "sk" (Tag connN) "m" in
  send "c" "m";;
  "n" <- !"n" + #1%nat.

Definition recv : val := λ: "cs",
  let: "c"  := channel "cs" in
  let: "rl" := role "cs" in
  let: "sk" := session_key "cs" in
  do_until (λ: <>,
    let: "t" := recv "c" in
    let: "r" := received "cs" in
    bind: "t" := sdec "sk" (Tag connN) "t" in
    bind: "t" := list_of_term "t" in
    list_match: ["rl'"; "r'"; "t"] := "t" in
    bind: "rl'" := to_int "rl'" in
    bind: "r'" := to_int "r'" in
    guard: ("rl" ≠ "rl'") && (!"r" = "r'") in
    "r" <- !"r" + #1;;
    SOME "t").

Definition free : val := λ: "cs",
  let: "counters" := Fst (Fst (Fst "cs")) in
  Free "counters";;
  Free ("counters" +ₗ #1%nat).
