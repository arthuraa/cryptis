From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role iso_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Impl.

Section Impl.

Variable N : namespace.

Definition session_key : val := λ: "cs",
  Snd "cs".

Definition connect : val := λ: "c" "skA" "vkB",
  let: "session_key" :=
    do_until (λ: <>, initiator N "c" "skA" "vkB") in
  let: "counters" := AllocN #2 #0%nat in
  ("counters", "session_key").

Definition listen : val := λ: "c",
  do_until (λ: <>,
    let: "req" := responder_wait "c" in
    let: "vkA" := Snd "req" in
    bind: "kt" := is_key "vkA" in
    guard: "kt" = repr Open in
    SOME "req").

Definition confirm : val := λ: "c" "skB" "req",
  let: "ga" := Fst "req" in
  let: "vkA" := Snd "req" in
  let: "sk" := do_until
    (λ: <>, responder_accept N "c" "skB" "ga" "vkA") in
  let: "counters" := AllocN #2 #0%nat in
  ("counters", "sk").

Definition sent     : val := λ: "cs", Fst "cs" +ₗ #0%nat.
Definition received : val := λ: "cs", Fst "cs" +ₗ #1%nat.

Definition write : val := λ: "N" "c" "cs" "ts",
  let: "n"  := sent "cs" in
  let: "sk" := session_key "cs" in
  let: "m"  := term_of_list (tint !"n" :: "ts") in
  let: "m"  := senc "N" "sk" "m" in
  send "c" "m";;
  "n" <- !"n" + #1%nat.

Definition try_open : val := λ: "N" "cs" "t",
  bind: "t" := untag "N" "t" in
  bind: "ts" := list_of_term "t" in
  let: "m" := !(received "cs") in
  match: "ts" with
    NONE => NONE
  | SOME "ts" =>
    bind: "m'" := to_int (Fst "ts") in
    guard: "m" = "m'" in
    received "cs" <- "m" + #1;;
    SOME (Snd "ts")
  end.

Definition make_handler : val := λ: "p" "cs" "t",
  let: "N" := Fst "p" in
  let: "handler" := Snd "p" in
  bind: "ts" := try_open "N" "cs" "t" in
  SOME ("handler" "ts").

Definition make_handlers : val := rec: "loop" "handlers" :=
  match: "handlers" with
    NONE => []%E
  | SOME "handlers" =>
    let: "handler" := Fst "handlers" in
    let: "handlers" := Snd "handlers" in
    make_handler "handler" :: "loop" "handlers"
  end.

Definition select_inner_body : val := rec: "loop" "cs" "m" "handlers" :=
  match: "handlers" with
    NONE => NONE
  | SOME "handlers" =>
    let: "handler" := Fst "handlers" in
    let: "handlers" := Snd "handlers" in
    match: "handler" "cs" "m" with
      NONE => "loop" "cs" "m" "handlers"
    | SOME "res" => SOME "res"
    end
  end.

Definition select_outer_body : val := λ: "c" "cs" "handlers",
  let: "sk" := session_key "cs" in
  do_until (λ: <>,
    let: "t" := recv "c" in
    bind: "t" := open (key Open "sk") "t" in
    select_inner_body "cs" "t" "handlers"
  ).

Definition select : val := λ: "c" "cs" "handlers",
  select_outer_body "c" "cs" (make_handlers "handlers").

Definition read : val :=
  λ: "N" "c" "cs", select "c" "cs" [("N", (λ: "ts", "ts"))%E].

Definition free : val := λ: "c" "cs",
  let: "counters" := Fst "cs" in
  Free "counters";;
  Free ("counters" +ₗ #1%nat).

End Impl.

End Impl.
