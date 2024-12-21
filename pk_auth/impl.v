From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PK.

Context `{!heapGS Σ, !cryptisG Σ, !sessionG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).

Variable N : namespace.

(*

A --> B: {nA; pkA}@pkB
B --> A: {nA; nB; pkB}@pkA
A --> B: {nB}@pkB

nA, nB

A --> B: {g^nA; pkA}@pkB
B --> A: {g^nA; g^nB; pkB}@pkA
A --> B: {g^nB}@pkB

g^{nAnB}

*)

Definition pk_auth_init : val :=
  λ: "c" "mk_key_share" "mk_sess_key" "skI" "pkR",
  let: "pkI"  := pkey "skI" in
  let: "nIsI" := "mk_key_share" #() in
  let: "nI"   := Fst "nIsI" in
  let: "sI"   := Snd "nIsI" in
  let: "m1"   := aenc (N.@"m1") "pkR" (term_of_list ["sI"; "pkI"]) in
  send "c" "m1";;
  bind: "m2"   := adec (N.@"m2") "skI" (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["sI'"; "sR"; "pkR'"] := "m2" in
  guard: eq_term "sI'" "sI" && eq_term "pkR'" "pkR" in
  let: "k" := "mk_sess_key" "nI" "sR" in
  let: "m3" := aenc (N.@"m3") "pkR" "sR" in
  send "c" "m3";;
  SOME "k".

Definition pk_auth_resp : val :=
  λ: "c" "mk_key_share" "mk_sess_key" "skR",
  let: "pkR" := pkey "skR" in
  bind: "m1" := adec (N.@"m1") "skR" (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["sI"; "pkI"] := "m1" in
  bind: "kt" := is_key "pkI" in
  guard: "kt" = repr Seal in
  let: "nRsR" := "mk_key_share" #() in
  let: "nR" := Fst "nRsR" in
  let: "sR" := Snd "nRsR" in
  let: "m2" := aenc (N.@"m2") "pkI" (term_of_list ["sI"; "sR"; "pkR"]) in
  send "c" "m2";;
  bind: "m3" := adec (N.@"m3") "skR" (recv "c") in
  guard: eq_term "m3" "sR" in
  let: "k" := "mk_sess_key" "nR" "sI" in
  SOME ("pkI", "k").

End PK.
