From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par ticket_lock assert.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.lib Require Import term_set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

(*

A --> B: {m1; nA; pkA}@pkB
B --> A: {m2; nA; nB; pkB}@pkA
A --> B: {m3; nB}@pkB

*)

Definition nslN := nroot.@"nsl".

Definition init : val := λ: "c" "skI" "pkR",
  let: "pkI" := pkey "skI" in
  let: "nI" := mk_nonce #() in
  let: "m1" := aenc "pkR" (Tag $ nslN.@"m1") (term_of_list ["nI"; "pkI"]) in
  send "c" "m1";;
  bind: "m2"   := adec "skI" (Tag $ nslN.@"m2") (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nI'"; "nR"; "pkR'"] := "m2" in
  guard: eq_term "nI'" "nI" && eq_term "pkR'" "pkR" in
  let: "m3" := aenc "pkR" (Tag $ nslN.@"m3") "nR" in
  send "c" "m3";;
  let: "sess_key" :=
    derive_senc_key (term_of_list ["pkI"; "pkR"; "nI"; "nR"]) in
  SOME "sess_key".

Definition resp : val := λ: "c" "skR",
  let: "pkR" := pkey "skR" in
  bind: "m1" := adec "skR" (Tag $ nslN.@"m1") (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["nI"; "pkI"] := "m1" in
  guard: is_aenc_key "pkI" in
  let: "nR" := mk_nonce #() in
  let: "m2" := aenc "pkI" (Tag $ nslN.@"m2") (term_of_list ["nI"; "nR"; "pkR"]) in
  send "c" "m2";;
  bind: "m3" := adec "skR" (Tag $ nslN.@"m3") (recv "c") in
  guard: eq_term "m3" "nR" in
  let: "sess_key" :=
    derive_senc_key (term_of_list ["pkI"; "pkR"; "nI"; "nR"]) in
  SOME ("pkI", "sess_key").
