From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis Require Import role cryptis primitives tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

A --> B: {g^a; nI; pkA}@pkB                         (msg1)
B --> A: {g^a; g^b; nI; nR; pkB; N}@pkA             (msg2)
A --> B: {g^a; g^b; pkA; nR}@pkB                     (msg3)

Result: derive_key [pkA; pkB; g^a; g^b; g^ab]

*)

Definition nsl_dhN := nroot.@"nsl_dh".

Definition mk_keyshare : val := λ: "k",
  texp (tint #0) "k".

Definition initiator : val := λ: "c" "skI" "pkR" "N",
  let: "pkI"  := pkey "skI" in
  let: "a"    := mk_nonce #() in
  let: "ga"   := mk_keyshare "a" in
  let: "nI"   := mk_nonce #() in
  let: "m1"   := aenc "pkR" (Tag $ nsl_dhN.@"m1")
                   (term_of_list ["ga"; "nI"; "pkI"]) in
  send "c" "m1";;
  bind: "m2"   := adec "skI" (Tag $ nsl_dhN.@"m2") (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["ga'"; "gb"; "nI'"; "nR"; "pkR'"; "N'"] := "m2" in
  guard: eq_term "ga" "ga'" && eq_term "nI" "nI'" &&
         eq_term "pkR" "pkR'" && eq_term "N" "N'" in
  let: "gab"    := texp "gb" "a" in
  let: "secret" := term_of_list ["pkI"; "pkR"; "ga"; "gb"; "gab"] in
  let: "m3"     := aenc "pkR" (Tag $ nsl_dhN.@"m3")
                     (term_of_list ["ga"; "gb"; "pkI"; "nR"]) in
  send "c" "m3";;
  SOME (derive_senc_key "secret").

Definition resp : val := λ: "c" "skR" "N",
  let: "pkR" := pkey "skR" in
  bind: "m1" := adec "skR" (Tag $ nsl_dhN.@"m1") (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["ga"; "nI"; "pkI"] := "m1" in
  guard: is_aenc_key "pkI" in
  let: "b"  := mk_nonce #() in
  let: "gb" := mk_keyshare "b" in
  let: "nR" := mk_nonce #() in
  let: "m2" := aenc "pkI" (Tag $ nsl_dhN.@"m2")
                 (term_of_list ["ga"; "gb"; "nI"; "nR"; "pkR"; "N"]) in
  send "c" "m2";;
  bind: "m3" := adec "skR" (Tag $ nsl_dhN.@"m3") (recv "c") in
  bind: "m3" := list_of_term "m3" in
  list_match: ["ga'"; "gb'"; "pkI'"; "nR'"] := "m3" in
  guard: eq_term "ga" "ga'" && eq_term "gb" "gb'" &&
         eq_term "pkI" "pkI'" && eq_term "nR" "nR'" in
  let: "gab"    := texp "ga" "b" in
  let: "secret" := term_of_list ["pkI"; "pkR"; "ga"; "gb"; "gab"] in
  SOME ("pkI", derive_senc_key "secret").
