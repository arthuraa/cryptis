From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis primitives tactics.
From cryptis Require Import role.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

A --> B: g^a; pkA
B --> A: {g^a; g^b; pkA}@skB
A --> B: {g^a; g^b; pkB; N; req}@skA

Result: derive_key [pkA; pkB; g^a; g^b; g^ab]

*)

Definition iso_dhN := nroot.@"iso_dh".

Definition mk_keyshare : val := λ: "k",
  texp (tint #0) "k".

Definition initiator : val := λ: "c" "skI" "pkR" "N",
  let: "pkI"  := pkey "skI" in
  let: "a"    := mk_nonce #() in
  let: "ga"   := mk_keyshare "a" in
  let: "m1"   := term_of_list ["ga"; "pkI"] in
  send "c" "m1";;
  bind: "m2"   := verify "pkR" (Tag $ iso_dhN.@"m2") (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["ga'"; "gb"; "pkI'"; "N'"] := "m2" in
  guard: eq_term "ga" "ga'" && eq_term "pkI" "pkI'" && eq_term "N" "N'" in
  let: "gab" := texp "gb" "a" in
  let: "secret" := term_of_list ["pkI"; "pkR"; "ga"; "gb"; "gab"] in
  let: "m3_body" := term_of_list ["ga"; "gb"; "pkR"] in
  let: "m3" := sign "skI" (Tag $ iso_dhN.@"m3") "m3_body" in
  send "c" "m3";;
  SOME (derive_senc_key "secret").

Definition responder_wait : val := λ: "c",
  do_until (λ: <>,
    let: "m1" := recv "c" in
    bind: "m1" := list_of_term "m1" in
    list_match: ["ga"; "pkI"] := "m1" in
    guard: is_verify_key "pkI" in
    SOME ("ga", "pkI")).

Definition responder_accept : val := λ: "c" "skR" "ga" "pkI" "N",
  let: "pkR" := pkey "skR" in
  let: "b" := mk_nonce #() in
  let: "gb" := mk_keyshare "b" in
  let: "m2" := sign "skR" (Tag $ iso_dhN.@"m2")
                 (term_of_list ["ga"; "gb"; "pkI"; "N"]) in
  send "c" "m2";;
  bind: "m3" := verify "pkI" (Tag $ iso_dhN.@"m3") (recv "c") in
  bind: "m3" := list_of_term "m3" in
  list_match: ["ga'"; "gb'"; "pkR'"] := "m3" in
  guard: eq_term "ga" "ga'" && eq_term "gb" "gb'" && eq_term "pkR" "pkR'" in
  let: "gab" := texp "ga" "b" in
  let: "secret" := term_of_list ["pkI"; "pkR"; "ga"; "gb"; "gab"] in
  SOME (derive_senc_key "secret").

Definition responder : val := λ: "c" "skR" "N",
  let: "res" := responder_wait "c" in
  let: "ga"  := Fst "res" in
  let: "pkI" := Snd "res" in
  bind: "kS" := responder_accept "c" "skR" "ga" "pkI" "N" in
  SOME ("pkI", "kS").
