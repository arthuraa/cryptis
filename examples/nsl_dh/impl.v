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

A --> B: {g^a; pkA}@pkB                     (msg1)
B --> A: {g^a; g^b; pkB; N}@pkA             (msg2)
A --> B: {g^b; pkA}@pkB                     (msg3)

Result: derive_key [pkA; pkB; g^a; g^b; g^ab]

*)

Definition nsl_dhN := nroot.@"nsl_dh".

Definition mk_dh_keys : val := λ: <>,
  let: "a"  := mk_nonce #() in
  let: "ga" := texp (tint #0) "a" in
  ("a", "ga").

(* Initiator subroutines *)

Definition initiator_send : val := λ: "c" "skI" "pkR" "N",
  let: "pkI"  := pkey "skI" in
  let: "keys" := mk_dh_keys #() in
  let: "a"    := Fst "keys" in
  let: "ga"   := Snd "keys" in
  let: "m1"   := aenc "pkR" (Tag $ nsl_dhN.@"m1")
                   (term_of_list ["ga"; "pkI"]) in
  send "c" "m1";;
  bind: "m2"   := adec "skI" (Tag $ nsl_dhN.@"m2") (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["ga'"; "gb"; "pkR'"; "N'"] := "m2" in
  guard: eq_term "ga" "ga'" &&
         eq_term "pkR" "pkR'" && eq_term "N" "N'" in
  SOME ("a", "ga", "gb").

Definition initiator_confirm : val := λ: "c" "skI" "pkR" "a" "ga" "gb",
  let: "pkI"    := pkey "skI" in
  let: "gab"    := texp "gb" "a" in
  let: "secret" := term_of_list ["pkI"; "pkR"; "ga"; "gb"; "gab"] in
  let: "m3"     := aenc "pkR" (Tag $ nsl_dhN.@"m3")
                     (term_of_list ["gb"; "pkI"]) in
  send "c" "m3";;
  derive_senc_key "secret".

Definition initiator : val := λ: "c" "skI" "pkR" "N",
  bind: "res" := initiator_send "c" "skI" "pkR" "N" in
  let: "a"  := Fst (Fst "res") in
  let: "ga" := Snd (Fst "res") in
  let: "gb" := Snd "res" in
  SOME (initiator_confirm "c" "skI" "pkR" "a" "ga" "gb").

(* Responder subroutines *)

Definition responder_listen : val := λ: "c" "skR",
  let: "pkR" := pkey "skR" in
  bind: "m1" := adec "skR" (Tag $ nsl_dhN.@"m1") (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["ga"; "pkI"] := "m1" in
  guard: is_aenc_key "pkI" in
  SOME ("ga", "pkI").

Definition responder_confirm : val := λ: "c" "skR" "ga" "pkI" "N",
  let: "pkR" := pkey "skR" in
  let: "keys" := mk_dh_keys #() in
  let: "b"    := Fst "keys" in
  let: "gb"   := Snd "keys" in
  let: "m2" := aenc "pkI" (Tag $ nsl_dhN.@"m2")
                 (term_of_list ["ga"; "gb"; "pkR"; "N"]) in
  send "c" "m2";;
  bind: "m3" := adec "skR" (Tag $ nsl_dhN.@"m3") (recv "c") in
  bind: "m3" := list_of_term "m3" in
  list_match: ["gb'"; "pkI'"] := "m3" in
  guard: eq_term "gb" "gb'" && eq_term "pkI" "pkI'" in
  let: "gab"    := texp "ga" "b" in
  let: "secret" := term_of_list ["pkI"; "pkR"; "ga"; "gb"; "gab"] in
  SOME (derive_senc_key "secret").

Definition responder : val := λ: "c" "skR" "N",
  bind: "res" := responder_listen "c" "skR" in
  let: "ga"  := Fst "res" in
  let: "pkI" := Snd "res" in
  bind: "kS" := responder_confirm "c" "skR" "ga" "pkI" "N" in
  SOME ("pkI", "kS").
