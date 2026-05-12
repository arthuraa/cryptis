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

Definition initiator_send_msg1 : val := λ: "c" "skI" "pkR",
  let: "pkI"  := pkey "skI" in
  let: "keys" := mk_dh_keys #() in
  let: "a"    := Fst "keys" in
  let: "ga"   := Snd "keys" in
  let: "m1"   := aenc "pkR" (Tag $ nsl_dhN.@"m1")
                   (term_of_list ["ga"; "pkI"]) in
  send "c" "m1";;
  "keys".

Definition initiator_recv_msg2 : val := λ: "c" "skI" "pkR" "N" "a" "ga",
  bind: "m2"   := adec "skI" (Tag $ nsl_dhN.@"m2") (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["ga'"; "gb"; "pkR'"; "N'"] := "m2" in
  guard: eq_term "ga" "ga'" &&
         eq_term "pkR" "pkR'" && eq_term "N" "N'" in
  SOME "gb".

Definition initiator_send_msg3 : val := λ: "c" "skI" "pkR" "a" "ga" "gb",
  let: "pkI"    := pkey "skI" in
  let: "gab"    := texp "gb" "a" in
  let: "secret" := term_of_list ["pkI"; "pkR"; "ga"; "gb"; "gab"] in
  let: "m3"     := aenc "pkR" (Tag $ nsl_dhN.@"m3") "gb" in
  send "c" "m3";;
  derive_senc_key "secret".

Definition initiator : val := λ: "c" "skI" "pkR" "N",
  let: "keys" := initiator_send_msg1 "c" "skI" "pkR" in
  let: "a" := Fst "keys" in
  let: "ga" := Snd "keys" in
  bind: "gb" := initiator_recv_msg2 "c" "skI" "pkR" "N" "a" "ga" in
  SOME (initiator_send_msg3 "c" "skI" "pkR" "a" "ga" "gb").

(* Responder subroutines *)

Definition responder_recv_msg1 : val := λ: "c" "skR",
  let: "pkR" := pkey "skR" in
  bind: "m1" := adec "skR" (Tag $ nsl_dhN.@"m1") (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["ga"; "pkI"] := "m1" in
  guard: is_aenc_key "pkI" in
  SOME ("ga", "pkI").

Definition responder_send_msg2 : val := λ: "c" "skR" "pkI" "N" "ga",
  let: "pkR" := pkey "skR" in
  let: "keys" := mk_dh_keys #() in
  let: "b"    := Fst "keys" in
  let: "gb"   := Snd "keys" in
  let: "m2" := aenc "pkI" (Tag $ nsl_dhN.@"m2")
                 (term_of_list ["ga"; "gb"; "pkR"; "N"]) in
  send "c" "m2";;
  "keys".

Definition responder_recv_msg3 : val := λ: "c" "skR" "pkI" "ga" "b" "gb",
  let: "pkR" := pkey "skR" in
  bind: "m3" := adec "skR" (Tag $ nsl_dhN.@"m3") (recv "c") in
  guard: eq_term "m3" "gb" in
  let: "gab"    := texp "ga" "b" in
  let: "secret" := term_of_list ["pkI"; "pkR"; "ga"; "gb"; "gab"] in
  SOME (derive_senc_key "secret").

Definition responder_listen := responder_recv_msg1.

Definition responder_confirm : val := λ: "c" "skR" "pkI" "N" "ga",
  let: "keys" := responder_send_msg2 "c" "skR" "pkI" "N" "ga" in
  let: "b" := Fst "keys" in
  let: "gb" := Snd "keys" in
  responder_recv_msg3 "c" "skR" "pkI" "ga" "b" "gb".

Definition responder : val := λ: "c" "skR" "N",
  bind: "info" := responder_listen "c" "skR" in
  let: "ga" := Fst "info" in
  let: "pkI" := Snd "info" in
  bind: "key" := responder_confirm "c" "skR" "pkI" "N" "ga" in
  SOME ("pkI", "key").
