From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import proofmode.

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib term cryptis primitives tactics rpc.
From cryptis.examples Require Import alist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Types N : namespace.

Local Existing Instance ticket_lock.

Notation opN := (nroot.@"op").

Definition _H : string -> val := fun _tag => (λ: "val", hash (tag (Tag $ opN.@_tag) "val"))%V.
Definition _H_list : string -> val := fun _tag => (λ: "val", _H _tag (term_of_list "val"))%V.
Definition prf  := _H_list.
Definition H    := _H_list.
Definition H'   := _H.
Definition AuthEnc : val := λ: "key" "v", senc "key" (Tag $ opN.@"AuthEnc") "v".
Definition AuthDec : val := λ: "key" "v", sdec "key" (Tag $ opN.@"AuthEnc") "v".
Definition g := (TInt 0).

Definition OPRF : val := λ: "k",
    λ: "x", H "rw" ["x"; (texp (H' "α" "x") "k")].

(* TODO: use the key exchange formula from the OPAQUE paper *)
Definition KE : val := λ: "p_a" "x_a" "P_b" "X_b",
    H "K" [texp "P_b" "p_a" ; texp "X_b" "x_a"].

Module Client.

Section Client.

Definition session : val := λ: "uid" "c" "pw",
    let: "x_u" := mk_nonce #() in
    let: "r" := mk_nonce #() in
    let: "α" := texp (H' "α" "pw") "r" in
    let: "X_u" := texp g "x_u" in
    let: "m1" := term_of_list [ "uid"; "α"; "X_u" ] in
    send "c" "m1" ;;
    bind: "m2" := list_of_term (recv "c") in
    list_match: [ "β"; "X_s"; "envelope"; "A_s" ] := "m2" in
    (* TODO: check β ∈ G *)
    let: "rw" := derive_senc_key (H "rw" [ "pw"; (texp "β" (hl_inv "r")) ]) in
    bind: "envelope_dec" := AuthDec "rw" "envelope" in
    bind: "list_envelope_dec" := list_of_term "envelope_dec" in
    list_match: [ "p_u"; "P_u"; "P_s" ] := "list_envelope_dec" in
    let: "K" := KE "p_u" "x_u" "P_s" "X_s" in
    let: "ssid'" := H "ssid'" ["uid"; "α"] in
    let: "SK" := prf "SK" [ "K"; "ssid'" ] in
    guard: eq_term "A_s" (prf "A_s" [ "K"; "ssid'" ]) in
    let: "A_u" := prf "A_u" [ "K"; "ssid'" ] in
    let: "m3" := "A_u"  in
    send "c" "m3" ;;
    SOME (term_of_list ["uid"; "SK"]).

End Client.

End Client.

Module Server.

Section Server.

(* OPRF and KE defined entirely in terms of other variables: defined elsewhere *)
(* enforce that other side is consistently the same person *)
Definition session : val := λ: "db" "c",
    bind: "m1" := list_of_term (recv "c") in
    list_match: [ "uid"; "α"; "X_u" ] := "m1" in
    (* TODO: check α ∈ G *)
    bind: "file" := AList.find "db" "uid" in
    bind: "file_list" := list_of_term "file" in
    list_match: [ "k_s"; "p_s"; "P_s"; "P_u"; "envelope" ] := "file_list" in
    let: "x_s" := mk_nonce #() in
    let: "β" := texp "α" "k_s" in
    let: "X_s" := texp g "x_s" in
    let: "K" := KE "p_s" "x_s" "P_u" "X_u" in
    let: "ssid'" := H "ssid'" [ "uid"; "α" ] in
    let: "SK" := prf "SK" [ "K"; "ssid'" ] in
    let: "A_s" := prf "A_s" [ "K"; "ssid'" ] in
    let: "m2" := term_of_list [ "β"; "X_s"; "envelope"; "A_s" ] in
    send "c" "m2" ;;
    let: "m3" := recv "c" in
    let: "A_u" := "m3" in
    guard: eq_term "A_u" (prf "A_u" [ "K"; "ssid'" ]) in
    SOME (term_of_list ["uid"; "SK"]).

Definition make_file : val := λ: "pw",
    let: "k_s" := mk_nonce #() in
    let: "rw" := derive_senc_key (OPRF "k_s" "pw") in
    let: "p_s" := mk_nonce #() in
    let: "p_u" := mk_nonce #() in
    let: "P_s" := texp g "p_s" in
    let: "P_u" := texp g "p_u" in
    let: "envelope" := AuthEnc "rw" (term_of_list ["p_u"; "P_u"; "P_s"]) in
    term_of_list ["k_s"; "p_s"; "P_s"; "P_u"; "envelope"].

End Server.

End Server.
