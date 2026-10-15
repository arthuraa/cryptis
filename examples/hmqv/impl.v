From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis Require Import role cryptis primitives tactics.
From cryptis.lib Require Import hmqv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

HMQV-C, the three-message variant of HMQV.  Each party [i] has a long-term
key pair [p_i, P_i = g^p_i]; the public keys stand in for the identities.

A --> B: g^a; P_A
B --> A: g^b; H(σ, N)
A --> B: H'(σ)

σ is the HMQV element [(X_B P_B^e)^(a + d p_A) = (X_A P_A^d)^(b + e p_B)],
with the multipliers [d = H(X_A, P_B)] and [e = H(X_B, P_A)] computed by
[hmqv_ke].  The two hashes are the authenticators of the HMQV-C paper, keyed
by σ; the responder's one also binds the resource namespace [N], as the
signed second message of ISO-DH does.

Result: derive_key (H''(σ))

*)

Definition hmqvN := nroot.@"hmqv".

Definition _H : string -> val :=
  fun _tag => (λ: "val", hash (tag (Tag $ hmqvN.@_tag) "val"))%V.
Definition _H_list : string -> val :=
  fun _tag => (λ: "val", _H _tag (term_of_list "val"))%V.
Definition H := _H_list.
Definition g := (TInt 0).

Definition mk_lt_key : val := λ: <>,
  let: "p" := mk_nonce #() in
  ("p", texp g "p").

Definition initiator : val := λ: "c" "p_a" "P_a" "P_b" "N",
  guard: (~ eq_term "P_a" "P_b") in
  let: "x_a" := mk_nonce #() in
  let: "X_a" := texp g "x_a" in
  send "c" (term_of_list ["X_a"; "P_a"]);;
  bind: "m2" := list_of_term (recv "c") in
  list_match: ["X_b"; "A_b"] := "m2" in
  let: "σ" :=
    hmqv_ke hmqvN "init" "resp" "p_a" "x_a" "P_a" "X_a" "P_b" "X_b" in
  guard: eq_term "A_b" (H "m2" ["σ"; "N"]) in
  send "c" (H "m3" ["σ"]);;
  SOME (derive_senc_key (H "key" ["σ"])).

(* A DH public key has no structure to check, so the responder only talks to
   the identities in its list [pks]. *)
Definition responder_listen : val := λ: "c" "P_b" "pks",
  do_until (λ: <>,
    bind: "m1" := list_of_term (recv "c") in
    list_match: ["X_a"; "P_a"] := "m1" in
    guard: mem_list eq_term "P_a" "pks" && (~ eq_term "P_a" "P_b") in
    SOME ("X_a", "P_a")).

Definition responder_confirm : val := λ: "c" "p_b" "P_b" "X_a" "P_a" "N",
  let: "x_b" := mk_nonce #() in
  let: "X_b" := texp g "x_b" in
  let: "σ" :=
    hmqv_ke hmqvN "resp" "init" "p_b" "x_b" "P_b" "X_b" "P_a" "X_a" in
  send "c" (term_of_list ["X_b"; H "m2" ["σ"; "N"]]);;
  let: "A_a" := recv "c" in
  guard: eq_term "A_a" (H "m3" ["σ"]) in
  SOME (derive_senc_key (H "key" ["σ"])).

Definition responder : val := λ: "c" "p_b" "P_b" "N" "pks",
  let: "res" := responder_listen "c" "P_b" "pks" in
  let: "X_a" := Fst "res" in
  let: "P_a" := Snd "res" in
  bind: "k" := responder_confirm "c" "p_b" "P_b" "X_a" "P_a" "N" in
  SOME ("P_a", "k").
