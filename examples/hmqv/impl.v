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
  A --> B: H'(σ, N)
  return (derive_key (H''(σ), X))

where σ is the HMQV secret computed from the parties' long-term and ephemeral
keys (cf. [cryptis.lib.hmqv.hmqv_K]), and X is the generated ephemeral key.
Checking the hashes H(σ, N) and H'(σ, N) proves that the other party was also
capable of computing σ, hence that the key is authentic.  The namespace [N] is a
_usage_ tag that allows us to distinguish different uses of the protocol, as in
ISO-DH.

*)

Definition hmqvN := nroot.@"hmqv".

Definition H (c : string) : val := λ: "xs",
  hash (tag (Tag $ hmqvN.@c) (term_of_list "xs")).
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
  send "c" (H "m3" ["σ"; "N"]);;
  SOME (derive_senc_key (H "key" ["σ"]), "x_a").

(* A DH public key carries nothing to check, so whether to confirm with the
   identity received here is the caller's decision. *)
Definition responder_listen : val := λ: "c",
  do_until (λ: <>,
    bind: "m1" := list_of_term (recv "c") in
    list_match: ["X_a"; "P_a"] := "m1" in
    SOME ("X_a", "P_a")).

Definition responder_confirm : val := λ: "c" "p_b" "P_b" "X_a" "P_a" "N",
  guard: (~ eq_term "P_a" "P_b") in
  let: "x_b" := mk_nonce #() in
  let: "X_b" := texp g "x_b" in
  let: "σ" :=
    hmqv_ke hmqvN "resp" "init" "p_b" "x_b" "P_b" "X_b" "P_a" "X_a" in
  send "c" (term_of_list ["X_b"; H "m2" ["σ"; "N"]]);;
  let: "A_a" := recv "c" in
  guard: eq_term "A_a" (H "m3" ["σ"; "N"]) in
  SOME (derive_senc_key (H "key" ["σ"]), "x_b").

