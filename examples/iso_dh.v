From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.examples.iso_dh Require Export shared initiator responder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*

A --> B: g^a; pkA
B --> A: {g^a; g^b; pkA}@skB
A --> B: {g^a; g^b; pkB}@skA

Key: [g^a; g^b; g^ab]

*)
