From iris.heap_lang Require Export primitive_laws notation.
From iris.heap_lang Require Export proofmode.
From iris.heap_lang.lib Require Import spin_lock.
From actris.channel Require Export proto.
From actris.utils Require Import llist.
Set Default Proof Using "Type".


From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.base_logic.lib Require Import invariants.
(* From iris.heap_lang Require Import notation proofmode. *)
From cryptis Require Import lib term gmeta cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh.
From cryptis.sess Require impl.
(* From cryptis.examples.gen_conn.proofs Require Import base. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation connN := (nroot.@"conn").

Section Proofs.

Context `{!cryptisGS Σ, !heapGS Σ, !connGS Σ, !iso_dhGS Σ}.
Notation iProp := (iProp Σ).

Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

Implicit Types (cs : state).
Implicit Types kS t : term.
Implicit Types skI skR : sign_key.
Implicit Types n m : nat.
Implicit Types γ : gname.
Implicit Types v : val.
Implicit Types (N : namespace).
