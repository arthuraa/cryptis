From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap coGset.
From iris.algebra Require Import agree auth gset gmap namespace_map.
From iris.base_logic.lib Require Import invariants auth.
From iris.heap_lang Require Import notation proofmode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "'assert:' e1 'in' e2" :=
  (if: e1 then e2 else NONE)%E
  (at level 200, e1, e2 at level 200,
  format "'[' 'assert:' '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Notation "'bind:' x := e1 'in' e2" :=
  (match: e1 with SOME x => e2  | NONE => NONE end)%E
  (at level 200, x at level 1, e1, e2 at level 200,
  format "'[' 'bind:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
