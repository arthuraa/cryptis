From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role iso_dh gen_conn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition connect : val := λ: "c" "skA" "pkB" "N",
  GenConn.connect "c" "skA" "pkB" "N".

Definition listen : val := λ: "c", GenConn.listen "c".

Definition confirm : val := λ: "c" "skB" "N" "req",
  GenConn.confirm "c" "skB" "N" "req".

Definition send : val := λ: "c" "m",
  GenConn.send "c" "m".

Definition recv : val := λ: "c",
  (* FIXME: This step is used to add an extra later credit during the proof, but
     it should be possible to remove it.  *)
  let: <> := #() in
  GenConn.recv "c".

(** ** Namespace-tagged select / branch runtime.

    A tagged SELECT is simply a [send] of [tag N t] (mirroring [rpc.call]).
    A tagged BRANCH receives once and dispatches on the namespace tag: it tries
    [untag N1]; on a match runs the first handler, otherwise tries [untag N2];
    if neither matches (only possible when the session key is public and the
    adversary forged a non-matching tag) it returns unit. *)

Definition select_tag : val := λ: "cs" "N" "t",
  send "cs" (tag "N" "t").

Definition tag_branch_1 : val := λ: "N" "handler" "cs" "m",
  bind: "t" := untag "N" "m" in
  SOME ("handler" "cs" "t").

Definition branch2 : val := λ: "cs" "N1" "h1" "N2" "h2",
  let: "m" := recv "cs" in
  match: untag "N1" "m" with
    SOME "t" => "h1" "cs" "t"
  | NONE =>
    match: untag "N2" "m" with
      SOME "t" => "h2" "cs" "t"
    | NONE => #()
    end
  end.
