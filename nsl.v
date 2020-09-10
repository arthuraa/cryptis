From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap excl dra sts.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import term crypto1 primitives.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSL.

Import sts.

Context `{!resG Σ, !heapG Σ}.

Inductive session :=
| SNew
| SAnswered of term & bool.

Inductive turn := Init | Resp.

Canonical turnO := leibnizO turn.

Implicit Types (s : session) (t : term).

Definition session_step : relation session := λ s1 s2,
  match s1, s2 with
  | SNew, SAnswered _ false => True
  | SAnswered t1 false, SAnswered t2 true => t1 = t2
  | _, _ => False
  end.

Definition session_token s : propset turn :=
  match s with
  | SNew => {[Init]}
  | SAnswered _ b => {[if b then Init else Resp]}
  end.

Canonical session_sts : stsT := Sts session_step session_token.

Class nslG := {
  in_nsl_sessG :> inG Σ (gmapUR term (stsR session_sts));
  in_nsl_keysG :> inG Σ (authR (gmapUR loc (agreeR turnO)));
  nsl_sess_name : gname;
  nsl_keys_name : gname;
}.

Context `{!nslG}.

Definition initiator_key l : iProp Σ :=
  own nsl_keys_name (◯ {[l := to_agree Init]}).

Definition responder_key l : iProp Σ :=
  own nsl_keys_name (◯ {[l := to_agree Resp]}).

Definition initiator_pred lA t : iProp Σ :=
  match t with
  | TPair (TNonce nA) (TPair (TNonce nB) (TKey KAEnc lB)) =>
    nonceT {[lA; lB]} nA ∗ nonceT {[lA; lB]} nB ∗ responder_key lB
  | _ => False
  end.

Definition responder_pred lB t : iProp Σ :=
  match t with
  | TPair (TNonce nA) (TKey KAEnc lA) =>
    nonceT {[lA; lB]} nA ∗ initiator_key lA
  | TNonce nB =>
    ∃ lA, nonceT {[lA; lB]} nB ∗ initiator_key lA
  | _ => False
  end.

Definition initiator (send recv skA pkA pkB nA : val) : val := λ: <>,
  bind: "m1"   := aenc pkB (tuple nA pkA) in
  send "m1";;
  bind: "m2"   := adec skA (recv #()) in
  bind: "nA'"  := term_projV "m2" #0 in
  bind: "nB"   := term_projV "m2" #1 in
  bind: "pkB'" := term_projV "m2" #2 in
  if: eq_term "pkB'" pkB then
    bind: "m3" := aenc pkB "nB" in
    send "nB";;
    SOME "nB"
  else NONE.

Definition responder (send recv skB pkB nB : val) : val := λ: <>,
  bind: "m1"  := adec skB (recv #()) in
  bind: "nA" := term_projV "m1" #0 in
  bind: "pkA" := term_projV "m1" #1 in
  bind: "m2" := aenc "pkA" (tuple "nA" (tuple nB pkB)) in
  send "m2";;
  bind: "nB'" := adec skB (recv #()) in
  if: "nB'" = nB then SOME "nA" else NONE.

End NSL.
