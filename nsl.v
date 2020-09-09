From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import term crypto1 primitives.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSL.

Context `{!resG Σ, !heapG Σ}.

Inductive session :=
| SNew
| SAnswered of term & bool
| SInvalid.

Canonical sessionO := leibnizO session.

Global Instance session_op : Op session := λ s1 s2,
  match s1, s2 with
  | SNew, s | s , SNew => s
  | SInvalid, _ | _, SInvalid => SInvalid
  | SAnswered t1 b1, SAnswered t2 b2 =>
    if bool_decide (t1 = t2) then SAnswered t1 (b1 || b2)
    else SInvalid
  end.

Global Instance session_valid : Valid session := λ s,
  match s with
  | SInvalid => False
  | _ => True
  end.

Global Instance session_validN : ValidN session := λ _, valid.

Global Instance session_pcore : PCore session := Some.

Lemma session_cmra_mixin : CmraMixin session.
Proof.
split.
- solve_contractive.
- move=> n x _ _ <- [<-]; eauto.
- by move=> n x _ <-.
- move=> x; split; first by eauto.
  apply; exact: 0.
- move=> ??; apply.
- rewrite /op; case=> [|t1 b1|] [|t2 b2|] [|t3 b3|] //=;
  try by case: bool_decide.
  case: (bool_decide_reflect (t1 = t2))=> [e12|ne12] //=;
  try subst t1;
  case: (bool_decide_reflect (t2 = t3))=> [e23|ne23] //=;
  try subst t2.
  + by rewrite bool_decide_true // orb_assoc.
  + by rewrite bool_decide_false.
- rewrite /op; case=> [|t1 b1|] [|t2 b2|] //=.
  case: (bool_decide_reflect (t1 = t2))=> [<-|ne12].
  + by rewrite bool_decide_true // orb_comm.
  + by rewrite bool_decide_false.
- rewrite /op; case=> [|t b|] _ [<-] //=.
  by rewrite bool_decide_true // orb_diag.
- by move=> ? _ [<-].
- by move=> x y _ xy [<-]; exists y.
- by move=> ? [|??|] [|??|].
- move=> ? x y1 y2 valid_x e.
  rewrite e in valid_x *; by exists y1, y2.
Qed.

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
