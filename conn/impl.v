From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role iso_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Impl.

Section Impl.

Variable N : namespace.

Definition session_key : val := λ: "cs",
  Snd "cs".

Definition connect : val := λ: "c" "skA" "vkB",
  let: "session_key" :=
    do_until (λ: <>, initiator (N.@"conn") "c" "skA" "vkB") in
  let: "counters" := AllocN #2 #0%nat in
  ("counters", "session_key").

Definition listen : val := λ: "c",
  do_until (λ: <>,
    let: "req" := responder_wait "c" in
    let: "vkA" := Snd "req" in
    bind: "kt" := is_key "vkA" in
    guard: "kt" = repr Open in
    SOME "req").

Definition confirm : val := λ: "c" "skB" "req",
  let: "ga" := Fst "req" in
  let: "vkA" := Snd "req" in
  let: "sk" := do_until
    (λ: <>, responder_accept (N.@"conn") "c" "skB" "ga" "vkA") in
  let: "counters" := AllocN #2 #0%nat in
  ("counters", "sk").

Definition sent     : val := λ: "cs", Fst "cs" +ₗ #0%nat.
Definition received : val := λ: "cs", Fst "cs" +ₗ #1%nat.

Definition write N : val := λ: "c" "cs" "ts",
  let: "n"  := sent "cs" in
  let: "sk" := session_key "cs" in
  let: "m"  := term_of_list (tint !"n" :: "ts") in
  let: "m"  := senc N "sk" "m" in
  send "c" "m";;
  "n" <- !"n" + #1%nat.

Definition try_open : val := λ: "N" "cs" "t",
  bind: "t" := untag "N" "t" in
  bind: "ts" := list_of_term "t" in
  let: "m" := !(received "cs") in
  match: "ts" with
    NONE => NONE
  | SOME "ts" =>
    bind: "m'" := to_int (Fst "ts") in
    guard: "m" = "m'" in
    received "cs" <- "m" + #1;;
    SOME (Snd "ts")
  end.

Definition make_handler_def (p : namespace * expr) : expr :=
  let N := p.1 in
  let: "handler" := p.2 in
  λ: "cs" "t",
    bind: "ts" := try_open (Tag N) "cs" "t" in
    SOME ("handler" "ts").

Definition make_handler_aux : base.seal make_handler_def. by eexists _. Qed.
Definition make_handler := unseal make_handler_aux.
Lemma make_handler_eq : make_handler = make_handler_def.
Proof. exact: seal_eq. Qed.

Lemma subst_make_handler var v p :
  subst var v (make_handler p) =
  make_handler (p.1, subst var v p.2).
Proof.
rewrite make_handler_eq /make_handler_def.
case: p => [N' handler] /=.
case: decide => [[_ not_shadow_handler]|shadow_handler //].
case: decide => [[_ not_shadow_n]|shadow_n //].
case: decide => [[_ not_shadow_m]|shadow_m //].
rewrite decide_False; last congruence.
rewrite decide_False; last congruence.
case: decide => [[_ not_shadow_ts]|shadow_ts //].
rewrite decide_False; last congruence.
by rewrite decide_False; last congruence.
Qed.

Fixpoint make_handlers (handlers : list (namespace * expr)) : expr :=
  match handlers with
  | [] => []%E
  | handler :: handlers => (make_handler handler :: make_handlers handlers)%E
  end.

Lemma subst_make_handlers var v handlers :
  subst var v (make_handlers handlers) =
  make_handlers (map (λ p, (p.1, subst var v p.2)) handlers).
Proof.
elim: handlers=> [|p handlers IH] //=.
by rewrite -IH -subst_make_handler.
Qed.

Definition select_inner_body : val := rec: "loop" "cs" "m" "handlers" :=
  match: "handlers" with
    NONE => NONE
  | SOME "handlers" =>
    let: "handler" := Fst "handlers" in
    let: "handlers" := Snd "handlers" in
    match: "handler" "cs" "m" with
      NONE => "loop" "cs" "m" "handlers"
    | SOME "res" => SOME "res"
    end
  end.

Definition select_outer_body : val := λ: "c" "cs" "handlers",
  let: "sk" := session_key "cs" in
  do_until (λ: <>,
    let: "t" := recv "c" in
    bind: "t" := open (key Open "sk") "t" in
    select_inner_body "cs" "t" "handlers"
  ).

Definition select_def (c cs : expr) handlers : expr :=
  select_outer_body c cs (make_handlers handlers).

Definition select_aux : base.seal select_def. by eexists _. Qed.
Definition select := unseal select_aux.
Lemma select_eq : select = select_def. Proof. exact: seal_eq. Qed.

Definition read N : val :=
  let handlers := [(N, (λ: "ts", "ts")%E)] in
  λ: "c" "cs", select "c" "cs" handlers.

Lemma subst_select var v c cs handlers :
  subst var v (select c cs handlers) =
  select
    (subst var v c) (subst var v cs)
    (map (λ p, (p.1, subst var v p.2)) handlers).
Proof.
by rewrite select_eq /select /= subst_make_handlers.
Qed.

Definition free : val := λ: "c" "cs",
  let: "counters" := Fst "cs" in
  Free "counters";;
  Free ("counters" +ₗ #1%nat).

End Impl.

End Impl.
