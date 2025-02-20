From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role iso_dh.
From cryptis.store Require Import alist db.

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
    do_until (λ: <>, initiator (N.@"conn".@"auth") "c" "skA" "vkB") in
  let: "timestamp" := ref #0%nat in
  let: "m" := senc (N.@"conn".@"init") "session_key" (TInt 0) in
  send "c" "m";;
  do_until (λ: <>,
    let: "m" := recv "c" in
    sdec (N.@"conn".@"ack_init") "session_key" "m");;
  ("timestamp", "session_key").

Definition listen : val := λ: "c" "skA",
  let: "result" := do_until (λ: <>, responder (N.@"conn".@"auth") "c" "skA") in
  let: "timestamp" := ref #0 in
  let: "vkB" := Fst "result" in
  let: "session_key" := Snd "result" in
  do_until (λ: <>,
    let: "m" := recv "c" in
    sdec (N.@"conn".@"init") "session_key" "m");;
  ("vkB", ("timestamp", "session_key")).

Definition confirm : val := λ: "c" "cs",
  let: "sk" := Snd "cs" in
  let: "m"  := senc (N.@"conn".@"ack_init") "sk" (TInt 0) in
  send "c" "m".

Definition timestamp : val := λ: "cs",
  let: "timestamp" := Fst "cs" in
  !"timestamp".

Definition tick : val := λ: "cs",
  let: "timestamp" := Fst "cs" in
  "timestamp" <- (!"timestamp" + #1).

Definition write N : val := λ: "c" "cs" "ts",
  let: "n"  := timestamp "cs" in
  let: "sk" := session_key "cs" in
  let: "m"  := term_of_list (tint "n" :: "ts") in
  let: "m"  := senc N "sk" "m" in
  send "c" "m".

Definition open' N : val := λ: "n" "m",
  bind: "m" := untag N "m" in
  bind: "ts" := list_of_term "m" in
  match: "ts" with
    NONE => NONE
  | SOME "ts" =>
    bind: "n'" := to_int (Fst "ts") in
    guard: "n" = "n'" in
    SOME (Snd "ts")
  end.

Definition make_handler_def (p : namespace * expr) : expr :=
  let N := p.1 in
  let: "handler" := p.2 in
  λ: "n" "m",
    bind: "ts" := open' N "n" "m" in
    "handler" "ts".

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

Definition select_inner_body : val := rec: "loop" "ts" "m" "handlers" :=
  match: "handlers" with
    NONE => NONE
  | SOME "handlers" =>
    let: "handler" := Fst "handlers" in
    let: "handlers" := Snd "handlers" in
    match: "handler" "ts" "m" with
      NONE => "loop" "ts" "m" "handlers"
    | SOME "res" => SOME "res"
    end
  end.

Definition select_outer_body : val := λ: "c" "cs" "handlers",
  let: "ts" := timestamp "cs" in
  let: "sk" := session_key "cs" in
  do_until (λ: <>,
    let: "m" := recv "c" in
    bind: "m" := open (key Open "sk") "m" in
    select_inner_body "ts" "m" "handlers"
  ).

Definition select_def (c cs : expr) handlers : expr :=
  select_outer_body c cs (make_handlers handlers).

Definition select_aux : base.seal select_def. by eexists _. Qed.
Definition select := unseal select_aux.
Lemma select_eq : select = select_def. Proof. exact: seal_eq. Qed.

Definition read N : val :=
  let handlers := [(N, (λ: "ts", SOME "ts")%E)] in
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
  let: "timestamp" := Fst "cs" in
  Free "timestamp".

Definition close : val := λ: "c" "cs",
  write (N.@"conn".@"close") "c" "cs" [];;
  read (N.@"conn".@"ack_close") "c" "cs";;
  free "c" "cs".

Definition handle_close N : val := λ: "c" "cs" "req",
  write (N.@"conn".@"ack_close") "c" "cs" [TInt 0];;
  free "c" "cs";;
  SOME #false.

Definition handle_loop : val :=
  rec: "loop" "c" "cs" "handlers" :=
    if: select_outer_body "c" "cs" "handlers" then
      "loop" "c" "cs" "handlers"
    else #().

Definition handle_def c cs handlers :=
  let handle_close :=
    make_handler (N.@"conn".@"close", handle_close N "c" "cs") in
  (λ: "c" "cs" "handlers",
    handle_loop "c" "cs" (handle_close :: "handlers"))%V
  c cs (make_handlers handlers).

Definition handle_aux : base.seal handle_def. by eexists _. Qed.
Definition handle := unseal handle_aux.
Lemma handle_eq : handle = handle_def. Proof. exact: seal_eq. Qed.

Lemma subst_handle var v c cs handlers :
  subst var v (handle c cs handlers) =
  handle
    (subst var v c) (subst var v cs)
    (map (λ p, (p.1, subst var v p.2)) handlers).
Proof.
by rewrite handle_eq /handle_def /= subst_make_handlers.
Qed.

End Impl.

End Impl.
