From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role iso_dh.
From cryptis.store Require Import alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

(* MOVE *)
Definition list_hd : val := λ: "l",
  match: "l" with
    NONE => NONE
  | SOME "l" => Fst "l"
  end.

Definition list_tl : val := λ: "l",
  match: "l" with
    NONE => NONE
  | SOME "l" => Snd "l"
  end.

Lemma repr_listE `{Repr A} (l : list A) :
  repr l =
  match l with
  | [] => NONEV
  | x :: xs => SOMEV (repr x, repr xs)
  end.
Proof.
rewrite /= repr_list_unseal. by case: l.
Qed.
(* /MOVE *)

Module Connection.

Section Connection.

Variable N : namespace.

Definition session_key : val := λ: "cs",
  Snd "cs".
Definition connect : val := λ: "c" "skA" "vkB",
  let: "session_key" :=
    do_until (λ: <>, initiator (N.@"auth") "c" "skA" "vkB") in
  let: "timestamp" := ref #0%nat in
  let: "m" := senc (N.@"init") "session_key" (TInt 0) in
  send "c" "m";;
  do_until (λ: <>,
    let: "m" := recv "c" in
    sdec (N.@"ack_init") "session_key" "m");;
  ("timestamp", "session_key").

Definition listen : val := λ: "c" "skA",
  let: "result" := do_until (λ: <>, responder (N.@"auth") "c" "skA") in
  let: "timestamp" := ref #0 in
  let: "vkB" := Fst "result" in
  let: "session_key" := Snd "result" in
  do_until (λ: <>,
    let: "m" := recv "c" in
    sdec (N.@"init") "session_key" "m");;
  ("vkB", ("timestamp", "session_key")).

Definition confirm : val := λ: "c" "cs",
  let: "sk" := Snd "cs" in
  let: "m"  := senc (N.@"ack_init") "sk" (TInt 0) in
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

Definition make_handler (p : namespace * expr) : expr :=
  let N := p.1 in
  let: "handler" := p.2 in
  λ: "n" "m",
    bind: "m" := untag N "m" in
    bind: "ts" := list_of_term "m" in
    match: "ts" with
      NONE => NONE
    | SOME "ts" =>
      bind: "n'" := to_int (Fst "ts") in
      guard: "n" = "n'" in
      "handler" (Snd "ts")
    end.

Lemma subst_make_handler var v p :
  subst var v (make_handler p) =
  make_handler (p.1, subst var v p.2).
Proof.
case: p => [N' handler] /=.
case: decide => [[_ not_shadow_handler]|shadow_handler //].
case: decide => [[_ not_shadow_n]|shadow_n //].
case: decide => [[_ not_shadow_m]|shadow_m //].
rewrite decide_False; last congruence.
case: decide => [[_ not_shadow_ts]|shadow_ts //].
rewrite decide_False; last congruence.
case: decide => [[_ not_shadow_n']|shadow_n' //].
rewrite decide_False; last congruence.
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

Definition select_body : val := rec: "loop" "ts" "m" "handlers" :=
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

Definition select_def (c cs : expr) handlers : expr :=
  (λ: "c" "cs" "handlers",
    let: "ts" := timestamp "cs" in
    let: "sk" := session_key "cs" in
    do_until (λ: <>,
      let: "m" := recv "c" in
      bind: "m" := open (key Open "sk") "m" in
      select_body "ts" "m" "handlers"
    ))%V c cs (make_handlers handlers).

Definition select_aux : base.seal select_def. by eexists _. Qed.
Definition select := unseal select_aux.
Lemma select_eq : select = select_def. Proof. exact: seal_eq. Qed.

Definition read N : val :=
  let handlers := [(N, (λ: "ts", SOME "ts")%E)] in
  λ: "c" "cs", select "c" "cs" handlers.

Lemma subst_select var v c cs handlers :
  subst var v (select c cs handlers) =
  select (subst var v c) (subst var v cs)
         (map (λ p, (p.1, subst var v p.2)) handlers).
Proof.
by rewrite select_eq /select /= subst_make_handlers.
Qed.

Definition close : val := λ: "c" "cs",
  let: "timestamp" := Fst "cs" in
  Free "timestamp".

End Connection.

End Connection.

Module Client.

Section Client.

Variable N : namespace.

Definition connect : val := λ: "c" "skA" "vkB",
  Connection.connect N "c" "skA" "vkB".

Definition store : val := λ: "c" "cs" "k" "v",
  Connection.write (N.@"store") "c" "cs" ["k"; "v"];;
  Connection.read (N.@"ack_store") "c" "cs";;
  Connection.tick "cs".

Definition load : val := λ: "c" "cs" "k",
  Connection.write (N.@"load") "c" "cs" ["k"];;
  let: "ts" := Connection.read (N.@"ack_load") "c" "cs" in
  Connection.tick "cs";;
  match: "ts" with
    NONE => TInt 0
  | SOME "ts" => Fst "ts"
  end.

Definition create : val := λ: "c" "cs" "k" "v",
  Connection.write (N.@"create") "c" "cs" ["k"; "v"];;
  Connection.read (N.@"ack_create") "c" "cs";;
  Connection.tick "cs".

Definition close : val := λ: "c" "cs",
  Connection.write (N.@"close") "c" "cs" [];;
  Connection.read (N.@"ack_close") "c" "cs";;
  Connection.close "c" "cs".

End Client.

End Client.

Module Server.

Implicit Types N : namespace.

Definition start : val := λ: "k",
  let: "accounts" := SAList.new #() in
  ("k", "accounts").

Definition handle_store N : val :=
λ: "c" "cs" "db" "req",
  list_match: ["k"; "v"] := "req" in
  SAList.insert "db" "k" "v";;
  Connection.write (N.@"ack_store") "c" "cs" [];;
  Connection.tick "cs";;
  SOME #true.

(* FIXME: Should return an error when the key is not present *)
Definition handle_load N : val :=
λ: "c" "cs" "db" "req",
  list_match: ["k"] := "req" in
  bind: "data" := SAList.find "db" "k" in
  Connection.write (N.@"ack_load") "c" "cs" ["data"];;
  Connection.tick "cs";;
  SOME #true.

Definition handle_create N : val :=
λ: "c" "cs" "db" "req",
  list_match: ["k"; "v"] := "req" in
  let: "success" :=
    match: SAList.find "db" "k" with
      SOME <> => #0
    | NONE =>
      SAList.insert "db" "k" "v";;
      #1
    end in
  let: "m" := ["k"; "v"; tint "success"] in
  Connection.write (N.@"ack_create") "c" "cs" "m";;
  Connection.tick "cs";;
  SOME #true.

Definition handle_close N : val :=
λ: "c" "cs" "db" "req",
  Connection.write (N.@"ack_close") "c" "cs" [TInt 0];;
  Connection.close "c" "cs";;
  SOME #false.

Definition conn_handler_body N : val :=
  let handlers := [
    (N.@"store", handle_store N "c" "cs" "db");
    (N.@"load", handle_load N "c" "cs" "db");
    (N.@"create", handle_create N "c" "cs" "db");
    (N.@"close", handle_close N "c" "cs" "db")
  ] in λ: "c" "cs" "db",
     Connection.select "c" "cs" handlers.

Definition conn_handler N : val := rec: "loop" "c" "cs" "db" "lock" :=
  if: conn_handler_body N "c" "cs" "db" then
    "loop" "c" "cs" "db" "lock"
  else lock.release "lock".

Definition find_client : val := λ: "ss" "client_key",
  let: "clients" := Snd "ss" in
  match: SAList.find "clients" "client_key" with
    NONE =>
    let: "db"   := SAList.new #() in
    let: "lock" := newlock #()    in
    SAList.insert "clients" "client_key" ("db", "lock");;
    ("db", "lock")
  | SOME "account" => "account"
  end.

Definition listen N : val := λ: "c" "ss",
  let: "secret_key" := Fst "ss" in
  let: "clients" := Snd "ss" in
  let: "res" := Connection.listen N "c" "secret_key" in
  let: "client_key" := Fst "res" in
  let: "cs" := Snd "res" in
  let: "account" := find_client "ss" "client_key" in
  let: "db" := Fst "account" in
  let: "lock" := Snd "account" in
  acquire "lock";;
  Connection.confirm N "c" "cs";;
  Fork (conn_handler N "c" "cs" "db" "lock").

End Server.
