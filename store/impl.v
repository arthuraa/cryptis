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

Module Connection.

Section Connection.

Variable N : namespace.

Definition connect : val := λ: "c" "skA" "vkB",
  do_until (λ: <>,
    bind: "session_key" := initiator (N.@"auth") "c" "skA" "vkB" in
    let: "timestamp"  := ref #0 in
    SOME ("timestamp", "session_key")
  ).

Definition listen : val := λ: "c" "skA",
  do_until (λ: <>,
    bind: "result" := responder (N.@"auth") "c" "skA" in
    let: "timestamp" := ref #0 in
    let: "vkB" := Fst "result" in
    let: "session_key" := Snd "result" in
    SOME ("vkB", ("timestamp", "session_key"))
  ).

Definition timestamp : val := λ: "cs",
  let: "timestamp" := Fst "cs" in
  !"timestamp".

Definition tick : val := λ: "cs",
  let: "timestamp" := Fst "cs" in
  "timestamp" <- (!"timestamp" + #1).

Definition session_key : val := λ: "cs",
  Snd "cs".

Definition send N : val := λ: "c" "cs" "t",
  let: "sk" := session_key "cs" in
  let: "m"  := senc N "sk" "t" in
  send "c" "m".

Definition make_handler (p : namespace * expr) : expr :=
  let N := p.1 in
  let: "handler" := p.2 in
  λ: "m", bind: "m" := untag N "m" in
          "handler" "m".

Lemma subst_make_handler var v p :
  subst var v (make_handler p) =
  make_handler (p.1, subst var v p.2).
Proof.
case: p => [N' handler] /=.
case: decide => [[_ not_shadow_handler]|shadow_handler //].
case: decide => [[_ not_shadow_m]|shadow_m //].
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

Definition select_body : val := rec: "loop" "m" "handlers" :=
  match: "handlers" with
    NONE => NONE
  | SOME "handlers" =>
    let: "handler" := Fst "handlers" in
    let: "handlers" := Snd "handlers" in
    match: "handler" "m" with
      NONE => "loop" "m" "handlers"
    | SOME "res" => SOME "res"
    end
  end.

Definition select_def (c cs : expr) handlers : expr :=
  (λ: "c" "cs" "handlers",
    let: "sk" := session_key "cs" in
    do_until (λ: <>,
      let: "m" := recv "c" in
      bind: "m" := open (key Open "sk") "m" in
      select_body "m" "handlers"
    ))%V c cs (make_handlers handlers).

Definition select_aux : base.seal select_def. by eexists _. Qed.
Definition select := unseal select_aux.
Lemma select_eq : select = select_def. Proof. exact: seal_eq. Qed.

Lemma subst_select var v c cs handlers :
  subst var v (select c cs handlers) =
  select (subst var v c) (subst var v cs)
         (map (λ p, (p.1, subst var v p.2)) handlers).
Proof.
by rewrite select_eq /select /= subst_make_handlers.
Qed.

Definition recv N : val := λ: "c" "cs" "f",
  let: "sk" := session_key "cs" in
  do_until (λ: <>,
    let: "m" := recv "c" in
    bind: "m" := sdec N "sk" "m" in
    "f" "m"
  ).

Definition close : val := λ: "c" "cs",
  let: "timestamp" := Fst "cs" in
  Free "timestamp".

End Connection.

End Connection.

Module Client.

Section Client.

Variable N : namespace.

Definition connect : val := λ: "c" "skA" "vkB",
  let: "cs" := Connection.connect N "c" "skA" "vkB" in
  Connection.send (N.@"init") "c" "cs" (TInt 0);;
  Connection.recv (N.@"ack_init") "c" "cs" (λ: <>,
    SOME "cs").

Definition send_store : val := λ: "c" "cs" "k" "v",
  let: "ts" := Connection.timestamp "cs" in
  Connection.tick "cs";;
  let: "m" := term_of_list [tint "ts"; "k"; "v"] in
  Connection.send (N.@"store") "c" "cs" "m".

Definition ack_store : val := λ: "c" "cs",
  let: "ts" := Connection.timestamp "cs" in
  Connection.recv (N.@"ack_store") "c" "cs" (λ: "m",
    guard: eq_term "m" (tint "ts") in
    SOME #()
  ).

Definition store : val := λ: "c" "cs" "k" "v",
  send_store "c" "cs" "k" "v";;
  ack_store "c" "cs".

Definition load : val := λ: "c" "cs" "k",
  let: "ts" := tint (Connection.timestamp "cs") in
  Connection.send (N.@"load") "c" "cs" (term_of_list ["ts"; "k"]);;
  Connection.recv (N.@"ack_load") "c" "cs" (λ: "resp",
    bind: "resp" := list_of_term "resp" in
    list_match: ["ts'"; "k'"; "t"] := "resp" in
    guard: eq_term "ts'" "ts" in
    guard: eq_term "k'" "k" in
    SOME "t"
  ).

Definition create : val := λ: "c" "cs" "k" "v",
  let: "ts" := Connection.timestamp "cs" in
  Connection.tick "cs";;
  let: "m"  := term_of_list [tint "ts"; "k"; "v"] in
  Connection.send (N.@"create") "c" "cs" "m";;
  Connection.recv (N.@"ack_create") "c" "cs" (λ: "resp",
    bind: "resp" :=  list_of_term "resp" in
    list_match: ["ts'"; "k'"; "v'"; "b"] := "resp" in
    guard: eq_term (tint "ts") "ts'" in
    guard: eq_term "k" "k'" in
    guard: eq_term "v" "v'" in
    SOME (eq_term "b" (tint #1))
  ).

Definition close : val := λ: "c" "cs",
  let: "ts" := Connection.timestamp "cs" in
  let: "m"  := tint "ts" in
  Connection.send (N.@"close") "c" "cs" "m";;
  Connection.recv (N.@"ack_close") "c" "cs" (λ: "resp",
    Connection.close "c" "cs";;
    SOME #()
  ).

End Client.

End Client.

Module Server.

Implicit Types N : namespace.

Definition start : val := λ: "k",
  let: "accounts" := SAList.new #() in
  ("k", "accounts").

Definition handle_store N : val :=
λ: "c" "cs" "db" "req",
  let: "timestamp" := Connection.timestamp "cs" in
  bind: "req" := list_of_term "req" in
  list_match: ["timestamp'"; "k"; "v"] := "req" in
  bind: "timestamp'" := to_int "timestamp'" in
  guard: "timestamp" = "timestamp'" in
  Connection.tick "cs";;
  SAList.insert "db" "k" "v";;
  Connection.send (N.@"ack_store") "c" "cs" (tint "timestamp'");;
  SOME #true.

(* FIXME: Should return an error when the key is not present *)
Definition handle_load N : val :=
λ: "c" "cs" "db" "req",
  let: "timestamp" := Connection.timestamp "cs" in
  bind: "req" := list_of_term "req" in
  list_match: ["timestamp'"; "k"] := "req" in
  bind: "timestamp'" := to_int "timestamp'" in
  guard: "timestamp" = "timestamp'" in
  bind: "data" := SAList.find "db" "k" in
  let: "m" := term_of_list [ tint "timestamp"; "k"; "data"] in
  Connection.send (N.@"ack_load") "c" "cs" "m";;
  SOME #true.

Definition handle_create N : val :=
λ: "c" "cs" "db" "req",
  let: "timestamp"   := Connection.timestamp "cs" in
  bind: "req" := list_of_term "req" in
  list_match: ["timestamp'"; "k"; "v"] := "req" in
  bind: "timestamp'" := to_int "timestamp'" in
  guard: "timestamp" = "timestamp'" in
  let: "success" :=
    match: SAList.find "db" "k" with
      SOME <> => #0
    | NONE =>
      SAList.insert "db" "k" "v";;
      Connection.tick "cs";;
      #1
    end in
  let: "m" := term_of_list [tint "timestamp"; "k"; "v"; tint "success"] in
  Connection.send (N.@"ack_create") "c" "cs" "m";;
  SOME #true.

Definition handle_close N : val :=
λ: "c" "cs" "db" "req",
  let: "timestamp"   := Connection.timestamp "cs" in
  bind: "timestamp'" := to_int "req" in
  guard: "timestamp" = "timestamp'" in
  Connection.send (N.@"ack_close") "c" "cs" (tint #0);;
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
  else (lock.release "lock";; Connection.close "c" "cs").

Definition wait_init N : val := λ: "c" "cs" "db" "lock",
  Connection.recv (N.@"init") "c" "cs" (λ: <>,
    Connection.send (N.@"ack_init") "c" "cs" (tint #0);;
    conn_handler N "c" "cs" "db" "lock";;
    SOME #()
  ).

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
  Fork (wait_init N "c" "cs" "db" "lock").

End Server.
