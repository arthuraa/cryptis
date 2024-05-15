From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.
From cryptis.store Require Import alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* FIXME: Maybe generalize this *)
Definition sess_recv N : val := λ: "c" "k" "f",
  do_until (λ: <>,
    let: "m" := recv "c" in
    bind: "m" := tsdec N "k" "m" in
    "f" "m"
  ).

Section SessRecv.

Context `{!cryptisGS Σ, !heapGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.
Implicit Types ok : bool.

(* FIXME: infer the invariant φ in a tactic, similarly to how iLöb works *)
Lemma wp_sess_recv E N c sk (f : val) φ Ψ :
  ↑cryptisN ⊆ E →
  channel c -∗
  minted sk -∗
  □ (∀ t,
      φ -∗
      public (TEnc sk (Spec.tag N t)) -∗
      WP f t @ E {{ v, ⌜v = NONEV⌝ ∗ φ ∨ ∃ v', ⌜v = SOMEV v'⌝ ∗ Ψ v' }}) -∗
  φ -∗ WP sess_recv N c (Spec.mkskey sk) f @ E {{ Ψ }}.
Proof.
iIntros "% #chan_c #s_sk #wp_f Hφ"; rewrite /sess_recv; wp_pures.
iRevert "Hφ". iApply wp_do_until; iIntros "!> Hφ". wp_pures.
wp_bind (recv _); iApply wp_recv => //.
iIntros "%t #p_t"; wp_pures.
wp_tsdec_eq t' e; wp_pures; eauto.
rewrite {}e {t}.
by iApply ("wp_f" with "Hφ").
Qed.

End SessRecv.

Module Client.

Section Client.

Variable N : namespace.

Definition connect : val := λ: "c" "skA" "pkA" "pkB",
  do_until (λ: <>,
    bind: "session_key" := pk_dh_init N "c" "skA" "pkA" "pkB" in
    let: "timestamp"  := ref #0 in
    let: "session_key" := mkskey (tag (nroot.@"keys".@"sym") "session_key") in
    send "c" (tsenc (N.@"init") "session_key" (TInt 0));;
    SOME ("timestamp", "session_key")
  ).

Definition get_timestamp : val := λ: "cs",
  let: "timestamp" := Fst "cs" in
  !"timestamp".

Definition incr_timestamp : val := λ: "cs",
  let: "timestamp" := Fst "cs" in
  "timestamp" <- (!"timestamp" + #1).

Definition get_session_key : val := λ: "cs",
  Snd "cs".

Definition send_store : val := λ: "c" "cs" "k" "v",
  let: "ts" := get_timestamp "cs" in
  incr_timestamp "cs";;
  let: "sk" := get_session_key "cs" in
  let: "m" := tsenc (N.@"store") "sk" (term_of_list [tint "ts"; "k"; "v"]) in
  send "c" "m".

Definition ack_store : val := λ: "c" "cs",
  let: "ts" := get_timestamp "cs" in
  let: "sk" := get_session_key "cs" in
  sess_recv (N.@"ack_store") "c" "sk" (λ: "m",
    assert: eq_term "m" (tint "ts") in
    SOME #()
  ).

Definition store : val := λ: "c" "cs" "k" "v",
  send_store "c" "cs" "k" "v";;
  ack_store "c" "cs".

Definition load : val := λ: "c" "cs" "k",
  let: "ts" := tint (get_timestamp "cs") in
  let: "sk" := get_session_key "cs" in
  send "c" (tsenc (N.@"load") "sk" (term_of_list ["ts"; "k"]));;
  sess_recv (N.@"ack_load") "c" "sk" (λ: "resp",
    bind: "resp" := list_of_term "resp" in
    list_match: ["ts'"; "k'"; "t"] := "resp" in
    assert: eq_term "ts'" "ts" in
    assert: eq_term "k'" "k" in
    SOME "t"
  ).

Definition create : val := λ: "c" "cs" "k" "v",
  let: "ts" := get_timestamp "cs" in
  let: "sk" := get_session_key "cs" in
  let: "m"  := term_of_list [tint "ts"; "k"; "v"] in
  let: "m"  := tsenc (N.@"create") "sk" "m" in
  send "c" "m";;
  sess_recv (N.@"ack_create") "c" "sk" (λ: "resp",
    bind: "resp" :=  list_of_term "resp" in
    list_match: ["ts'"; "k'"; "v'"; "b"] := "resp" in
    assert: eq_term (tint "ts") "ts'" in
    assert: eq_term "k" "k'" in
    assert: eq_term "v" "v'" in
    SOME (eq_term "b" (tint #1))
  ).

End Client.

End Client.

Module Server.

Implicit Types N : namespace.

Definition handle_store N : val :=
λ: "c" "ss" "req",
  let: "timestamp" := Fst (Fst "ss") in
  let: "session_key" := Snd (Fst "ss") in
  let: "db" := Snd "ss" in
  bind: "req" := tsdec (N.@"store") "session_key" "req" in
  bind: "req" := list_of_term "req" in
  list_match: ["timestamp'"; "k"; "v"] := "req" in
  bind: "timestamp'" := to_int "timestamp'" in
  assert: !"timestamp" = "timestamp'" in
  "timestamp" <- !"timestamp" + #1;;
  "db" <- AList.insert !"db" "k" "v";;
  send "c" (tsenc (N.@"ack_store") "session_key" (tint "timestamp'"));;
  SOME #().

Definition handle_load N : val :=
λ: "c" "ss" "req",
  let: "timestamp" := ! (Fst (Fst "ss")) in
  let: "session_key" := Snd (Fst "ss") in
  let: "db" := ! (Snd "ss") in
  bind: "req" := tsdec (N.@"load") "session_key" "req" in
  bind: "req" := list_of_term "req" in
  list_match: ["timestamp'"; "k"] := "req" in
  bind: "timestamp'" := to_int "timestamp'" in
  assert: "timestamp" = "timestamp'" in
  bind: "data" := AList.find "db" "k" in
  let: "m" := term_of_list [ tint "timestamp"; "k"; "data"] in
  send "c" (tsenc (N.@"ack_load") "session_key" "m");;
  SOME #().

Definition handle_create N : val :=
λ: "c" "ss" "req",
  let: "ltimestamp"  := Fst (Fst "ss") in
  let: "timestamp"   := !"ltimestamp"  in
  let: "session_key" := Snd (Fst "ss") in
  let: "ldb" := Snd "ss" in
  let: "db"  := !"ldb" in
  bind: "req" := tsdec (N.@"create") "session_key" "req" in
  bind: "req" := list_of_term "req" in
  list_match: ["timestamp'"; "k"; "v"] := "req" in
  bind: "timestamp'" := to_int "timestamp'" in
  assert: "timestamp" = "timestamp'" in
  let: "success" :=
    match: AList.find "db" "k" with
      SOME <> => #0
    | NONE =>
      "ldb" <- AList.insert "db" "k" "v";;
      "ltimestamp" <- "timestamp" + #1;;
      #1
    end in
  let: "m" := term_of_list [tint "timestamp"; "k"; "v"; tint "success"] in
  send "c" (tsenc (N.@"ack_create") "session_key" "m");;
  SOME #().

Definition conn_handler_body N : val :=
λ: "c" "ss",
  let: "m" := recv "c" in
  match: handle_store N "c" "ss" "m" with
    SOME <> => #()
  | NONE => match: handle_load N "c" "ss" "m" with
    SOME <> => #()
  | NONE => match: handle_create N "c" "ss" "m" with
    SOME <> => #()
  | NONE => #()
  end end end.

Definition conn_handler N : val :=
rec: "loop" "c" "ss" :=
  conn_handler_body N "c" "ss";;
  "loop" "c" "ss".

Definition wait_init N : val :=
  λ: "c" "session_key",
  sess_recv (N.@"init") "c" "session_key" (λ: <>,
    let: "db" := ref (AList.empty #()) in
    conn_handler N "c" (ref #0, "session_key", "db")
  ).

Definition listen N : val :=
rec: "loop" "c" "secret_key" "public_key" :=
  match: pk_dh_resp N "c" "secret_key" "public_key" with
    NONE =>
    "loop" "c" "secret_key" "public_key"
  | SOME "res" =>
    (* Unused for now *)
    let: "client_key" := Fst "res" in
    let: "session_key"  := mkskey (tag (nroot.@"keys".@"sym") (Snd "res")) in
    Fork (wait_init N "c" "session_key");;
    "loop" "c" "secret_key" "public_key"
  end.

End Server.
