From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis primitives tactics.
From cryptis Require Import role iso_dh conn.
From cryptis.rpc Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Props.

Definition clockR := dfrac_agreeR natO.

Class rpcGS Σ := RpcGS {
  rpcGS_clock  : inG Σ clockR;
}.

Local Existing Instance rpcGS_clock.

Definition rpcΣ := #[
  GFunctor clockR
].

Global Instance subG_rpcGS Σ : subG rpcΣ Σ → rpcGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !rpcGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (kI kR kS t : term) (ts : list term).
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types (ok : Prop) (failed : bool).
Implicit Types si : sess_info.

Definition client_connected kI kR cs : iProp :=
  Conn.connected kI kR Init cs ∗
  release_token (si_init_share cs).

Lemma client_connected_ok kI kR cs :
  client_connected kI kR cs -∗
  secret kI -∗
  secret kR -∗
  sign_key kI -∗
  sign_key kR -∗
  ◇ □ ¬ compromised_session Init cs.
Proof.
iIntros "(conn & _)".
by iApply (Conn.connected_ok with "conn").
Qed.

Lemma client_connected_keys kI kR cs :
  client_connected kI kR cs -∗
  ⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝.
Proof.
iIntros "(conn & _)".
by iPoseProof (Conn.connected_keyE with "conn") as "(-> & -> & _)".
Qed.

Definition server_connected kI kR cs : iProp :=
  Conn.connected kI kR Resp cs ∗
  release_token (si_resp_share cs).

Lemma server_connected_ok kI kR cs :
  server_connected kI kR cs -∗
  secret kI -∗
  secret kR -∗
  sign_key kI -∗
  sign_key kR -∗
  ◇ □ ¬ compromised_session Resp cs.
Proof.
iIntros "(conn & _)".
by iApply (Conn.connected_ok with "conn").
Qed.

Lemma server_connected_keys kI kR cs :
  server_connected kI kR cs -∗
  ⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝.
Proof.
iIntros "(conn & _)".
by iPoseProof (Conn.connected_keyE with "conn") as "(-> & -> & _)".
Qed.

Definition rpc_pred N (s : string) φ ψ : iProp :=
  seal_pred (N.@s.@"call") (Conn.conn_pred Init φ) ∗
  seal_pred (N.@s.@"resp") (Conn.conn_pred Resp ψ).

Lemma rpc_pred_set N (s : string) φ ψ E :
  ↑N.@s ⊆ E →
  seal_pred_token E ==∗
  rpc_pred N s φ ψ ∗ seal_pred_token (E ∖ ↑N.@s).
Proof.
iIntros "%sub token".
iMod (seal_pred_set (N.@s.@"call") with "token") as "[? token]";
  first by solve_ndisj. iFrame.
iMod (seal_pred_set (N.@s.@"resp") with "token") as "[? token]";
  first by solve_ndisj. iFrame.
iModIntro. iApply (seal_pred_token_drop with "token").
solve_ndisj.
Qed.

Definition error_pred kI kR si ts : iProp := True.

Definition close_pred kI kR si ts : iProp :=
  released (si_init_share si).

Definition ack_close_pred kI kR si ts : iProp :=
  False.

Definition ctx : iProp :=
  seal_pred (rpcN.@"error") (Conn.conn_pred Resp error_pred) ∗
  seal_pred (rpcN.@"close".@"call") (Conn.conn_pred Init close_pred) ∗
  seal_pred (rpcN.@"close".@"resp") (Conn.conn_pred Resp ack_close_pred) ∗
  iso_dh_ctx.

Lemma ctx_alloc E :
  ↑rpcN ⊆ E →
  seal_pred_token E -∗
  iso_dh_ctx ==∗
  ctx ∗ seal_pred_token (E ∖ ↑rpcN).
Proof.
iIntros "%sub token #?".
rewrite (seal_pred_token_difference (↑rpcN)); try solve_ndisj.
iDestruct "token" as "[token ?]". iFrame.
iMod (seal_pred_set (rpcN.@"error") with "token")
  as "[error token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (rpcN.@"close".@"call") with "token")
  as "[init token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (rpcN.@"close".@"resp") with "token")
  as "[ack_init token]"; try solve_ndisj.
Qed.

Ltac solve_ctx :=
  iIntros "ctx"; repeat (
    try solve [iApply "ctx"];
    iDestruct "ctx" as "[H ctx]";
    first [iApply "H" | iClear "H"]
  ).

Lemma ctx_error :
  ctx -∗
  seal_pred (rpcN.@"error") (Conn.conn_pred Resp error_pred).
Proof. solve_ctx. Qed.

Lemma ctx_close :
  ctx -∗
  seal_pred (rpcN.@"close".@"call") (Conn.conn_pred Init close_pred).
Proof. solve_ctx. Qed.

Lemma ctx_ack_close :
  ctx -∗
  seal_pred (rpcN.@"close".@"resp") (Conn.conn_pred Resp ack_close_pred).
Proof. solve_ctx. Qed.

Lemma ctx_conn_ctx : ctx -∗ iso_dh_ctx.
Proof. solve_ctx. Qed.

End Defs.

End Props.

Arguments Props.rpcGS Σ : clear implicits.
