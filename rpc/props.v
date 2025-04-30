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

Definition clock k N n :=
  term_own k N (to_frac_agree (1 / 2) n).

Lemma clock_alloc k N E :
  ↑N ⊆ E →
  term_token k E ==∗
  clock k N 0 ∗
  clock k N 0 ∗
  term_token k (E ∖ ↑N).
Proof.
iIntros "%sub token".
iMod (term_own_alloc N (to_frac_agree 1 0) with "token")
  as "[own token]" => //.
iFrame. rewrite -Qp.half_half frac_agree_op.
iDestruct "own" as "[??]". by iFrame.
Qed.

Lemma clock_agree k N n m :
  clock k N n -∗
  clock k N m -∗
  ⌜n = m⌝.
Proof.
iIntros "own1 own2".
iPoseProof (term_own_valid_2 with "own1 own2") as "%valid".
rewrite frac_agree_op_valid_L in valid.
by case: valid.
Qed.

Lemma clock_update p k N n m :
  clock k N n -∗
  clock k N m ==∗
  clock k N p ∗ clock k N p.
Proof.
iIntros "own1 own2". rewrite /clock.
iMod (term_own_update_2 with "own1 own2") as "[own1 own2]".
{ apply: (frac_agree_update_2 _ _ _ _ p).
  by rewrite Qp.half_half. }
by iFrame.
Qed.

Variable N : namespace.

Definition never_connected kI kR : iProp :=
  term_token kR (↑N.@"server".@kI).

Lemma first_connection kI kR :
  never_connected kI kR ==∗ □ ¬ never_connected kI kR.
Proof.
iIntros "token".
iMod (term_meta_set _ () with "token") as "#meta"; eauto.
iIntros "!> !> contra".
by iDestruct (term_meta_token with "contra meta") as "[]".
Qed.

Definition client_clock kI kR n : iProp :=
  clock kI (N.@"client".@kR.@"clock".@1) n.

Definition server_clock' kI kR n : iProp :=
  clock kI (N.@"client".@kR.@"clock".@2) n.

Definition tick kI kR n : iProp :=
  client_clock kI kR (S n) ∗
  server_clock' kI kR n ∗
  (⌜n = 0⌝ ∗ server_clock' kI kR 0 ∨ □ ¬ never_connected kI kR).

Definition tock kI kR n : iProp :=
  client_clock kI kR n ∗
  server_clock' kI kR n ∗
  (⌜n = 0⌝ ∗ server_clock' kI kR 0 ∨ □ ¬ never_connected kI kR).

Definition server_clock kI kR n : iProp :=
  ⌜n = 0⌝ ∗ never_connected kI kR ∨
  ⌜n ≠ 0⌝ ∗ server_clock' kI kR n ∗ □ ¬ never_connected kI kR.

Lemma client_clock_tock kI kR n m :
  client_clock kI kR n -∗
  tock kI kR m -∗
  ⌜n = m⌝.
Proof.
iIntros "c1 (c2 & _)". iApply (clock_agree with "c1 c2").
Qed.

Lemma client_clock_alloc kI kR E :
  ↑N.@"client".@kR.@"clock" ⊆ E →
  term_token kI E ==∗
  client_clock kI kR 0 ∗ tock kI kR 0 ∗
  term_token kI (E ∖ ↑N.@"client".@kR.@"clock").
Proof.
iIntros "%sub token".
iMod (clock_alloc kI ( N:= N.@"client".@kR.@"clock".@1) with "token")
  as "(? & ? & token)"; first solve_ndisj.
iFrame.
iMod (clock_alloc kI ( N:= N.@"client".@kR.@"clock".@2) with "token")
  as "(c1 & c2 & token)"; first solve_ndisj.
iModIntro. iFrame.
iSplitL "c1".
- iLeft. by iFrame.
- iApply (term_token_drop with "token"). solve_ndisj.
Qed.

Lemma server_clock_alloc kI kR E :
  ↑N.@"server".@kI ⊆ E →
  term_token kR E ==∗
  server_clock kI kR 0 ∗ term_token kR (E ∖ ↑N.@"server".@kI).
Proof.
iIntros "%sub token".
rewrite term_token_difference //. iDestruct "token" as "[??]".
iFrame. iModIntro. iLeft. by iFrame.
Qed.

Lemma tock_tick kI kR n m :
  client_clock kI kR n -∗
  tock kI kR m ==∗
  ⌜m = n⌝ ∗
  client_clock kI kR (S n) ∗
  tick kI kR n.
Proof.
iIntros "client1 (client2 & server1 & ?)".
iPoseProof (clock_agree with "client1 client2") as "<-".
iFrame.
iMod (clock_update (S n) with "client1 client2") as "[??]".
by iFrame.
Qed.

Lemma tick_tock kI kR n m :
  server_clock kI kR n -∗
  tick kI kR m ==∗
  ⌜m = n⌝ ∗
  server_clock kI kR (S n) ∗
  tock kI kR (S n).
Proof.
iIntros "server tick".
iDestruct "server" as "[(-> & never)|(%n0 & s1 & #first1)]";
iDestruct "tick" as "(c1 & s2 & [(-> & s3)| #first2])".
- iMod (first_connection with "never") as "#first".
  iMod (clock_update 1 with "s2 s3") as "[s2 s3]".
  iModIntro. iSplit => //. iFrame.
  iSplitL "s2".
  + iRight. by iSplit; iFrame.
  + by iRight.
- by iPoseProof ("first2" with "never") as "[]".
- iPoseProof (clock_agree with "s1 s2") as "->".
  iModIntro. by iSplit => //.
- iPoseProof (clock_agree with "s1 s2") as "<-".
  iMod (clock_update (S n) with "s1 s2") as "[s1 s2]".
  iModIntro. iFrame. iSplit => //.
  iSplitL; last by eauto.
  iRight. iFrame. by iSplit.
Qed.

Definition client_disconnected kI kR n : iProp :=
  Conn.failure kI kR ∨
  client_clock kI kR n ∗ tock kI kR n.

Definition client_connected kI kR cs n : iProp :=
  Conn.connected kI kR Init cs ∗
  release_token (si_init_share cs) ∗
  (compromised_session Init cs ∨ client_clock kI kR n ∗ tock kI kR n).

Lemma client_connected_ok kI kR cs n :
  client_connected kI kR cs n -∗
  secret kI -∗
  secret kR -∗
  sign_key kI -∗
  sign_key kR -∗
  ◇ □ ¬ compromised_session Init cs.
Proof.
iIntros "(conn & _)".
by iApply (Conn.connected_ok with "conn").
Qed.

Lemma client_connected_keys kI kR cs n :
  client_connected kI kR cs n -∗
  ⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝.
Proof.
iIntros "(conn & _)".
by iPoseProof (Conn.connected_keyE with "conn") as "(-> & -> & _)".
Qed.

Definition server_disconnected kI kR n : iProp :=
  Conn.failure kI kR ∨ server_clock kI kR n.

Definition server_connected kI kR cs n : iProp :=
  Conn.connected kI kR Resp cs ∗
  release_token (si_resp_share cs) ∗
  (compromised_session Resp cs ∨ server_clock kI kR n).

Lemma server_connected_ok kI kR cs n :
  server_connected kI kR cs n -∗
  secret kI -∗
  secret kR -∗
  sign_key kI -∗
  sign_key kR -∗
  ◇ □ ¬ compromised_session Resp cs.
Proof.
iIntros "(conn & _)".
by iApply (Conn.connected_ok with "conn").
Qed.

Lemma server_connected_keys kI kR cs n :
  server_connected kI kR cs n -∗
  ⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝.
Proof.
iIntros "(conn & _)".
by iPoseProof (Conn.connected_keyE with "conn") as "(-> & -> & _)".
Qed.

Lemma client_alloc kI kR E :
  ↑N.@"client".@kR.@"clock" ⊆ E →
  term_token kI E ={⊤}=∗
  client_disconnected kI kR 0 ∗
  term_token kI (E ∖ ↑N.@"client".@kR.@"clock").
Proof.
iIntros "%sub kI_token".
rewrite (term_token_difference _ _ _ sub).
iDestruct "kI_token" as "[kI_token ?]". iFrame.
iMod (client_clock_alloc kI (kR := kR)
       with "kI_token") as "(c1 & c2 & token)" => //.
iModIntro. iRight. iFrame.
Qed.

Lemma server_alloc kI kR E :
  ↑N.@"server".@kI ⊆ E →
  term_token kR E ==∗
  server_disconnected kI kR 0 ∗
  term_token kR (E ∖ ↑N.@"server".@kI).
Proof.
iIntros "%sub token".
rewrite (term_token_difference _ (↑N.@"server".@kI)) //.
iDestruct "token" as "[token ?]". iFrame.
iModIntro. iRight. iLeft. by eauto.
Qed.

Definition call_pred φ kI kR si ts : iProp :=
  ∃ n, tick kI kR n ∗ φ kI kR si n ts.

Definition resp_pred φ kI kR si ts : iProp :=
  ∃ n, tock kI kR (S n) ∗ φ kI kR si n ts.

Definition rpc_pred (s : string) φ ψ : iProp :=
  seal_pred (N.@s.@"call") (Conn.conn_pred Init (call_pred φ)) ∗
  seal_pred (N.@s.@"resp") (Conn.conn_pred Resp (resp_pred ψ)).

Lemma rpc_pred_set (s : string) φ ψ E :
  ↑N.@s ⊆ E →
  seal_pred_token E ==∗
  rpc_pred s φ ψ ∗ seal_pred_token (E ∖ ↑N.@s).
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
  seal_pred (N.@"rpc".@"error") (Conn.conn_pred Resp error_pred) ∗
  seal_pred (N.@"rpc".@"close".@"call") (Conn.conn_pred Init close_pred) ∗
  seal_pred (N.@"rpc".@"close".@"resp") (Conn.conn_pred Resp ack_close_pred) ∗
  Conn.ctx  (N.@"rpc".@"auth").

Lemma ctx_alloc E :
  ↑N.@"rpc" ⊆ E →
  seal_pred_token E ==∗
  ctx ∗ seal_pred_token (E ∖ ↑N.@"rpc").
Proof.
iIntros "%sub token".
rewrite (seal_pred_token_difference (↑N.@"rpc")); try solve_ndisj.
iDestruct "token" as "[token ?]". iFrame.
iMod (seal_pred_set (N.@"rpc".@"error") with "token")
  as "[error token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"rpc".@"close".@"call") with "token")
  as "[init token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"rpc".@"close".@"resp") with "token")
  as "[ack_init token]"; try solve_ndisj.
iFrame.
iMod (iso_dh_ctx_alloc (N.@"rpc".@"auth") with "token")
  as "#iso_dh"; try solve_ndisj.
Qed.

Ltac solve_ctx :=
  iIntros "ctx"; repeat (
    try solve [iApply "ctx"];
    iDestruct "ctx" as "[H ctx]";
    first [iApply "H" | iClear "H"]
  ).

Lemma ctx_error :
  ctx -∗
  seal_pred (N.@"rpc".@"error") (Conn.conn_pred Resp error_pred).
Proof. solve_ctx. Qed.

Lemma ctx_close :
  ctx -∗
  seal_pred (N.@"rpc".@"close".@"call") (Conn.conn_pred Init close_pred).
Proof. solve_ctx. Qed.

Lemma ctx_ack_close :
  ctx -∗
  seal_pred (N.@"rpc".@"close".@"resp") (Conn.conn_pred Resp ack_close_pred).
Proof. solve_ctx. Qed.

Lemma ctx_conn_ctx : ctx -∗ Conn.ctx (N.@"rpc".@"auth").
Proof. solve_ctx. Qed.

End Defs.

End Props.

Arguments Props.rpcGS Σ : clear implicits.
