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

Definition clock kI kR n :=
  term_own kI (N.@"client".@kR.@"clock") (to_frac_agree (1 / 2) n).

Lemma clock_alloc kI kR E :
  ↑N.@"client".@kR.@"clock" ⊆ E →
  term_token kI E ==∗
  clock kI kR 0 ∗
  clock kI kR 0 ∗
  term_token kI (E ∖ ↑N.@"client".@kR.@"clock").
Proof.
iIntros "%sub token".
iMod (term_own_alloc (N.@"client".@kR.@"clock") (to_frac_agree 1 0)
       with "token") as "[own token]" => //.
iFrame. rewrite -Qp.half_half frac_agree_op.
iDestruct "own" as "[??]". by iFrame.
Qed.

Lemma clock_agree kI kR n m :
  clock kI kR n -∗
  clock kI kR m -∗
  ⌜n = m⌝.
Proof.
iIntros "own1 own2".
iPoseProof (term_own_valid_2 with "own1 own2") as "%valid".
rewrite frac_agree_op_valid_L in valid.
by case: valid.
Qed.

Lemma clock_update p kI kR n m :
  clock kI kR n -∗
  clock kI kR m ==∗
  clock kI kR p ∗ clock kI kR p.
Proof.
iIntros "own1 own2".
rewrite /clock.
iMod (term_own_update_2 with "own1 own2") as "[own1 own2]".
{ apply: (frac_agree_update_2 _ _ _ _ p).
  by rewrite Qp.half_half. }
by iFrame.
Qed.

Definition client_clock kI kR n : iProp :=
  clock kI kR n ∗
  ((□ ¬ never_connected kI kR) ∨ clock kI kR 0).

Definition server_clock kI kR n : iProp :=
  ⌜n = 0⌝ ∗ never_connected kI kR ∨
  ⌜n ≠ 0⌝ ∗ clock kI kR n.

Lemma clocks_agree kI kR n m :
  client_clock kI kR n -∗
  server_clock kI kR m -∗
  ⌜n = m⌝.
Proof.
iIntros "[cI [#cS1|cS1]] [[-> cS2]|[% cS2]]".
- by iDestruct ("cS1" with "cS2") as "[]".
- by iPoseProof (clock_agree with "cI cS2") as "%".
- by iPoseProof (clock_agree with "cI cS1") as "->".
- by iPoseProof (clock_agree with "cS1 cS2") as "<-".
Qed.

Lemma clocks_update kI kR n m :
  client_clock kI kR n -∗
  server_clock kI kR m ==∗
  ⌜n = m⌝ ∗
  client_clock kI kR (S n) ∗
  server_clock kI kR (S n).
Proof.
iIntros "[cI [#cS1|cS1]] [[-> cS2]|[% cS2]]".
- by iDestruct ("cS1" with "cS2") as "[]".
- iPoseProof (clock_agree with "cI cS2") as "%".
  iMod (clock_update (S n) with "cI cS2") as "[cI cS2]".
  iModIntro. iSplit => //. iFrame.
  iSplitR; first by eauto.
  iRight. iFrame. by eauto.
- iPoseProof (clock_agree with "cI cS1") as "->".
  iMod (first_connection with "cS2") as "#?".
  iMod (clock_update 1 with "cI cS1") as "[cI cS1]".
  iModIntro. iSplit => //. iFrame.
  iSplitR; first by eauto. by iRight; iFrame.
- by iPoseProof (clock_agree with "cS1 cS2") as "<-".
Qed.

Definition client_disconnected kI kR n : iProp :=
  Conn.failure kI kR ∨ client_clock kI kR n.

Definition client_connected kI kR cs n : iProp := ∃ n1 n0,
  ⌜n = (n0 + n1)%nat⌝ ∗
  Conn.connected kI kR Init cs n1 n1 ∗
  term_meta (si_init_share cs) (isoN.@"conn".@"beg") n0 ∗
  release_token (si_init_share cs) ∗
  (compromised_session Init cs ∨ client_clock kI kR n).

Lemma client_connected_ok kI kR cs n :
  client_connected kI kR cs n -∗
  secret kI -∗
  secret kR -∗
  sign_key kI -∗
  sign_key kR -∗
  ◇ □ ¬ compromised_session Init cs.
Proof.
iIntros "(% & % & % & conn & _)".
by iApply (Conn.connected_ok with "conn").
Qed.

Lemma client_connected_keys kI kR cs n :
  client_connected kI kR cs n -∗
  ⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝.
Proof.
iIntros "(% & % & % & conn & _)".
by iPoseProof (Conn.connected_keyE with "conn") as "(-> & -> & _)".
Qed.

Definition server_disconnected kI kR n : iProp :=
  Conn.failure kI kR ∨ server_clock kI kR n.

Definition server_connected kI kR cs n : iProp := ∃ n1 n0,
  ⌜n = (n0 + n1)%nat⌝ ∗
  Conn.connected kI kR Resp cs n1 n1 ∗
  term_meta (si_resp_share cs) (isoN.@"conn".@"beg") n0 ∗
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
iIntros "(% & % & % & conn & _)".
by iApply (Conn.connected_ok with "conn").
Qed.

Lemma server_connected_keys kI kR cs n :
  server_connected kI kR cs n -∗
  ⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝.
Proof.
iIntros "(% & % & % & conn & _)".
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
iMod (clock_alloc kI (kR := kR)
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

Definition call_pred φ kI kR si n1 ts : iProp :=
  ∃ n0,
    term_meta (si_init_share si) (isoN.@"conn".@"beg") n0 ∗
    client_clock kI kR (n0 + n1) ∗
    φ kI kR si (n0 + n1) ts.

Definition resp_pred φ kI kR si n1 ts : iProp :=
  ∃ n0,
    term_meta (si_init_share si) (isoN.@"conn".@"beg") n0 ∗
    client_clock kI kR (n0 + S n1) ∗
    φ kI kR si (n0 + n1) ts.

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

Definition error_pred kI kR si n1 ts : iProp := True.

Definition close_pred kI kR si n1 ts : iProp :=
  released (si_init_share si).

Definition ack_close_pred kI kR si n1 ts : iProp :=
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
