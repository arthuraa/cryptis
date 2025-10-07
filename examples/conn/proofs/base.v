From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac numbers.
From iris.algebra Require Import max_prefix_list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term cryptis primitives tactics role.
From cryptis.lib Require Import saved_prop.
From cryptis.examples Require Import iso_dh gen_conn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation connN := (nroot.@"conn").

Record params Σ := Params {
  msg_inv : sign_key → sign_key → sess_info → role → term → iProp Σ;
}.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !GenConn.connGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (kS t : term) (ts : list term).
Implicit Types (skI skR : sign_key).
Implicit Types n m : nat.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types (ok : Prop) (failed : bool).
Implicit Types (si : sess_info) (rl : role).
Implicit Types (ps : params Σ).

Definition gen_conn_params ps : GenConn.params Σ := {|
  GenConn.chan_inv := λ skI skR si tsI tsR,
    ([∗ list] t ∈ tsI, msg_inv ps skI skR si Init t) ∗
    ([∗ list] t ∈ tsR, msg_inv ps skI skR si Resp t);
|}%I.

Local Coercion gen_conn_params : params >-> GenConn.params.

Definition connected ps skI skR rl cs : iProp :=
  GenConn.connected ps skI skR rl cs.

Lemma connected_public_key ps skI skR rl cs :
  connected ps skI skR rl cs -∗
  release_token (si_share_of rl cs) -∗
  public (si_key cs) -∗
  ◇ compromised cs.
Proof. exact: GenConn.connected_public_key. Qed.

Lemma connected_public_key_or ps skI skR rl cs P :
  connected ps skI skR rl cs -∗
  release_token (si_share_of rl cs) -∗
  public (si_key cs) ∨ P -∗
  connected ps skI skR rl cs ∗
  release_token (si_share_of rl cs) ∗
  ◇ (compromised cs ∨ P).
Proof. exact: GenConn.connected_public_key_or. Qed.

Lemma connected_released_session ps skI skR rl cs :
  connected ps skI skR rl cs -∗
  □ (▷ released_session cs → public (si_key cs)).
Proof. exact: GenConn.connected_released_session. Qed.

Lemma connected_keyE ps skI skR rl cs :
  connected ps skI skR rl cs -∗
  ⌜skI = si_init cs⌝ ∗ ⌜skR = si_resp cs⌝ ∗ ⌜rl = GenConn.cs_role cs⌝.
Proof. exact: GenConn.connected_keyE. Qed.

Lemma connected_ok ps skI skR rl cs :
  connected ps skI skR rl cs -∗
  secret skI -∗
  secret skR -∗
  ◇ session_ok cs.
Proof. exact: GenConn.connected_ok. Qed.

Lemma session_failed_failure si :
  compromised si  ⊢ GenConn.failure (si_init si) (si_resp si).
Proof. exact: GenConn.session_failed_failure. Qed.

Lemma connected_failure ps skI skR rl cs :
  connected ps skI skR rl cs -∗
  release_token (si_share_of rl cs) -∗
  public (si_key cs) -∗
  ◇ GenConn.failure skI skR.
Proof. exact: GenConn.connected_failure. Qed.

Definition pre_ctx `{!iso_dhGS Σ} : iProp :=
  GenConn.pre_ctx.

Lemma pre_ctx_alloc `{!iso_dhGS Σ} E :
  ↑connN ⊆ E →
  iso_dh_ctx -∗
  seal_pred_token SENC E ==∗
  pre_ctx ∗ seal_pred_token SENC (E ∖ ↑connN).
Proof. exact: GenConn.pre_ctx_alloc. Qed.

Definition ctx `{!iso_dhGS Σ} N ps : iProp :=
  GenConn.ctx N ps.

Lemma ctx_alloc `{!iso_dhGS Σ} N ps E :
  ↑N ⊆ E →
  pre_ctx -∗
  iso_dh_token E ==∗
  ctx N ps ∗ iso_dh_token (E ∖ ↑N).
Proof. exact: GenConn.ctx_alloc. Qed.

End Defs.
