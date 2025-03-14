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
From cryptis Require Import role iso_dh.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Props.

Record state := State {
  cs_si   :> sess_info;
  cs_ts   :  loc;
  cs_role :  role;
}.

Definition cs_share cs := si_share_of (cs_role cs) cs.

#[global]
Instance cs_repr : Repr state :=
  λ s, (#(cs_ts s), si_key s)%V.

Definition clockR := dfrac_agreeR natO.

Class connGS Σ := ConnGS {
  connGS_clock  : inG Σ clockR;
}.

Local Existing Instance connGS_clock.

Definition connΣ := #[
  GFunctor clockR
].

Global Instance subG_connGS Σ : subG connΣ Σ → connGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !connGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : state).
Implicit Types (kI kR kS t : term) (ts : list term).
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types (ok : Prop) (failed : bool).
Implicit Types si : sess_info.

Variable N : namespace.

Definition failure kI kR : iProp :=
  compromised_key kI ∨ compromised_key kR.

Definition wf_sess_info rl si : iProp :=
  minted (si_key si) ∗
  senc_key (si_key si) ∗
  session rl si.

#[global]
Instance wf_sess_info_persistent rl si : Persistent (wf_sess_info rl si).
Proof. apply _. Qed.

Definition never_connected kI kR : iProp :=
  term_token kR (↑N.@"server".@kI).

Lemma never_connected_switch kI kR Q : ⊢ switch (never_connected kI kR) Q.
Proof. apply term_token_switch. Qed.

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

Definition server_clock_ready kI kR :=
  escrow nroot (never_connected kI kR)
    (clock kI kR 0).

Definition client_disconnected kI kR n : iProp :=
  server_clock_ready kI kR ∗
  (failure kI kR ∨ clock kI kR n).

Definition client_disconnecting kI kR cs : iProp :=
  ⌜cs_role cs = Init⌝ ∗
  server_clock_ready kI kR ∗
  term_token (si_init_share cs) (↑isoN.@"end").

Definition connected' kI kR cs b n n0 : iProp :=
  ⌜si_init cs = kI⌝ ∗
  ⌜si_resp cs = kR⌝ ∗
  wf_sess_info (cs_role cs) cs ∗
  (if b then released (cs_share cs) else release_token (cs_share cs)) ∗
  cs_ts cs ↦ #n ∗
  (compromised_session (cs_role cs) cs ∨
     term_meta (si_init_share cs) (isoN.@"beginning") n0).

Definition connected kI kR cs n : iProp :=
  ∃ n' n0, ⌜n = (n' + n0)%nat⌝ ∗
           term_meta (cs_share cs) (isoN.@"beginning") n0 ∗
           connected' kI kR cs false n' n0.

Lemma connected_keyE kI kR cs n :
  connected kI kR cs n -∗
  ⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝.
Proof. by iIntros "(% & % & % & _ & -> & -> & _)". Qed.

Definition client_token kI kR cs : iProp :=
  ⌜cs_role cs = Init⌝ ∗
  server_clock_ready kI kR ∗
  term_token (si_init_share cs) (↑isoN.@"end").

Definition client_connecting cs n0 : iProp :=
  let kI := si_init cs in
  let kR := si_resp cs in
  server_clock_ready kI kR ∗
  wf_sess_info Init cs ∗
  term_meta  (si_init_share cs) (isoN.@"beginning") n0 ∗
  term_token (si_init_share cs) (↑isoN.@"end").

Definition conn_ready si n :=
  escrow nroot
         (term_token (si_resp_share si) (↑isoN.@"begin"))
         (clock (si_init si) (si_resp si) n).

Lemma client_connectedI cs n0 :
  cs_role cs = Init →
  client_connecting cs n0 -∗
  cs_ts cs ↦ #0%nat -∗
  release_token (si_init_share cs) ={⊤}=∗
  ▷ (connected (si_init cs) (si_resp cs) cs n0 ∗
     client_token (si_init cs) (si_resp cs) cs).
Proof.
iIntros "%e_rl (#server & #? & #? & ?) ts rel".
rewrite /connected /connected' /client_token /cs_share e_rl /=.
iFrame. do 2!iModIntro. iSplit; last by do 4!iSplit => //.
iExists n0. do 4!iSplit => //; eauto.
Qed.

Lemma connected_ok kI kR cs n :
  connected kI kR cs n -∗
  secret kI -∗
  secret kR -∗
  sign_key kI -∗
  sign_key kR -∗
  ◇ □ ¬ compromised_session (cs_role cs) cs.
Proof.
iIntros "(% & % & % & _ & conn) s_kI s_kR #signI #signR".
iDestruct "conn" as "(<- & <- & #conn & rel & _)".
iDestruct "conn" as "(m_k & s_k & sess)".
by iApply (session_not_compromised with "[//] s_kI s_kR").
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
iMod (@clock_alloc kI kR with "kI_token") as "(c1 & c2 & token)" => //.
iAssert (|={⊤}=> server_clock_ready kI kR)%I
  with "[c1]" as ">#server".
{ iApply (escrowI with "c1").
  iApply never_connected_switch. }
iModIntro. by iFrame.
Qed.

Definition server_token cs : iProp :=
  ⌜cs_role cs = Resp⌝ ∗
  (compromised_session Resp cs ∨ ∃ n0,
     clock (si_init cs) (si_resp cs) n0 ∗
     clock (si_init cs) (si_resp cs) n0).

Definition server_disconnected kI kR n : iProp :=
  failure kI kR ∨
  (⌜n = 0⌝ ∗ never_connected kI kR ∨ clock kI kR n).

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

Definition session_msg_pred (Q : sess_info → term → iProp) kS m : iProp :=
  ∃ si, ⌜kS = (si_key si)⌝ ∗ public m ∗ Q si m.

Definition init_pred si t : iProp := ∃ (beginning : nat),
  server_clock_ready (si_init si) (si_resp si) ∗
  term_meta (si_init_share si) (isoN.@"beginning") beginning ∗
  conn_ready si beginning.

Lemma init_predI cs beginning m :
  client_connecting cs beginning -∗
  compromised_session Init cs ∨ conn_ready cs beginning -∗
  □ (compromised_session Init cs ∨ init_pred cs m).
Proof.
iIntros "(#server & #? & #? & ?) #[fail|ready]"; eauto.
iModIntro. iRight. iExists _. eauto 10.
Qed.

Definition ack_init_pred si t : iProp := True.

Definition conn_pred φ kS m : iProp :=
  ∃ si n ts n0,
    ⌜kS = si_key si⌝ ∗
    ⌜m = Spec.of_list (TInt n :: ts)⌝ ∗
    ([∗ list] t ∈ ts, public t) ∗
    term_meta (si_init_share si) (isoN.@"beginning") n0 ∗
    φ (si_init si) (si_resp si) si (n + n0) ts.

Definition close_pred kI kR si n ts : iProp :=
  True.

Definition conn_closed si ending :=
  escrow nroot
         (term_token (si_init_share si) (↑isoN.@"end"))
         (clock (si_init si) (si_resp si) ending).

Definition ack_close_pred kI kR si n ts : iProp :=
  conn_closed si n ∗
  released (si_resp_share si).

Lemma session_failed_failure rl si :
  compromised_session rl si  ⊢ failure (si_init si) (si_resp si).
Proof. by iIntros "(#failed & _)". Qed.

Definition ctx : iProp :=
  seal_pred  (N.@"conn".@"init")      (session_msg_pred init_pred) ∗
  seal_pred  (N.@"conn".@"ack_init")  (session_msg_pred ack_init_pred) ∗
  seal_pred  (N.@"conn".@"close")     (conn_pred close_pred) ∗
  seal_pred  (N.@"conn".@"ack_close") (conn_pred ack_close_pred) ∗
  iso_dh_ctx (N.@"conn".@"auth").

Lemma ctx_alloc E :
  ↑N.@"conn" ⊆ E →
  seal_pred_token E ==∗
  ctx ∗ seal_pred_token (E ∖ ↑N.@"conn").
Proof.
iIntros "%sub token".
rewrite (seal_pred_token_difference (↑N.@"conn"));
  try solve_ndisj.
iDestruct "token" as "[token ?]". iFrame.
iMod (seal_pred_set (N.@"conn".@"init") with "token")
  as "[init token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"conn".@"ack_init") with "token")
  as "[ack_init token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"conn".@"close") with "token")
  as "[close token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"conn".@"ack_close") with "token")
  as "[ack_close token]"; try solve_ndisj.
iFrame.
iMod (iso_dh_ctx_alloc (N.@"conn".@"auth") with "token")
  as "#iso_dh"; try solve_ndisj.
Qed.

Ltac solve_ctx :=
  iIntros "ctx"; repeat (
    try solve [iApply "ctx"];
    iDestruct "ctx" as "[H ctx]";
    first [iApply "H" | iClear "H"]
  ).

Lemma ctx_init :
  ctx -∗ seal_pred (N.@"conn".@"init") (session_msg_pred init_pred).
Proof. solve_ctx. Qed.

Lemma ctx_ack_init :
  ctx -∗ seal_pred (N.@"conn".@"ack_init") (session_msg_pred ack_init_pred).
Proof. solve_ctx. Qed.

Lemma ctx_close :
  ctx -∗ seal_pred (N.@"conn".@"close") (conn_pred close_pred).
Proof. solve_ctx. Qed.

Lemma ctx_ack_close :
  ctx -∗ seal_pred (N.@"conn".@"ack_close") (conn_pred ack_close_pred).
Proof. solve_ctx. Qed.

Lemma ctx_iso_dh_ctx : ctx -∗ iso_dh_ctx (N.@"conn".@"auth").
Proof. solve_ctx. Qed.

End Defs.

End Props.

Arguments Props.connGS Σ : clear implicits.
