From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib version term gmeta nown.
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

Definition wf_sess_info si : iProp :=
  minted (si_key si) ∗
  senc_key (si_key si) ∗
  key_secrecy si.

#[global]
Instance wf_sess_info_persistent cs : Persistent (wf_sess_info cs).
Proof. apply _. Qed.

Definition session_failed_for si rl (failed : bool) : iProp :=
  term_meta (si_share_of rl si) (isoN.@"failed") failed ∗
  (if failed then compromised_session si
   else □ (public (si_key si) ↔ ▷ released_session si))%I.

#[global]
Instance session_failed_for_persistent si rl failed :
  Persistent (session_failed_for si rl failed).
Proof. by apply _. Qed.

Lemma session_failed_for_agree si rl failed1 failed2 :
  session_failed_for si rl failed1 -∗
  session_failed_for si rl failed2 -∗
  ⌜failed1 = failed2⌝.
Proof.
iIntros "(#meta1 & _) (#meta2 & _)".
iApply (term_meta_agree with "meta1 meta2").
Qed.

Definition session_failed si failed : iProp :=
  if failed then
    (session_failed_for si Init true ∨
     session_failed_for si Resp true)%I
  else
    (session_failed_for si Init false ∗
     session_failed_for si Resp false)%I.

Lemma session_failedI si failed1 failed2 :
  session_failed_for si Init failed1 -∗
  session_failed_for si Resp failed2 -∗
  session_failed si (failed1 || failed2).
Proof.
iIntros "#? #?".
case: failed1 => //=; eauto.
case: failed2 => //=; eauto.
Qed.

Lemma session_failedI' si rl failed1 failed2 :
  session_failed_for si rl failed1 -∗
  session_failed_for si (swap_role rl) failed2 -∗
  session_failed si (failed1 || failed2).
Proof.
iIntros "#failed1 #failed2". case: rl.
- iApply (session_failedI with "failed1 failed2").
- rewrite Bool.orb_comm. iApply (session_failedI with "failed2 failed1").
Qed.

Lemma session_okI si failed :
  session_failed si failed -∗
  (compromised_session si -∗ ▷ False) -∗
  ◇ session_failed si false.
Proof.
case: failed => //; eauto.
by iIntros "#[[_ fail1]|[_ fail2]] contra";
iDestruct ("contra" with "[]") as ">[]".
Qed.

#[global]
Instance session_failed_persistent si failed :
  Persistent (session_failed si failed).
Proof. apply _. Qed.

Lemma session_failed_agree si failed1 failed2 :
  session_failed si failed1 -∗
  session_failed si failed2 -∗
  ⌜failed1 = failed2⌝.
Proof.
iIntros "#failed1 #failed2".
iAssert (session_failed si true -∗
         session_failed si false -∗ False)%I
  as "P".
{ iIntros "#[fail|fail] #[succ1 succ2]".
  - by iPoseProof (session_failed_for_agree with "fail succ1") as "%".
  - by iPoseProof (session_failed_for_agree with "fail succ2") as "%". }
case: failed1 failed2 => [] [] //.
- by iDestruct ("P" with "failed1 failed2") as "[]".
- by iDestruct ("P" with "failed2 failed1") as "[]".
Qed.

Lemma session_failed_forI cs (P : iProp) (failed : bool) :
  wf_sess_info cs -∗
  (if failed then compromised_session cs else P) -∗
  term_token (cs_share cs) (↑isoN) ==∗ ∃ failed',
  ⌜failed → failed'⌝ ∗
  session_failed_for cs (cs_role cs) failed' ∗
  (⌜failed'⌝ ∨ P) ∗
  term_token (cs_share cs) (↑isoN ∖ ↑isoN.@"failed").
Proof.
iIntros "#wf HP token".
iPoseProof "wf" as "(_ & _ & #? & [fail|#succ])".
{ iMod (term_meta_set' true (N := isoN.@"failed") with "token")
    as "[#failed token]" => //; try solve_ndisj.
  iAssert (session_failed_for cs (cs_role cs) true) as "#?".
  { iSplit => //. }
  iExists true. iModIntro. iFrame. do !iSplit => //; eauto. }
case: failed.
{ iPoseProof "HP" as "#fail".
  iMod (term_meta_set' true (N := isoN.@"failed") with "token")
    as "[#failed token]" => //; try solve_ndisj.
  iFrame "token". iModIntro. iExists true.
  do !iSplit => //; eauto. }
iMod (term_meta_set' false (N := isoN.@"failed") with "token")
  as "[#failed token]" => //; try solve_ndisj.
iAssert (session_failed_for cs (cs_role cs) false) as "#?".
{ iSplit => //. iModIntro. by iSplit => //. }
iFrame "token". iModIntro. iExists false.
do !iSplit => //; eauto.
Qed.

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

Definition client_disconnected kI kR n failed : iProp :=
  server_clock_ready kI kR ∗
  if failed then failure kI kR else clock kI kR n.

Definition client_disconnecting kI kR cs : iProp :=
  ⌜cs_role cs = Init⌝ ∗
  server_clock_ready kI kR ∗
  term_token (si_init_share cs) (↑isoN.@"end").

Definition connected' kI kR cs n n0 : iProp :=
  ⌜si_init cs = kI⌝ ∗
  ⌜si_resp cs = kR⌝ ∗
  wf_sess_info cs ∗
  (∃ failed, session_failed_for cs (cs_role cs) failed) ∗
  release_token (cs_share cs) ∗
  cs_ts cs ↦ #n ∗
  (∃ failed, session_failed cs failed) ∗
  (session_failed cs true ∨
     term_meta (si_init_share cs) (isoN.@"beginning") n0).

Definition connected kI kR cs n : iProp :=
  ∃ n' n0, ⌜n = (n' + n0)%nat⌝ ∗
           term_meta (cs_share cs) (isoN.@"beginning") n0 ∗
           connected' kI kR cs n' n0.

Lemma connected_keyE kI kR cs n :
  connected kI kR cs n -∗
  ⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝.
Proof. by iIntros "(% & % & % & _ & -> & -> & _)". Qed.

Definition client_token kI kR cs : iProp :=
  ⌜cs_role cs = Init⌝ ∗
  server_clock_ready kI kR ∗
  term_token (si_init_share cs) (↑isoN.@"end").

Definition client_connecting cs n0 failed : iProp :=
  let kI := si_init cs in
  let kR := si_resp cs in
  server_clock_ready kI kR ∗
  wf_sess_info cs ∗
  term_meta  (si_init_share cs) (isoN.@"beginning") n0 ∗
  term_token (si_init_share cs) (↑isoN.@"end") ∗
  session_failed_for cs Init failed.

Lemma client_connecting_failed cs n0 failed :
  client_connecting cs n0 failed -∗
  session_failed_for cs Init failed.
Proof. by iIntros "(_ & _ & _ & _ & ?)". Qed.

Definition conn_ready si n :=
  escrow nroot
         (term_token (si_resp_share si) (↑isoN.@"begin"))
         (clock (si_init si) (si_resp si) n).

Lemma client_connectingI kI kR cs beginning failed :
  si_init cs = kI →
  si_resp cs = kR →
  cs_role cs = Init →
  cryptis_ctx -∗
  £ 1 ∗ £ 1 -∗
  wf_sess_info cs -∗
  term_token (si_init_share cs) (↑isoN) -∗
  client_disconnected kI kR beginning failed ={⊤}=∗ ∃ failed',
  ⌜failed → failed'⌝ ∗
  client_connecting cs beginning failed' ∗
  term_meta (si_init_share cs) (isoN.@"beginning") beginning ∗
  (⌜failed'⌝ ∨ conn_ready cs beginning).
Proof.
move=> <- <- e_rl {kI kR}.
iIntros "#? [c1 c2] #sess token dis".
iDestruct "dis" as "(#server & status)".
have e_sh : si_init_share cs = cs_share cs by rewrite /cs_share e_rl.
rewrite e_sh.
iMod (session_failed_forI with "sess status token")
  as "(%failed' & % & #conn & status & token)".
iMod (term_meta_set' (N:=isoN.@"beginning") beginning with "token")
  as "[#beginning token]"; try solve_ndisj.
iExists failed'. iSplitR => //. iSplitL "token" => //.
{ rewrite /client_connecting e_sh e_rl. iModIntro. do !iSplit => //.
  rewrite (term_token_difference _ (↑isoN.@"end")); try solve_ndisj.
  iDestruct "token" as "[token' token]". iFrame "token'". }
iSplitR => //.
iDestruct "status" as "[#?|status]"; eauto.
iRight. iApply (escrowI with "status"). iApply term_token_switch.
Qed.

Lemma client_connectedI cs n0 failedI failedR :
  cs_role cs = Init →
  client_connecting cs n0 failedI -∗
  cs_ts cs ↦ #0%nat -∗
  release_token (si_init_share cs) -∗
  session_failed_for cs Resp failedR ={⊤}=∗
  ▷ (connected (si_init cs) (si_resp cs) cs n0 ∗
     client_token (si_init cs) (si_resp cs) cs).
Proof.
iIntros "%e_rl (#server & #? & #? & ? & #conn) ts rel #status".
rewrite /connected /connected' /client_token /cs_share e_rl /=.
iFrame. do 2!iModIntro. iSplit; last by do 4!iSplit => //.
iExists n0. do 6!iSplit => //; eauto.
iSplit; eauto.
iExists (failedI || failedR).
case: failedI => /=; eauto.
case: failedR => /=; eauto.
Qed.

Lemma connected_ok kI kR cs n :
  connected kI kR cs n -∗
  (failure kI kR -∗ ▷ False) -∗
  ◇ session_failed cs false.
Proof.
iIntros "(% & % & % & _ & conn) post".
iDestruct "conn"
  as "(<- & <- & #conn & #? & rel & ts & #(%failed & status) & _)".
by iDestruct (session_okI with "status post") as ">?".
Qed.

Lemma client_alloc kI kR E :
  ↑N.@"client".@kR.@"clock" ⊆ E →
  term_token kI E ={⊤}=∗
  client_disconnected kI kR 0 false ∗
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
  session_failed cs true ∨ ∃ n0,
    clock (si_init cs) (si_resp cs) n0 ∗
    clock (si_init cs) (si_resp cs) n0.

Definition server_disconnected kI kR n failed : iProp :=
  if failed then failure kI kR
  else (⌜n = 0⌝ ∗ never_connected kI kR ∨ clock kI kR n)%I.

Lemma server_alloc kI kR E :
  ↑N.@"server".@kI ⊆ E →
  term_token kR E ==∗
  server_disconnected kI kR 0 false ∗
  term_token kR (E ∖ ↑N.@"server".@kI).
Proof.
iIntros "%sub token".
rewrite (term_token_difference _ (↑N.@"server".@kI)) //.
iDestruct "token" as "[token ?]". iFrame.
iModIntro. iLeft. by eauto.
Qed.

Definition session_msg_pred (Q : sess_info → term → iProp) rl kS m : iProp :=
  ∃ si failed,
    ⌜kS = (si_key si)⌝ ∗ public m ∗ session_failed_for si rl failed ∗
    (⌜failed⌝ ∨ Q si m).

Definition init_pred si t : iProp := ∃ (beginning : nat),
  server_clock_ready (si_init si) (si_resp si) ∗
  term_meta (si_init_share si) (isoN.@"beginning") beginning ∗
  conn_ready si beginning.

Lemma init_predI cs beginning failed m :
  client_connecting cs beginning failed -∗
  ⌜failed⌝ ∨ conn_ready cs beginning -∗
  □ (⌜failed⌝ ∨ init_pred cs m).
Proof.
iIntros "(#server & #? & #? & ? & ? & #status) #[fail|ready]"; eauto.
iModIntro. iRight. iExists _. eauto 10.
Qed.

Definition incoming_connection kR cs : iProp :=
  wf_sess_info cs ∗
  cs_ts cs ↦ #0%nat ∗
  ⌜si_resp cs = kR⌝ ∗
  ⌜cs_role cs = Resp⌝ ∗
  release_token (cs_share cs) ∗
  term_token (si_resp_share cs) (↑isoN) ∗
  (∀ failed,
     release_token (cs_share cs) -∗
     session_failed_for cs (cs_role cs) failed ={⊤}=∗ ∃ failed',
     ⌜failed → failed'⌝ ∗
     release_token (cs_share cs) ∗
     session_failed cs failed' ∗
     (⌜failed'⌝ ∨ ∃ m, init_pred cs m)).

Lemma server_connect kR cs n0 failed :
  server_disconnected (si_init cs) kR n0 failed -∗
  incoming_connection kR cs ={⊤}=∗
  □ (⌜failed⌝ -∗ session_failed cs true) ∗
  connected (si_init cs) kR cs n0 ∗
  server_token cs.
Proof.
iIntros "dis (#sess & ts & <- & %e_rl & rel & token & close)".
have ->: si_resp_share cs = cs_share cs.
{ by rewrite /cs_share e_rl. }
iMod (session_failed_forI with "sess dis token")
  as "(%failed' & %le_failed & #failed & dis & token)".
iMod ("close" with "rel failed")
  as "(%failed'' & %le_failed' & rel & #failed' & #init)".
rewrite /connected /connected' /cs_share e_rl /=.
iMod (term_meta_set' (N := isoN.@"beginning") n0
       with "token") as "[#beginning token]"; try solve_ndisj.
rewrite (term_token_difference _ (↑isoN.@"begin")); try solve_ndisj.
iDestruct "token" as "[token _]".
iDestruct "dis" as "[%fail|dis]".
{ iAssert (session_failed cs true) as "#?".
  { by case: failed'' => //= in le_failed' *. }
  iFrame. do !iSplitR => //; eauto.
  iExists n0. do !iSplitR => //; eauto.
  by iLeft. }
iDestruct "init" as "[%fail|(%m & init)]".
{ case: failed'' {le_failed'} => // in fail *.
  iFrame. do !iSplitR => //; eauto.
  iExists n0. do !iSplitR => //; eauto.
  by iLeft. }
iDestruct "init" as "(%n0' & clock & beginningI & ready)".
iMod (escrowE with "ready token") as ">c1" => //.
iAssert (|={⊤}=> clock (si_init cs) (si_resp cs) n0)%I
  with "[dis]" as "> c2".
{ iDestruct "dis" as "[(-> & never)|c2]" => //.
  iMod (escrowE with "clock never") as ">?" => //. }
iPoseProof (clock_agree with "c1 c2") as "->".
iModIntro. iFrame. do !iSplit => //; eauto.
- iIntros "!> %fail".
  have: failed'' by tauto.
  by case: (failed'').
- iExists n0. do !iSplit => //; eauto.
- iRight. iFrame.
Qed.

Definition ack_init_pred si t : iProp := True.

Definition conn_pred φ kS m : iProp :=
  ∃ si n ts,
    ⌜kS = si_key si⌝ ∗
    ⌜m = Spec.of_list (TInt n :: ts)⌝ ∗
    ([∗ list] t ∈ ts, public t) ∗
    (∃ failed, session_failed si failed) ∗
    (session_failed si true ∨ ∃ n0,
      term_meta (si_init_share si) (isoN.@"beginning") n0 ∗
      φ (si_init si) (si_resp si) si (n + n0) ts).

Lemma conn_predI kI kR cs m n0 φ n ts :
  connected' kI kR cs m n0 -∗
  ([∗ list] t ∈ ts, public t) -∗
  □ (session_failed cs true ∨ φ kI kR (cs_si cs) (n + n0) ts) -∗
  □ conn_pred φ (si_key cs) (Spec.of_list (TInt n :: ts)).
Proof.
iIntros "(<- & <- & #conn & #? & _ & _ & #failed & #beginning)".
iIntros "#p_ts #inv !>".
iExists cs, n, ts.
do 4!iSplit => //.
iDestruct "beginning" as "[?|beginning]"; eauto.
iDestruct "inv" as "[?|inv]"; eauto.
Qed.

Lemma conn_predE kI kR cs m n n0 φ ts :
  connected' kI kR cs m n0 -∗
  □ conn_pred φ (si_key cs) (Spec.of_list (TInt n :: ts)) -∗
  ([∗ list] t ∈ ts, public t) ∗
  □ (session_failed cs true ∨ φ kI kR (cs_si cs) (n + n0) ts).
Proof.
iIntros "(<- & <- & #conn & #? & _ & _ & #failed & #beginning)".
iIntros "#(%si & %n' & %ts' & %e_kS & %e_m & p_ts & failed' & inv)".
case/Spec.of_list_inj: e_m => e_n <-.
have {e_n} ?: n = n' by lia. subst n'.
rewrite -(session_agree e_kS) {e_kS}.
iSplit => //. iModIntro.
iDestruct "beginning" as "[?|beginning]"; eauto.
iDestruct "inv" as "[?|(%n0' & beginning' & inv)]"; eauto.
iPoseProof (term_meta_agree with "beginning beginning'") as "<-".
by iRight.
Qed.

Definition close_pred kI kR si n ts : iProp :=
  True.

Definition conn_closed si ending :=
  escrow nroot
         (term_token (si_init_share si) (↑isoN.@"end"))
         (clock (si_init si) (si_resp si) ending).

Definition ack_close_pred kI kR si n ts : iProp :=
  conn_closed si n.

Lemma session_failed_failure si failed :
  session_failed si failed ⊢ ⌜failed⌝ → compromised_session si.
Proof.
iIntros "#failed %fail".
case: failed in fail * => //=.
by iDestruct "failed" as "[[_ fail]|[_ fail]]".
Qed.

Definition ctx : iProp :=
  seal_pred  (N.@"conn".@"init")      (session_msg_pred init_pred Init) ∗
  seal_pred  (N.@"conn".@"ack_init")  (session_msg_pred ack_init_pred Resp) ∗
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
  ctx -∗ seal_pred (N.@"conn".@"init") (session_msg_pred init_pred Init).
Proof. solve_ctx. Qed.

Lemma ctx_ack_init :
  ctx -∗ seal_pred (N.@"conn".@"ack_init") (session_msg_pred ack_init_pred Resp).
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
