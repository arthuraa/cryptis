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
From cryptis Require Import role dh_auth.
From cryptis.store Require Import alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record conn_state := ConnState {
  cs_si   :> sess_info;
  cs_ts   :  loc;
  cs_name :  gname;
  cs_role :  role;
}.

#[global]
Instance cs_repr : Repr conn_state :=
  λ s, (#(cs_ts s), Spec.mkskey (si_key s))%V.

Record server_state := {
  ss_key : term;
  ss_clients : val;
}.

#[global]
Instance ss_repr : Repr server_state :=
  λ s, (TKey Dec (ss_key s), TKey Enc (ss_key s), ss_clients s)%V.

Record server_client_state := {
  scs_db   : val;
  scs_name : gname;
  scs_lock : val;
}.

#[global]
Instance scs_repr : Repr server_client_state :=
  λ s, (scs_db s, scs_lock s)%V.

Section Status.

(**

Each party of the protocol can be in one of two states:

- [Disconnected n] means that the [n] database operations have been performed so
  far and processed by the server.

- [Connected kS n] means that the participant is connected using the session key
  [kS] and that, at the beginning of the connection, [n] database operations had
  been performed.

*)

Variant lstatus :=
| Disconnected of nat
| Connected of term & nat.

Canonical lstatusO := leibnizO lstatus.

Global Instance lstatus_inhabited : Inhabited lstatus :=
  populate (Disconnected inhabitant).

(**

Combining client and server, the system can be in one of four states:

- [BothDisconnected n] means that both parties are disconnected.  If [n = None],
  then they have never connected to each other; otherwise, [n] indicates how
  many database operations had been performed previously.

- [ClientConnecting kS n] means that the client is attempting to connected with
  the server using the session key [kS]. If [n = None], this is the first
  connection between them; otherwise, [n] is the number of performed database
  operations.

- [BothConnected kS n] means that the server has accepted the connection of the
  client.  At this point, we don't need to distinguish between the first and
  subsequent connection attempts, which is why the number of operations [n] is
  not optional.

- [ClientDisconnecting kS n] means that the client wants to disconnect the
  session identified by the key [kS], and that [n] operations have been
  performed.

*)

Variant gstatus :=
| BothDisconnected of nat
| ClientConnecting of term & nat
| BothConnected of term & nat
| ClientDisconnecting of term & nat & nat.

Canonical gstatusO := leibnizO gstatus.

Global Instance gstatus_inhabited : Inhabited gstatus :=
  populate (BothDisconnected inhabitant).

Definition status_view : Type := excl' lstatus.

Implicit Types gs : gstatus.
Implicit Types ls : lstatus.
Implicit Types v : status_view.
Implicit Types n : nat.

Definition to_client_status gs :=
  match gs with
  | BothDisconnected n => Disconnected n
  | ClientConnecting kS n => Connected kS n
  | BothConnected kS n => Connected kS n
  | ClientDisconnecting kS beginning ending => Disconnected ending
  end.

Definition to_server_status gs :=
  match gs with
  | BothDisconnected n => Disconnected n
  | ClientConnecting kS n => Disconnected n
  | BothConnected kS n => Connected kS n
  | ClientDisconnecting kS beginning _ => Connected kS beginning
  end.

Definition to_status gs := Excl' (to_server_status gs).

Definition status_view_rel_raw n gs v :=
  v ≼ to_status gs.

Lemma status_view_rel_raw_mono n1 n2 gs1 gs2 v1 v2 :
  status_view_rel_raw n1 gs1 v1 →
  gs1 ≡{n2}≡ gs2 →
  v2 ≼{n2} v1 →
  n2 ≤ n1 →
  status_view_rel_raw n2 gs2 v2.
Proof.
rewrite /status_view_rel_raw.
move=> v1_gs1 /leibniz_equiv_iff <- {gs2}.
move=> /cmra_discrete_included_iff v2_v1 n2_n1.
by trans v1.
Qed.
Lemma status_view_rel_raw_valid n gs v :
  status_view_rel_raw n gs v → ✓{n} v.
Proof.
rewrite /status_view_rel_raw => v_gs.
move: n; apply/cmra_valid_validN.
apply: cmra_valid_included v_gs.
by [].
Qed.
Lemma status_view_rel_raw_unit n :
  ∃ gs, status_view_rel_raw n gs ε.
Proof.
exists (BothDisconnected 0).
exact: ucmra_unit_least.
Qed.
Canonical Structure status_view_rel : view_rel gstatusO _ :=
  ViewRel status_view_rel_raw
    status_view_rel_raw_mono
    status_view_rel_raw_valid
    status_view_rel_raw_unit.

Global Instance status_view_rel_discrete : ViewRelDiscrete status_view_rel.
Proof. by move. Qed.

Notation status := (view status_view_rel).

Definition client_view gs : status :=
  ●V gs.

Definition server_view ls : status :=
  ◯V Excl' ls.

Lemma status_valid gs ls :
  ✓ (client_view gs ⋅ server_view ls) ↔
  ls = to_server_status gs.
Proof.
rewrite view_both_valid /= /status_view_rel_raw /to_status.
split.
- move=> /(_ 0). by rewrite Excl_included.
- by move=> -> _.
Qed.

Lemma client_connect_update kS n :
  client_view (BothDisconnected n) ~~> client_view (ClientConnecting kS n).
Proof.
apply: (view_update_auth _ _ _ None); rewrite /= /status_view_rel_raw /=.
move=> _ [ls|_]; last exact: ucmra_unit_least.
move=> lsE; have ->: ls = Excl (to_server_status (BothDisconnected n)).
{ rewrite -leibniz_equiv_iff.
  exact: Some_included_exclusive. }
exact/Excl_included.
Qed.

Lemma server_connect_update kS n ls :
  client_view (ClientConnecting kS n) ⋅ server_view ls ~~>
  client_view (BothConnected kS n) ⋅ server_view (Connected kS n).
Proof.
apply/view_update; rewrite /= /status_view_rel_raw /= => _.
move=> f incl; have /exclusive_Some_l: ✓ (Excl' ls ⋅ f).
{ exact: cmra_valid_included incl. }
by move=> ->; rewrite ucmra_unit_right_id.
Qed.

Lemma client_disconnect_update kS n ending :
  client_view (BothConnected kS n) ~~>
  client_view (ClientDisconnecting kS n ending).
Proof.
apply: (view_update_auth _ _ _ None); rewrite /= /status_view_rel_raw /=.
move=> _ [ls|_]; last exact: ucmra_unit_least.
move=> lsE; have ->: ls = Excl (to_server_status (BothConnected kS n)).
{ rewrite -leibniz_equiv_iff.
  exact: Some_included_exclusive. }
exact/Excl_included.
Qed.

Lemma server_disconnect_update kS n ending ls :
  client_view (ClientDisconnecting kS n ending) ⋅ server_view ls ~~>
  client_view (BothDisconnected ending) ⋅ server_view (Disconnected ending).
Proof.
apply/view_update; rewrite /= /status_view_rel_raw /= => _.
move=> f incl; have /exclusive_Some_l: ✓ (Excl' ls ⋅ f).
{ exact: cmra_valid_included incl. }
by move=> ->; rewrite ucmra_unit_right_id.
Qed.

End Status.

Notation status := (view status_view_rel_raw).
Notation statusUR := (viewUR status_view_rel).

Definition oneshotUR : ucmra :=
  authUR (optionUR (agreeR natO)).

Definition Free dq : oneshotUR :=
  ●{dq} None.

Definition Shot n : oneshotUR :=
  ◯ Some (to_agree n).

Lemma shoot n : Free (DfracOwn 1) ~~> Shot n.
Proof.
trans (● (Some (to_agree n)) ⋅ Shot n); last first.
  exact: cmra_update_op_r.
apply: auth_update_alloc.
by apply: alloc_option_local_update.
Qed.

Class storeGS Σ := StoreGS {
  storeGS_db      : dbGS Σ;
  storeGS_status  : inG Σ statusUR;
  storeGS_oneshot : inG Σ oneshotUR
}.

Local Existing Instance storeGS_db.
Local Existing Instance storeGS_status.
Local Existing Instance storeGS_oneshot.

Definition storeΣ := #[
  dbΣ;
  GFunctor statusUR;
  GFunctor oneshotUR
].

Global Instance subG_storeGS Σ : subG storeΣ Σ → storeGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : conn_state).
Implicit Types kI kR kS t : term.
Implicit Types db : gmap term term.
Implicit Types accounts : gmap term server_client_state.
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types γ γ_db γ_s : gname.
Implicit Types v : val.
Implicit Types ok : Prop.
Implicit Types si : sess_info.

Variable N : namespace.

Definition dbCN kR := nroot.@"db".@"client".@kR.
Definition dbSN kI := nroot.@"db".@"server".@kI.

Definition is_conn_state cs n : iProp :=
  cs_ts cs ↦ #n ∗
  session (cs_name cs) cs (cs_role cs) ∗
  minted (si_key cs) ∗
  □ (∀ kt, public (TKey kt (si_key cs)) ↔ ▷ session_fail cs).

Lemma conn_state_session cs n :
  is_conn_state cs n -∗
  session (cs_name cs) cs (cs_role cs).
Proof. by iIntros "(? & ? & ?)". Qed.

Definition db_signed_up kI kR : iProp := 
  term_meta kR (dbSN kI) ().

Definition db_not_signed_up kI kR : iProp :=
  term_token kR (↑dbSN kI).

Lemma db_signed_up_switch kI kR Q :
  ⊢ switch (db_not_signed_up kI kR) Q.
Proof.
iExists (db_signed_up kI kR). iSplit; iModIntro.
- iIntros "[token meta]".
  by iDestruct (term_meta_token with "token meta") as "[]".
- iIntros "token".
  iMod (term_meta_set (dbSN kI) () with "token") as "#meta" => //.
Qed.

Definition server_status_ready kI kR :=
  escrow (nroot.@"db") (db_not_signed_up kI kR) (
    term_own kI (dbCN kR.@"status") (server_view (Disconnected 0))
  ).

Definition conn_not_started si rl : iProp := ∃ γ_sR,
  session γ_sR si rl ∗
  gmeta_token γ_sR (↑nroot.@"db".@"begin").

Definition conn_started si rl : iProp := ∃ γ_sR,
  session γ_sR si rl  ∗
  gmeta γ_sR (nroot.@"db".@"begin") ().

Lemma conn_started_switch si rl Q :
  ⊢ switch (conn_not_started si rl)
    (session_fail si ∨ Q).
Proof.
iExists (conn_started si rl). iSplit; iModIntro.
- iIntros "[no #yes]".
  iDestruct "no" as "(%γ_sR1 & #sess1 & token)".
  iDestruct "yes" as "(%γ_sR2 & #sess2 & #meta)".
  iDestruct (session_agree_name with "sess1 sess2") as "[fail|[? ->]]" => //.
  + by iLeft.
  + iRight.
    iDestruct (gmeta_gmeta_token with "token meta") as "[]" => //.
- iIntros "(%γ_sR & #sess & token)".
  iMod (gmeta_set _ _ (nroot.@"db".@"begin") () with "token") as "#meta" => //.
  iIntros "!> !>". iExists _. eauto.
Qed.

Definition conn_not_ended si rl : iProp := ∃ γ_sR,
  session γ_sR si rl ∗
  gmeta_token γ_sR (↑nroot.@"db".@"end").

Definition conn_ended si rl : iProp := ∃ γ_sR,
  session γ_sR si rl  ∗
  gmeta γ_sR (nroot.@"db".@"end") ().

Lemma conn_ended_switch si rl Q :
  ⊢ switch (conn_not_ended si rl) (session_fail si ∨ Q).
Proof.
iExists (conn_ended si rl). iSplit; iModIntro.
- iIntros "[no #yes]".
  iDestruct "no" as "(%γ_sR1 & #sess1 & token)".
  iDestruct "yes" as "(%γ_sR2 & #sess2 & #meta)".
  iDestruct (session_agree_name with "sess1 sess2") as "[fail|[_ ->]]" => //.
  + by iLeft.
  + iRight.
    by iDestruct (gmeta_gmeta_token with "token meta") as "[]".
- iIntros "(%γ_sR & #sess & token)".
  iMod (gmeta_set _ _ (nroot.@"db".@"end") () with "token") as "#meta" => //.
  iIntros "!> !>". iExists _. eauto.
Qed.

Implicit Types (ls : lstatus) (gs : gstatus).

Definition key_corruption kI kR : iProp :=
  public (TKey Enc kI) ∨ public (TKey Enc kR).

Definition client_disconnected_int kI kR n : iProp :=
  DB.client_view kI (dbCN kR.@"state") n ∗
  server_status_ready kI kR ∗
  (key_corruption kI kR ∨
   term_own kI (dbCN kR.@"status") (client_view (BothDisconnected n))).

Definition client_disconnected kI kR : iProp := ∃ n,
  client_disconnected_int kI kR n.

Definition client_connected_int cs n beginning : iProp :=
  let kI := si_init cs in
  let kR := si_resp cs in
  ⌜cs_role cs = Init⌝ ∗
  DB.client_view kI (dbCN kR.@"state") (n + beginning) ∗
  server_status_ready kI kR ∗
  conn_not_ended cs Init ∗
  gmeta (cs_name cs) (nroot.@"db".@"beginning") beginning ∗
  gmeta_token (cs_name cs) (↑nroot.@"db".@"ending") ∗
  (session_fail cs ∨
   term_own kI (dbCN kR.@"status")
     (client_view (BothConnected (si_key cs) beginning))).

Definition client_connecting_int cs beginning : iProp :=
  let kI := si_init cs in
  let kR := si_resp cs in
  ⌜cs_role cs = Init⌝ ∗
  DB.client_view kI (dbCN kR.@"state") beginning ∗
  server_status_ready kI kR ∗
  conn_not_started cs Init ∗
  conn_not_ended cs Init ∗
  gmeta (cs_name cs) (nroot.@"db".@"beginning") beginning ∗
  gmeta_token (cs_name cs) (↑nroot.@"db".@"ending").

Definition client_disconnecting_int cs n beginning : iProp :=
  let kI := si_init cs in
  let kR := si_resp cs in
  ⌜cs_role cs = Init⌝ ∗
  DB.client_view kI (dbCN kR.@"state") (n + beginning) ∗
  server_status_ready kI kR ∗
  conn_not_ended cs Init ∗
  gmeta (cs_name cs) (nroot.@"db".@"ending") (n + beginning).

Definition conn_ready si n :=
  escrow (nroot.@"db")
         (conn_not_started si Resp)
         (session_fail si ∨
          term_own (si_init si) (dbCN (si_resp si).@"status")
            (client_view (ClientConnecting (si_key si) n))).

Lemma client_connectingI E1 E2 kI kR cs dq n T beginning :
  ↑cryptisN ⊆ E1 →
  ↑nroot.@"db" ⊆ E1 →
  ↑nroot.@"db" ⊆ E2 →
  si_init cs = kI →
  si_resp cs = kR →
  si_time cs = n  →
  cs_role cs = Init →
  cryptis_ctx -∗
  £ 1 ∗ £ 1 -∗
  ●H{dq|n} T -∗
  is_conn_state cs 0 -∗
  gmeta_token (cs_name cs) E2 -∗
  client_disconnected_int kI kR beginning ={E1}=∗
  ●H{dq|n} T ∗
  is_conn_state cs 0 ∗
  client_connecting_int cs beginning ∗
  gmeta (cs_name cs) (nroot.@"db".@"beginning") beginning ∗
  conn_ready cs beginning.
Proof.
move=> ? ? ? <- <- <- e_rl {kI kR n}.
iIntros "#? [c1 c2] hon conn token client".
iPoseProof (conn_state_session with "conn") as "#sess".
iFrame "conn".
iDestruct "client" as "(client_view & #server & status)".
iPoseProof (DB.client_view_server_view with "client_view")
  as "(%db & #server_view)".
rewrite (gmeta_token_difference _ (↑nroot.@"db".@"begin"));
  try solve_ndisj.
iDestruct "token" as "[token' token]".
iAssert (conn_not_started cs Init)
  with "[token']" as "not_started".
{ iExists (cs_name cs). iFrame. rewrite e_rl. eauto. }
rewrite (gmeta_token_difference _ (↑nroot.@"db".@"end")); try solve_ndisj.
iDestruct "token" as "[token' token]".
iAssert (conn_not_ended cs Init) with "[token']" as "not_ended".
{ iExists (cs_name cs). iFrame. rewrite e_rl. eauto. }
iMod (gmeta_set' _ _ (nroot.@"db".@"beginning") beginning with "token")
  as "[#beginning token]"; try solve_ndisj.
iPoseProof (@gmeta_token_drop _ _ (↑nroot.@"db".@"ending") with "token")
  as "token"; try solve_ndisj.
iAssert (|={E1}=> ●H{dq|si_time cs} T ∗ (
                      session_fail cs ∨
                      term_own (si_init cs) (dbCN (si_resp cs).@"status")
                        (client_view (ClientConnecting (si_key cs) beginning))))%I
  with "[c1 hon status]" as ">[hon status]".
{ iDestruct "status" as "[#fail|status]".
  - iAssert (|={E1}=> ●H{dq|si_time cs} T ∗ session_fail cs)%I
    with "[c1 hon]"
    as ">[hon #fail']".
    { iDestruct "fail" as "[fail|fail]".
      - iMod (public_atI with "[//] c1 hon fail") as "{fail} [hon fail]".
        { solve_ndisj. }
        by iFrame.
      - iMod (public_atI with "[//] c1 hon fail") as "{fail} [hon fail]".
        { solve_ndisj. }
        by iFrame. }
    iFrame.
    by iLeft.
  - iFrame.
    iMod (term_own_update with "status") as "status".
    { apply: (client_connect_update (si_key cs)). }
    iModIntro. by iRight. }
iAssert (|={E1}=> conn_ready cs beginning)%I with "[status]" as ">#ready".
{ iApply (escrowI with "status").
  iApply conn_started_switch. }
iFrame "hon". iSplitL => //; eauto.
iFrame. by eauto.
Qed.

Definition conn_accepted si beginning :=
  escrow (nroot.@"db")
    (conn_not_started si Init)
    (session_fail si ∨
     term_own (si_init si) (dbCN (si_resp si).@"status")
       (client_view (BothConnected (si_key si) beginning))).

Lemma client_connected_intI cs beginning E :
  ↑nroot.@"db" ⊆ E →
  client_connecting_int cs beginning -∗
  session_fail cs ∨
    conn_accepted cs beginning ={E}=∗
  ▷ client_connected_int cs 0 beginning.
Proof.
move=> sub.
iIntros "(%e_rl & client & #server & not_started & not_ended &
          #beginning & ending) #status".
iFrame. do 3!iSplitR => //.
iDestruct "status" as "[fail|accepted]".
- by eauto.
- iMod (escrowE with "accepted not_started") as "status" => //.
Qed.

Definition client_connected kI kR cs : iProp := ∃ n beginning,
  ⌜si_init cs = kI⌝ ∗
  ⌜si_resp cs = kR⌝ ∗
  is_conn_state cs n ∗
  client_connected_int cs n beginning.

Definition rem_mapsto kI kR t1 t2 : iProp :=
  DB.mapsto kI (dbCN kR.@"state") t1 t2.

Definition rem_free_at kI kR T : iProp :=
  DB.free_at kI (dbCN kR.@"state") T.

Lemma rem_free_at_diff kI kR T1 T2 :
  T1 ⊆ T2 →
  rem_free_at kI kR T2 ⊣⊢ rem_free_at kI kR T1 ∗ rem_free_at kI kR (T2 ∖ T1).
Proof. iIntros "%sub". by iApply DB.free_at_diff. Qed.

Lemma rem_mapsto_update t2' cs t1 t2 n beginning :
  is_conn_state cs n -∗
  client_connected_int cs n beginning -∗
  rem_mapsto (si_init cs) (si_resp cs) t1 t2 ==∗
  client_connected_int cs (S n) beginning ∗
  is_conn_state cs n ∗
  rem_mapsto (si_init cs) (si_resp cs) t1 t2' ∗
  DB.update_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 t2'.
Proof.
iIntros "conn (%e_rl & client & #server & not_ended &
          #beginning & ending & status)".
iPoseProof (conn_state_session with "conn") as "#sessI". iFrame "conn".
iIntros "mapsto".
iMod (DB.update_client t2' with "client mapsto")
  as "(client & #update & mapsto)".
iFrame.
iSplitR.
{ iFrame. eauto. }
by eauto.
Qed.

Lemma rem_mapsto_alloc cs t1 t2 n beginning T :
  t1 ∈ T →
  is_conn_state cs n -∗
  client_connected_int cs n beginning -∗
  rem_free_at (si_init cs) (si_resp cs) T ==∗
  is_conn_state cs n ∗
  client_connected_int cs (S n) beginning ∗
  rem_mapsto (si_init cs) (si_resp cs) t1 t2 ∗
  rem_free_at (si_init cs) (si_resp cs) (T ∖ {[t1]}) ∗
  DB.create_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 t2.
Proof.
iIntros "%t1_T".
iIntros "conn (%e_rl & client & #server & not_ended &
          #beginning & ending & status)".
iPoseProof (conn_state_session with "conn") as "#sessI". iFrame "conn".
have {}t1_T : {[t1]} ⊆ T by set_solver.
rewrite (rem_free_at_diff _ _ t1_T).
iIntros "[free free']". iFrame "free'".
iMod (DB.create_client _ t2 with "client free") as "(create & client & mapsto)".
iFrame. iModIntro.
iSplitR.
{ iFrame. by eauto. }
by eauto.
Qed.

Lemma client_alloc kI kR E E' :
  ↑dbCN kR ⊆ E →
  ↑nroot.@"db" ⊆ E' →
  term_token kI E ={E'}=∗
  client_disconnected kI kR ∗
  rem_free_at kI kR ⊤ ∗
  term_token kI (E ∖ ↑dbCN kR).
Proof.
iIntros "%sub %sub' kI_token".
rewrite (term_token_difference _ _ _ sub).
iDestruct "kI_token" as "[kI_token ?]". iFrame.
iMod (DB.alloc _ (N := dbCN kR.@"state") with "kI_token")
  as "(client_view & free & #server_view & kI_token)".
{ solve_ndisj. }
iMod (term_own_alloc (dbCN kR.@"status")
        (client_view (BothDisconnected 0) ⋅ server_view (Disconnected 0))
  with "kI_token") as "[[client server] kI_token]" => //.
- solve_ndisj.
- exact/status_valid.
iAssert (|={E'}=> server_status_ready kI kR)%I
  with "[server]" as ">#server".
{ iApply (escrowI with "server").
  iApply db_signed_up_switch. }
iModIntro. iSplitR "free".
- iExists 0. by iFrame.
- by iFrame.
Qed.

Definition public_db db : iProp :=
  [∗ map] t1 ↦ t2 ∈ db, public t1 ∗ public t2.

Lemma public_db_insert db t1 t2 :
  public t1 -∗
  public t2 -∗
  public_db db -∗
  public_db (<[t1 := t2]> db).
Proof.
rewrite /public_db !big_sepM_forall.
iIntros "#p_t1 #p_t2 #p_db %t1' %t2'".
case: (decide (t1' = t1)) => [-> {t1'} | ne].
- rewrite lookup_insert. iIntros "%e". case: e => ->. by eauto.
- by rewrite lookup_insert_ne //.
Qed.

Definition server_connected cs n db : iProp :=
  ⌜cs_role cs = Resp⌝ ∗
  conn_not_ended cs Resp ∗
  public_db db ∗
  (session_fail cs ∨ ∃ γ_sI beginning,
   session γ_sI cs Init ∗
   DB.server_view (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) db ∗
   gmeta γ_sI (nroot.@"db".@"beginning") beginning ∗
   term_own (si_init cs) (dbCN (si_resp cs).@"status")
     (server_view (Connected (si_key cs) beginning))).

Definition server_disconnected kI kR db : iProp :=
  public_db db ∗
  (key_corruption kI kR ∨
   ⌜db = ∅⌝ ∗ db_not_signed_up kI kR ∨ ∃ n,
   DB.server_view kI (dbCN kR.@"state") n db ∗
   term_own kI (dbCN kR.@"status") (server_view (Disconnected n))).

Definition server_connecting cs db : iProp :=
  public_db db ∗
  (session_fail cs ∨
   ⌜db = ∅⌝ ∗ db_not_signed_up (si_init cs) (si_resp cs) ∨ ∃ n,
   DB.server_view (si_init cs) (dbCN (si_resp cs).@"state") n db ∗
   term_own (si_init cs) (dbCN (si_resp cs).@"status") (server_view (Disconnected n))).

Lemma server_connectingI cs db dq T :
  cryptis_ctx -∗
  ●H{dq|si_time cs} T -∗
  £ 1 -∗
  server_disconnected (si_init cs) (si_resp cs) db ={⊤}=∗
  ●H{dq|si_time cs} T ∗
  server_connecting cs db.
Proof.
iIntros "#ctx hon c (#p_db & [#fail | status])"; last first.
{ iModIntro. by iFrame. }
iAssert (|={⊤}=> ●H{dq|si_time cs} T ∗ session_fail cs)%I
  with "[hon c]" as "{fail} >[hon fail]".
{ iDestruct "fail" as "[fail|fail]".
  - iMod (public_atI with "[//] c hon fail") as "[hon ?]" => //.
    iModIntro. by iFrame.
  - iMod (public_atI with "[//] c hon fail") as "[hon ?]" => //.
    iModIntro. by iFrame. }
iModIntro. by iFrame.
Qed.

Definition account_inv kI kR vdb : iProp := ∃ db,
  server_disconnected kI kR db ∗
  SAList.is_alist vdb (repr <$> db).

Lemma account_alloc kI kR vdb E :
  ↑dbSN kI ⊆ E →
  term_token kR E -∗
  SAList.is_alist vdb ∅ -∗
  term_token kR (E ∖ ↑dbSN kI) ∗
  account_inv kI kR vdb.
Proof.
iIntros "%sub token vdb".
rewrite (term_token_difference kR (↑dbSN kI)) //.
iDestruct "token" as "[token H]". iFrame "H".
iExists ∅. iFrame "vdb".
iSplit; first by rewrite /public_db big_sepM_empty.
iRight. iLeft. iSplit => //.
Qed.

Definition server ss : iProp := ∃ accounts E,
  public (TKey Dec (ss_key ss)) ∗
  SAList.is_alist (ss_clients ss) (repr <$> accounts) ∗
  term_token (ss_key ss) E ∗
  ⌜∀ kI, TKey Dec kI ∉ dom accounts → ↑dbSN kI ⊆ E⌝ ∗
  [∗ map] vkI ↦ scs ∈ accounts, ∃ kI, ⌜vkI = TKey Dec kI⌝ ∗
     is_lock (scs_name scs) (scs_lock scs)
       (account_inv kI (ss_key ss) (scs_db scs)).

Lemma serverI kR vclients :
  term_token kR (↑nroot.@"db".@"server") -∗
  public (TKey Dec kR) -∗
  SAList.is_alist vclients ∅ -∗
  server {| ss_key := kR; ss_clients := vclients |}.
Proof.
iIntros "token #p_vk clients".
iExists ∅, (↑nroot.@"db".@"server") => /=.
iFrame. iSplit => //. iSplit => //.
iPureIntro. move=> *. solve_ndisj.
Qed.

Definition init_pred kS (m : term) : iProp := ∃ si γ_sI (beginning : nat),
  ⌜si_key si = kS⌝ ∗
  session γ_sI si Init ∗
  gmeta γ_sI (nroot.@"db".@"beginning") beginning ∗
  server_status_ready (si_init si) (si_resp si) ∗
  conn_ready si beginning ∗
  DB.server_view (si_init si) (dbCN (si_resp si).@"state") 0 ∅.

Lemma init_predI cs beginning m :
  is_conn_state cs 0 -∗
  client_connecting_int cs beginning -∗
  conn_ready cs beginning -∗
  is_conn_state cs 0 ∗
  client_connecting_int cs beginning ∗
  □ init_pred (si_key cs) m.
Proof.
iIntros "conn (%e_rl & client & #server & not_started & not_ended &
          #beginning & ending) #ready".
iPoseProof (DB.client_view_server_view with "client")
  as "(%db & #server_view)".
iPoseProof (DB.server_view_to_0 with "server_view") as "#server_view0".
iPoseProof (conn_state_session with "conn") as "#sessI".
iFrame. iSplit; first by eauto.
iModIntro. iExists cs, (cs_name cs), beginning. rewrite e_rl.
by eauto 10.
Qed.

Definition ack_init_pred kS (m : term) : iProp := ∃ γ_sR si,
  ⌜si_key si = kS⌝ ∗
  session γ_sR si Resp ∗
  (session_fail si ∨ ∃ γ_sI beginning,
   session γ_sI si Init ∗
   gmeta γ_sI (nroot.@"db".@"beginning") beginning ∗
   conn_accepted si beginning).

Lemma ack_init_predI cs db m :
  cs_role cs = Resp →
  server_connecting cs db -∗
  is_conn_state cs 0 -∗
  conn_not_started cs Resp -∗
  conn_not_ended cs Resp -∗
  (session_fail cs ∗ public m ∨ init_pred (si_key cs) m) ={⊤}▷=∗
  is_conn_state cs 0 ∗
  server_connected cs 0 db ∗
  □ ack_init_pred (si_key cs) (TInt 0).
Proof.
iIntros "%e_rl (#p_db & status) conn not_started not_ended p_m".
iPoseProof (conn_state_session with "conn") as "#sessR".
iFrame "conn".
iAssert (□ (▷ session_fail cs -∗ conn_not_ended cs Resp ={⊤}▷=∗
            server_connected cs 0 db ∗
            □ ack_init_pred (si_key cs) (TInt 0)))%I
  as "failure".
{ iIntros "!> #fail not_ended !> !> !>". iSplit.
  - by iFrame; eauto.
  - iModIntro. iExists _, _. rewrite e_rl.
    iSplit => //. iSplit => //.
    by iLeft. }
iDestruct "p_m" as "[[#fail _]|p_m]".
{ by iApply ("failure" with "[//] not_ended"). }
iDestruct "status" as "[#fail|status]".
{ by iApply ("failure" with "[//] not_ended"). }
iDestruct "p_m"
  as "(%si & %γ_sI & %beginning & %e_kS & #sessI &
       #beginning & #server & #conn_ready & #server_view)".
iDestruct (session_agree with "sessI sessR") as "[#fail|->]" => //.
{ by iApply ("failure" with "[//] not_ended"). }
iMod (escrowE with "conn_ready not_started") as "[#fail|statusI]" => //.
{ by iApply ("failure" with "[//] not_ended"). }
iAssert (|={⊤}▷=> ∃ n, DB.server_view (si_init cs) (dbCN (si_resp cs).@"state") n db ∗
                         term_own (si_init cs) (dbCN (si_resp cs).@"status")
                         (server_view (Disconnected n)))%I
  with "[status]" as ">status".
{ iDestruct "status" as "[[-> fresh]|status]"; last first.
  { iDestruct "status" as "(%n & #server_view' & status)".
    iIntros "!> !> !>". iExists n. by iFrame. }
  iMod (escrowE with "server fresh") as "status" => //.
  iIntros "!> !> !>". iExists 0.  by iFrame. }
iIntros "!> !>".
iMod "status" as "(%n & #? & status)".
iPoseProof (term_own_valid_2 with "statusI status") as "%valid".
case/status_valid: valid => -> {n}.
iMod (term_own_update_2 with "statusI status") as "[statusI status]".
{ apply: server_connect_update. }
iAssert (|={⊤}=> conn_accepted cs beginning)%I
  with "[statusI]" as ">#accepted".
{ iApply (escrowI with "[statusI]"); first by iFrame.
  iApply conn_started_switch. }
iModIntro. iSplit.
{ iFrame. do 2!iSplit => //. iRight.
  iExists _, _. iFrame. by eauto. }
iIntros "!>". iExists _, _. iSplit => //.
rewrite e_rl. iSplit => //. iRight.
iExists _, _. by eauto.
Qed.

Lemma ack_init_predE cs m beginning E :
  ↑nroot.@"db" ⊆ E →
  is_conn_state cs 0 -∗
  client_connecting_int cs beginning -∗
  (session_fail cs ∗ public m ∨ ack_init_pred (si_key cs) m) ={E}=∗
  is_conn_state cs 0 ∗
  ▷ client_connected_int cs 0 beginning.
Proof.
iIntros "%sub conn".
iIntros "(%e_rl & client & #server & not_started & not_ended &
          #beginning & ending) m".
iPoseProof (conn_state_session with "conn") as "#sess". iFrame "conn".
iAssert (|={E}=> ▷ (session_fail cs ∨
                    term_own (si_init cs) (dbCN (si_resp cs).@"status")
                        (client_view (BothConnected (si_key cs) beginning))))%I
  with "[not_started m]" as ">status".
{ iDestruct "m" as "[[m _]|m]"; eauto.
  iDestruct "m" as "(%γ_sR & %si & %e_kS & #sess' & m)".
  iDestruct (session_agree with "sess' sess") as "[fail|->]" => //.
  { by iLeft. }
  iDestruct "m" as "[fail|m]".
  { by iLeft. }
  iDestruct "m" as "(%γ_sI & %beginning' & #sess'' & #beginning' &
                     #accepted)".
  rewrite e_rl.
  iDestruct (session_agree_name with "sess sess''") as "[fail|[_ <-]]" => //.
  { by iLeft. }
  iMod (escrowE with "accepted not_started") as "status" => //.
  eauto.
  by iPoseProof (gmeta_agree with "beginning beginning'") as "->". }
do !iModIntro.
iFrame. eauto.
Qed.

Definition store_pred kS m : iProp := ∃ (n : nat) t1 t2 si γ beginning,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  ⌜si_key si = kS⌝ ∗
  session γ si Init ∗
  public t1 ∗
  public t2 ∗
  gmeta γ (nroot.@"db".@"beginning") beginning ∗
  DB.update_at (si_init si) (dbCN (si_resp si).@"state") (n + beginning) t1 t2.

Lemma store_predI cs n beginning t1 t2 :
  is_conn_state cs (S n) -∗
  client_connected_int cs (S n) beginning -∗
  public t1 -∗
  public t2 -∗
  DB.update_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 t2 -∗
  is_conn_state cs (S n) ∗
  client_connected_int cs (S n) beginning ∗
  □ store_pred (si_key cs) (Spec.of_list [TInt n; t1; t2]).
Proof.
iIntros "conn (%e_rl & client & #server & not_ended &
          #beginning & ending & status)".
iPoseProof (conn_state_session with "conn") as "#sessI". iFrame "conn".
iIntros "#p_t1 #p_t2 #update".
iFrame. iSplit; first by eauto.
iModIntro. iExists n, t1, t2, cs, (cs_name cs), beginning. rewrite e_rl.
by eauto 10.
Qed.

Lemma store_predE cs n db t1 t2 :
  let m := Spec.of_list [TInt n; t1; t2] in
  is_conn_state cs n -∗
  server_connected cs n db -∗
  session_fail cs ∗ public m ∨ store_pred (si_key cs) m -∗
  is_conn_state cs n ∗
  server_connected cs (S n) (<[t1 := t2]>db).
Proof.
iIntros "%m conn server m_inv".
iPoseProof (conn_state_session with "conn") as "#sessR".
iFrame "conn".
iDestruct "server" as "(%e_rl & not_ended & #p_db & status)".
iFrame "not_ended".
iSplit => //.
iDestruct "m_inv" as "[[#fail #p_m]|m_inv]".
{ rewrite public_of_list /=.
  iDestruct "p_m" as "(_ & p_t1 & p_t2 & _)".
  iSplitR; last by eauto.
  by iApply public_db_insert. }
iDestruct "m_inv"
  as "(%n' & %t1' & %t2' & %si & %γ_sI & %beginning &
      %e_m & %e_kS & #sessI & #p_t1 & #p_t2 &
      #beginning & #update)".
case/Spec.of_list_inj: e_m => e_n <- <- {t1' t2'}.
have {e_n} <- : n = n' by lia.
iSplit.
{ by iApply public_db_insert. }
iDestruct "status" as "[#fail|status]"; first by eauto.
iDestruct "status"
  as "(%γ_sI' & %beginning' & #sessI' &
       #server & #beginning' & status)".
iPoseProof (session_agree with "sessI sessR") as "[fail|->]" => //.
{ by eauto. }
iPoseProof (session_agree_name with "sessI' sessI") as "[fail|[_ ->]]" => //.
{ by eauto. }
iPoseProof (gmeta_agree with "beginning' beginning") as "{beginning'} ->".
iPoseProof (DB.update_server with "server update") as "{server} server".
iRight. iExists _, _. iFrame.
do !iSplit => //.
Qed.

Definition ack_store_pred kS m : iProp := ∃ (n : nat),
  ⌜m = TInt n⌝. (* FIXME: Do we need anything else here? *)

Definition load_pred (kS m : term) : iProp := True.

Definition ack_load_pred (kS m : term) : iProp := ∃ n t1 t2 γ si,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  ⌜si_key si = kS⌝ ∗
  public t2 ∗
  session γ si Resp ∗
  (session_fail si ∨ ∃ γ' beginning,
   session γ' si Init ∗
   gmeta γ' (nroot.@"db".@"beginning") beginning ∗
   DB.stored_at (si_init si) (dbCN (si_resp si).@"state") (n + beginning) t1 t2).


Lemma ack_load_predI {cs n db t1 t2} :
  db !! t1 = Some t2 →
  is_conn_state cs n -∗
  server_connected cs n db -∗
  public (Spec.of_list [TInt n; t1; t2]) ∗
  □ ack_load_pred (si_key cs) (Spec.of_list [TInt n; t1; t2]).
Proof.
iIntros "%t1_t2 conn server".
iPoseProof (conn_state_session with "conn") as "#sessR".
iDestruct "server" as "(%e_rl & not_ended & #public & status)".
rewrite /public_db big_sepM_forall.
iDestruct ("public" with "[//]") as "[p_t1 p_t2]".
iSplit.
{ rewrite public_of_list /= public_TInt. by eauto. }
rewrite e_rl. iExists n, t1, t2, (cs_name cs), cs.
do !iSplitR => //.
iDestruct "status" as "[#fail|status]"; first by eauto.
iDestruct "status"
  as "(%γ_sI & %beginning & #sessI & #server & #beginning & _)".
iPoseProof (DB.load_server _ _ _ t1_t2 with "server") as "#load".
iModIntro. iRight. iExists _, _. by eauto.
Qed.

Lemma ack_loadE cs n beginning t1 t2 t2' :
  let m := Spec.of_list [TInt n; t1; t2'] in
  is_conn_state cs n -∗
  client_connected_int cs n beginning -∗
  rem_mapsto (si_init cs) (si_resp cs) t1 t2 -∗
  □ (session_fail cs ∗ public m ∨ ack_load_pred (si_key cs) m) -∗
  is_conn_state cs n ∗
  client_connected_int cs n beginning ∗
  rem_mapsto (si_init cs) (si_resp cs) t1 t2 ∗
  public t2' ∗
  (session_fail cs ∨ ⌜t2' = t2⌝).
Proof.
iIntros "conn (%e_rl & client & #server & not_ended &
          #beginning & ending & status)".
iPoseProof (conn_state_session with "conn") as "#sessI". iFrame "conn".
iIntros "mapsto".
iIntros "[[#fail p_m]|p_m]".
{ rewrite public_of_list /=. iDestruct "p_m" as "(_ & _ & p_t2' & _)".
  iFrame. iSplit; eauto. }
iDestruct "p_m"
  as "#(%n' & %t1' & %t2'' & %γ & %si & %e & %e_key & #p_t2' & #sessR & r)".
case/Spec.of_list_inj: e => e_n <- <- {t1' t2''}.
have {n' e_n} <-: n = n' by lia.
rewrite (assoc bi_sep). iSplit.
{ iSplitR "mapsto".
  { iFrame. by eauto. }
  by iFrame. }
iSplit => //.
iPoseProof (session_agree with "sessR sessI") as "[fail|->]" => //.
{ by iLeft. }
iDestruct "r" as "[fail|r]"; first by iLeft.
iDestruct "r"
  as "(%γ' & %beginning' & #sessI' & #beginning' & #stored)".
rewrite e_rl.
iPoseProof (session_agree_name with "sessI' sessI") as "[fail|[_ ->]]" => //.
{ by iLeft. }
iPoseProof (gmeta_agree with "beginning' beginning") as "{beginning'} ->".
iRight.
by iApply (DB.load_client with "client mapsto stored").
Qed.

Definition create_pred kS m : iProp := ∃ n t1 t2 si γ beginning,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  ⌜si_key si = kS⌝ ∗
  session γ si Init ∗
  gmeta γ (nroot.@"db".@"beginning") beginning ∗
  public t1 ∗
  public t2 ∗
  DB.create_at (si_init si) (dbCN (si_resp si).@"state") (n + beginning) t1 t2.

Lemma create_predI cs n m t1 t2 beginning :
  is_conn_state cs m -∗
  client_connected_int cs (S n) beginning -∗
  public t1 -∗
  public t2 -∗
  DB.create_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 t2 -∗
  is_conn_state cs m ∗
  client_connected_int cs (S n) beginning ∗
  □ create_pred (si_key cs) (Spec.of_list [TInt n; t1; t2]).
Proof.
iIntros "conn (%e_rl & client & #server & not_ended &
          #beginning & ending & status)".
iPoseProof (conn_state_session with "conn") as "#sessI". iFrame "conn".
iIntros "#p_t1 #p_t2 #create".
iFrame.
iSplit; first by eauto.
iExists n, t1, t2, cs, (cs_name cs), beginning. rewrite e_rl.
by eauto 10.
Qed.

Lemma public_create_pred cs n t1 t2 :
  let m := Spec.of_list [TInt n; t1; t2] in
  (session_fail cs ∗ public m ∨ create_pred (si_key cs) m) -∗
  public t1 ∗ public t2.
Proof.
iIntros "[[_ p_m]|m_inv]".
- rewrite public_of_list /=.
  iDestruct "p_m" as "(_ & p_t1 & p_t2 & _)".
  by eauto.
- iDestruct "m_inv"
    as "(%n' & %t1' & %t2' & %si & %γ_sI & %beginning &
       %e_m & %e_kS & #sessI & #beginning & #p_t1 & #p_t2 &
       #created)".
  case/Spec.of_list_inj: e_m => e_n <- <- {t1' t2'}.
  by eauto.
Qed.

Lemma create_predE cs n db t1 t2 :
  let m := Spec.of_list [TInt n; t1; t2] in
  db !! t1 = None →
  is_conn_state cs n -∗
  server_connected cs n db -∗
  (session_fail cs ∗ public m ∨ create_pred (si_key cs) m) -∗
  is_conn_state cs n ∗
  server_connected cs (S n) (<[t1 := t2]> db).
Proof.
iIntros "%m %db_t1 conn server m_inv".
iPoseProof (conn_state_session with "conn") as "#sessR".
iFrame "conn".
iDestruct "server" as "(%e_rl & not_ended & #p_db & status)".
iFrame. iSplitR => //.
iDestruct "m_inv" as "[[#fail #p_m] | m_inv]".
{ rewrite public_of_list /=.
  iDestruct "p_m" as "(_ & p_t1 & p_t2 & _)".
  iSplitR; last by eauto.
  by iApply public_db_insert. }
iDestruct "m_inv"
  as "(%n' & %t1' & %t2' & %si & %γ_sI & %beginning &
       %e_m & %e_kS & #sessI & #beginning & #p_t1 & #p_t2 &
       #created)".
case/Spec.of_list_inj: e_m => e_n <- <- {t1' t2'}.
have {n' e_n} <- : n = n' by lia.
iSplitR.
{  by iApply public_db_insert. }
iDestruct "status" as "[#fail | status]"; first by iLeft.
iDestruct "status"
  as "(%γ_sI' & %beginning' & #sessI' & #server &
       #beginning' & status)".
iPoseProof (session_agree_name with "sessI sessI'") as "[fail |[-> <-]]" => //.
{ by iLeft. }
iClear "sessI'".
iPoseProof (gmeta_agree with "beginning' beginning") as "{beginning'} ->".
iPoseProof (DB.create_server with "server created") as "{server} server" => //.
iRight.
iExists _, _. iFrame. by eauto.
Qed.

Definition ack_create_pred kS (m : term) : iProp := True.

Definition conn_done si beginning ending :=
  escrow (nroot.@"db")
         (conn_not_ended si Resp)
         (session_fail si ∨
            term_own (si_init si) (dbCN (si_resp si).@"status")
                 (client_view (ClientDisconnecting (si_key si) beginning ending))).

Definition close_pred kS m : iProp := ∃ n si γ beginning,
  ⌜m = TInt n⌝ ∗
  ⌜si_key si = kS⌝ ∗
  session γ si Init ∗
  gmeta γ (nroot.@"db".@"beginning") beginning ∗
  gmeta γ (nroot.@"db".@"ending") (n + beginning) ∗
  conn_done si beginning (n + beginning).

Lemma close_predI cs beginning n E :
  ↑nroot.@"db" ⊆ E →
  is_conn_state cs n -∗
  client_connected_int cs n beginning ={E}=∗
  is_conn_state cs n ∗
  client_disconnecting_int cs n beginning ∗
  □ close_pred (si_key cs) (TInt n).
Proof.
iIntros "%sub conn
         (%e_rl & client & #server & not_ended &
          #beginning & ending & status)".
iPoseProof (conn_state_session with "conn") as "#sess".
iFrame "conn".
iAssert (|==> (session_fail cs ∨
           term_own (si_init cs) (dbCN (si_resp cs).@"status")
                (client_view (ClientDisconnecting (si_key cs) beginning
                                (n + beginning)))))%I
  with "[status]" as ">status".
{ iDestruct "status" as "[fail|status]"; first by eauto.
  iRight.
  iApply (term_own_update with "status").
  exact: client_disconnect_update. }
iAssert (|={E}=> conn_done cs beginning (n + beginning))%I
  with "[status]" as ">#done".
{ iApply (escrowI with "status").
  iApply conn_ended_switch. }
iMod (gmeta_set _ _ (nroot.@"db".@"ending") (n + beginning) with "ending")
  as "#ending" => //.
iSplitL.
{ iFrame. by eauto. }
iIntros "!> !>". iExists n, cs, (cs_name cs), beginning.
rewrite -e_rl. by eauto 10.
Qed.

Definition conn_closed si ending :=
  escrow (nroot.@"db")
         (conn_not_ended si Init)
         (session_fail si ∨
             term_own (si_init si) (dbCN (si_resp si).@"status")
                  (client_view (BothDisconnected ending))).

Definition ack_close_pred kS (m : term) : iProp := ∃ si γ_sR,
  ⌜si_key si = kS⌝ ∗
  session γ_sR si Resp ∗
  (session_fail si ∨ ∃ γ_sI ending,
     session γ_sI si Init ∗
     gmeta γ_sI (nroot.@"db".@"ending") ending ∗
     conn_closed si ending).

Lemma ack_close_predI cs n db E :
  let m := TInt n in
  ↑nroot.@"db" ⊆ E →
  is_conn_state cs n -∗
  server_connected cs n db -∗
  session_fail cs ∗ public m ∨ close_pred (si_key cs) m ={E}▷=∗
  is_conn_state cs n ∗
  server_disconnected (si_init cs) (si_resp cs) db ∗
  □ ack_close_pred (si_key cs) (TInt 0).
Proof.
iIntros "%m %sub conn server p_m".
iPoseProof (conn_state_session with "conn") as "#sessR".
iFrame "conn".
iDestruct "server" as "(%e_rl & not_ended & #p_db & status)".
iAssert (□ (▷ session_fail cs ={E}▷=∗
              server_disconnected (si_init cs) (si_resp cs) db ∗
              □ ack_close_pred (si_key cs) (TInt 0)))%I
  as "#failure".
{ iIntros "!> #fail !> !> !>". iSplit.
  - iSplit => //. iLeft.
    by iDestruct "fail" as "[fail|fail]"; [iLeft|iRight];
    iApply public_at_public.
  - iModIntro. iExists _, _. rewrite e_rl. by eauto. }
iDestruct "status" as "[#fail|status]"; first by iApply "failure".
iDestruct "p_m" as "[[#fail _] | p_m]"; first by iApply "failure".
iDestruct "status" as
  "(%γ_sI & %beginning & #sessI & #server &
    #beginning & status)".
iDestruct "p_m" as
  "(%n' & %si & %γ_sI' & %beginning' & %e_m & %e_kS &
    #sessI' & #beginning' & #ending & #done)".
iPoseProof (session_agree_name with "sessI' sessI") as
  "[#fail | [-> ->]]" => //; first by iApply "failure".
iClear "sessI'".
iPoseProof (gmeta_agree with "beginning beginning'") as "{beginning'} <-".
case: e_m => e_n. have {e_n} <- : n = n' by lia.
iMod (escrowE with "done not_ended") as "[#fail|statusI]" => //;
  first by iApply "failure".
iIntros "!> !>".
iMod (term_own_update_2 with "statusI status") as "status".
{ apply: server_disconnect_update. }
iDestruct "status" as "[statusI status]".
iAssert (|={E}=> conn_closed cs (n + beginning))%I
  with "[statusI]" as ">#closed".
{ iApply (escrowI with "[statusI]").
  - by eauto.
  - iApply conn_ended_switch. }
iModIntro. iSplit.
- iSplit => //. iRight. iRight. iExists _. iFrame. by eauto.
- iModIntro. iExists cs, (cs_name cs). rewrite e_rl. do 2!iSplit => //.
  iRight. iExists _, _. by eauto.
Qed.

Lemma ack_close_predE cs m n beginning E :
  ↑nroot.@"db" ⊆ E →
  is_conn_state cs n -∗
  client_disconnecting_int cs n beginning -∗
  session_fail cs ∗ public m ∨ ack_close_pred (si_key cs) m ={E}=∗
  is_conn_state cs n ∗
  ▷ client_disconnected_int (si_init cs) (si_resp cs) (n + beginning).
Proof.
iIntros "%sub conn (%e_rl & client & #server & not_ended & #ending)".
iIntros "p_m".
iPoseProof (conn_state_session with "conn") as "#sessI".
iFrame "conn".
iDestruct "p_m" as "[[#fail _]|p_m]".
{ iFrame. iSplitR => //. iLeft. iModIntro.
  iDestruct "fail" as "[fail|fail]"; [iLeft|iRight];
  by iApply public_at_public. }
iDestruct "p_m" as "(%si & %γ_sR & %e_si & #sessR & p_m)" .
iDestruct (session_agree with "sessR sessI") as "[fail|->]" => //.
{ iFrame. do !iSplitR => //. iLeft. iModIntro.
  iDestruct "fail" as "[fail|fail]"; [iLeft|iRight];
  by iApply public_at_public. }
iDestruct "p_m" as "[fail|p_m]".
{ iFrame. do !iSplitR => //. iLeft. iModIntro.
  iDestruct "fail" as "[fail|fail]"; [iLeft|iRight];
  by iApply public_at_public. }
iDestruct "p_m"
  as "(%γ_sI & %ending & #sessI' & #ending' & #closed)".
rewrite e_rl.
iDestruct (session_agree_name with "sessI sessI'") as "[fail|[_ <-]]" => //.
{ iFrame. do !iSplitR => //. iLeft. iModIntro.
  iDestruct "fail" as "[fail|fail]"; [iLeft|iRight];
  by iApply public_at_public. }
iPoseProof (gmeta_agree with "ending' ending") as "{ending'} ->".
iMod (escrowE with "closed not_ended") as "[fail|status]" => //.
{ iFrame. do !iSplitR => //. iLeft. iModIntro.
  iDestruct "fail" as "[fail|fail]"; [iLeft|iRight];
  by iApply public_at_public. }
iFrame. by eauto.
Qed.

Definition server_handler_inv cs n ldb db : iProp :=
  server_connected cs n db ∗
  SAList.is_alist ldb (repr <$> db).

Definition server_handler_post cs ldb v : iProp := ∃ n db,
  ⌜v = #true⌝ ∗
  is_conn_state cs n ∗
  server_connected cs n db ∗
  SAList.is_alist ldb (repr <$> db) ∨
  ⌜v = #false⌝ ∗
  is_conn_state cs n ∗
  server_disconnected (si_init cs) (si_resp cs) db ∗
  SAList.is_alist ldb (repr <$> db).

Definition store_ctx : iProp :=
  enc_pred (N.@"init") init_pred ∗
  enc_pred (N.@"ack_init") ack_init_pred ∗
  enc_pred (N.@"store") store_pred ∗
  enc_pred (N.@"ack_store") ack_store_pred ∗
  enc_pred (N.@"load") load_pred ∗
  enc_pred (N.@"ack_load") ack_load_pred ∗
  enc_pred (N.@"create") create_pred ∗
  enc_pred (N.@"ack_create") ack_create_pred ∗
  enc_pred (N.@"close") close_pred ∗
  enc_pred (N.@"ack_close") ack_close_pred ∗
  dh_auth_ctx (N.@"auth").

Lemma store_ctx_alloc E :
  ↑N ⊆ E →
  enc_pred_token E ==∗
  store_ctx ∗ enc_pred_token (E ∖ ↑N).
Proof.
iIntros "%sub token".
rewrite (enc_pred_token_difference (↑N)) => //.
iDestruct "token" as "[token ?]". iFrame.
iMod (enc_pred_set (N.@"init") init_pred with "token")
  as "[init token]"; try solve_ndisj.
iFrame.
iMod (enc_pred_set (N.@"ack_init") ack_init_pred with "token")
  as "[ack_init token]"; try solve_ndisj.
iFrame.
iMod (enc_pred_set (N.@"store") store_pred with "token")
  as "[store token]"; try solve_ndisj.
iFrame.
iMod (enc_pred_set (N.@"ack_store") ack_store_pred with "token")
  as "[ack_store token]"; try solve_ndisj.
iFrame.
iMod (enc_pred_set (N.@"load") load_pred with "token")
  as "[load token]"; try solve_ndisj.
iFrame.
iMod (enc_pred_set (N.@"ack_load") ack_load_pred with "token")
  as "[ack_load token]"; try solve_ndisj.
iFrame.
iMod (enc_pred_set (N.@"create") create_pred with "token")
  as "[create token]"; try solve_ndisj.
iFrame.
iMod (enc_pred_set (N.@"ack_create") ack_create_pred with "token")
  as "[ack_create token]"; try solve_ndisj.
iFrame.
iMod (enc_pred_set (N.@"close") close_pred with "token")
  as "[close token]"; try solve_ndisj.
iFrame.
iMod (enc_pred_set (N.@"ack_close") ack_close_pred with "token")
  as "[ack_close token]"; try solve_ndisj.
iFrame.
iMod (dh_auth_ctx_alloc (N.@"auth") with "token")
  as "#dh_auth"; try solve_ndisj.
Qed.

Ltac solve_ctx :=
  iIntros "ctx"; repeat (
    try solve [iApply "ctx"];
    iDestruct "ctx" as "[H ctx]";
    first [iApply "H" | iClear "H"]
  ).

Lemma store_ctx_init : store_ctx -∗ enc_pred (N.@"init") init_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_init : store_ctx -∗ enc_pred (N.@"ack_init") ack_init_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_store : store_ctx -∗ enc_pred (N.@"store") store_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_store :
  store_ctx -∗ enc_pred (N.@"ack_store") ack_store_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_load :
  store_ctx -∗ enc_pred (N.@"load") load_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_load :
  store_ctx -∗ enc_pred (N.@"ack_load") ack_load_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_create :
  store_ctx -∗ enc_pred (N.@"create") create_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_create :
  store_ctx -∗ enc_pred (N.@"ack_create") ack_create_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_close :
  store_ctx -∗ enc_pred (N.@"close") close_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_close :
  store_ctx -∗ enc_pred (N.@"ack_close") ack_close_pred.
Proof. solve_ctx. Qed.

Lemma store_ctx_dh_auth_ctx : store_ctx -∗ dh_auth_ctx (N.@"auth").
Proof. solve_ctx. Qed.

End Defs.

Arguments storeGS Σ : clear implicits.
