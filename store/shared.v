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
From cryptis.store Require Import alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Record conn_state := ConnState {
  cs_si   :> sess_info;
  cs_ts   :  loc;
  cs_role :  role;
}.

#[global]
Instance cs_repr : Repr conn_state :=
  λ s, (#(cs_ts s), si_key s)%V.

Record server_state := {
  ss_key : term;
  ss_clients : val;
}.

#[global]
Instance ss_repr : Repr server_state :=
  λ s, (ss_key s, ss_clients s)%V.

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
  (session_fail cs ∨ session cs) ∗
  minted (si_key cs) ∗
  □ (∀ kt, public (TKey kt (si_key cs)) ↔ ▷ session_fail cs).

Definition db_not_signed_up kI kR : iProp :=
  term_token kR (↑dbSN kI).

Lemma db_signed_up_switch kI kR Q : ⊢ switch (db_not_signed_up kI kR) Q.
Proof. apply term_token_switch. Qed.

Definition server_status_ready kI kR :=
  escrow (nroot.@"db") (db_not_signed_up kI kR) (
    term_own kI (dbCN kR.@"status") (server_view (Disconnected 0))
  ).

Implicit Types (ls : lstatus) (gs : gstatus).

Definition key_corruption kI kR : iProp :=
  public (TKey Seal kI) ∨ public (TKey Seal kR).

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
  (session_fail cs ∨
     term_meta (si_key cs) (nroot.@"client".@"beginning") beginning ∗
     term_token (si_key cs) (↑nroot.@"client".@"end") ∗
     term_token (si_key cs) (↑nroot.@"client".@"ending") ∗
     term_own kI (dbCN kR.@"status")
       (client_view (BothConnected (si_key cs) beginning))).

Definition client_connecting_int cs beginning : iProp :=
  let kI := si_init cs in
  let kR := si_resp cs in
  ⌜cs_role cs = Init⌝ ∗
  DB.client_view kI (dbCN kR.@"state") beginning ∗
  server_status_ready kI kR ∗
  (session_fail cs ∨
     term_token (si_key cs) (↑nroot.@"client".@"begin") ∗
     term_token (si_key cs) (↑nroot.@"client".@"end") ∗
     term_meta  (si_key cs) (nroot.@"client".@"beginning") beginning ∗
     term_token (si_key cs) (↑nroot.@"client".@"ending")).

Definition client_disconnecting_int cs n beginning : iProp :=
  let kI := si_init cs in
  let kR := si_resp cs in
  ⌜cs_role cs = Init⌝ ∗
  DB.client_view kI (dbCN kR.@"state") (n + beginning) ∗
  server_status_ready kI kR ∗
  (session_fail cs ∨
     term_token (si_key cs) (↑nroot.@"client".@"end") ∗
     term_meta  (si_key cs) (nroot.@"client".@"ending") (n + beginning)).

Definition conn_ready si n :=
  escrow (nroot.@"db")
         (term_token (si_key si) (↑nroot.@"server".@"begin"))
         (term_own (si_init si) (dbCN (si_resp si).@"status")
            (client_view (ClientConnecting (si_key si) n))).

Lemma client_connectingI E kI kR cs dq n beginning :
  ↑cryptisN ⊆ E →
  ↑nroot.@"db" ⊆ E →
  si_init cs = kI →
  si_resp cs = kR →
  si_time cs = n  →
  cs_role cs = Init →
  cryptis_ctx -∗
  £ 1 ∗ £ 1 -∗
  ●Ph{dq} n -∗
  session_fail cs ∨
    term_token (si_key cs) (↑nroot.@"client") -∗
  client_disconnected_int kI kR beginning ={E}=∗
  ●Ph{dq} n ∗
  client_connecting_int cs beginning ∗
  (session_fail cs ∨
     term_meta (si_key cs) (nroot.@"client".@"beginning") beginning ∗
     conn_ready cs beginning).
Proof.
move=> ? ? <- <- <- e_rl {kI kR n}.
iIntros "#? [c1 c2] hon token client".
iDestruct "client" as "(client_view & #server & status)".
iPoseProof (DB.client_view_server_view with "client_view")
  as "(%db & #server_view)".
iDestruct "status" as "[#fail|status]".
{ iAssert (|={E}=> ●Ph{dq} si_time cs ∗ session_fail cs)%I
    with "[c1 hon]" as ">[hon #fail']".
  { iDestruct "fail" as "[fail|fail]".
    - iMod (public_atI with "[] c1 hon fail") as "{fail} [hon fail]";
        eauto.
      { solve_ndisj. }
      by iFrame.
    - iMod (public_atI with "[] c1 hon fail") as "{fail} [hon fail]";
        eauto.
      { solve_ndisj. }
      by iFrame. }
  iFrame. iModIntro. iSplit => //; last by iLeft. iSplit => //.
  iSplit => //. by iLeft. }
iDestruct "token" as "[#fail|token]".
{ iFrame. iModIntro. iSplit => //; last by iLeft. iSplit => //.
  iSplit => //. by iLeft. }
iFrame.
iMod (term_own_update with "status") as "status".
{ apply: (client_connect_update (si_key cs)). }
iAssert (|={E}=> conn_ready cs beginning)%I with "[status]" as ">#ready".
{ iApply (escrowI with "status").
  iApply term_token_switch. }
iMod (term_meta_set' (N:=nroot.@"client".@"beginning") beginning with "token")
  as "[#beginning token]"; try solve_ndisj.
iSplitL; last by iRight; eauto.
iSplitR => //. iSplitR => //. iRight.
rewrite (term_token_difference _ (↑nroot.@"client".@"begin"));
  try solve_ndisj.
iDestruct "token" as "[token' token]". iFrame "token'".
rewrite (term_token_difference _ (↑nroot.@"client".@"end")); try solve_ndisj.
iDestruct "token" as "[token' token]". iFrame "token'".
iSplitR => //. iModIntro.
iApply (term_token_drop with "token"). solve_ndisj.
Qed.

Definition conn_accepted si beginning :=
  escrow (nroot.@"db")
    (term_token (si_key si) (↑nroot.@"client".@"begin"))
    (term_own (si_init si) (dbCN (si_resp si).@"status")
       (client_view (BothConnected (si_key si) beginning))).

Lemma client_connected_intI cs beginning E :
  ↑nroot.@"db" ⊆ E →
  client_connecting_int cs beginning -∗
  session_fail cs ∨ conn_accepted cs beginning ={E}=∗
  ▷ client_connected_int cs 0 beginning.
Proof.
move=> sub.
iIntros "(%e_rl & client & #server & conn) #status".
iFrame. do !iSplitR => //.
iDestruct "status" as "[fail|accepted]"; first by eauto.
iDestruct "conn" as "[#fail|conn]"; first by eauto.
iDestruct "conn" as "(not_started & ? & #? & ?)".
iMod (escrowE with "accepted not_started") as "status" => //.
iIntros "!> !>". iRight. iFrame. by eauto.
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
  client_connected_int cs n beginning -∗
  rem_mapsto (si_init cs) (si_resp cs) t1 t2 ==∗
  client_connected_int cs (S n) beginning ∗
  rem_mapsto (si_init cs) (si_resp cs) t1 t2' ∗
  DB.update_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 t2'.
Proof.
iIntros "(%e_rl & client & #server & conn) mapsto".
iMod (DB.update_client t2' with "client mapsto")
  as "(client & #update & mapsto)".
iFrame. iSplitR => //. by eauto.
Qed.

Lemma rem_mapsto_alloc cs t1 t2 n beginning T :
  t1 ∈ T →
  client_connected_int cs n beginning -∗
  rem_free_at (si_init cs) (si_resp cs) T ==∗
  client_connected_int cs (S n) beginning ∗
  rem_mapsto (si_init cs) (si_resp cs) t1 t2 ∗
  rem_free_at (si_init cs) (si_resp cs) (T ∖ {[t1]}) ∗
  DB.create_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 t2.
Proof.
iIntros "%t1_T (%e_rl & client & #server & conn)".
have {}t1_T : {[t1]} ⊆ T by set_solver.
rewrite (rem_free_at_diff _ _ t1_T).
iIntros "[free free']". iFrame "free'".
iMod (DB.create_client _ t2 with "client free") as "(create & client & mapsto)".
iFrame. by eauto.
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
  public_db db ∗
  (session_fail cs ∨ ∃ beginning,
   DB.server_view (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) db ∗
   term_meta (si_key cs) (nroot.@"client".@"beginning") beginning ∗
   term_token (si_key cs) (↑nroot.@"server".@"end") ∗
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

Lemma server_connectingI cs db dq :
  cryptis_ctx -∗
  ●Ph{dq} si_time cs -∗
  £ 1 -∗
  server_disconnected (si_init cs) (si_resp cs) db ={⊤}=∗
  ●Ph{dq} si_time cs ∗
  server_connecting cs db.
Proof.
iIntros "#ctx hon c (#p_db & [#fail | status])"; last first.
{ iModIntro. iFrame. by eauto. }
iAssert (|={⊤}=> ●Ph{dq} si_time cs ∗ session_fail cs)%I
  with "[hon c]" as "{fail} >[hon fail]".
{ iDestruct "fail" as "[fail|fail]".
  - iMod (public_atI with "[] c hon fail") as "[hon ?]" => //; eauto.
    iModIntro. by iFrame.
  - iMod (public_atI with "[] c hon fail") as "[hon ?]" => //; eauto.
    iModIntro. by iFrame. }
iModIntro. iFrame. by eauto.
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
  public (TKey Open (ss_key ss)) ∗
  SAList.is_alist (ss_clients ss) (repr <$> accounts) ∗
  term_token (ss_key ss) E ∗
  ⌜∀ kI, TKey Open kI ∉ dom accounts → ↑dbSN kI ⊆ E⌝ ∗
  [∗ map] vkI ↦ scs ∈ accounts, ∃ kI, ⌜vkI = TKey Open kI⌝ ∗
     is_lock (scs_name scs) (scs_lock scs)
       (account_inv kI (ss_key ss) (scs_db scs)).

Lemma serverI kR vclients :
  term_token kR (↑nroot.@"db".@"server") -∗
  public (TKey Open kR) -∗
  SAList.is_alist vclients ∅ -∗
  server {| ss_key := kR; ss_clients := vclients |}.
Proof.
iIntros "token #p_vk clients".
iExists ∅, (↑nroot.@"db".@"server") => /=.
iFrame. iSplit => //. iSplit => //.
iPureIntro. move=> *. solve_ndisj.
Qed.

Definition session_msg_pred (Q : sess_info → term → iProp) kS m : iProp :=
  ∃ si : sess_info, ⌜kS = (si_key si)⌝ ∗ session si ∗ public m ∗ Q si m.

Definition init_pred si t : iProp := ∃ (beginning : nat),
  server_status_ready (si_init si) (si_resp si) ∗
  DB.server_view (si_init si) (dbCN (si_resp si).@"state") 0 ∅ ∗
  term_meta (si_key si) (nroot.@"client".@"beginning") beginning ∗
  conn_ready si beginning.

Lemma init_predI cs beginning m :
  client_connecting_int cs beginning -∗
  session_fail cs ∨ conn_ready cs beginning -∗
  (session_fail cs ∨ □ init_pred cs m).
Proof.
iIntros "(%e_rl & client & #server & [#fail|conn_meta]) #ready".
{ iFrame. by eauto 10. }
iDestruct "ready" as "[fail|ready]"; first by eauto.
iDestruct "conn_meta" as "(? & ? & #? & ?)".
iPoseProof (DB.client_view_server_view with "client")
  as "(%db & #server_view)".
iPoseProof (DB.server_view_to_0 with "server_view") as "#server_view0".
iRight. iModIntro. iExists _. by eauto 10.
Qed.

Definition ack_init_pred si t : iProp := ∃ (beginning : nat),
  term_meta (si_key si) (nroot.@"client".@"beginning") beginning ∗
  conn_accepted si beginning.

Lemma ack_init_predI cs db m :
  cs_role cs = Resp →
  server_connecting cs db -∗
  term_token (si_key cs) (↑nroot.@"server".@"begin") -∗
  term_token (si_key cs) (↑nroot.@"server".@"end") -∗
  (session_fail cs ∨ init_pred cs m) ={⊤}▷=∗
  server_connected cs 0 db ∗
  (session_fail cs ∨ □ ack_init_pred cs (TInt 0)).
Proof.
iIntros "%e_rl (#p_db & status) not_started not_ended p_m".
iDestruct "p_m" as "[#fail|p_m]".
{ iIntros "!> !> !>". iSplit; last by iLeft.
  do !iSplit => //. by eauto. }
iDestruct "status" as "[#fail|status]".
{ iIntros "!> !> !>". iSplit; last by iLeft.
  do !iSplit => //. by eauto. }
iDestruct "p_m"
  as "(%beginning & #server & #server_view & #beginning & #conn_ready)".
iMod (escrowE with "conn_ready not_started") as "statusI" => //.
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
  iApply term_token_switch. }
iModIntro. iSplit.
{ iFrame. do 2!iSplit => //. iRight.
  iExists _. iFrame. by eauto. }
iRight. iIntros "!>". iExists _. do !iSplit => //.
Qed.

Lemma ack_init_predE cs m beginning E :
  ↑nroot.@"db" ⊆ E →
  client_connecting_int cs beginning -∗
  (session_fail cs ∨ ack_init_pred cs m) ={E}=∗
  ▷ client_connected_int cs 0 beginning.
Proof.
iIntros "%sub".
iIntros "(%e_rl & client & #server & conn) m".
iDestruct "m" as "[#fail|m]".
{ do !iModIntro. iFrame. do !iSplit => //. by iLeft. }
iDestruct "conn" as "[#fail|conn]".
{ do !iModIntro. iFrame. do !iSplit => //. by iLeft. }
iDestruct "conn" as "(begin & end & #beginning & ending)".
iDestruct "m" as "(%beginning' & #beginning' & #accepted)".
iPoseProof (term_meta_agree with "beginning' beginning") as "->".
iMod (escrowE with "accepted begin") as "status" => //.
do !iModIntro. iFrame. eauto. do !iSplit => //. iRight.
iFrame. by eauto.
Qed.

Definition store_pred si m : iProp := ∃ (n : nat) t1 t2 beginning,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  term_meta (si_key si) (nroot.@"client".@"beginning") beginning ∗
  DB.update_at (si_init si) (dbCN (si_resp si).@"state") (n + beginning) t1 t2.

Lemma store_predI cs n beginning t1 t2 :
  client_connected_int cs (S n) beginning -∗
  DB.update_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 t2 -∗
  session_fail cs ∨
  □ store_pred cs (Spec.of_list [TInt n; t1; t2]).
Proof.
iIntros "(%e_rl & client & #server & conn) #update".
iDestruct "conn" as "[?|conn]"; eauto.
iDestruct "conn" as "(#? & ? & ? & ?)". iRight.
iModIntro. iExists _. by eauto 10.
Qed.

Lemma store_predE cs n db t1 t2 :
  let m := Spec.of_list [TInt n; t1; t2] in
  server_connected cs n db -∗
  public m -∗
  session_fail cs ∨ store_pred cs m -∗
  server_connected cs (S n) (<[t1 := t2]>db).
Proof.
iIntros "%m server p_m m_inv".
rewrite public_of_list /=.
iDestruct "p_m" as "(_ & #p_t1 & #p_t2 & _)".
iDestruct "server" as "(%e_rl & #p_db & status)".
iDestruct "m_inv" as "[#fail|m_inv]".
{ do !iSplit => //; eauto.
  by iApply public_db_insert. }
iDestruct "m_inv" as "(%n' & %t1' & %t2' & %beginning &
      %e_m & #beginning & #update)".
case/Spec.of_list_inj: e_m => e_n <- <- {t1' t2'}.
have {e_n} <- : n = n' by lia.
iDestruct "status" as "[#fail|status]".
{ do !iSplit => //; eauto.
  by iApply public_db_insert. }
iDestruct "status"
  as "(%beginning' & #server & #beginning' & end & status)".
iPoseProof (term_meta_agree with "beginning' beginning") as "{beginning'} ->".
iPoseProof (DB.update_server with "server update") as "{server} server".
do !iSplit => //.
{ by iApply public_db_insert. }
iRight. iExists beginning. iFrame. by eauto.
Qed.

Definition ack_store_pred (si : sess_info) m : iProp := ∃ (n : nat),
  ⌜m = TInt n⌝. (* FIXME: Do we need anything else here? *)

Definition load_pred (si : sess_info) (m : term) : iProp := True.

Definition ack_load_pred si m : iProp := ∃ n t1 t2 beginning,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  term_meta (si_key si) (nroot.@"client".@"beginning") beginning ∗
  DB.stored_at (si_init si) (dbCN (si_resp si).@"state") (n + beginning) t1 t2.

Lemma ack_load_predI {cs n db t1 t2} :
  db !! t1 = Some t2 →
  server_connected cs n db -∗
  public (Spec.of_list [TInt n; t1; t2]) ∗
  (session_fail cs ∨ □ ack_load_pred cs (Spec.of_list [TInt n; t1; t2])).
Proof.
iIntros "%t1_t2 server".
iDestruct "server" as "(%e_rl & #public & status)".
rewrite /public_db big_sepM_forall.
iDestruct ("public" with "[//]") as "[p_t1 p_t2]".
iSplit.
{ rewrite public_of_list /= public_TInt. by eauto. }
iDestruct "status" as "[#fail|status]"; first by eauto.
iDestruct "status" as "(%beginning & #server & #beginning & _)".
iRight. iModIntro. iExists n, t1, t2, beginning. do !iSplit => //.
by iPoseProof (DB.load_server _ _ _ t1_t2 with "server") as "#load".
Qed.

Lemma ack_loadE cs n beginning t1 t2 t2' :
  let m := Spec.of_list [TInt n; t1; t2'] in
  client_connected_int cs n beginning -∗
  rem_mapsto (si_init cs) (si_resp cs) t1 t2 -∗
  public m -∗
  □ (session_fail cs ∨ ack_load_pred cs m) -∗
  public t2' ∗ (session_fail cs ∨ ⌜t2' = t2⌝).
Proof.
iIntros "%m (%e_rl & client & #server & conn) mapsto #p_m #inv_m".
rewrite public_of_list /=.
iDestruct "p_m" as "(_ & _ & p_t2' & _)".
iSplit => //.
iDestruct "inv_m" as "[#fail|#inv_m]"; first by eauto.
iDestruct "inv_m"
  as "#(%n' & %t1' & %t2'' & %beginning' & %e & #beginning' & #stored)".
case/Spec.of_list_inj: e => e_n <- <- {t1' t2''}.
have {n' e_n} <-: n = n' by lia.
iDestruct "conn" as "[#fail|conn]"; first by eauto.
iRight.
iDestruct "conn" as "(#beginning & ?)".
iPoseProof (term_meta_agree with "beginning' beginning") as "{beginning'} ->".
by iApply (DB.load_client with "client mapsto stored").
Qed.

Definition create_pred si m : iProp := ∃ n t1 t2 beginning,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  term_meta (si_key si) (nroot.@"client".@"beginning") beginning ∗
  DB.create_at (si_init si) (dbCN (si_resp si).@"state") (n + beginning) t1 t2.

Lemma create_predI cs n t1 t2 beginning :
  client_connected_int cs (S n) beginning -∗
  public t1 -∗
  public t2 -∗
  DB.create_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 t2 -∗
  session_fail cs ∨
  □ create_pred cs (Spec.of_list [TInt n; t1; t2]).
Proof.
iIntros "(%e_rl & client & #server & conn) #p_t1 #p_t2 #create".
iDestruct "conn" as "[fail|conn]"; eauto. iRight.
iDestruct "conn" as "(#? & ? & ? & ?)".
iModIntro.
iExists n, t1, t2, beginning.
by eauto 10.
Qed.

Lemma create_predE cs n db t1 t2 :
  let m := Spec.of_list [TInt n; t1; t2] in
  db !! t1 = None →
  server_connected cs n db -∗
  public m -∗
  (session_fail cs ∨ create_pred cs m) -∗
  server_connected cs (S n) (<[t1 := t2]> db).
Proof.
iIntros "%m %db_t1 server #p_m m_inv".
rewrite public_of_list /=.
iDestruct "p_m" as "(_ & p_t1 & p_t2 & _)".
iDestruct "server" as "(%e_rl & #p_db & status)".
iSplitR => //.
iSplitR => //.
{ by iApply public_db_insert. }
iDestruct "m_inv" as "[#fail| m_inv]"; first by eauto.
iDestruct "m_inv"
  as "(%n' & %t1' & %t2' & %beginning & %e_m & #beginning & #created)".
case/Spec.of_list_inj: e_m => e_n <- <- {t1' t2'}.
have {n' e_n} <- : n = n' by lia.
iDestruct "status" as "[#fail | status]"; first by iLeft.
iDestruct "status"
  as "(%beginning' & #server & #beginning' & status)".
iPoseProof (term_meta_agree with "beginning' beginning") as "{beginning'} ->".
iPoseProof (DB.create_server with "server created") as "{server} server" => //.
iRight.
iExists _. iFrame. by eauto.
Qed.

Definition ack_create_pred (si : sess_info) (m : term) : iProp := True.

Definition conn_done si beginning ending :=
  escrow (nroot.@"db")
         (term_token (si_key si) (↑nroot.@"server".@"end"))
         (term_own (si_init si) (dbCN (si_resp si).@"status")
            (client_view (ClientDisconnecting (si_key si) beginning ending))).

Definition close_pred si m : iProp := ∃ n beginning,
  ⌜m = TInt n⌝ ∗
  term_meta (si_key si) (nroot.@"client".@"beginning") beginning ∗
  term_meta (si_key si) (nroot.@"client".@"ending") (n + beginning) ∗
  conn_done si beginning (n + beginning).

Lemma close_predI cs beginning n E :
  ↑nroot.@"db" ⊆ E →
  client_connected_int cs n beginning ={E}=∗
  client_disconnecting_int cs n beginning ∗
  (session_fail cs ∨ □ close_pred cs (TInt n)).
Proof.
iIntros "%sub (%e_rl & client & #server & conn)".
iDestruct "conn" as "[#fail|conn]".
{ iModIntro. iSplit; last by eauto. iFrame.
  do !iSplit => //. by eauto. }
iDestruct "conn" as "(#beginning & end & ending & status)".
iMod (term_own_update with "status") as "status".
{ exact: (@client_disconnect_update _ _ (n + beginning)). }
iAssert (|={E}=> conn_done cs beginning (n + beginning))%I
  with "[status]" as ">#done".
{ iApply (escrowI with "status").
  iApply term_token_switch. }
iMod (term_meta_set (nroot.@"client".@"ending") (n + beginning) with "ending")
  as "#ending" => //.
iSplitL.
{ iFrame. iModIntro. by eauto. }
iIntros "!>". iRight. iExists n, beginning.
by eauto 10.
Qed.

Definition conn_closed si ending :=
  escrow (nroot.@"db")
         (term_token (si_key si) (↑nroot.@"client".@"end"))
         (term_own (si_init si) (dbCN (si_resp si).@"status")
                  (client_view (BothDisconnected ending))).

Definition ack_close_pred si (m : term) : iProp := ∃ ending,
  term_meta (si_key si) (nroot.@"client".@"ending") ending ∗
  conn_closed si ending.

Lemma ack_close_predI cs n db E :
  let m := TInt n in
  ↑nroot.@"db" ⊆ E →
  server_connected cs n db -∗
  session_fail cs ∨ close_pred cs m ={E}▷=∗
  server_disconnected (si_init cs) (si_resp cs) db ∗
  (session_fail cs ∨ □ ack_close_pred cs (TInt 0)).
Proof.
iIntros "%m %sub server p_m".
iDestruct "server" as "(%e_rl & #p_db & status)".
iDestruct "p_m" as "[#fail|p_m]".
{ do !iModIntro. iSplit; eauto.
  do !iSplit => //. iLeft.
  by iDestruct "fail" as "[fail|fail]"; [iLeft|iRight];
  iApply public_at_public. }
iDestruct "status" as "[#fail|status]".
{ do !iModIntro. iSplit; eauto.
  do !iSplit => //. iLeft.
  by iDestruct "fail" as "[fail|fail]"; [iLeft|iRight];
  iApply public_at_public. }
iDestruct "status" as
  "(%beginning & #server & #beginning & end & status)".
iDestruct "p_m" as
  "(%n' & %beginning' & %e_m & #beginning' & #ending & #done)".
iPoseProof (term_meta_agree with "beginning beginning'") as "{beginning'} <-".
case: e_m => e_n. have {e_n} <- : n = n' by lia.
iMod (escrowE with "done end") as "statusI" => //.
iIntros "!> !>".
iMod (term_own_update_2 with "statusI status") as "status".
{ apply: server_disconnect_update. }
iDestruct "status" as "[statusI status]".
iAssert (|={E}=> conn_closed cs (n + beginning))%I
  with "[statusI]" as ">#closed".
{ iApply (escrowI with "[statusI]").
  - by eauto.
  - iApply term_token_switch. }
iModIntro. iSplit.
- iSplit => //. iRight. iRight. iExists _. iFrame. by eauto.
- iRight. iModIntro. iExists _. iFrame. by eauto.
Qed.

Lemma ack_close_predE cs m n beginning E :
  ↑nroot.@"db" ⊆ E →
  client_disconnecting_int cs n beginning -∗
  session_fail cs ∨ ack_close_pred cs m ={E}=∗
  ▷ client_disconnected_int (si_init cs) (si_resp cs) (n + beginning).
Proof.
iIntros "%sub (%e_rl & client & #server & conn) p_m".
iDestruct "p_m" as "[#fail|p_m]".
{ iFrame. iSplitR => //. iLeft. iModIntro.
  iDestruct "fail" as "[fail|fail]"; [iLeft|iRight];
  by iApply public_at_public. }
iDestruct "p_m" as "(%ending & #ending' & #closed)".
iDestruct "conn" as "[#fail|(end & #ending)]".
{ iFrame. iSplitR => //. iLeft. iModIntro.
  iDestruct "fail" as "[fail|fail]"; [iLeft|iRight];
  by iApply public_at_public. }
iPoseProof (term_meta_agree with "ending' ending") as "{ending'} ->".
iMod (escrowE with "closed end") as "status" => //.
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
  seal_pred (N.@"init")       (session_msg_pred init_pred) ∗
  seal_pred (N.@"ack_init")   (session_msg_pred ack_init_pred) ∗
  seal_pred (N.@"store")      (session_msg_pred store_pred) ∗
  seal_pred (N.@"ack_store")  (session_msg_pred ack_store_pred) ∗
  seal_pred (N.@"load")       (session_msg_pred load_pred) ∗
  seal_pred (N.@"ack_load")   (session_msg_pred ack_load_pred) ∗
  seal_pred (N.@"create")     (session_msg_pred create_pred) ∗
  seal_pred (N.@"ack_create") (session_msg_pred ack_create_pred) ∗
  seal_pred (N.@"close")      (session_msg_pred close_pred) ∗
  seal_pred (N.@"ack_close")  (session_msg_pred ack_close_pred) ∗
  iso_dh_ctx (N.@"auth").

Lemma store_ctx_alloc E :
  ↑N ⊆ E →
  seal_pred_token E ==∗
  store_ctx ∗ seal_pred_token (E ∖ ↑N).
Proof.
iIntros "%sub token".
rewrite (seal_pred_token_difference (↑N)) => //.
iDestruct "token" as "[token ?]". iFrame.
iMod (seal_pred_set (N.@"init") with "token")
  as "[init token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"ack_init") with "token")
  as "[ack_init token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"store") with "token")
  as "[store token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"ack_store") with "token")
  as "[ack_store token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"load") with "token")
  as "[load token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"ack_load") with "token")
  as "[ack_load token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"create") with "token")
  as "[create token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"ack_create") with "token")
  as "[ack_create token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"close") with "token")
  as "[close token]"; try solve_ndisj.
iFrame.
iMod (seal_pred_set (N.@"ack_close") with "token")
  as "[ack_close token]"; try solve_ndisj.
iFrame.
iMod (iso_dh_ctx_alloc (N.@"auth") with "token")
  as "#iso_dh"; try solve_ndisj.
Qed.

Ltac solve_ctx :=
  iIntros "ctx"; repeat (
    try solve [iApply "ctx"];
    iDestruct "ctx" as "[H ctx]";
    first [iApply "H" | iClear "H"]
  ).

Lemma store_ctx_init :
  store_ctx -∗ seal_pred (N.@"init") (session_msg_pred init_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_init :
  store_ctx -∗ seal_pred (N.@"ack_init") (session_msg_pred ack_init_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_store :
  store_ctx -∗ seal_pred (N.@"store") (session_msg_pred store_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_store :
  store_ctx -∗ seal_pred (N.@"ack_store") (session_msg_pred ack_store_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_load :
  store_ctx -∗ seal_pred (N.@"load") (session_msg_pred load_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_load :
  store_ctx -∗ seal_pred (N.@"ack_load") (session_msg_pred ack_load_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_create :
  store_ctx -∗ seal_pred (N.@"create") (session_msg_pred create_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_create :
  store_ctx -∗ seal_pred (N.@"ack_create") (session_msg_pred ack_create_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_close :
  store_ctx -∗ seal_pred (N.@"close") (session_msg_pred close_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_close :
  store_ctx -∗ seal_pred (N.@"ack_close") (session_msg_pred ack_close_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_dh_auth_ctx : store_ctx -∗ iso_dh_ctx (N.@"auth").
Proof. solve_ctx. Qed.

End Defs.

Arguments storeGS Σ : clear implicits.
