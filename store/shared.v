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

Definition cs_share cs := si_share_of (cs_role cs) cs.

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

Definition statusR := dfrac_agreeR natO.

Class storeGS Σ := StoreGS {
  storeGS_db      : dbGS Σ;
  storeGS_status  : inG Σ statusR;
}.

Local Existing Instance storeGS_db.
Local Existing Instance storeGS_status.

Definition storeΣ := #[
  dbΣ;
  GFunctor statusR
].

Global Instance subG_storeGS Σ : subG storeΣ Σ → storeGS Σ.
Proof. solve_inG. Qed.

Section Defs.

Context `{!cryptisGS Σ, !heapGS Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : conn_state).
Implicit Types (kI kR kS t : term) (ts : list term).
Implicit Types db : gmap term term.
Implicit Types accounts : gmap term server_client_state.
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types γ γ_db γ_s : gname.
Implicit Types v : val.
Implicit Types (ok : Prop) (failed : bool).
Implicit Types si : sess_info.

Variable N : namespace.

Definition dbCN kR := nroot.@"db".@"client".@kR.
Definition dbSN kI := nroot.@"db".@"server".@kI.

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
  term_token kR (↑dbSN kI).

Lemma never_connected_switch kI kR Q : ⊢ switch (never_connected kI kR) Q.
Proof. apply term_token_switch. Qed.

Definition clock kI kR n :=
  term_own kI (dbCN kR.@"status") (to_frac_agree (1 / 2) n).

Lemma clock_alloc kI kR E :
  ↑dbCN kR.@"status" ⊆ E →
  term_token kI E ==∗
  clock kI kR 0 ∗
  clock kI kR 0 ∗
  term_token kI (E ∖ ↑dbCN kR.@"status").
Proof.
iIntros "%sub token".
iMod (term_own_alloc (dbCN kR.@"status") (to_frac_agree 1 0)
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
  escrow (nroot.@"db") (never_connected kI kR)
    (clock kI kR 0).

Definition client_disconnected kI kR n failed : iProp :=
  server_clock_ready kI kR ∗
  if failed then failure kI kR else clock kI kR n.

Definition db_disconnected kI kR : iProp := ∃ n failed,
  DB.client_view kI (dbCN kR.@"state") n ∗
  client_disconnected kI kR n failed.

Definition client_disconnecting kI kR cs : iProp :=
  ⌜cs_role cs = Init⌝ ∗
  server_clock_ready kI kR ∗
  term_token (si_init_share cs) (↑isoN.@"end").

Definition connected kI kR cs n n0 : iProp :=
  ⌜si_init cs = kI⌝ ∗
  ⌜si_resp cs = kR⌝ ∗
  wf_sess_info cs ∗
  (∃ failed, session_failed_for cs (cs_role cs) failed) ∗
  release_token (cs_share cs) ∗
  cs_ts cs ↦ #n ∗
  (∃ failed, session_failed cs failed) ∗
  (session_failed cs true ∨
     term_meta (si_init_share cs) (isoN.@"beginning") n0).

Lemma connected_keyE kI kR cs n n0 :
  connected kI kR cs n n0 -∗
  ⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝.
Proof. by iIntros "(-> & -> & _)". Qed.

Definition client_token kI kR cs : iProp :=
  ⌜cs_role cs = Init⌝ ∗
  server_clock_ready kI kR ∗
  term_token (si_init_share cs) (↑isoN.@"end").

Definition db_connected kI kR cs : iProp := ∃ n n0,
  DB.client_view kI (dbCN kR.@"state") (n + n0) ∗
  connected kI kR cs n n0 ∗
  client_token kI kR cs.

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
  escrow (nroot.@"db")
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
  ▷ (connected (si_init cs) (si_resp cs) cs 0 n0 ∗
     client_token (si_init cs) (si_resp cs) cs).
Proof.
iIntros "%e_rl (#server & #? & ? & ? & #conn) ts rel #status".
rewrite /connected /client_token /cs_share e_rl /=.
iFrame. do 2!iModIntro. do 4!iSplit => //.
iSplit; eauto.
iExists (failedI || failedR).
case: failedI => /=; eauto.
case: failedR => /=; eauto.
Qed.

Lemma connected_ok kI kR cs n n0 :
  connected kI kR cs n n0 -∗
  (failure kI kR -∗ ▷ False) -∗
  ◇ session_failed cs false.
Proof.
iIntros "(<- & <- & #conn & #? & rel & ts & #(%failed & status) & _) post".
by iDestruct (session_okI with "status post") as ">?".
Qed.

Lemma db_connected_ok kI kR cs :
  db_connected kI kR cs -∗
  (failure kI kR -∗ ▷ False) -∗
  ◇ session_failed cs false.
Proof.
iIntros "(% & % & ? & conn & _) fail".
iApply (connected_ok with "conn fail").
Qed.

Definition rem_mapsto kI kR t1 t2 : iProp :=
  DB.mapsto kI (dbCN kR.@"state") t1 t2.

Definition rem_free_at kI kR T : iProp :=
  DB.free_at kI (dbCN kR.@"state") T.

Lemma rem_free_at_diff kI kR T1 T2 :
  T1 ⊆ T2 →
  rem_free_at kI kR T2 ⊣⊢ rem_free_at kI kR T1 ∗ rem_free_at kI kR (T2 ∖ T1).
Proof. iIntros "%sub". by iApply DB.free_at_diff. Qed.

Lemma rem_mapsto_store t2' kI kR t1 t2 n :
  DB.client_view kI (dbCN kR.@"state") n -∗
  rem_mapsto kI kR t1 t2 ==∗
  DB.client_view kI (dbCN kR.@"state") (S n) ∗
  rem_mapsto kI kR t1 t2' ∗
  DB.store_at kI (dbCN kR.@"state") n t1 t2'.
Proof.
iIntros "client mapsto".
iMod (DB.store_client t2' with "client mapsto")
  as "(client & #update & mapsto)".
by iFrame.
Qed.

Lemma rem_mapsto_alloc kI kR t1 t2 n T :
  t1 ∈ T →
  DB.client_view kI (dbCN kR.@"state") n -∗
  rem_free_at kI kR T ==∗
  DB.client_view kI (dbCN kR.@"state") (S n) ∗
  rem_mapsto kI kR t1 t2 ∗
  rem_free_at kI kR (T ∖ {[t1]}) ∗
  DB.create_at kI (dbCN kR.@"state") n t1 t2.
Proof.
iIntros "%t1_T client".
have {}t1_T : {[t1]} ⊆ T by set_solver.
rewrite (rem_free_at_diff _ _ t1_T).
iIntros "[free free']". iFrame "free'".
iMod (DB.create_client _ t2 with "client free") as "(create & client & mapsto)".
iFrame. by eauto.
Qed.

Lemma client_alloc kI kR E :
  ↑dbCN kR ⊆ E →
  term_token kI E ={⊤}=∗
  db_disconnected kI kR ∗
  rem_free_at kI kR ⊤ ∗
  term_token kI (E ∖ ↑dbCN kR).
Proof.
iIntros "%sub kI_token".
rewrite (term_token_difference _ _ _ sub).
iDestruct "kI_token" as "[kI_token ?]". iFrame.
iMod (DB.alloc _ (N := dbCN kR.@"state") with "kI_token")
  as "(client_view & free & #server_view & kI_token)".
{ solve_ndisj. }
iMod (term_own_alloc (dbCN kR.@"status") (to_frac_agree 1 0)
  with "kI_token") as "[status kI_token]" => //.
{ solve_ndisj. }
rewrite -Qp.half_half frac_agree_op.
iDestruct "status" as "[client server]".
iAssert (|={⊤}=> server_clock_ready kI kR)%I
  with "[server]" as ">#server".
{ iApply (escrowI with "server").
  iApply never_connected_switch. }
iModIntro. iSplitR "free".
- iExists 0, false. by iFrame.
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

Definition server_token cs : iProp :=
  session_failed cs true ∨ ∃ n0,
    clock (si_init cs) (si_resp cs) n0 ∗
    clock (si_init cs) (si_resp cs) n0.

Definition server_db_connected' kI kR cs n n0 vdb : iProp :=
  ∃ db, public_db db ∗
        SAList.is_alist vdb (repr <$> db) ∗
        (session_failed cs true ∨
           DB.db_at kI (dbCN kR.@"state") (n + n0) db) ∗
        server_token cs.

Definition server_db_connected kI kR cs n n0 vdb : iProp :=
  connected kI kR cs n n0 ∗
  server_db_connected' kI kR cs n n0 vdb.

Definition server_disconnected kI kR n failed : iProp :=
  if failed then failure kI kR
  else (⌜n = 0⌝ ∗ never_connected kI kR ∨ clock kI kR n)%I.

Definition server_db_disconnected' kI kR n vdb failed : iProp :=
  ∃ db,
    public_db db ∗
    SAList.is_alist vdb (repr <$> db) ∗
    (⌜failed⌝ ∨ DB.db_at kI (dbCN kR.@"state") n db).

Definition server_db_disconnected kI kR vdb : iProp :=
  ∃ n failed,
    server_disconnected kI kR n failed ∗
    server_db_disconnected' kI kR n vdb failed.

Lemma server_db_alloc kI kR vdb E :
  ↑dbSN kI ⊆ E →
  term_token kR E -∗
  SAList.is_alist vdb ∅ -∗
  term_token kR (E ∖ ↑dbSN kI) ∗
  server_db_disconnected kI kR vdb.
Proof.
iIntros "%sub token vdb".
rewrite (term_token_difference kR (↑dbSN kI)) //.
iDestruct "token" as "[token H]". iFrame "H".
iExists 0, false. iSplitL "token".
- iLeft. by iSplit => //.
- iExists ∅. iFrame.
  iSplit; first by rewrite /public_db big_sepM_empty.
  iRight. iLeft. do !iSplit => //.
Qed.

Definition server ss : iProp := ∃ accounts E,
  sign_key (ss_key ss) ∗
  SAList.is_alist (ss_clients ss) (repr <$> accounts) ∗
  term_token (ss_key ss) E ∗
  ⌜∀ kI, TKey Open kI ∉ dom accounts → ↑dbSN kI ⊆ E⌝ ∗
  [∗ map] vkI ↦ scs ∈ accounts, ∃ kI, ⌜vkI = TKey Open kI⌝ ∗
     is_lock (scs_name scs) (scs_lock scs)
       (server_db_disconnected kI (ss_key ss) (scs_db scs)).

Lemma serverI kR vclients :
  term_token kR (↑nroot.@"db".@"server") -∗
  sign_key kR -∗
  SAList.is_alist vclients ∅ -∗
  server {| ss_key := kR; ss_clients := vclients |}.
Proof.
iIntros "token #p_vk clients".
iExists ∅, (↑nroot.@"db".@"server") => /=.
iFrame. iSplit => //. iSplit => //.
iPureIntro. move=> *. solve_ndisj.
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
  connected (si_init cs) kR cs 0 n0 ∗
  server_token cs.
Proof.
iIntros "dis (#sess & ts & <- & %e_rl & rel & token & close)".
have ->: si_resp_share cs = cs_share cs.
{ by rewrite /cs_share e_rl. }
iMod (session_failed_forI with "sess dis token")
  as "(%failed' & %le_failed & #failed & dis & token)".
iMod ("close" with "rel failed")
  as "(%failed'' & %le_failed' & rel & #failed' & #init)".
rewrite /connected /cs_share e_rl /=.
rewrite (term_token_difference _ (↑isoN.@"begin")); try solve_ndisj.
iDestruct "token" as "[token _]".
iDestruct "dis" as "[%fail|dis]".
{ iAssert (session_failed cs true) as "#?".
  { by case: failed'' => //= in le_failed' *. }
  iFrame. do !iSplitR => //; eauto. by iLeft. }
iDestruct "init" as "[%fail|(%m & init)]".
{ case: failed'' {le_failed'} => // in fail *.
  iFrame. do !iSplitR => //; eauto. by iLeft. }
iDestruct "init" as "(%n0' & clock & beginning & ready)".
iMod (escrowE with "ready token") as ">c1" => //.
iAssert (|={⊤}=> clock (si_init cs) (si_resp cs) n0)%I
  with "[dis]" as "> c2".
{ iDestruct "dis" as "[(-> & never)|c2]" => //.
  iMod (escrowE with "clock never") as ">?" => //. }
iPoseProof (clock_agree with "c1 c2") as "->".
iModIntro. iFrame. do !iSplit => //; eauto.
{ iIntros "!> %fail".
  have: failed'' by tauto.
  by case: (failed''). }
iRight. iFrame.
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
  connected kI kR cs m n0 -∗
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
  connected kI kR cs m n0 -∗
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

Definition store_pred kI kR si n ts : iProp := ∃ t1 t2,
  ⌜ts = [t1; t2]⌝ ∗
  DB.store_at kI (dbCN kR.@"state") n t1 t2.

Definition ack_store_pred kI kR si n ts : iProp := True.

Definition load_pred kI kR si n ts : iProp :=
  ∃ t1, ⌜ts = [t1]⌝ ∗
        DB.load_at kI (dbCN kR.@"state") n t1.

Definition ack_load_pred kI kR si n ts : iProp :=
  ∃ t1 t2, ⌜ts = [t2]⌝ ∗
    DB.load_at kI (dbCN kR.@"state") n t1 ∗
    DB.stored_at kI (dbCN kR.@"state") (S n) t1 t2.

Definition create_pred kI kR si n ts : iProp := ∃ t1 t2,
  ⌜ts = [t1; t2]⌝ ∗
  DB.create_at kI (dbCN kR.@"state") n t1 t2.

Definition ack_create_pred kI kR si n ts : iProp := True.

Definition close_pred kI kR si n ts : iProp :=
  True.

Definition conn_closed si ending :=
  escrow (nroot.@"db")
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

Definition server_handler_post kI kR cs n0 vdb v : iProp :=
  ⌜v = #true⌝ ∗
  (∃ n, server_db_connected kI kR cs n n0 vdb) ∨
  ⌜v = #false⌝ ∗ server_db_disconnected kI kR vdb.

Lemma ack_load_predI skI skR cs n t1 t2 db :
  db !! t1 = Some t2 →
  □ (session_failed cs true ∨ load_pred skI skR cs n [t1]) -∗
  □ (session_failed cs true ∨ DB.db_at skI (dbCN skR.@"state") n db) -∗
  (session_failed cs true ∨ □ ack_load_pred skI skR cs n [t2]) ∗
  □ (session_failed cs true ∨ DB.db_at skI (dbCN skR.@"state") (S n) db).
Proof.
iIntros "%db_t1 #[?|load] #[?|db_at]"; eauto.
iDestruct "load" as "(%t1' & %e & load)".
case: e => <- {t1'}.
iSplit; iRight.
- iModIntro. iExists t1, t2. do !iSplit => //.
  iApply DB.load_at_stored_at => //.
  by iApply DB.stored_atI.
- iModIntro. iApply (DB.db_at_op_at with "db_at load").
Qed.

Definition store_ctx : iProp :=
  seal_pred (N.@"init")       (session_msg_pred init_pred Init) ∗
  seal_pred (N.@"ack_init")   (session_msg_pred ack_init_pred Resp) ∗
  seal_pred (N.@"store")      (conn_pred store_pred) ∗
  seal_pred (N.@"ack_store")  (conn_pred ack_store_pred) ∗
  seal_pred (N.@"load")       (conn_pred load_pred) ∗
  seal_pred (N.@"ack_load")   (conn_pred ack_load_pred) ∗
  seal_pred (N.@"create")     (conn_pred create_pred) ∗
  seal_pred (N.@"ack_create") (conn_pred ack_create_pred) ∗
  seal_pred (N.@"close")      (conn_pred close_pred) ∗
  seal_pred (N.@"ack_close")  (conn_pred ack_close_pred) ∗
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
  store_ctx -∗ seal_pred (N.@"init") (session_msg_pred init_pred Init).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_init :
  store_ctx -∗ seal_pred (N.@"ack_init") (session_msg_pred ack_init_pred Resp).
Proof. solve_ctx. Qed.

Lemma store_ctx_store :
  store_ctx -∗ seal_pred (N.@"store") (conn_pred store_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_store :
  store_ctx -∗ seal_pred (N.@"ack_store") (conn_pred ack_store_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_load :
  store_ctx -∗ seal_pred (N.@"load") (conn_pred load_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_load :
  store_ctx -∗ seal_pred (N.@"ack_load") (conn_pred ack_load_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_create :
  store_ctx -∗ seal_pred (N.@"create") (conn_pred create_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_create :
  store_ctx -∗ seal_pred (N.@"ack_create") (conn_pred ack_create_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_close :
  store_ctx -∗ seal_pred (N.@"close") (conn_pred close_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_close :
  store_ctx -∗ seal_pred (N.@"ack_close") (conn_pred ack_close_pred).
Proof. solve_ctx. Qed.

Lemma store_ctx_iso_dh_ctx : store_ctx -∗ iso_dh_ctx (N.@"auth").
Proof. solve_ctx. Qed.

End Defs.

Arguments storeGS Σ : clear implicits.
