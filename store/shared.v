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

Definition session_failed_for_or si rl (P : iProp) : iProp :=
  ∃ failed, session_failed_for si rl failed ∗ (⌜failed⌝ ∨ P).

Lemma session_failed_for_orE si rl P Q :
  session_failed_for_or si rl P -∗
  (P -∗ Q ∨ session_failed_for_or si rl Q) -∗
  session_failed_for_or si rl Q.
Proof.
iIntros "(%failed & #failed & HP) PQ".
iDestruct "HP" as "[%fail|HP]".
{ iExists failed. iSplit; eauto. }
iDestruct ("PQ" with "HP") as "[Q|Q]" => //.
iExists failed. eauto.
Qed.

Lemma session_failed_for_or_True si rl P :
  session_failed_for_or si rl P ⊢ session_failed_for_or si rl True.
Proof.
iIntros "HP". iApply (session_failed_for_orE with "HP").
by eauto.
Qed.

Lemma session_failed_for_or_later si rl P :
  session_failed_for_or si rl (▷ P) ⊢ ▷ session_failed_for_or si rl P.
Proof.
iIntros "(%failed & #failed & [%fail|HP]) !>";
iExists failed; eauto.
Qed.

Lemma session_failed_for_or_fupd si rl P E :
  session_failed_for_or si rl (|={E}=> P) ⊢
  |={E}=> session_failed_for_or si rl P.
Proof.
iIntros "(%failed & #failed & [%fail|>HP]) !>";
iExists failed; eauto.
Qed.

Lemma session_failed_for_or_box si rl P :
  session_failed_for_or si rl (□ P) ⊣⊢
  □ session_failed_for_or si rl P.
Proof.
rewrite /session_failed_for_or. iSplit.
- iIntros "(%failed & #? & [%|#?]) !>"; eauto.
- iIntros "#(%failed & #? & [%|?])"; eauto.
Qed.

Definition session_failed si : iProp :=
  session_failed_for si Init true ∨
  session_failed_for si Resp true.

Lemma session_failed_failure si :
  session_failed si -∗
  failure (si_init si) (si_resp si).
Proof. by iIntros "[[_ #fail]|[_ #fail]]". Qed.

Definition session_ok si : iProp :=
  session_failed_for si Init false ∗
  session_failed_for si Resp false.

Lemma session_failed_ok si :
  session_failed si -∗
  session_ok si -∗
  False.
Proof.
iIntros "[#fail|#fail] [#ok1 #ok2]".
- by iPoseProof (session_failed_for_agree with "fail ok1") as "%".
- by iPoseProof (session_failed_for_agree with "fail ok2") as "%".
Qed.

Definition session_failed_or si P : iProp :=
  session_failed si ∨ session_ok si ∗ P.

Lemma session_failed_orE si P Q :
  session_failed_or si P -∗
  (P -∗ Q ∨ session_failed_or si Q) -∗
  session_failed_or si Q.
Proof.
iIntros "[#failed|[#ok HP]] PQ"; first by iLeft.
iDestruct ("PQ" with "HP") as "[Q|Q]" => //.
by iRight; eauto.
Qed.

Lemma session_okI si (P : iProp) :
  session_failed_or si P -∗
  (failure (si_init si) (si_resp si) -∗ ▷ False) -∗
  ◇ session_ok si.
Proof.
iIntros "[#fail|[#ok HP]] contra"; eauto.
iPoseProof (session_failed_failure with "fail") as "{fail} fail".
iDestruct ("contra" with "[$]") as ">[]".
Qed.

Lemma session_failed_orI si P Q :
  session_failed_for_or si Init P -∗
  session_failed_for_or si Resp Q -∗
  session_failed_or si (P ∗ Q).
Proof.
iIntros "(%failed1 & #failed1 & HP) (%failed2 & #failed2 & HQ)".
case: failed1; first by iLeft; iLeft.
iDestruct "HP" as "[[]|HP]".
case: failed2; first by iLeft; iRight.
iDestruct "HQ" as "[[]|HQ]".
iRight. iFrame. by iSplit.
Qed.

Lemma session_failed_orI' si rl P Q :
  session_failed_for_or si rl P -∗
  session_failed_or si Q -∗
  session_failed_or si P ∗ session_failed_or si Q.
Proof.
iIntros "(%failed & #failed1 & HP) [#failed2|[#[ok1 ok2] HQ]]".
{ by iSplitR; iLeft. }
iAssert (⌜failed = false⌝)%I as "->".
{ case: rl.
  - iApply (session_failed_for_agree with "failed1 ok1").
  - iApply (session_failed_for_agree with "failed1 ok2"). }
iDestruct "HP" as "[[]|HP]".
by iSplitL "HP"; iRight; iFrame; iSplit.
Qed.

Lemma session_failed_or_later si P :
  session_failed_or si (▷ P) ⊢ ▷ session_failed_or si P.
Proof.
iIntros "[#fail|[#ok HP]] !>"; [iLeft|iRight]; eauto.
Qed.

Lemma session_failed_or_fupd si P E :
  session_failed_or si (|={E}=> P) ⊢
  |={E}=> session_failed_or si P.
Proof.
iIntros "[#fail|[#ok >HP]] !>"; [iLeft|iRight]; eauto.
Qed.

Lemma session_failed_or_box si P :
  □ session_failed_or si P ⊣⊢ session_failed_or si (□ P).
Proof.
rewrite /session_failed_or.
rewrite bi.intuitionistically_or bi.intuitionistically_sep.
by rewrite !bi.intuitionistic_intuitionistically.
Qed.

Lemma session_failed_or_ok si P :
  session_ok si -∗
  session_failed_or si P -∗
  P.
Proof.
iIntros "#ok [#fail|[_ ?]]" => //.
by iDestruct (session_failed_ok with "fail ok") as "[]".
Qed.

Lemma session_failed_or_sep si P Q :
  session_failed_or si P ∗ session_failed_or si Q ⊣⊢
  session_failed_or si (P ∗ Q).
Proof.
iSplit.
- iIntros "[[#fail|[#ok HP]] HQ]"; first by iLeft.
  iPoseProof (session_failed_or_ok with "ok HQ") as "HQ".
  iRight. by iFrame.
- iIntros "[#fail|[#ok [HP HQ]]]"; first by iSplitR; iLeft.
  by iSplitR "HQ"; iRight; eauto.
Qed.

Definition wf_conn_state cs : iProp :=
  wf_sess_info cs ∗
  session_failed_for_or cs (cs_role cs) True.

Lemma wf_conn_stateI cs (P : iProp) :
  wf_sess_info cs -∗
  failure (si_init cs) (si_resp cs) ∨ P -∗
  term_token (cs_share cs) (↑isoN) ==∗
  wf_conn_state cs ∗
  session_failed_for_or cs (cs_role cs) P ∗
  term_token (cs_share cs) (↑isoN ∖ ↑isoN.@"failed").
Proof.
iIntros "#wf HP token".
iPoseProof "wf" as "(_ & _ & #? & [fail|#succ])".
{ iMod (term_meta_set' true (N := nroot.@"iso".@"failed") with "token")
    as "[#failed token]" => //; try solve_ndisj.
  iAssert (session_failed_for_or cs (cs_role cs) P) as "H".
  { iExists true. iSplit => //; eauto. by iSplit => //. }
  iModIntro. iFrame. do !iSplit => //.
  iApply (session_failed_for_orE with "H").
  by iIntros "_"; eauto. }
iDestruct "HP" as "[#fail|HP]".
{ iMod (term_meta_set' true (N := nroot.@"iso".@"failed") with "token")
    as "[#failed token]" => //; try solve_ndisj.
  iAssert (session_failed_for cs (cs_role cs) true) as "#?".
  { by iSplit => //. }
  rewrite /session_failed_for_or.
  iModIntro. iFrame. do !iSplit => //; eauto.
  iExists true. eauto. }
iMod (term_meta_set' false (N := isoN.@"failed") with "token")
  as "[#failed token]" => //; try solve_ndisj.
iAssert (session_failed_for cs (cs_role cs) false) as "#?".
{ iSplit => //. iModIntro. by iSplit => //. }
rewrite /wf_conn_state /session_failed_for_or.
iFrame. by eauto 10.
Qed.

Definition db_not_signed_up kI kR : iProp :=
  term_token kR (↑dbSN kI).

Lemma db_signed_up_switch kI kR Q : ⊢ switch (db_not_signed_up kI kR) Q.
Proof. apply term_token_switch. Qed.

Definition db_clock kI kR n :=
  term_own kI (dbCN kR.@"status") (to_frac_agree (1 / 2) n).

Lemma db_clock_alloc kI kR E :
  ↑dbCN kR.@"status" ⊆ E →
  term_token kI E ==∗
  db_clock kI kR 0 ∗
  db_clock kI kR 0 ∗
  term_token kI (E ∖ ↑dbCN kR.@"status").
Proof.
iIntros "%sub token".
iMod (term_own_alloc (dbCN kR.@"status") (to_frac_agree 1 0)
       with "token") as "[own token]" => //.
iFrame. rewrite -Qp.half_half frac_agree_op.
iDestruct "own" as "[??]". by iFrame.
Qed.

Lemma db_clock_agree kI kR n m :
  db_clock kI kR n -∗
  db_clock kI kR m -∗
  ⌜n = m⌝.
Proof.
iIntros "own1 own2".
iPoseProof (term_own_valid_2 with "own1 own2") as "%valid".
rewrite frac_agree_op_valid_L in valid.
by case: valid.
Qed.

Lemma db_clock_update p kI kR n m :
  db_clock kI kR n -∗
  db_clock kI kR m ==∗
  db_clock kI kR p ∗ db_clock kI kR p.
Proof.
iIntros "own1 own2".
rewrite /db_clock.
iMod (term_own_update_2 with "own1 own2") as "[own1 own2]".
{ apply: (frac_agree_update_2 _ _ _ _ p).
  by rewrite Qp.half_half. }
by iFrame.
Qed.

Definition server_status_ready kI kR :=
  escrow (nroot.@"db") (db_not_signed_up kI kR)
    (db_clock kI kR 0).

Implicit Types (failed : bool).

Definition client_disconnected_int kI kR n : iProp :=
  DB.client_view kI (dbCN kR.@"state") n ∗
  server_status_ready kI kR ∗
  (failure kI kR ∨ db_clock kI kR n).

Definition client_disconnected kI kR : iProp := ∃ n,
  client_disconnected_int kI kR n.

Definition client_connected_int cs n beginning : iProp :=
  let kI := si_init cs in
  let kR := si_resp cs in
  DB.client_view kI (dbCN kR.@"state") (n + beginning) ∗
  server_status_ready kI kR ∗
  term_meta  (si_init_share cs) (isoN.@"beginning") beginning ∗
  term_token (si_init_share cs) (↑isoN.@"end") ∗
  term_token (si_init_share cs) (↑isoN.@"ending") ∗
  session_failed_or cs True.

Definition client_connecting_int cs beginning : iProp :=
  let kI := si_init cs in
  let kR := si_resp cs in
  DB.client_view kI (dbCN kR.@"state") beginning ∗
  server_status_ready kI kR ∗
  term_meta  (si_init_share cs) (isoN.@"beginning") beginning ∗
  term_token (si_init_share cs) (↑isoN.@"end") ∗
  term_token (si_init_share cs) (↑isoN.@"ending") ∗
  session_failed_for_or cs Init True.

Definition client_disconnecting_int cs n beginning : iProp :=
  let kI := si_init cs in
  let kR := si_resp cs in
  DB.client_view kI (dbCN kR.@"state") (n + beginning) ∗
  server_status_ready kI kR ∗
  term_token (si_init_share cs) (↑isoN.@"end") ∗
  term_meta  (si_init_share cs) (isoN.@"ending") (n + beginning) ∗
  session_failed_or cs True.

Definition conn_ready si n :=
  escrow (nroot.@"db")
         (term_token (si_resp_share si) (↑isoN.@"begin"))
         (db_clock (si_init si) (si_resp si) n).

Lemma client_connectingI E kI kR cs beginning :
  ↑cryptisN ⊆ E →
  ↑nroot.@"db" ⊆ E →
  si_init cs = kI →
  si_resp cs = kR →
  cs_role cs = Init →
  cryptis_ctx -∗
  £ 1 ∗ £ 1 -∗
  wf_sess_info cs -∗
  term_token (si_init_share cs) (↑isoN) -∗
  client_disconnected_int kI kR beginning ={E}=∗
  client_connecting_int cs beginning ∗
  wf_conn_state cs ∗
  term_meta (si_init_share cs) (isoN.@"beginning") beginning ∗
  session_failed_for_or cs Init (conn_ready cs beginning).
Proof.
move=> ? ? <- <- e_rl {kI kR}.
iIntros "#? [c1 c2] #sess token client".
iDestruct "client" as "(client_view & #server & status)".
iPoseProof (DB.client_view_db_at with "client_view") as "(%db & #db_at)".
have e_sh : si_init_share cs = cs_share cs by rewrite /cs_share e_rl.
rewrite e_sh.
iMod (wf_conn_stateI with "sess status token")
  as "(#conn & status & token)".
rewrite e_rl.
iMod (term_meta_set' (N:=isoN.@"beginning") beginning with "token")
  as "[#beginning token]"; try solve_ndisj.
iPoseProof (session_failed_for_or_True with "status") as "#failed".
iSplitL "client_view token".
{ rewrite /client_connecting_int. iFrame.
  rewrite e_sh. iModIntro. do !iSplit => //.
  rewrite (term_token_difference _ (↑isoN.@"end")); try solve_ndisj.
  iDestruct "token" as "[token' token]". iFrame "token'".
  iSplit => //.
  iApply (term_token_drop with "token"). solve_ndisj. }
iSplitR => //. iSplitR => //.
iApply session_failed_for_or_fupd.
iApply (session_failed_for_orE with "status").
iIntros "status". iLeft.
iApply (escrowI with "status").
iApply term_token_switch.
Qed.

Lemma client_connected_intI cs beginning E :
  ↑nroot.@"db" ⊆ E →
  client_connecting_int cs beginning -∗
  session_failed_for_or cs Resp True ={E}=∗
  ▷ client_connected_int cs 0 beginning.
Proof.
move=> sub.
iIntros "(client & #server & #? & ? & ? & #conn) #status".
iFrame. do !iSplitR => //.
rewrite -session_failed_or_later -session_failed_or_fupd.
iPoseProof (session_failed_orI with "conn status") as "{status} status".
iApply (session_failed_orE with "status"). by eauto.
Qed.

Definition client_connected kI kR cs : iProp := ∃ n beginning,
  ⌜si_init cs = kI⌝ ∗
  ⌜si_resp cs = kR⌝ ∗
  ⌜cs_role cs = Init ⌝ ∗
  wf_conn_state cs ∗
  release_token (cs_share cs) ∗
  cs_ts cs ↦ #n ∗
  client_connected_int cs n beginning.

Lemma client_connected_ok kI kR cs :
  client_connected kI kR cs -∗
  (failure kI kR -∗ ▷ False) -∗
  ◇ session_ok cs.
Proof.
iIntros "(%n & %beginning & <- & <- & % & #conn & rel & ts & client) post".
iDestruct "client" as "(client & #ready & #? & ? & ? & #status)".
by iMod (session_okI with "status post") as "#ok".
Qed.

Definition rem_mapsto kI kR t1 t2 : iProp :=
  DB.mapsto kI (dbCN kR.@"state") t1 t2.

Definition rem_free_at kI kR T : iProp :=
  DB.free_at kI (dbCN kR.@"state") T.

Lemma rem_free_at_diff kI kR T1 T2 :
  T1 ⊆ T2 →
  rem_free_at kI kR T2 ⊣⊢ rem_free_at kI kR T1 ∗ rem_free_at kI kR (T2 ∖ T1).
Proof. iIntros "%sub". by iApply DB.free_at_diff. Qed.

Lemma rem_mapsto_store t2' cs t1 t2 n beginning :
  client_connected_int cs n beginning -∗
  rem_mapsto (si_init cs) (si_resp cs) t1 t2 ==∗
  client_connected_int cs (S n) beginning ∗
  rem_mapsto (si_init cs) (si_resp cs) t1 t2' ∗
  DB.store_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 t2'.
Proof.
iIntros "(client & #server & conn) mapsto".
iMod (DB.store_client t2' with "client mapsto")
  as "(client & #update & mapsto)".
iFrame. iSplitR => //.
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
iIntros "%t1_T (client & #server & conn)".
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
iMod (term_own_alloc (dbCN kR.@"status") (to_frac_agree 1 0)
  with "kI_token") as "[status kI_token]" => //.
{ solve_ndisj. }
rewrite -Qp.half_half frac_agree_op.
iDestruct "status" as "[client server]".
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
  public_db db ∗
  session_failed_or cs (∃ beginning,
    DB.db_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) db ∗
    term_meta (si_init_share cs) (isoN.@"beginning") beginning ∗
    db_clock (si_init cs) (si_resp cs) beginning ∗
    db_clock (si_init cs) (si_resp cs) beginning).

Lemma server_connected_ok cs n db :
  server_connected cs n db -∗
  (failure (si_init cs) (si_resp cs) -∗ ▷ False) -∗
  ◇ session_ok cs.
Proof.
iIntros "(#p_db & server) post".
by iMod (session_okI with "server post") as "#?".
Qed.

Definition server_disconnected kI kR db : iProp :=
  public_db db ∗
  (failure kI kR ∨
   ⌜db = ∅⌝ ∗ db_not_signed_up kI kR ∨ ∃ n,
   DB.db_at kI (dbCN kR.@"state") n db ∗
   db_clock kI kR n).

Definition server_connecting cs db : iProp :=
  public_db db ∗
  session_failed_for_or cs Resp (
    ⌜db = ∅⌝ ∗ db_not_signed_up (si_init cs) (si_resp cs) ∨ ∃ n,
    DB.db_at (si_init cs) (dbCN (si_resp cs).@"state") n db ∗
    db_clock (si_init cs) (si_resp cs) n).

Lemma server_connectingI cs db :
  cs_role cs = Resp →
  cryptis_ctx -∗
  £ 1 -∗
  wf_sess_info cs -∗
  term_token (cs_share cs) (↑isoN) -∗
  server_disconnected (si_init cs) (si_resp cs) db ={⊤}=∗
  wf_conn_state cs ∗
  server_connecting cs db ∗
  term_token (cs_share cs) (↑isoN ∖ ↑isoN.@"failed").
Proof.
iIntros "%e_rl #ctx c #sess token (#p_db & status)".
iMod (wf_conn_stateI with "sess status token")
  as "(#conn & ? & token)".
iFrame. rewrite e_rl. iModIntro. iSplit; eauto.
iSplit; eauto.
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
  sign_key (ss_key ss) ∗
  SAList.is_alist (ss_clients ss) (repr <$> accounts) ∗
  term_token (ss_key ss) E ∗
  ⌜∀ kI, TKey Open kI ∉ dom accounts → ↑dbSN kI ⊆ E⌝ ∗
  [∗ map] vkI ↦ scs ∈ accounts, ∃ kI, ⌜vkI = TKey Open kI⌝ ∗
     is_lock (scs_name scs) (scs_lock scs)
       (account_inv kI (ss_key ss) (scs_db scs)).

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
  ∃ si, ⌜kS = (si_key si)⌝ ∗ public m ∗
        (session_failed_for_or si (swap_role rl) True →
         session_failed_or si (Q si m)).

Definition init_pred si t : iProp := ∃ (beginning : nat),
  server_status_ready (si_init si) (si_resp si) ∗
  term_meta (si_init_share si) (isoN.@"beginning") beginning ∗
  conn_ready si beginning.

Lemma init_predI cs beginning m :
  client_connecting_int cs beginning -∗
  session_failed_for_or cs Init (conn_ready cs beginning) -∗
  □ (session_failed_for_or cs Resp True → session_failed_or cs (init_pred cs m)).
Proof.
iIntros "(client & #server & #? & ? & ? & #status) ready".
iAssert (□ session_failed_for_or cs Init (init_pred cs m))%I as "#p_m".
{ rewrite -session_failed_for_or_box.
  iApply (session_failed_for_orE with "ready").
  iIntros "#ready". iRight.
  iApply (session_failed_for_orE with "status").
  iIntros "_". iLeft. iModIntro. iExists _. by eauto 10. }
iIntros "!> #failed".
iPoseProof (session_failed_orI with "p_m failed") as "#res".
iApply (session_failed_orE with "res"). iIntros "[? _]". by eauto.
Qed.

Definition ack_init_pred si t : iProp := True.

Lemma ack_init_predI cs db m :
  cs_role cs = Resp →
  server_connecting cs db -∗
  term_token (si_resp_share cs) (↑isoN.@"begin") -∗
  session_failed_or cs (init_pred cs m) ={⊤}▷=∗
  server_connected cs 0 db ∗
  □ session_failed_or cs (ack_init_pred cs (TInt 0)).
Proof.
iIntros "%e_rl (#p_db & status) not_started #p_m".
iPoseProof (session_failed_orI' with "status p_m") as "[status _]".
rewrite session_failed_or_box.
rewrite /server_connected -!bi.sep_assoc session_failed_or_sep.
iSplitR => //.
rewrite -!(session_failed_or_fupd, session_failed_or_later).
iApply (session_failed_orE with "p_m"). iIntros "{p_m} p_m".
iRight.
iApply (session_failed_orE with "status"). iIntros "status".
iLeft.
iDestruct "p_m"
  as "(%n & #server & #beginning & #conn_ready)".
iMod (escrowE with "conn_ready not_started") as ">statusI" => //.
iAssert (|={⊤}▷=>
           DB.db_at (si_init cs) (dbCN (si_resp cs).@"state") n db ∗
           db_clock (si_init cs) (si_resp cs) n ∗
           db_clock (si_init cs) (si_resp cs) n)%I
  with "[status statusI]" as ">status".
{ iDestruct "status" as "[[-> fresh]|status]"; last first.
  { iDestruct "status" as "(%n' & #server_view' & status)".
    iPoseProof (db_clock_agree with "status statusI") as "->".
    iIntros "!> !> !>". by iFrame. }
  iMod (escrowE with "server fresh") as ">status" => //.
  iPoseProof (db_clock_agree with "status statusI") as "<-".
  iIntros "!> !> !>".  iFrame. by iLeft. }
iIntros "!> !>". iMod "status" as "(#? & status)".
iModIntro. iSplit.
{ iFrame. do 2!iSplit => //. }
by iIntros "!>".
Qed.

Lemma ack_init_predE cs m beginning E :
  ↑nroot.@"db" ⊆ E →
  client_connecting_int cs beginning -∗
  session_failed_or cs (ack_init_pred cs m) ={E}=∗
  ▷ client_connected_int cs 0 beginning.
Proof.
iIntros "%sub".
iIntros "(client & #server & #? & ? & ? & #conn) m".
iPoseProof (session_failed_orI' with "conn m") as "{conn} [conn m]".
iFrame. by eauto.
Qed.

Definition store_pred si m : iProp := ∃ (n : nat) t1 t2 beginning,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  term_meta (si_init_share si) (isoN.@"beginning") beginning ∗
  DB.store_at (si_init si) (dbCN (si_resp si).@"state") (n + beginning) t1 t2.

Lemma store_predI cs n beginning t1 t2 :
  client_connected_int cs (S n) beginning -∗
  DB.store_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 t2 -∗
  □ session_failed_or cs (store_pred cs (Spec.of_list [TInt n; t1; t2])).
Proof.
iIntros "(client & #server & #? & _ & _ & #conn) #update".
iApply session_failed_or_box.
iApply (session_failed_orE with "conn").
iIntros "_". iLeft. iModIntro. iExists _. by eauto 10.
Qed.

Lemma store_predE cs n db t1 t2 :
  let m := Spec.of_list [TInt n; t1; t2] in
  server_connected cs n db -∗
  public m -∗
  session_failed_or cs (store_pred cs m) -∗
  server_connected cs (S n) (<[t1 := t2]>db).
Proof.
iIntros "%m server p_m m_inv".
rewrite public_of_list /=.
iDestruct "p_m" as "(_ & #p_t1 & #p_t2 & _)".
iDestruct "server" as "(#p_db & status)".
iSplitR; first by iApply public_db_insert.
iApply (session_failed_orE with "status"). iIntros "status". iRight.
iApply (session_failed_orE with "m_inv"). iIntros "#m_inv". iLeft.
iDestruct "m_inv" as "(%n' & %t1' & %t2' & %beginning &
      %e_m & #beginning & #update)".
case/Spec.of_list_inj: e_m => e_n <- <- {t1' t2'}.
have {e_n} <- : n = n' by lia.
iDestruct "status"
  as "(%beginning' & #server & #beginning' & end & status)".
iPoseProof (term_meta_agree with "beginning' beginning") as "{beginning'} ->".
iPoseProof (DB.db_at_store_at with "server update") as "{server} server".
iExists beginning. iFrame. by eauto.
Qed.

Definition ack_store_pred (si : sess_info) m : iProp := ∃ (n : nat),
  ⌜m = TInt n⌝. (* FIXME: Do we need anything else here? *)

Definition load_pred (si : sess_info) (m : term) : iProp :=
  ∃ (n : nat) (t1 : term) beginning,
    ⌜m = Spec.of_list [TInt n; t1]⌝ ∗
    term_meta (si_init_share si) (isoN.@"beginning") beginning ∗
    DB.load_at (si_init si) (dbCN (si_resp si).@"state") (n + beginning) t1.

Lemma load_predI cs n beginning t1 :
  client_connected_int cs n beginning ==∗
  client_connected_int cs (S n) beginning ∗
  DB.load_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 ∗
  □ session_failed_or cs (load_pred cs (Spec.of_list [TInt n; t1])).
Proof.
iIntros "(view & ? & #? & ? & ? & #H)".
rewrite session_failed_or_box.
iMod (DB.load_client t1 with "view") as "[#load view]".
iFrame. iModIntro. do !iSplit => //.
iApply (session_failed_orE with "H").
iIntros "_". iLeft. iModIntro. iExists n, t1, beginning.
by eauto.
Qed.

Definition ack_load_pred si m : iProp := ∃ n t1 t2 beginning,
  ⌜m = Spec.of_list [TInt n; t2]⌝ ∗
  term_meta (si_init_share si) (isoN.@"beginning") beginning ∗
  DB.load_at (si_init si) (dbCN (si_resp si).@"state") (n + beginning) t1 ∗
  DB.stored_at (si_init si) (dbCN (si_resp si).@"state") (S (n + beginning)) t1 t2.

Lemma ack_load_predI {cs n db t1 t2} :
  let m := Spec.of_list [TInt n; t1] in
  db !! t1 = Some t2 →
  server_connected cs n db -∗
  session_failed_or cs (load_pred cs m) -∗
  public (Spec.of_list [TInt n; t2]) ∗
  □ session_failed_or cs (ack_load_pred cs (Spec.of_list [TInt n; t2])).
Proof.
iIntros "%m %t1_t2 server load".
iDestruct "server" as "(#public & status)".
rewrite /public_db big_sepM_forall.
iDestruct ("public" with "[//]") as "[p_t1 p_t2]".
iSplit.
{ rewrite public_of_list /= public_TInt. by eauto. }
iApply session_failed_or_box.
iApply (session_failed_orE with "load"). iIntros "#load". iRight.
iApply (session_failed_orE with "status"). iIntros "status". iLeft.
iDestruct "load" as "(%n' & %t1' & %beginning & %e_m & beginning & load)".
iDestruct "status" as "(%beginning' & #server & #beginning' & _)".
iPoseProof (term_meta_agree with "beginning beginning'") as "<-".
case/Spec.of_list_inj: e_m => e_n <- {t1'}.
have <- : n = n' by lia.
iModIntro. iExists n, t1, t2, beginning. do !iSplit => //.
iPoseProof (DB.stored_atI _ _ _ t1_t2 with "server") as "#stored_at".
by iPoseProof (DB.load_at_stored_at with "stored_at load") as "#?".
Qed.

Lemma ack_loadE cs n beginning t1 t2 t2' :
  let m := Spec.of_list [TInt n; t2'] in
  client_connected_int cs (S n) beginning -∗
  DB.load_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 -∗
  rem_mapsto (si_init cs) (si_resp cs) t1 t2 -∗
  public m -∗
  session_failed_or cs (ack_load_pred cs m) -∗
  public t2' ∗ (session_failed_or cs ⌜t2' = t2⌝).
Proof.
iIntros "%m (client & #server & #beginning & ? & ? & #conn)".
iIntros "#load_at mapsto #p_m inv_m".
rewrite public_of_list /=.
iDestruct "p_m" as "(_ & p_t2' & _)".
iSplit => //.
iApply (session_failed_orE with "inv_m"). iIntros "#inv_m". iRight.
iDestruct "inv_m"
  as "#(%n' & %t1' & %t2'' & %beginning' & %e & beginning' & load_at' & stored)".
iApply (session_failed_orE with "conn"). iIntros "_". iLeft.
iPoseProof (term_meta_agree with "beginning' beginning") as "{beginning'} ->".
case/Spec.of_list_inj: e => e_n <- {t2''}.
have {n' e_n} <-: n = n' by lia.
iPoseProof (DB.op_at_agree with "load_at load_at'") as "%e_t1".
case: e_t1 => <-.
by iApply (DB.client_view_stored_at with "client mapsto stored").
Qed.

Definition create_pred si m : iProp := ∃ n t1 t2 beginning,
  ⌜m = Spec.of_list [TInt n; t1; t2]⌝ ∗
  term_meta (si_init_share si) (isoN.@"beginning") beginning ∗
  DB.create_at (si_init si) (dbCN (si_resp si).@"state") (n + beginning) t1 t2.

Lemma create_predI cs n t1 t2 beginning :
  client_connected_int cs (S n) beginning -∗
  public t1 -∗
  public t2 -∗
  DB.create_at (si_init cs) (dbCN (si_resp cs).@"state") (n + beginning) t1 t2 -∗
  □ session_failed_or cs (create_pred cs (Spec.of_list [TInt n; t1; t2])).
Proof.
iIntros "(client & #server & #? & ? & ? & #conn) #p_t1 #p_t2 #create".
iApply session_failed_or_box.
iApply (session_failed_orE with "conn"). iIntros "_". iLeft.
iModIntro.
iExists n, t1, t2, beginning.
by eauto 10.
Qed.

Lemma create_predE cs n db t1 t2 :
  let m := Spec.of_list [TInt n; t1; t2] in
  db !! t1 = None →
  server_connected cs n db -∗
  public m -∗
  session_failed_or cs (create_pred cs m) -∗
  server_connected cs (S n) (<[t1 := t2]> db).
Proof.
iIntros "%m %db_t1 server #p_m m_inv".
rewrite public_of_list /=.
iDestruct "p_m" as "(_ & p_t1 & p_t2 & _)".
iDestruct "server" as "(#p_db & status)".
iSplitR => //.
{ by iApply public_db_insert. }
iApply (session_failed_orE with "m_inv"). iIntros "#m_inv". iRight.
iApply (session_failed_orE with "status"). iIntros "status". iLeft.
iDestruct "m_inv"
  as "(%n' & %t1' & %t2' & %beginning & %e_m & #beginning & #created)".
case/Spec.of_list_inj: e_m => e_n <- <- {t1' t2'}.
have {n' e_n} <- : n = n' by lia.
iDestruct "status"
  as "(%beginning' & #server & #beginning' & status)".
iPoseProof (term_meta_agree with "beginning' beginning") as "{beginning'} ->".
iPoseProof (DB.db_at_create_at with "server created") as "{server} server" => //.
iExists _. iFrame. by eauto.
Qed.

Definition ack_create_pred (si : sess_info) (m : term) : iProp := True.

Definition close_pred si m : iProp := ∃ n beginning,
  ⌜m = TInt n⌝ ∗
  term_meta (si_init_share si) (isoN.@"beginning") beginning ∗
  term_meta (si_init_share si) (isoN.@"ending") (n + beginning).

Lemma close_predI cs beginning n E :
  ↑nroot.@"db" ⊆ E →
  client_connected_int cs n beginning ={E}=∗
  client_disconnecting_int cs n beginning ∗
  □ session_failed_or cs (close_pred cs (TInt n)).
Proof.
iIntros "%sub (client & #server & #? & end & ending & #conn)".
rewrite session_failed_or_box /client_disconnecting_int.
iFrame. rewrite -!bi.sep_assoc. iSplitR => //.
iMod (term_meta_set (isoN.@"ending") (n + beginning) with "ending")
  as "#ending" => //.
iSplitR => //.
rewrite session_failed_or_sep -session_failed_or_fupd.
iApply (session_failed_orE with "conn"). iIntros "_". iLeft.
iIntros "!>". iSplit => //. iExists n, beginning.
by eauto 10.
Qed.

Definition conn_closed si ending :=
  escrow (nroot.@"db")
         (term_token (si_init_share si) (↑isoN.@"end"))
         (db_clock (si_init si) (si_resp si) ending).

Definition ack_close_pred si (m : term) : iProp := ∃ ending,
  term_meta (si_init_share si) (isoN.@"ending") ending ∗
  conn_closed si ending.

Lemma session_failed_or_failure si P :
  session_failed_or si P ⊢ failure (si_init si) (si_resp si) ∨ P.
Proof.
iIntros "[#fail|[_ HP]]"; eauto. iLeft.
by iDestruct "fail" as "[[_ fail]|[_ fail]]".
Qed.

Lemma ack_close_predI cs n db E :
  let m := TInt n in
  ↑nroot.@"db" ⊆ E →
  server_connected cs n db -∗
  session_failed_or cs (close_pred cs m) ={E}▷=∗
  server_disconnected (si_init cs) (si_resp cs) db ∗
  □ session_failed_or cs (ack_close_pred cs (TInt 0)).
Proof.
iIntros "%m %sub server p_m".
iDestruct "server" as "(#p_db & status)".
rewrite session_failed_or_box /server_disconnected -!bi.sep_assoc.
iSplitR => //.
rewrite -(session_failed_or_failure cs) session_failed_or_sep.
rewrite -!(session_failed_or_fupd, session_failed_or_later).
iApply (session_failed_orE with "status"). iIntros "status". iRight.
iApply (session_failed_orE with "p_m"). iIntros "p_m". iLeft.
iDestruct "status" as
  "(%beginning & #server & #beginning & status1 & status2)".
iDestruct "p_m" as
  "(%n' & %beginning' & %e_m & #beginning' & #ending)".
case: e_m => e_m. have {e_m} <-: n = n' by lia.
iPoseProof (term_meta_agree with "beginning' beginning") as "->".
iMod (db_clock_update (n + beginning) with "status1 status2")
  as "[status1 status2]".
iAssert (|={E}=> conn_closed cs (n + beginning))%I
  with "[status2]" as ">#closed".
{ iApply (escrowI with "[status2]").
  - by eauto.
  - iApply term_token_switch. }
iModIntro. iModIntro. iModIntro. iSplit.
- iRight. iExists _. iFrame. by eauto.
- iModIntro. iExists _. by eauto.
Qed.

Lemma ack_close_predE cs m n beginning E :
  ↑nroot.@"db" ⊆ E →
  client_disconnecting_int cs n beginning -∗
  session_failed_or cs (ack_close_pred cs m) ={E}=∗
  ▷ client_disconnected_int (si_init cs) (si_resp cs) (n + beginning).
Proof.
iIntros "%sub (client & #server & end & #ending & #conn) p_m".
rewrite /client_disconnected_int. iFrame.
iSplitR => //.
rewrite -(session_failed_or_failure cs) -session_failed_or_later.
rewrite -session_failed_or_fupd.
iApply (session_failed_orE with "conn"). iIntros "_". iRight.
iApply (session_failed_orE with "p_m"). iIntros "p_m". iLeft.
iDestruct "p_m" as "(%ending & #ending' & #closed)".
iPoseProof (term_meta_agree with "ending' ending") as "{ending'} ->".
by iMod (escrowE with "closed end") as "status" => //.
Qed.

Definition server_handler_inv cs n ldb db : iProp :=
  server_connected cs n db ∗
  SAList.is_alist ldb (repr <$> db).

Definition server_handler_post cs ldb v : iProp := ∃ n db,
  ⌜v = #true⌝ ∗
  cs_ts cs ↦ #n ∗
  release_token (cs_share cs) ∗
  server_connected cs n db ∗
  SAList.is_alist ldb (repr <$> db) ∨
  ⌜v = #false⌝ ∗
  cs_ts cs ↦ #n ∗
  release_token (cs_share cs) ∗
  server_disconnected (si_init cs) (si_resp cs) db ∗
  SAList.is_alist ldb (repr <$> db).

Definition store_ctx : iProp :=
  seal_pred (N.@"init")       (session_msg_pred init_pred Init) ∗
  seal_pred (N.@"ack_init")   (session_msg_pred ack_init_pred Resp) ∗
  seal_pred (N.@"store")      (session_msg_pred store_pred Init) ∗
  seal_pred (N.@"ack_store")  (session_msg_pred ack_store_pred Resp) ∗
  seal_pred (N.@"load")       (session_msg_pred load_pred Init) ∗
  seal_pred (N.@"ack_load")   (session_msg_pred ack_load_pred Resp) ∗
  seal_pred (N.@"create")     (session_msg_pred create_pred Init) ∗
  seal_pred (N.@"ack_create") (session_msg_pred ack_create_pred Resp) ∗
  seal_pred (N.@"close")      (session_msg_pred close_pred Init) ∗
  seal_pred (N.@"ack_close")  (session_msg_pred ack_close_pred Resp) ∗
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
  store_ctx -∗ seal_pred (N.@"store") (session_msg_pred store_pred Init).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_store :
  store_ctx -∗ seal_pred (N.@"ack_store") (session_msg_pred ack_store_pred Resp).
Proof. solve_ctx. Qed.

Lemma store_ctx_load :
  store_ctx -∗ seal_pred (N.@"load") (session_msg_pred load_pred Init).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_load :
  store_ctx -∗ seal_pred (N.@"ack_load") (session_msg_pred ack_load_pred Resp).
Proof. solve_ctx. Qed.

Lemma store_ctx_create :
  store_ctx -∗ seal_pred (N.@"create") (session_msg_pred create_pred Init).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_create :
  store_ctx -∗ seal_pred (N.@"ack_create") (session_msg_pred ack_create_pred Resp).
Proof. solve_ctx. Qed.

Lemma store_ctx_close :
  store_ctx -∗ seal_pred (N.@"close") (session_msg_pred close_pred Init).
Proof. solve_ctx. Qed.

Lemma store_ctx_ack_close :
  store_ctx -∗ seal_pred (N.@"ack_close") (session_msg_pred ack_close_pred Resp).
Proof. solve_ctx. Qed.

Lemma store_ctx_dh_auth_ctx : store_ctx -∗ iso_dh_ctx (N.@"auth").
Proof. solve_ctx. Qed.

End Defs.

Arguments storeGS Σ : clear implicits.
