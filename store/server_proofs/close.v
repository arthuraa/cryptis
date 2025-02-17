From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role conn.
From cryptis.store Require Import impl shared alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeGS Σ}.

Implicit Types (cs : Conn.state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Ltac failure := iLeft; iFrame.

Lemma wp_server_handle_close c skI skR cs n n0 vdb :
  Conn.cs_role cs = Resp →
  channel c -∗
  store_ctx N -∗
  Conn.handler_correct
    (server_db_connected' N skI skR cs n n0 vdb)
    (server_handler_post N skI skR cs n0 vdb)
    skI skR cs n n0
    (N.@"conn".@"close", Server.handle_close N c (repr cs) vdb).
Proof.
iIntros "%e_rl #chan_c #ctx".
iPoseProof (store_ctx_conn_ctx with "ctx") as "{ctx} ctx".
iPoseProof (Conn.ctx_close with "ctx") as "?".
iPoseProof (Conn.ctx_ack_close with "ctx") as "?".
rewrite /Conn.handler_correct /=. wp_lam; wp_pures. iModIntro.
iExists _. iSplit => //.
iIntros "!> %ts conn _ _ db". wp_pures.
iDestruct "db" as "(%db & #p_db & vdb & #db_at & token)".
iPoseProof (Conn.connected_keyE with "conn") as "%e".
iAssert (|={⊤}=>
  (Conn.session_failed cs true ∨
     □ Conn.ack_close_pred N skI skR cs (n + n0) [TInt 0]) ∗
  server_db_disconnected N skI skR vdb)%I
  with "[vdb token]" as ">(#? & server)".
{ case: e => -> ->. iFrame.
  iDestruct "db_at" as "[fail|db_at]".
  { iModIntro. do !iSplit => //=; eauto.
    iExists (n + n0), true. do !iSplit => //=; eauto.
    iApply (Conn.session_failed_failure cs true with "fail [//]"). }
  iDestruct "token" as "[fail|(%n' & c1 & c2)]".
  { iModIntro. do !iSplit => //=; eauto.
    iExists (n + n0), true. do !iSplit => //=; eauto.
    iApply (Conn.session_failed_failure cs true with "fail [//]"). }
  iMod (Conn.clock_update N (n + n0) with "c1 c2") as "[c1 c2]".
  iAssert (|={⊤}=> Conn.conn_closed N cs (n + n0))%I with "[c2]" as ">#?".
  { iApply (escrowI with "c2"). iApply term_token_switch. }
  iModIntro. iSplit; eauto.
  iExists (n + n0), false. do !iSplit => //; eauto.
  by iRight. }
wp_list.
wp_apply (Conn.wp_write with "[//] [] [] [] [$]") => //.
{ by rewrite /= public_TInt; eauto. }
iIntros "conn". wp_pures.
iDestruct "conn" as "(? & ? & ? & ? & rel & ts & _)".
wp_apply (Conn.wp_close with "ts"). iIntros "_".
wp_pures. iModIntro. iRight. iExists _. iSplit => //.
iRight. by iFrame.
Qed.

End Verif.
