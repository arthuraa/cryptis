From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta nown cryptis.
From cryptis Require Import primitives tactics role iso_dh.
From cryptis.store Require Import impl shared db connection_proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types (cs : conn_state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_close c kI kR cs :
  channel c -∗
  store_ctx N -∗
  {{{ db_connected kI kR cs }}}
    Client.close N c (repr cs)
  {{{ RET #(); db_disconnected kI kR }}}.
Proof.
iIntros "#chan_c (_ & _ & _ & _ & _ & _ & _ & _ & #close & #ack & _)".
iIntros "!> %Φ client post".
iDestruct "client" as "(%n & %n0 & client & conn & token)".
iPoseProof (connected_keyE with "conn") as "[-> ->]".
wp_lam. wp_pures.
wp_apply (@wp_nil term).
wp_apply (wp_connection_write with "[//] [] [] [] [$]") => //.
- iRight. iModIntro. by eauto.
iIntros "conn". wp_pures.
wp_apply (wp_connection_read with "[//] [] [$]") => //.
iIntros "%ts (conn & _ & #inv)".
wp_pures.
iAssert (|={⊤}=>
  ∃ failed, client_disconnected (si_init cs) (si_resp cs) (n + n0) failed)%I
  with "[token]" as ">(%failed & dis)".
{ iDestruct "token" as "(%e_rl & #server & end)".
  iDestruct "inv" as "[fail|inv]".
  - iExists true. iModIntro. iSplit => //.
    by iApply (session_failed_failure with "fail").
  - iMod (escrowE with "inv end") as ">c1" => //.
    iExists false. iModIntro. iSplit => //. }
iDestruct "conn" as "(_ & _ & _ & _ & rel & ts & _)".
wp_apply (wp_connection_close with "[$]"). iIntros "_".
iApply "post". by iFrame.
Qed.

End Verif.
