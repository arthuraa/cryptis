From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib cryptis.
From cryptis Require Import primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn conn rpc.
From cryptis.examples.store Require Import impl.
From cryptis.examples.store.proofs Require Import base db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ}.
Context `{!RPC.rpcGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_client_close skI skR cs :
  cryptis_ctx -∗
  store_ctx -∗
  {{{ db_connected skI skR cs }}}
    Client.close (repr cs)
  {{{ RET #(); db_disconnected skI skR ∗ public (si_key cs) }}}.
Proof.
iIntros "#? (_ & _ & _ & #?)".
iIntros "!> %Φ client post".
iDestruct "client" as "(conn & %db & ready & state)".
rewrite compromised_public.
iAssert (RPC.client_connected skI skR cs ∗
         ◇ (GenConn.failure skI skR ∨ db_client_ready skI skR db))%I
  with "[conn ready]" as "[conn >ready]".
{ iDestruct "ready" as  "[fail|ready]"; last by iFrame; eauto.
  iPoseProof (RPC.client_connected_failure with "conn fail") as "#H".
  iFrame "conn". by iLeft. }
wp_lam. wp_pures.
wp_apply (RPC.wp_close with "[$conn]"); eauto.
iIntros "pub". iApply "post". by iFrame.
Qed.

End Verif.
