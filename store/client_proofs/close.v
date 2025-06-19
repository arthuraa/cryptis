From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis.
From cryptis Require Import primitives tactics role iso_dh conn rpc.
From cryptis.store Require Import impl shared db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !RPC.rpcGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : Conn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_client_close skI skR cs :
  store_ctx -∗
  {{{ db_connected skI skR cs }}}
    Client.close (repr cs)
  {{{ RET #(); db_disconnected skI skR ∗ public (si_key cs) }}}.
Proof.
iIntros "(_ & _ & _ & #?)".
iIntros "!> %Φ client post".
iDestruct "client" as "(conn & %db & ready & state)".
iPoseProof (RPC.client_connected_keys with "conn") as "#[-> ->]".
wp_lam. wp_pures.
wp_apply (RPC.wp_close with "[$conn]"); eauto.
iIntros "pub". iApply "post". iFrame. 
iDestruct "ready" as "[#?|ready]"; eauto.
iLeft. by iApply Conn.session_failed_failure.
Qed.

End Verif.
