From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role iso_dh.
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

Lemma wp_client_store c kI kR cs t1 t2 t2' :
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  public t2' -∗
  {{{ db_connected kI kR cs ∗ rem_mapsto kI kR t1 t2 }}}
    Client.store N c (repr cs) t1 t2'
  {{{ RET #(); db_connected kI kR cs ∗ rem_mapsto kI kR t1 t2' }}}.
Proof.
iIntros "#chan_c #ctx #p_t1 #p_t2 !> %Φ [client mapsto] post".
iDestruct "client" as "(%n & %n0 & db & conn & token)".
wp_lam. wp_pures. wp_list.
iMod (rem_mapsto_store t2' with "db mapsto") as "(db & mapsto & #store)".
wp_apply (wp_connection_write with "[//] [] [] [] [$]").
- by iApply store_ctx_store.
- rewrite /=; eauto.
- iRight. by iExists t1, t2'; eauto.
iIntros "conn". wp_pures.
wp_apply (wp_connection_read with "[//] [] [$]").
- by iApply store_ctx_ack_store.
iIntros "%ts [conn _]". wp_pures.
wp_apply (wp_connection_tick with "[$]"). iIntros "conn".
iApply "post". by iFrame.
Qed.

End Verif.
