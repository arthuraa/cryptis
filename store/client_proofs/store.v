From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role conn rpc.
From cryptis.store Require Import impl shared db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types (cs : Conn.state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_store c kI kR cs t1 t2 t2' :
  channel c -∗
  cryptis_ctx -∗
  store_ctx N -∗
  public t1 -∗
  public t2' -∗
  {{{ db_connected N kI kR cs ∗ rem_mapsto N kI kR t1 t2 }}}
    Client.store N c (repr cs) t1 t2'
  {{{ RET #(); db_connected N kI kR cs ∗ rem_mapsto N kI kR t1 t2' }}}.
Proof.
iIntros "#chan_c #? #ctx #p_t1 #p_t2 !> %Φ [client mapsto] post".
iDestruct "client" as "(%n & %db & conn & version & #db_at & state)".
wp_lam. wp_pures. wp_list.
iMod (DB.store_client t2' with "version db_at state mapsto")
  as "(version & #db_at' & #store_at & state & mapsto)".
iPoseProof (store_ctx_store with "[//]") as "?".
iPoseProof (store_ctx_rpc_ctx with "[//]") as "?".
wp_apply (RPC.wp_call with "[$conn]").
{ do 4!iSplit => //=; first by eauto.
  iSplit => //. iRight. iExists _, _. by eauto. }
iIntros "%ts' (conn & _ & _)". wp_pures. iApply "post".
by iFrame.
Qed.

End Verif.
