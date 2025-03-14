From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis.
From cryptis Require Import primitives tactics role rpc.
From cryptis.store Require Import impl shared db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types (cs : RPC.state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_create c kI kR cs t1 t2 :
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  public t2 -∗
  {{{ db_connected N kI kR cs ∗
      rem_free_at N kI kR {[t1]} }}}
    Client.create N c (repr cs) t1 t2
  {{{ RET #();
      db_connected N kI kR cs ∗
      rem_mapsto N kI kR t1 t2 }}}.
Proof.
iIntros "#chan_c (_ & _ & _ & _ & #create & #ack & _) #p_t1 #p_t2".
iIntros "!> %Φ [client free] post".
iDestruct "client"
  as "(%n & %db & conn & version & #db_at & state & token)".
iMod (DB.create_client t1 t2 with "version db_at state free")
  as "(#create_at & version & #db_at' & state & mapsto)".
wp_lam. wp_pures. wp_list.
wp_apply (RPC.wp_write with "[//] [] [] [] [$]") => //.
- by rewrite /=; eauto.
- iRight. iExists _, _. by eauto.
iIntros "conn". wp_pures.
wp_apply (RPC.wp_read with "[//] [] [$]") => //.
- iIntros "%ts (conn & _ & _)". wp_pures.
wp_apply (RPC.wp_tick with "[$]").
iIntros "conn". iApply "post".
by iFrame.
Qed.

End Verif.
