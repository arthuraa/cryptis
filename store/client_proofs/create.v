From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis.
From cryptis Require Import primitives tactics role conn rpc.
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

Lemma wp_client_create c kI kR cs t1 t2 :
  channel c -∗
  cryptis_ctx -∗
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
iIntros "#chan_c #? (_ & _ & #create & #ctx) #p_t1 #p_t2".
iIntros "!> %Φ [client free] post".
iDestruct "client" as "(%db & conn & ready & state)".
iMod (DB.create_client t1 t2 with "ready state free")
  as "(waiting & created & state & mapsto)".
wp_lam. wp_pures. wp_list.
wp_apply (RPC.wp_call with "[$conn created]").
{ do !iSplit => //.
  iDestruct "created" as "[#?|created]"; eauto.
  iRight. iExists _, _. by eauto. }
iIntros "%ts (conn & created & _)". wp_pures.
iApply "post". iFrame.
iDestruct "waiting" as "[?|waiting]"; eauto.
iDestruct "created" as "[?|created]"; eauto.
iPoseProof (DB.create_respE with "waiting created") as "?". by eauto.
Qed.

End Verif.
