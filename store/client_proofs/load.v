From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list dfrac_agree.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis.
From cryptis Require Import primitives tactics.
From cryptis Require Import role iso_dh conn rpc.
From cryptis.store Require Import impl shared db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_load c kI kR cs t1 t2 :
  channel c -∗
  cryptis_ctx -∗
  store_ctx N -∗
  public t1 -∗
  {{{ db_connected N kI kR cs ∗
      rem_mapsto N kI kR t1 t2 }}}
    Client.load N c (repr cs) t1
  {{{ t2', RET (repr t2');
      db_connected N kI kR cs ∗
      rem_mapsto N kI kR t1 t2 ∗
      public t2' ∗
      (compromised_session Init cs ∨ ⌜t2' = t2⌝) }}}.
Proof.
iIntros "#chan_c #? #ctx #p_t1 !> %Φ [client mapsto] post".
iDestruct "client" as "(%n & %db & conn & version & #db_at & state)".
wp_lam; wp_pures. wp_list.
iMod (DB.load_client t1 with "version db_at")
  as "(#load_at & version & db)".
iDestruct "ctx" as "(_ & load & _ & ctx)".
wp_apply (RPC.wp_call with "[$conn]").
{ do 4!iSplit => //=; first by eauto.
  iSplit => //. iRight. iExists _. by eauto. }
iIntros "%ts' (conn & #inv_ts & p_ts)". wp_pures.
rewrite [repr_list ts']repr_listE.
iDestruct "inv_ts" as "[fail|inv_ts]".
- wp_pures. case: ts' => [|t ts]; wp_pures.
  + iApply "post". iFrame. rewrite public_TInt. by eauto.
  + rewrite /=. iDestruct "p_ts" as "[p_t _]".
    iApply "post". iFrame. by eauto.
iDestruct "inv_ts" as "(%t1' & %t2' & -> & load_at' & stored_at)".
iPoseProof (DB.op_at_agree with "load_at load_at'") as "%e".
case: e => <-.
iPoseProof (DB.client_view_stored_at with "db state mapsto stored_at") as "->".
rewrite /=. iDestruct "p_ts" as "[? _]".
wp_pures. iApply "post". iFrame. by eauto.
Qed.

End Verif.
