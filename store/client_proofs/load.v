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

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !RPC.rpcGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_client_load kI kR cs t1 t2 :
  cryptis_ctx -∗
  store_ctx -∗
  public t1 -∗
  {{{ db_connected kI kR cs ∗
      db_mapsto kI kR t1 t2 }}}
    Client.load (repr cs) t1
  {{{ t2', RET (repr t2');
      db_connected kI kR cs ∗
      db_mapsto kI kR t1 t2 ∗
      public t2' ∗
      (compromised_session Init cs ∨ ⌜t2' = t2⌝) }}}.
Proof.
iIntros "#? #ctx #p_t1 !> %Φ [client mapsto] post".
iDestruct "client" as "(conn & db)".
iMod (load_call t1 with "db mapsto") as "(load & mapsto & waiting)".
wp_lam; wp_pures. wp_list.
iDestruct "ctx" as "(_ & ? & _ & ctx)".
wp_apply (RPC.wp_call with "[$conn $load]").
{ do 4!iSplit => //=; by eauto. }
iIntros "%ts' (conn & inv_ts & p_ts)". wp_pures.
iPoseProof ("waiting" with "inv_ts") as "(res & db)".
iApply (wp_wand _ _ _ (λ v : val, ⌜v = default (TInt 0) (head ts')⌝)%I).
{ rewrite [repr_list ts']repr_listE.
  by case: ts' => [|t2' ?] /=; wp_pures. }
iIntros "% ->". iApply "post". iFrame.
iDestruct "res" as "[#?|->]".
- iSplit; eauto. case: ts' => [|??] //=; first by rewrite public_TInt.
  by iDestruct "p_ts" as "[??]".
- iSplit; eauto. by iDestruct "p_ts" as "[??]".
Qed.

End Verif.
