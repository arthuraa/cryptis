From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list dfrac_agree.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis.
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

Context `{!storeG Σ}.

Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_client_load skI skR cs t1 t2 :
  cryptis_ctx -∗
  store_ctx -∗
  public t1 -∗
  {{{ db_connected skI skR cs ∗
      db_mapsto skI skR t1 t2 }}}
    Client.load (repr cs) t1
  {{{ t2', RET (repr t2');
      db_connected skI skR cs ∗
      db_mapsto skI skR t1 t2 ∗
      public t2' ∗
      (compromised cs ∨ ⌜t2' = t2⌝) }}}.
Proof.
iIntros "#? #ctx #p_t1 !> %Φ [client mapsto] post".
iDestruct "client" as "(conn & db)".
iMod (load_call t1 with "db mapsto") as "(load & mapsto & waiting)".
wp_lam; wp_pures. wp_list.
iDestruct "ctx" as "(_ & ? & _ & ctx)".
iApply wp_fupd.
wp_apply (RPC.wp_call with "[$conn $load]").
{ do 4!iSplit => //=; by eauto. }
iIntros "%t' (conn & inv_t & p_t)".
iPoseProof ("waiting" with "inv_t") as "(res & db)".
iApply "post". by iFrame.
Qed.

End Verif.
