From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib cryptis primitives tactics role.
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

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_client_create skI skR cs t1 t2 :
  cryptis_ctx -∗
  store_ctx -∗
  public t1 -∗
  public t2 -∗
  {{{ db_connected skI skR cs ∗
      db_free_at skI skR {[t1]} }}}
    Client.create (repr cs) t1 t2
  {{{ RET #();
      db_connected skI skR cs ∗
      db_mapsto skI skR t1 t2 }}}.
Proof.
iIntros "#? (_ & _ & #create & #ctx) #p_t1 #p_t2".
iIntros "!> %Φ [client free] post".
iDestruct "client" as "(conn & db)".
iMod (create_call t1 t2 with "db free") as "(call & mapsto & waiting)".
wp_lam. wp_pures. wp_list. wp_term_of_list.
wp_apply (RPC.wp_call with "[$conn $call]").
{ rewrite public_of_list. do !iSplit => //. }
iIntros "%ts (conn & created & _)". wp_pures.
iApply "post". iFrame. iModIntro. by iApply "waiting".
Qed.

End Verif.
