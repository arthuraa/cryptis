From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list dfrac_agree.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta nown cryptis.
From cryptis Require Import primitives tactics.
From cryptis Require Import role iso_dh.
From cryptis.store Require Import impl shared db connection_proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_load c kI kR cs t1 t2 :
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  {{{ db_connected kI kR cs ∗
      rem_mapsto kI kR t1 t2 }}}
    Client.load N c (repr cs) t1
  {{{ t2', RET (repr t2');
      db_connected kI kR cs ∗
      rem_mapsto kI kR t1 t2 ∗
      public t2' ∗
      (session_failed cs true ∨ ⌜t2' = t2⌝) }}}.
Proof.
iIntros "#chan_c #ctx #p_t1 !> %Φ [client mapsto] post".
iDestruct "client" as "(%n & %n0 & db & conn & token)".
wp_lam; wp_pures. wp_list.
iMod (DB.load_client t1 with "db") as "[#load_at db]".
iDestruct "ctx" as "(_ & _ & _ & _ & load & ack_load & _)".
wp_apply (wp_connection_write with "chan_c load [] [] [$]").
- by rewrite /=; eauto.
- iRight. iIntros "!>". iExists _. by eauto.
iIntros "conn". wp_pures.
wp_apply (wp_connection_read with "chan_c [//] [$]").
iIntros "%ts (conn & #p_ts & #inv_ts)". wp_pures.
wp_apply (wp_connection_tick with "conn"). iIntros "conn".
rewrite [repr_list ts]repr_listE.
iDestruct "inv_ts" as "[fail|inv_ts]".
- wp_pures. case: ts => [|t ts]; wp_pures.
  + iApply "post". iFrame. rewrite public_TInt. by eauto.
  + rewrite /=. iDestruct "p_ts" as "[p_t _]".
    iApply "post". iFrame. by eauto.
iDestruct "inv_ts" as "(%t1' & %t2' & -> & load_at' & stored_at)".
iPoseProof (DB.op_at_agree with "load_at load_at'") as "%e".
case: e => <-.
iPoseProof (DB.client_view_stored_at with "db mapsto stored_at") as "->".
rewrite /=. iDestruct "p_ts" as "[? _]".
wp_pures. iApply "post". iFrame. by eauto.
Qed.

End Verif.
