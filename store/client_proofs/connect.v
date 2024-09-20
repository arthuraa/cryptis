From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.algebra Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta nown.
From cryptis Require Import cryptis primitives tactics.
From cryptis Require Import role dh_auth.
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

Lemma wp_client_connect E c kI kR dq ph T :
  ↑cryptisN ⊆ E →
  ↑nroot.@"db" ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  store_ctx N -∗
  public (TKey Dec kI) -∗
  public (TKey Dec kR) -∗
  {{{ ●H{dq|ph} T ∗
      client_disconnected kI kR }}}
    Client.connect N c
      (TKey Enc kI)
      (TKey Dec kI)
      (TKey Dec kR) @ E
  {{{ cs, RET (repr cs);
      ⌜si_time cs = ph⌝ ∗
      ⌜si_hon cs = T⌝ ∗
      ●H{dq|ph} T ∗
      client_connected kI kR cs }}}.
Proof.
iIntros "% % #chan_c #ctx (#? & #? & _ & _ & _ & _ & _ & _ & _ & _ & #ctx')".
iIntros "#p_ekI #p_ekR".
iIntros "!> %Φ [hon client] post".
rewrite /Client.connect.
wp_pure _ credit:"c1". wp_pure _ credit:"c2". wp_pures.
wp_bind (Connection.connect _ _ _ _ _).
iApply (wp_connection_connect with "[//] [//] [//] [] [] [hon]") => //.
iIntros "!> %cs (hon & conn & % & % & % & % & % & token)".
iDestruct "client" as "(%beginning & client)".
iMod (client_connectingI with "[//] [$] hon conn token client")
  as "(hon & conn & client & #beginning & #ready)" => //; try solve_ndisj.
subst kI kR.
iPoseProof (init_predI _ _ (TInt 0) with "conn client ready")
  as "(conn & client & #?)".
wp_pures. wp_bind (Connection.send _ _ _ _).
iApply (wp_connection_send with "[//] [] [] [] conn") => //.
{ by rewrite public_TInt. }
iIntros "!> conn".
wp_pures.
iCombine "hon client post" as "I". iRevert "conn I".
iApply (wp_connection_recv with "[//] []") => //.
iIntros "!> %m conn (hon & client & post) _ #mP".
iMod (ack_init_predE with "conn client mP") as "(conn & client)" => //.
wp_pures.
iRight. iExists _. iSplitR => //.
iApply "post". iFrame. iModIntro. do 2!iSplit => //.
by iExists _, _; iFrame.
Qed.

End Verif.
