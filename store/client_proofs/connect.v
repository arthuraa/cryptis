From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role dh_auth.
From cryptis.store Require Import impl shared db.
From cryptis.store.client_proofs Require Import common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types (cs : cst).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_connect E c kI kR dq ph T :
  ↑N ⊆ E →
  ↑cryptisN ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  store_ctx N -∗
  public (TKey Dec kI) -∗
  public (TKey Dec kR) -∗
  {{{ ●H{dq|ph} T }}}
    Client.connect N c (TKey Enc kI) (TKey Dec kI) (TKey Dec kR) @ E
  {{{ cs, RET (repr cs);
      ●H{dq|ph} T ∗
      ⌜si_init cs = kI ∧ si_resp cs = kR ∧ si_time cs = ph ∧ si_hon cs = T⌝ ∗
      client cs }}}.
Proof.
iIntros "% % #chan_c #ctx (#? & _ & _ & _ & _ & _ & _ & #ctx') #p_ekI #p_ekR".
iIntros "!> %Φ hon post". rewrite /Client.connect. wp_pures.
iCombine "hon post" as "post". iRevert "post".
iApply wp_do_until. iIntros "!> [hon post]". wp_pures.
wp_bind (initiator _ _ _ _ _).
iMod DB.alloc as "(%γ & auth & free & #frag)". wp_pures.
iApply (wp_initiator γ with "[//] [//] [//] [] [] [hon]"); try solve_ndisj; eauto.
iIntros "!> %okS (hon & HokS)".
case: okS => [kS|]; wp_pures; last by iLeft; iFrame; eauto.
iDestruct "HokS" as "(#s_kS & #sessI & #key)".
wp_alloc timestamp as "ts". wp_pures.
wp_tsenc. wp_bind (send _ _).
iApply (wp_send with "[#] [#]") => //.
  iModIntro. iApply public_TEncIS => //.
  - by rewrite minted_TKey.
  - iModIntro. iExists _, γ. do !iSplit => //. by [].
  - by rewrite minted_TInt.
  - iIntros "!> _". by rewrite public_TInt.
wp_pures. iRight. iExists _. iSplitR; eauto.
set si := SessInfo _ _ _ _ _.
iApply ("post" $! {| cst_si := si;
                     cst_ts := timestamp;
                     cst_name := γ |}).
rewrite /client /=. iFrame. iModIntro. iSplit => //.
iExists 0. iFrame. iSplit => //. iSplit => //.
Qed.

End Verif.
