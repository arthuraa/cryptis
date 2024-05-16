From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.
From cryptis.store Require Import impl shared db.
From cryptis.store.client_proofs Require Import common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Local Instance STORE : PK := PK_DH (λ _ _ _ _, True)%I.

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
  public (TKey Enc kI) -∗
  public (TKey Enc kR) -∗
  {{{ ●H{dq|ph} T }}}
    Client.connect N c (TKey Dec kI) (TKey Enc kI) (TKey Enc kR) @ E
  {{{ cs, RET (repr cs);
      ●H{dq|ph} T ∗
      ⌜cst_ok cs = in_honest kI kR T⌝ ∗
      client N cs }}}.
Proof.
iIntros "% % #chan_c #ctx (#? & _ & _ & _ & _ & _ & _ & #ctx') #p_ekI #p_ekR".
iIntros "!> %Φ hon post". rewrite /Client.connect. wp_pures.
iCombine "hon post" as "post". iRevert "post".
iApply wp_do_until. iIntros "!> [hon post]". wp_pures.
wp_bind (pk_dh_init _ _ _ _ _).
iApply (wp_pk_dh_init with "[] [] [] [] [] [hon]"); eauto.
  by iFrame.
iIntros "!> %okS [hon HokS]".
case: okS => [kS|]; wp_pures; last by iLeft; iFrame; eauto.
wp_alloc timestamp as "ts". wp_pures. wp_tag.
wp_bind (mkskey _). iApply wp_mkskey.
iMod DB.alloc as "(%γ & auth & #frag)". wp_pures.
iDestruct "HokS" as "(#s_kS & _ & #sessW & status)".
set (ok := in_honest kI kR T).
set (kS' := Spec.tag _ kS).
iAssert (handshake_done N kS' ok) as "#done".
  iExists kI, kR, kS, ph, T.
  by do 2!iSplit => //.
iAssert (|==> if ok then wf_key N kS' γ else True)%I
  with "[status]" as ">#key".
{ case e_ok: ok => //.
  iDestruct "status" as "(#p_kS & token & #session)".
  iMod (term_meta_set _ _ γ N with "token") as "#meta"; eauto.
  iModIntro. iSplit.
  - iIntros "!> %kt #p_kS'".
    iPoseProof (public_sym_keyE with "[//] p_kS'") as ">contra".
    by iDestruct ("p_kS" with "contra") as ">[]".
  - iIntros "!> %kS'' %e".
    case/Spec.tag_inj: e => _ <- {kS''}.
    iExists kI, kR, ph, T. by eauto. }
wp_tsenc. wp_bind (send _ _).
iApply (wp_send with "[#] [#]") => //.
  iModIntro. iApply public_TEncIS => //.
  - by rewrite minted_TKey minted_tag.
  - iModIntro. iExists ok, γ. by eauto.
  - by rewrite minted_TInt.
  - iIntros "!> _". by rewrite public_TInt.
wp_pures. iRight. iExists _. iSplitR; eauto.
iApply ("post" $! {| cst_ts := timestamp;
                     cst_key := Spec.tag (nroot.@"keys".@"sym") kS;
                     cst_name := γ;
                     cst_ok := ok |}).
rewrite /client /=. iFrame. iModIntro. iSplit => //.
iExists 0. iFrame. iSplit => //. iSplit => //.
by rewrite minted_tag.
Qed.

End Verif.
