From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role dh_auth.
From cryptis.store Require Import impl shared alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeGS Σ}.

Implicit Types (cs : cst) (ss : sst).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_server_handle_load E c ss m :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public m -∗
  {{{ server ss }}}
    Server.handle_load N c (repr ss) m @ E
  {{{ (v : option val), RET (repr v); server ss }}}.
Proof.
iIntros "%sub #chan_c #ctx #p_m !> %Φ state post".
rewrite /Server.handle_load. wp_pures.
iDestruct "state" as "(%γ & %n & %kvs & %db & #sessR & #key & #minted_key & ts &
                       db & %kvs_db & #pub_db & #view)".
wp_load. wp_pures. wp_load. wp_pures.
iAssert (server ss) with "[ts db view]" as "state".
{ iExists γ, n, kvs, db. iFrame. eauto 8. }
wp_tsdec m; wp_pures; last by iApply ("post" $! None).
wp_list_of_term m; wp_pures; last by iApply ("post" $! None).
wp_list_match => [timestamp t1 ->| _]; wp_pures; last by iApply ("post" $! None).
wp_bind (to_int _). iApply wp_to_int.
case: Spec.to_intP => [ {m} n' -> | _]; wp_pures; last by iApply ("post" $! None).
case: bool_decide_reflect => [[<-]|?]; wp_pures; last by iApply ("post" $! None).
wp_bind (AList.find _ _). iApply AList.wp_find => //.
iIntros "!> _".
rewrite lookup_fmap.
case db_t1: (db !! t1) => [t2|]; wp_pures; last by iApply ("post" $! None).
wp_list. wp_bind (tint _). iApply wp_tint. wp_list. wp_term_of_list.
wp_pures. wp_tsenc. wp_bind (send _ _).
iApply (wp_send with "[//] [#]") => //; last by wp_pures;
  iApply ("post" $! (Some #())).
iDestruct "ctx" as "(_ & _ & _ & _ & ? & _)".
iModIntro.
rewrite big_sepM_delete //. iDestruct "pub_db" as "[[? ?] _]".
iApply public_TEncIS => //.
- rewrite minted_TKey.
  iPoseProof (public_minted with "p_m") as "{p_m} p_m".
  by rewrite minted_TEnc; iDestruct "p_m" as "[??]".
- iModIntro. iExists n, t1, t2, ss, γ. iSplit => //.
  do 3!iSplit => //.
  iDestruct "view" as "[?|(%γ' & sessI & view)]"; first by iLeft.
  iRight. iExists γ'. iSplit => //. iApply DB.load_server; eauto.
- rewrite minted_of_list /= minted_TInt -[minted t1]public_minted.
  rewrite -[minted t2]public_minted; eauto.
- iIntros "!> _". by rewrite public_of_list /= public_TInt; eauto.
Qed.

End Verif.
