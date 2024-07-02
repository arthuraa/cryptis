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

Lemma ack_storeI kS n :
  store_ctx N -∗
  minted kS -∗
  public (TEnc kS (Spec.tag (N.@"ack_store") (TInt n))).
Proof.
iIntros "(_ & _ & #ctx & _) #s_kS".
iApply public_TEncIS => //.
- by rewrite minted_TKey.
- iModIntro. by iExists n.
- by rewrite minted_TInt.
- by rewrite public_TInt; eauto.
Qed.

Lemma wp_server_handle_store E c ss m :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public m -∗
  {{{ server ss }}}
    Server.handle_store N c (repr ss) m @ E
  {{{ (v : option val), RET (repr v); server ss }}}.
Proof.
iIntros "%sub #chan_c #ctx #p_m !> %Φ state post".
rewrite /Server.handle_store. wp_pures.
wp_tsdec m; wp_pures; last by iApply ("post" $! None).
wp_list_of_term m; wp_pures; last by iApply ("post" $! None).
wp_list_match => [n' t1 t2 ->|_]; wp_pures; last by iApply ("post" $! None).
wp_bind (to_int _). iApply wp_to_int.
case: Spec.to_intP => [ {}n' -> | _]; wp_pures; last by iApply ("post" $! None).
iDestruct "state" as "(%γ & %n & %kvs & %db & #sessR & #sec_key &
                       #minted_key & ts & db & %kvs_db & #pub_db & view)".
wp_load. wp_pures.
case: bool_decide_reflect => [[<-]|ne]; wp_pures; last first.
{ iModIntro. iApply ("post" $! None).
  iExists γ, n, kvs, db. iFrame. by eauto. }
wp_load. wp_pures.
replace (n + 1)%Z with (S n : Z) by lia.
wp_store. wp_load. wp_bind (AList.insert _ _ _).
wp_pures. iApply AList.wp_insert; eauto. iIntros "!> %kvs' %kvs'_db'".
iDestruct (store_predE with "[//] sessR sec_key [#] p_m") as "(p_t1 & p_t2 & wf')".
{ case: (decide (session_ok ss)) => [ok|not_ok].
  - iDestruct ("view" with "[//]") as "(% & #? & ?)". eauto.
  - iIntros "!> %". tauto. }
wp_store. wp_bind (tint _). iApply wp_tint.
wp_tsenc.
iApply wp_fupd.
wp_bind (send _ _). iApply wp_send => //.
{ iModIntro. iApply ack_storeI => //. }
wp_pures. iApply ("post" $! (Some #())).
iExists γ, (S n), kvs', (<[t1 := t2]>db). iFrame.
rewrite -fmap_insert in kvs'_db'.
do 4!iSplitR => //.
iSplitR.
{ iModIntro. iApply big_sepM_insert_2 => //. eauto. }
case: (decide (session_ok ss)) => [ok|not_ok]; last first.
{ iIntros "!> %". tauto. }
iDestruct ("wf'" with "[//]") as "(%γ1 & sessI1 & update)".
iDestruct ("view" with "[//]") as "(%γ2 & #sessI2 & #view)".
iPoseProof (session_agree_name with "sessI1 sessI2") as "(_ & ->)" => //.
iPoseProof (DB.update_server with "view update") as "view'".
iIntros "!> _". iExists _. iSplit => //.
Qed.

End Verif.
