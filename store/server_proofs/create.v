From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.
From cryptis.store Require Import impl shared alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeGS Σ}.

Local Instance STORE : PK := PK_DH (λ _ _ _ _, True)%I.

Implicit Types (cs : cst) (ss : sst).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_server_handle_create E c ss m :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public m -∗
  {{{ server N ss }}}
    Server.handle_create N c (repr ss) m @ E
  {{{ (v : option val), RET (repr v); server N ss }}}.
Proof.
iIntros "%sub #chan_c #ctx #p_m !> %Φ state post".
rewrite /Server.handle_create. wp_pures.
iDestruct "state" as "(%n & %kvs & %db & #handshake & #minted_key & ts &
                       db & %kvs_db & #pub_db & #view)".
wp_load. wp_pures. wp_load. wp_pures.
iAssert (server N ss) with "[ts db view]" as "state".
{ iExists n, kvs, db. iFrame. eauto. }
wp_tsdec m; wp_pures; last by iApply ("post" $! None).
wp_list_of_term m; wp_pures; last by iApply ("post" $! None).
wp_list_match => [timestamp t1 t2 ->| _]; wp_pures; last by iApply ("post" $! None).
wp_bind (to_int _). iApply wp_to_int.
case: Spec.to_intP => [ {m} n' ->| _]; wp_pures;
  last by iApply ("post" $! None).
case: bool_decide_reflect => [[<-] {n'}|?]; wp_pures;
  last by iApply ("post" $! None).
wp_bind (AList.find _ _). iApply AList.wp_find => //.
iIntros "!> _".
iDestruct "ctx" as "(_ & _ & _ & _ & _ & ? & ? & _)".
wp_bind (match: _ with InjL <> => _ | InjR <> => _ end)%E.
iApply (wp_wand _ _ _ (λ v, server N ss ∗ ∃ b : bool,
  ⌜v = #(((if b then 1 else 0) : Z))⌝ ∗
  (⌜b = false⌝ ∨
   ⌜b = true⌝ ∗
   if sst_ok ss then
     ∃ γ, wf_key N (sst_key ss) γ ∗ DB.free_at γ n t1
   else True))%I with "[state]").
{ case db_t1: (db !! t1) => [t2'|]; wp_pures;
    first by iFrame; iExists false; eauto.
  iDestruct "state" as "(%n' & %kvs' & %db' & _ & _ & ts & db & _ & _ & _)".
  wp_bind (AList.insert _ _ _). iApply AList.wp_insert => //.
  iIntros "!> %kvs'' %kvs''_db'". wp_store. wp_pures.
  iDestruct (public_TEncE with "p_m [//]") as "{p_m} [p_m|p_m]".
  - case is_ok: sst_ok.
    { iDestruct "view" as "(%γ & (#contra & _) & _)".
      iDestruct "p_m" as "[p_k _]".
      iDestruct ("contra" with "p_k") as ">[]". }
    wp_store.
    have -> : (n + 1)%Z = S n :> Z by lia.
    iModIntro. iSplit; last by iExists true; eauto.
    iExists (S n), kvs'', _. iFrame. rewrite is_ok.
    do 4!iSplit => //.
    iApply big_sepM_insert_2 => //.
    rewrite public_of_list /=.
    by iDestruct "p_m" as "(_ & _ & ? & ? & _)"; eauto.
  - iDestruct "p_m" as "(#p_m & _)". wp_store.
    have -> : (n + 1)%Z = S n :> Z by lia.
    iDestruct "p_m" as "(%γ & %n'' & %t1' & %t2' & %ok & %e & handshake' &
                         wf & p_t1 & p_t2 & t1_t2)".
    case/Spec.of_list_inj: e => e <- <- {t1' t2'}.
    have {n'' e} <- : n = n'' by lia.
    case is_ok: sst_ok => //; last first.
    { iSplitL; last by iExists true; eauto.
      iModIntro. iExists (S n), kvs'', _. iFrame. rewrite is_ok.
      do 4!iSplit => //.
      iApply big_sepM_insert_2 => //.
      by eauto. }
    iDestruct "view" as "(%γ' & wf' & view)".
    iPoseProof (handshake_done_agree with "wf' handshake handshake'")
      as "<-".
    iPoseProof (wf_key_agree with "handshake wf' wf") as "->".
    iSplitL.
    + iModIntro.
      iExists (S n), kvs'', _. iFrame. rewrite is_ok.
      do 4!iSplit => //.
      * iApply big_sepM_insert_2 => //.
        by eauto.
      * iExists γ. iSplit => //. by iApply DB.create_server.
    + iExists true. iSplitR => //.
      iRight. iSplitR => //. iExists γ. iModIntro. iSplit => //.
      by iApply DB.free_atI. }
iIntros "%v (state & %b & -> & #vP)".
wp_pures. wp_bind (tint _). iApply wp_tint. wp_list.
wp_bind (tint _). iApply wp_tint. wp_list. wp_term_of_list.
iAssert (▷ (public t1 ∗ public t2))%I as "[p_t1 p_t2]".
  { iDestruct (public_TEncE with "p_m [//]") as "{p_m} [[_ p_m]|p_m]".
    - rewrite public_of_list /=. iDestruct "p_m" as "(_ & ? & ? & _)".
      by eauto.
    - iDestruct "p_m" as "(#p_m & _)". iModIntro.
      iDestruct "p_m" as "(%γ & %n'' & %t1' & %t2' & %ok & %e &
                           _ & ? & ? & ? & _)".
      by case/Spec.of_list_inj: e => _ <- <-; eauto. }
wp_pures. wp_tsenc. wp_bind (send _ _).
iApply (wp_send with "[//] [#]") => //; last by wp_pures;
  iApply ("post" $! (Some #())).
iModIntro. iApply public_TEncIS => //.
- rewrite minted_TKey.
  iPoseProof (public_minted with "p_m") as "{p_m} p_m".
  by rewrite minted_TEnc; iDestruct "p_m" as "[??]".
- iModIntro. iExists n, t1, t2, b, (sst_ok ss). iSplit => //.
  iSplit => //.
  case: sst_ok => //.
  iDestruct "view" as "(%γ & key & view)".
  iExists γ. iSplit => //.
  iDestruct "vP" as "[->| (-> & vP)]" => //.
  iDestruct "vP" as "(%γ' & key' & free)".
  by iPoseProof (wf_key_agree with "handshake key key'") as "->".
- iPoseProof (public_minted with "p_m") as "m_m".
  rewrite minted_TEnc minted_tag !minted_of_list /= !minted_TInt.
  iDestruct "m_m" as "(? & _ & ? & ? & _)". by eauto.
- iIntros "!> _". by rewrite public_of_list /= !public_TInt; eauto.
Qed.

End Verif.
