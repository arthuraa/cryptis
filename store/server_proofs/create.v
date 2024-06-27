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

Lemma wp_server_handle_create E c ss m :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public m -∗
  {{{ server ss }}}
    Server.handle_create N c (repr ss) m @ E
  {{{ (v : option val), RET (repr v); server ss }}}.
Proof.
iIntros "%sub #chan_c #ctx #p_m !> %Φ state post".
rewrite /Server.handle_create. wp_pures.
iDestruct "state" as "(%γ & %n & %kvs & %db & #sessR & #key_sec & #minted_key
                       & ts & kvs & %kvs_db & #pub_db & #view)".
wp_load. wp_pures. wp_load. wp_pures.
iAssert (server ss) with "[ts kvs view]" as "state".
{ iExists _, n, kvs, db. iFrame. eauto 8. }
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
iApply (wp_wand _ _ _ (λ v, server ss ∗ ∃ b : bool,
  ⌜v = #(((if b then 1 else 0) : Z))⌝ ∗
  (⌜b = false⌝ ∨
   ⌜b = true⌝ ∗
   □ (⌜session_ok ss⌝ -∗ ∃ γ', session ss Init γ' ∗ DB.free_at γ' n t1)))%I
  with "[state]").
{ case db_t1: (db !! t1) => [t2'|]; wp_pures;
    first by iFrame; iExists false; eauto.
  iDestruct "state" as "(% & %n' & %kvs' & %db' & _ & _ & _ & ts & kvs & _ & _)".
  wp_bind (AList.insert _ _ _). iApply AList.wp_insert => //.
  iIntros "!> %kvs'' %kvs''_db'". wp_store. wp_pures.
  iDestruct (public_TEncE with "p_m [//]") as "{p_m} [p_m|p_m]".
  - iDestruct "p_m" as "[p_k p_m]".
    iDestruct ("key_sec" with "p_k") as ">%".
    wp_store.
    have -> : (n + 1)%Z = S n :> Z by lia.
    iModIntro. iSplitL.
    { iExists _, (S n), kvs'', (<[t1 := t2]>db). iFrame.
      do 5!iSplit => //.
      + iApply big_sepM_insert_2 => //.
        rewrite public_of_list /=.
        by iDestruct "p_m" as "(_ & ? & ? & _)"; eauto.
      + iIntros "%ok". tauto. }
    iExists true. iSplit => //. iRight. iSplit => //.
    iIntros "!> %"; tauto.
  - iDestruct "p_m" as "(#p_m & _)". wp_store.
    have -> : (n + 1)%Z = S n :> Z by lia.
    iDestruct "p_m" as "(%n'' & %t1' & %t2' & %si & %γ' & %e & %e_kS &
                         sessI & p_t1 & p_t2 & t1_t2)".
    case/Spec.of_list_inj: e => e <- <- {t1' t2'}.
    have {n'' e} <- : n = n'' by lia.
    iSplitL.
    { iExists γ, (S n), _, _. iFrame. iModIntro. do !iSplit => //.
      - iApply big_sepM_insert_2; eauto.
      - iIntros "%ok".
        iDestruct ("view" with "[//]") as "{view} (%γ'' & sessI' & view)".
        iPoseProof (session_agree with "sessI sessR") as "->" => //.
        iPoseProof (session_agree_name with "sessI sessI'") as "(_ & ->)" => //.
        iExists _. iSplit => //.
        by iApply DB.create_server. }
    iModIntro. iExists true. iSplit => //. iRight. iSplit => //.
    iIntros "!> %ok".
    iDestruct ("view" with "[//]") as "{view} (%γ'' & sessI' & view)".
    iPoseProof (session_agree with "sessI sessR") as "->" => //.
    iPoseProof (session_agree_name with "sessI sessI'") as "(_ & ->)" => //.
    iExists _. iSplit => //. by iApply DB.free_atI. }
iIntros "%v (state & %b & -> & #vP)".
wp_pures. wp_bind (tint _). iApply wp_tint. wp_list.
wp_bind (tint _). iApply wp_tint. wp_list. wp_term_of_list.
iAssert (▷ (public t1 ∗ public t2))%I as "[p_t1 p_t2]".
  { iDestruct (public_TEncE with "p_m [//]") as "{p_m} [[_ p_m]|p_m]".
    - rewrite public_of_list /=. iDestruct "p_m" as "(_ & ? & ? & _)".
      by eauto.
    - iDestruct "p_m" as "(#p_m & _)". iModIntro.
      iDestruct "p_m" as "(%n'' & %t1' & %t2' & %si & %γ' & %e &
                           _ & ? & ? & ? & _)".
      by case/Spec.of_list_inj: e => _ <- <-; eauto. }
wp_pures. wp_tsenc. wp_bind (send _ _).
iApply (wp_send with "[//] [#]") => //; last by wp_pures;
  iApply ("post" $! (Some #())).
iModIntro. iApply public_TEncIS => //.
- rewrite minted_TKey.
  iPoseProof (public_minted with "p_m") as "{p_m} p_m".
  by rewrite minted_TEnc; iDestruct "p_m" as "[??]".
- iModIntro. iExists n, t1, t2, b, ss, γ. do !iSplit => //.
  iIntros "%ok %b_holds".
  iDestruct "vP" as "[->|(_ & #vP)]" => //.
  by iApply "vP".
- iPoseProof (public_minted with "p_m") as "m_m".
  rewrite minted_TEnc minted_tag !minted_of_list /= !minted_TInt.
  iDestruct "m_m" as "(? & _ & ? & ? & _)". by eauto.
- iIntros "!> _". by rewrite public_of_list /= !public_TInt; eauto.
Qed.

End Verif.
