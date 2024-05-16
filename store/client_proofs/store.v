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

Lemma wp_client_get_timestamp E cs (n : nat) :
  {{{ cst_ts cs ↦ #n }}}
    Client.get_timestamp (repr cs) @ E
  {{{ RET #n; cst_ts cs ↦ #n }}}.
Proof.
rewrite /Client.get_timestamp.
iIntros "%Φ Hn post".
wp_pures. wp_load. iApply "post". iModIntro. by iFrame.
Qed.

Lemma wp_client_incr_timestamp E cs (n : nat) :
  {{{ cst_ts cs ↦ #n }}}
    Client.incr_timestamp (repr cs) @ E
  {{{ RET #(); cst_ts cs ↦ #(S n) }}}.
Proof.
iIntros "%Ψ Hn post".
rewrite /Client.incr_timestamp; wp_pures; wp_load; wp_store.
iApply "post"; iFrame.
rewrite (_ : (n + 1)%Z = (S n)%nat :> Z); last by lia.
by iFrame.
Qed.

Lemma wp_client_get_session_key E cs :
  {{{ True }}}
    Client.get_session_key (repr cs) @ E
  {{{ RET (repr (Spec.mkskey (cst_key cs))); True }}}.
Proof.
rewrite /Client.get_session_key.
iIntros "%Φ ? post". wp_pures. by iApply "post".
Qed.

Lemma wp_client_send_store E c cs t1 t2 t2' :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  public t2' -∗ (* FIXME: t1 and t2' do not have to be public already *)
  {{{ client N cs ∗ rem_mapsto cs t1 t2 }}}
    Client.send_store N c (repr cs) t1 t2' @ E
  {{{ RET #(); client N cs ∗ rem_mapsto cs t1 t2' }}}.
Proof.
rewrite /Client.send_store /rem_mapsto.
iIntros "% #chan_c (_ & #? & _) #p_t1 #p_t2' !> %Φ [client mapsto] post".
iDestruct "client" as "(%n & #handshake & #key & #minted & ts & client)".
iMod (DB.update_client t2' with "client mapsto") as "(client & #update & mapsto)".
wp_pures. wp_bind (Client.get_timestamp _).
iApply (wp_client_get_timestamp with "ts"); iIntros "!> ts".
wp_pures. wp_bind (Client.incr_timestamp _).
iApply (wp_client_incr_timestamp with "ts"). iIntros "!> ts".
wp_pures. wp_bind (Client.get_session_key _).
iApply (wp_client_get_session_key with "[//]"); iIntros "!> _".
wp_pures. wp_list. wp_bind (tint _). iApply wp_tint. wp_list.
wp_term_of_list. wp_tsenc. wp_pures.
iPoseProof ("post" with "[client ts mapsto]") as "post".
{ iFrame. iExists (S n). iFrame. by eauto. }
iApply (wp_send with "[//] [#]") => //. iClear "post".
iModIntro. iApply public_TEncIS => //.
- by rewrite minted_TKey.
- iModIntro. iExists (cst_name cs), n, t1, t2', (cst_ok cs).
  do 5?iSplit => //.
- rewrite minted_of_list /= minted_TInt; do ![iSplit => //];
  by iApply public_minted.
- iModIntro. iIntros "_". rewrite public_of_list /= public_TInt. iSplit => //.
  by eauto.
Qed.

Lemma wp_client_ack_store E c cs :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  {{{ client N cs }}}
    Client.ack_store N c (repr cs) @ E
  {{{ RET #(); client N cs }}}.
Proof.
iIntros "% #chan_c (_ & _ & #? & _) !> %Φ client post".
rewrite /Client.ack_store. wp_pures.
iDestruct "client" as "(%n & #handshake & #key & #minted & ts & client)".
wp_bind (Client.get_timestamp _).
iApply (wp_client_get_timestamp with "ts"). iIntros "!> ts". wp_pures.
wp_bind (Client.get_session_key _).
iApply (wp_client_get_session_key with "[//]") => //.
iIntros "!> _". wp_pures.
iCombine "client post ts" as "I". iRevert "I".
iApply wp_sess_recv => //. iIntros "!> %m (client & post & ts) _".
wp_pures. wp_bind (tint _). iApply wp_tint.
wp_eq_term e; wp_pures; iModIntro; last first.
  iLeft. by iFrame.
iRight. iExists _; iSplit => //. iApply "post".
iExists n. by iFrame; eauto.
Qed.

Lemma wp_client_store E c cs t1 t2 t2' :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  public t2' -∗
  {{{ client N cs ∗ rem_mapsto cs t1 t2 }}}
    Client.store N c (repr cs) t1 t2' @ E
  {{{ RET #(); client N cs ∗ rem_mapsto cs t1 t2' }}}.
Proof.
iIntros "% #chan_c #ctx #p_t1 #p_t2 !> %Φ [client mapsto] post".
rewrite /Client.store.
wp_pures. wp_bind (Client.send_store _ _ _ _ _).
iApply (wp_client_send_store with "[] [] [] [//] [$client $mapsto] [post]")
  => //.
iIntros "!> [client mapsto]". wp_pures.
iApply (wp_client_ack_store with "[] [] [client] [post mapsto]") => //.
iIntros "!> client". iApply "post". by iFrame.
Qed.

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

Lemma wp_client_load E c cs t1 t2 :
  ↑N ⊆ E →
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public t1 -∗
  {{{ client N cs ∗ rem_mapsto cs t1 t2 }}}
    Client.load N c (repr cs) t1 @ E
  {{{ t2', RET (repr t2');
      client N cs ∗
      rem_mapsto cs t1 t2 ∗
      ⌜cst_ok cs → t2' = t2⌝ }}}.
Proof.
iIntros "% % #chan_c #ctx #p_t1 !> %Φ [client mapsto] post".
iDestruct "client" as "(%n & #handshake & #key & #minted_key &
                        ts & view)".
rewrite /Client.load. wp_pures.
wp_bind (Client.get_timestamp _).
iApply (wp_client_get_timestamp with "ts").
iIntros "!> ts". wp_bind (tint _). iApply wp_tint.
wp_pures. wp_bind (Client.get_session_key _).
iApply (wp_client_get_session_key with "[//]"). iIntros "!> _". wp_pures.
wp_list. wp_term_of_list. wp_tsenc. wp_pures.
wp_bind (send _ _). iApply wp_send; eauto.
  iDestruct "ctx" as "(_ & _ & _ & ? & _)".
  iModIntro. iApply public_TEncIS; eauto.
  - by rewrite minted_TKey.
  - rewrite minted_of_list /= minted_TInt.
    iPoseProof (public_minted with "p_t1") as "?". by eauto.
  - iIntros "!> _". rewrite public_of_list /= public_TInt; eauto.
wp_pures.
iCombine "view mapsto post ts" as "I". iRevert "I". iApply wp_sess_recv => //.
iIntros "!> %ts (view & mapsto & post & ts) #p_t2'". wp_pures.
wp_list_of_term ts; wp_pures; last by iLeft; iFrame.
wp_list_match => [n' t1' t2' -> {ts}|_]; wp_pures; last by iLeft; iFrame.
wp_eq_term e; last by wp_pures; iLeft; iFrame.
subst n'. wp_pures.
wp_eq_term e; last by wp_pures; iLeft; iFrame.
subst t1'.
iDestruct (ack_loadE with "handshake key view mapsto ctx p_t2'")
  as "{p_t2'} (#p_t2' & #e_t2')".
wp_pures. iModIntro. iRight. iExists _; iSplit; eauto.
iApply ("post" $! t2'). iFrame. iSplitL.
- iExists n. iFrame. by eauto.
- case: (cst_ok cs) => //=.
  iPoseProof "e_t2'" as "->". by eauto.
Qed.

End Verif.
