From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.
From cryptis.store Require Import impl shared.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Local Instance STORE : PK := PK_DH (λ _ _ _ _, True)%I.

Implicit Types (cs : cst) (ss : sst).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Definition server_state s n t : iProp :=
  sst_ts s ↦ #n ∗
  sst_val s ↦ repr t ∗
  minted (sst_key s) ∗
  public t ∗
  handshake_done N (sst_key s) (sst_ok s) ∗
  if sst_ok s then value_frag N (sst_key s) n t else True%I.

Lemma server_state_frag s n t :
  server_state s n t -∗
  minted (sst_key s) ∗
  public t ∗
  handshake_done N (sst_key s) (sst_ok s) ∗
  if sst_ok s then value_frag N (sst_key s) n t else True%I.
Proof. by iIntros "(_ & _ & ?)". Qed.

Lemma wp_server_get_ts E ss n t :
  {{{ server_state ss n t }}}
    Server.get_ts (repr ss) @ E
  {{{ RET #n; server_state ss n t }}}.
Proof.
iIntros "%Φ (ts & val & ?) post".
rewrite /Server.get_ts. wp_pures. wp_load. iApply "post".
by iFrame.
Qed.

Lemma wp_server_upd_val E ss n t n' t' :
  {{{ ▷ server_state ss n t ∗
      ▷ public t' ∗
      ▷ if sst_ok ss then value_frag N (sst_key ss) n' t' else True%I }}}
    Server.upd_val (repr ss) #n' t' @ E
  {{{ RET #(); server_state ss n' t' }}}.
Proof.
iIntros "%Φ ((ts & val & ? & ? & #frag & key) & p_t' & #frag') post".
rewrite /Server.upd_val. wp_pures. wp_store. wp_pures. wp_store.
iApply "post". iFrame. by eauto.
Qed.

Lemma wp_server_get_val E ss n t :
  {{{ server_state ss n t }}}
    Server.get_val (repr ss) @ E
  {{{ RET (repr t);
      public t ∗
      (if sst_ok ss then value_frag N (sst_key ss) n t else True%I) ∗
      server_state ss n t }}}.
Proof.
iIntros "%Φ (ts & val & ? & #? & #done & #frag) post".
rewrite /Server.get_val. wp_pures. wp_load. iApply "post".
iFrame. iModIntro. by eauto.
Qed.

Lemma wp_server_get_key E ss n t :
  {{{ server_state ss n t }}}
    Server.get_key (repr ss) @ E
  {{{ RET (repr (Spec.mkskey (sst_key ss)));
      server_state ss n t }}}.
Proof.
iIntros "%Φ ? post".
rewrite /Server.get_key. wp_pures. by iApply "post".
Qed.

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

Lemma wp_server_handle_store E c ss n t m :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public (TEnc (sst_key ss) (Spec.tag (N.@"store") m)) -∗
  {{{ server_state ss n t }}}
    Server.handle_store N c (repr ss) m @ E
  {{{ n' t' v, RET v; server_state ss n' t' }}}.
Proof.
iIntros "%sub #chan_c #ctx #p_m !> %Φ state post".
rewrite /Server.handle_store. wp_pures.
wp_list_of_term m; wp_pures; last by iApply "post".
wp_list_match => [n' t' ->|_]; wp_pures; last by iApply "post".
wp_bind (to_int _). iApply wp_to_int.
case: Spec.to_intP => [ {}n' -> | _]; wp_pures; last by iApply "post".
wp_bind (Server.get_ts _). iApply (wp_server_get_ts with "state").
iIntros "!> state". wp_pures.
case: bool_decide_reflect => [nn'|_]; wp_pures; last by iApply "post".
have {n' nn'} [n' ->] : ∃ n'' : nat, n' = n''.
  exists (Z.to_nat n'). by lia.
iPoseProof (server_state_frag with "state") as "#(_ & _ & done & frag)".
iAssert (if sst_ok ss then ∃ γ, wf_key N (sst_key ss) γ else True)%I
  as "{frag} #frag".
{ case: sst_ok => //.
  by iDestruct "frag" as "(% & _ & ?)"; eauto. }
iPoseProof (store_predE with "done frag ctx p_m") as "(#p_t' & #frag')".
wp_bind (Server.upd_val _ _ _).
iApply (wp_server_upd_val with "[$]").
iIntros "!> state". wp_pures.
wp_bind (Server.get_key _).
iApply (wp_server_get_key with "[$]") => //.
iIntros "!> state". wp_tsenc. rewrite /=.
iApply wp_send => //.
  iModIntro. iApply ack_storeI => //.
  iPoseProof (public_minted with "p_m") as "s_m".
  rewrite minted_TEnc. by iDestruct "s_m" as "[??]".
iApply "post". by eauto.
Qed.

Lemma wp_server_handle_load E c ss n t m :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  public (TEnc (sst_key ss) (Spec.tag (N.@"load") m)) -∗
  {{{ server_state ss n t }}}
    Server.handle_load N c (repr ss) m @ E
  {{{ v, RET v; server_state ss n t }}}.
Proof.
iIntros "%sub #chan_c #ctx #p_m !> %Φ state post".
rewrite /Server.handle_load. wp_pures.
wp_bind (to_int _). iApply wp_to_int.
case: Spec.to_intP => [ {m} n' -> | _]; wp_pures; last by iApply "post".
wp_bind (Server.get_ts _). iApply (wp_server_get_ts with "[$]").
iIntros "!> state". wp_pures.
case: bool_decide_reflect => [[ {n'} <-]| _]; wp_pures; last by iApply "post".
wp_bind (Server.get_val _). iApply (wp_server_get_val with "[$]").
iIntros "!> (#p_t & #frag & state)". wp_pures.
wp_list. wp_term_of_list. wp_bind (Server.get_key _).
iApply (wp_server_get_key with "[$]").
iIntros "!> state". wp_tsenc. rewrite /=.
iApply (wp_send with "[//] [#]") => //; last by iApply "post".
iDestruct "ctx" as "(_ & _ & _ & _ & ? & _)".
iDestruct "state" as "(_ & _ & #? & _ & #frag' & #key)".
iModIntro. iApply public_TEncIS => //.
- rewrite minted_TKey.
  iPoseProof (public_minted with "p_m") as "{p_m} p_m".
  by rewrite minted_TEnc; iDestruct "p_m" as "[??]".
- iModIntro.
  iExists n, t, (sst_ok ss).
  by eauto.
- rewrite minted_of_list /= minted_TInt -[minted t]public_minted; eauto.
- iIntros "!> _". by rewrite public_of_list /= public_TInt; eauto.
Qed.

Lemma wp_server_conn_handler_body E c ss n t :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  {{{ server_state ss n t }}}
    Server.conn_handler_body N c (repr ss) @ E
  {{{ n' t' v, RET v; server_state ss n' t' }}}.
Proof.
iIntros "% #chan_c #ctx !> %Φ state post". rewrite /Server.conn_handler_body.
wp_pures. wp_bind (Server.get_key _).
iApply (wp_server_get_key with "[$]"). iIntros "!> state".
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m #p_m". wp_pures.
wp_tsdec m; wp_pures; last wp_tsdec m; wp_pures; last by iApply "post".
- iApply (wp_server_handle_store with "[# //] [# //] [# //] [$] [$]") => //.
- iApply (wp_server_handle_load with "[# //] [# //] [# //] [$]") => //.
Qed.

Lemma wp_server_conn_handler E c ss n t :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  {{{ server_state ss n t }}}
    Server.conn_handler N c (repr ss) @ E
  {{{ v, RET v; False }}}.
Proof.
iIntros "% #chan_c #ctx".
iLöb as "IH" forall (n t). iIntros "!> %Φ state post". wp_rec.
wp_pures. wp_bind (Server.conn_handler_body _ _ _).
iApply (wp_server_conn_handler_body with "[# //] [# //] [$]") => //.
iIntros "!> %n' %t' %v state". wp_pures.
by iApply ("IH" with "[$]").
Qed.

Lemma initE kS t :
  store_ctx N -∗
  public (TEnc kS (Spec.tag (N.@"init") t)) -∗
  public (TKey Enc kS) ∨
  ▷ ∃ ok, handshake_done N kS ok ∗
            (if ok then value_frag N kS 0 (TInt 0) else True)%I.
Proof.
iIntros "(#initP & _) #p_t".
iDestruct (public_TEncE with "[//] [//]") as "[[??]|#tP]"; first by eauto.
iRight. by iDestruct "tP" as "(#init & _ & _)".
Qed.

Lemma wp_server_listen E c kR dq ph T :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  {{{ cryptis_ctx ∗ channel c ∗ store_ctx N ∗
      public (TKey Enc kR) ∗ ●H{dq|ph} T }}}
    Server.listen N c (TKey Dec kR) (TKey Enc kR) @ E
  {{{ RET #(); False }}}.
Proof.
iIntros "% %". iLöb as "IH".
iIntros "%Φ (#? & #chan_c & #ctx & #p_ek & hon) post".
wp_pures. wp_rec. wp_pures. wp_bind (pk_dh_resp _ _ _ _).
iAssert (pk_dh_ctx N (λ _ _ _ _, True)%I) as "#?".
  by iDestruct "ctx" as "(_ & _ & _ & _ & _ & ?)".
iApply (wp_pk_dh_resp with "[# //] [# //] [# //] [# //] [hon]") => //.
  iFrame. by eauto.
iIntros "!> %res (hon & resP)". case: res => [[pkI kS]|]; wp_pures; last first.
  iApply ("IH" with "[hon] [$]"). iFrame. by eauto.
iDestruct "resP" as "(%kI & -> & #p_pkI & #s_kS & _ & #sessW & key)".
wp_tag. wp_bind (mkskey _). iApply wp_mkskey. wp_pures.
wp_bind (Fork _). iApply (wp_fork with "[key]"); last first.
  iModIntro. wp_pures. iApply ("IH" with "[-post] post"). iFrame.
  by eauto.
iClear "IH". iModIntro. rewrite /Server.wait_init. wp_pures.
iRevert "key". iApply wp_sess_recv => //.
  by rewrite minted_tag.
iIntros "!> %t key #p_t".
wp_pures. wp_alloc v as "Hv". wp_alloc ts as "Hts".
pose (ss := {| sst_ts := ts; sst_val := v;
               sst_key := Spec.tag (nroot.@"keys".@"sym") kS;
               sst_ok := in_honest kI kR T |}).
iAssert (handshake_done N (sst_key ss) (sst_ok ss)) as "#done".
{ iExists kI, kR, kS, ph, T; eauto. }
iAssert (▷ server_state ss 0 (TInt 0))%I with "[Hts Hv key]" as "state".
{ iFrame.
  rewrite /= minted_tag public_TInt. do 3!iSplit => //.
  case e_ok: in_honest => //.
  iDestruct "key" as "(#sec & _ & #key)".
  iAssert (∀ kt, public (TKey kt (sst_key ss)) -∗ ◇ False)%I as "{sec} sec".
  { iIntros "%kt #p_kS'".
    iPoseProof (public_sym_keyE with "[//] p_kS'") as ">sym".
    by iApply "sec". }
  iPoseProof (initE with "ctx p_t") as "{p_t} [contra|p_t]".
    by iDestruct ("sec" with "contra") as ">[]".
  iModIntro. iDestruct "p_t" as "(%ok & #done' & frag)".
  iPoseProof (handshake_done_session_key with "done' key") as "->".
  by rewrite e_ok. }
wp_pures.
iApply (wp_server_conn_handler _ ss with "[#] [#] [$]") => //.
by iIntros "!> % []".
Qed.

End Verif.
