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

Context `{!cryptisG Σ, !heapGS Σ, !sessionG Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Local Instance STORE : PK := PK_DH (λ _ _ _ _, True)%I.

Implicit Types (cs : cst) (ss : sst).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Definition client_state s n t : iProp :=
  cst_ts s ↦ #n ∗
  sterm (cst_key s) ∗
  handshake_done N (cst_key s) (cst_ok s) ∗
  (if cst_ok s then value_auth N (cst_key s) n t else True%I).

Lemma client_state_frag s n t :
  client_state s n t -∗
  sterm (cst_key s) ∗
  handshake_done N (cst_key s) (cst_ok s) ∗
  if cst_ok s then value_frag N (cst_key s) n t else True%I.
Proof.
iIntros "(_ & ? & ? & ?)"; case: cst_ok => //; iFrame.
by iApply value_auth_frag.
Qed.

Lemma wp_client_get_ts E s n t :
  {{{ client_state s n t }}}
    Client.get_ts (repr s) @ E
  {{{ RET #n; client_state s n t }}}.
Proof.
rewrite /Client.get_ts.
iIntros "%Φ (Hl & #s_kS & Hγ & state) post".
wp_pures. wp_load. iApply "post". iModIntro. by iFrame.
Qed.

Lemma wp_client_next_ts t' E s n t :
  {{{ client_state s n t }}}
    Client.next_ts (repr s) @ E
  {{{ RET #(); client_state s (S n) t' }}}.
Proof.
iIntros "%Ψ (n_stored & #s_key & n_t & auth) post".
iAssert (|==> if cst_ok s then value_auth N (cst_key s) (S n) t' else True)%I
  with "[auth]" as ">auth".
{ case: cst_ok => //.
  by iApply (value_auth_update N t'). }
rewrite /Client.next_ts; wp_pures; wp_load; wp_store.
iApply "post"; iFrame.
rewrite (_ : (n + 1)%Z = (S n)%nat :> Z); last by lia.
by iFrame.
Qed.

Lemma wp_client_get_sk E s n t :
  {{{ client_state s n t }}}
    Client.get_sk (repr s) @ E
  {{{ RET (repr (Spec.mkskey (cst_key s))); client_state s n t }}}.
Proof.
rewrite /Client.get_sk.
iIntros "%Φ ? post". wp_pures. by iApply "post".
Qed.

Lemma wp_client_send_store E c s n t t' :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  pterm t' -∗ (* FIXME: t' does not have to be public already *)
  {{{ client_state s n t }}}
    Client.send_store N c (repr s) t' @ E
  {{{ RET #(); client_state s (S n) t' }}}.
Proof.
rewrite /Client.send_store.
iIntros "% #chan_c (_ & #? & _) #p_t' !> %Φ state post".
wp_pures. wp_bind (Client.next_ts _).
iApply (wp_client_next_ts t' with "state"); iIntros "!> state".
wp_pures. wp_bind (Client.get_ts _).
iApply (wp_client_get_ts with "state"); iIntros "!> state".
wp_pures. wp_bind (Client.get_sk _).
iApply (wp_client_get_sk with "state"); iIntros "!> state".
iPoseProof (client_state_frag with "state") as "# (s_k & p_k & frag)".
wp_pures. wp_list. wp_bind (tint _). iApply wp_tint. wp_list.
wp_term_of_list. wp_tsenc. wp_pures.
iApply (wp_send with "[//] [#]"); eauto; last by iApply "post".
iModIntro. iApply pterm_TEncIS => //.
- by rewrite sterm_TKey.
- iModIntro. iExists (S n), t', (cst_ok s).
  by do 3?iSplit => //.
- rewrite sterm_of_list /= sterm_TInt; do ![iSplit => //].
  by iApply pterm_sterm.
- iModIntro. iIntros "_". rewrite pterm_of_list /= pterm_TInt. iSplit => //.
  by iSplit => //.
Qed.

Lemma wp_client_ack_store E c s n t :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  {{{ client_state s n t }}}
    Client.ack_store N c (repr s) @ E
  {{{ RET #(); client_state s n t }}}.
Proof.
iIntros "% #chan_c (_ & _ & #? & _) !> %Φ state post".
rewrite /Client.ack_store. wp_pures.
wp_bind (Client.get_ts _). iApply (wp_client_get_ts with "state") => //.
iIntros "!> state". wp_pures.
wp_bind (Client.get_sk _). iApply (wp_client_get_sk with "state") => //.
iIntros "!> state". wp_pures.
iPoseProof (client_state_frag with "state") as "#(s_k & ?)".
iCombine "post state" as "I". iRevert "I".
iApply wp_sess_recv => //. iIntros "!> %m [post state] _".
wp_pures. wp_bind (tint _). iApply wp_tint.
wp_eq_term e; wp_pures; iModIntro; last first.
  iLeft. by iFrame.
iRight. iExists _; iSplit => //. by iApply "post".
Qed.

Lemma wp_client_store E c s n t t' :
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  pterm t' -∗
  {{{ client_state s n t }}}
    Client.store N c (repr s) t' @ E
  {{{ RET #(); client_state s (S n) t' }}}.
Proof.
iIntros "% #chan_c #ctx #p_t' !> %Φ state post". rewrite /Client.store.
wp_pures. wp_bind (Client.send_store _ _ _ _).
iApply (wp_client_send_store with "[] [] [] [state] [post]") => //.
iIntros "!> state". wp_pures.
iApply (wp_client_ack_store with "[] [] [state] [post]") => //.
Qed.

Lemma wp_client_connect E c kI kR dq ph T :
  ↑N ⊆ E →
  ↑cryptisN ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  store_ctx N -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  {{{ ●H{dq|ph} T }}}
    Client.connect N c (TKey Dec kI) (TKey Enc kI) (TKey Enc kR) @ E
  {{{ s, RET (repr s);
      ●H{dq|ph} T ∗
      ⌜cst_ok s = in_honest kI kR T⌝ ∗
      client_state s 0 (TInt 0) }}}.
Proof.
iIntros "% % #chan_c #ctx (#? & _ & _ & _ & _ & #ctx' & #?) #p_ekI #p_ekR".
iIntros "!> %Φ hon post". rewrite /Client.connect. wp_pures.
iCombine "hon post" as "post". iRevert "post".
iApply wp_do_until. iIntros "!> [hon post]". wp_pures.
wp_bind (pk_dh_init _ _ _ _ _).
iApply (wp_pk_dh_init with "[] [] [] [] [] [hon]"); eauto.
  by iFrame.
iIntros "!> %okS [hon HokS]".
case: okS => [kS|]; wp_pures; last by iLeft; iFrame; eauto.
wp_alloc l as "Hl". wp_pures. wp_tag. wp_bind (mkskey _). iApply wp_mkskey.
iMod (version_alloc (TInt 0)) as "[%γ cur_term]".
wp_pures.
iDestruct "HokS" as "(#s_kS & _ & #sessW & status)".
set (ok := in_honest kI kR T).
set (kS' := Spec.tag _ kS).
iAssert (handshake_done N kS' ok) as "#done".
  iExists kI, kR, kS, ph, T.
  by do 2!iSplit => //.
iAssert (|==> if ok then value_auth N kS' 0 (TInt 0) else True)%I
  with "[status cur_term]" as ">key".
{ case e_ok: ok => //.
  iDestruct "status" as "(#p_kS & token & #session)".
  iMod (term_meta_set _ _ γ N with "token") as "#meta"; eauto.
  iModIntro. iExists γ. iFrame. iSplit.
  - iIntros "!> %kt #p_kS'".
    rewrite (pterm_TKey kt) pterm_tag sterm_tag.
    iDestruct "p_kS'" as "[?|[_ p_kS']]"; first by iApply "p_kS".
    by iMod (wf_key_elim with "p_kS' [//]") as "#[]".
  - iIntros "!> %kS'' %e".
    case/Spec.tag_inj: e => _ <- {kS''}.
    iExists kI, kR, ph, T. by eauto. }
iAssert (if ok then value_frag N kS' 0 (TInt 0) else True)%I as "#frag".
  case: ok => //.
  by iApply value_auth_frag.
wp_tsenc. wp_bind (send _ _).
iApply (wp_send with "[#] [#]") => //.
  iModIntro. iApply pterm_TEncIS => //.
  - by rewrite sterm_TKey sterm_tag.
  - iModIntro. iExists ok.
    by iSplit => //.
  - by rewrite sterm_TInt.
  - iIntros "!> _". by rewrite pterm_TInt.
wp_pures. iRight. iExists _. iSplitR; eauto.
iApply ("post" $! {| cst_ts := l; cst_key := Spec.tag (N.@"key") kS;
                     cst_ok := ok |}).
rewrite /client_state /=. iFrame. rewrite sterm_tag.
do 2!iSplitR => //.
Qed.

Lemma wp_client_load E c s n t :
  ↑N ⊆ E →
  ↑cryptisN ⊆ E →
  channel c -∗
  store_ctx N -∗
  {{{ client_state s n t }}}
    Client.load N c (repr s) @ E
  {{{ t', RET (repr t');
      client_state s n t ∗
      ◇ ⌜cst_ok s → t' = t⌝ }}}.
Proof.
iIntros "% % #chan_c #ctx !> %Φ state post".
rewrite /Client.load. wp_pures.
wp_bind (Client.get_ts _). iApply (wp_client_get_ts with "state").
iIntros "!> state". wp_pures. wp_bind (tint _). iApply wp_tint.
wp_pures. wp_bind (Client.get_sk _).
iApply (wp_client_get_sk with "state"). iIntros "!> state". wp_pures.
wp_tsenc. wp_pures.
iPoseProof (client_state_frag with "state") as "#(s_k & done & frag)".
wp_bind (send _ _). iApply wp_send; eauto.
  iDestruct "ctx" as "(_ & _ & _ & ? & _)".
  iModIntro. iApply pterm_TEncIS; eauto.
  - by rewrite sterm_TKey.
  - by rewrite sterm_TInt.
  - rewrite pterm_TInt. by eauto.
wp_pures.
iCombine "post state" as "I". iRevert "I". iApply wp_sess_recv => //.
iIntros "!> %ts [post state] #p_t'". wp_pures.
wp_list_of_term ts; wp_pures; last by iLeft; iFrame.
wp_list_match => [n' v -> {ts}|_]; wp_pures; last by iLeft; iFrame.
wp_eq_term e; wp_pures; last by iLeft; iFrame.
subst n'. iModIntro. iRight. iExists _; iSplit; eauto.
iApply ("post" $! v). iSplit => //.
case e_ok: (cst_ok s) => //=. iIntros "_".
iAssert (∃ γ, wf_key N (cst_key s) γ)%I as "#status".
  by iDestruct "frag" as "(% & _ & ?)"; eauto.
iDestruct (ack_loadE with "done status ctx p_t'") as "[_ frag']".
iDestruct "state" as "(_ & _ & auth & _)".
iPoseProof (value_frag_agree with "done frag frag'") as ">->".
by eauto.
Qed.

End Verif.
