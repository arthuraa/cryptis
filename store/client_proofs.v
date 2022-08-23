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

Definition client_state kI kR s n t : iProp :=
  cst_ts s ↦ #n ∗
  sterm (cst_key s) ∗
  version_auth (cst_name s) (DfracOwn 1) n t ∗
  store_key N Init kI kR (cst_key s) (cst_ok s) (cst_name s).

Lemma client_state_version_frag kI kR s n t :
  client_state kI kR s n t -∗
  version_frag (cst_name s) n t.
Proof.
iIntros "(_ & _ & ? & _)".
by iApply version_auth_frag.
Qed.

Lemma client_state_store_key kI kR s n t :
  client_state kI kR s n t -∗
  sterm (cst_key s) ∗
  store_key N Init kI kR (cst_key s) (cst_ok s) (cst_name s).
Proof. by iIntros "(_ & ? & _ & ?)"; eauto. Qed.

Lemma wp_client_get_ts E kI kR s n t :
  {{{ client_state kI kR s n t }}}
    Client.get_ts (repr s) @ E
  {{{ RET #n; client_state kI kR s n t }}}.
Proof.
rewrite /Client.get_ts.
iIntros "%Φ (Hl & #s_kS & Hγ & state) post".
wp_pures. wp_load. iApply "post". iModIntro. by iFrame.
Qed.

Lemma wp_client_next_ts t' E kI kR s n t :
  {{{ client_state kI kR s n t }}}
    Client.next_ts (repr s) @ E
  {{{ RET #(); client_state kI kR s (S n) t' }}}.
Proof.
iIntros "%Ψ (n_stored & #s_key & n_t & auth) post".
iMod (version_update t' with "n_t") as "n_t".
rewrite /Client.next_ts; wp_pures; wp_load; wp_store.
iApply "post"; iFrame.
rewrite (_ : (n + 1)%Z = (S n)%nat :> Z); last by lia.
by iFrame.
Qed.

Lemma wp_client_get_sk E kI kR s n t :
  {{{ client_state kI kR s n t }}}
    Client.get_sk (repr s) @ E
  {{{ RET (repr (Spec.mkskey (cst_key s))); client_state kI kR s n t }}}.
Proof.
rewrite /Client.get_sk.
iIntros "%Φ ? post". wp_pures. by iApply "post".
Qed.

Lemma wp_client_send_store E kI kR c s n t t' :
  ↑cryptisN ⊆ E →
  channel c -∗
  ctx N -∗
  pterm t' -∗ (* FIXME: t' does not have to be public already *)
  {{{ client_state kI kR s n t }}}
    Client.send_store N c (repr s) t' @ E
  {{{ RET #(); client_state kI kR s (S n) t' }}}.
Proof.
rewrite /Client.send_store.
iIntros "% #chan_c (#? & _) #p_t' !> %Φ state post".
wp_pures. wp_bind (Client.next_ts _).
iApply (wp_client_next_ts t' with "state"); iIntros "!> state".
iPoseProof (client_state_version_frag with "state") as "#frag".
wp_pures. wp_bind (Client.get_ts _).
iApply (wp_client_get_ts with "state"); iIntros "!> state".
wp_pures. wp_bind (Client.get_sk _).
iApply (wp_client_get_sk with "state"); iIntros "!> state".
iPoseProof (client_state_store_key with "state") as "# (s_k & p_k)".
wp_pures. wp_list. wp_bind (tint _). iApply wp_tint. wp_list.
wp_term_of_list. wp_tsenc. wp_pures.
iApply (wp_send with "[//]"); eauto; last by iApply "post".
iModIntro. iApply pterm_TEncIS => //.
- by rewrite sterm_TKey.
- iModIntro. iExists (S n), t', kI, kR, (cst_ok s), (cst_name s).
  by eauto.
- rewrite sterm_of_list /= sterm_TInt; do ![iSplit => //].
  by iApply pterm_sterm.
- iModIntro. iIntros "_". rewrite pterm_of_list /= pterm_TInt. iSplit => //.
  by iSplit => //.
Qed.

Lemma wp_client_ack_store E kI kR c s n t :
  ↑cryptisN ⊆ E →
  channel c -∗
  ctx N -∗
  {{{ client_state kI kR s n t }}}
    Client.ack_store N c (repr s) @ E
  {{{ RET #(); client_state kI kR s n t }}}.
Proof.
iIntros "% #chan_c (_ & #? & _) !> %Φ state post".
rewrite /Client.ack_store. wp_pures.
wp_bind (Client.get_ts _). iApply (wp_client_get_ts with "state") => //.
iIntros "!> state". wp_pures.
wp_bind (Client.get_sk _). iApply (wp_client_get_sk with "state") => //.
iIntros "!> state". wp_pures.
iPoseProof (client_state_store_key with "state") as "#[s_k ?]".
iCombine "post state" as "I". iRevert "I".
iApply wp_sess_recv => //. iIntros "!> %m [post state] _".
wp_pures. wp_bind (tint _). iApply wp_tint.
wp_eq_term e; wp_pures; iModIntro; last first.
  iLeft. by iFrame.
iRight. iExists _; iSplit => //. by iApply "post".
Qed.

Lemma wp_client_store E kI kR c s n t t' :
  ↑cryptisN ⊆ E →
  channel c -∗
  ctx N -∗
  pterm t' -∗
  {{{ client_state kI kR s n t }}}
    Client.store N c (repr s) t' @ E
  {{{ RET #(); client_state kI kR s (S n) t' }}}.
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
  ctx N -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  {{{ ●H{dq|ph} T }}}
    Client.connect N c (TKey Dec kI) (TKey Enc kI) (TKey Enc kR) @ E
  {{{ s, RET (repr s);
      ●H{dq|ph} T ∗
      ⌜cst_ok s = in_honest kI kR T⌝ ∗
      client_state kI kR s 0 (TInt 0) }}}.
Proof.
iIntros "% % #chan_c #ctx (_ & _ & _ & _ & #ctx' & #key) #p_ekI #p_ekR".
iIntros "!> %Φ hon post". rewrite /Client.connect. wp_pures.
iCombine "hon post" as "post". iRevert "post".
iApply wp_do_until. iIntros "!> [hon post]". wp_pures.
wp_bind (pk_dh_init _ _ _ _ _).
iApply (wp_pk_dh_init with "[] [] [] [] [] [hon]"); eauto.
  by iFrame.
iIntros "!> %okS [hon HokS]".
case: okS => [kS|]; wp_pures; last by iLeft; iFrame; eauto.
wp_alloc l as "Hl". wp_pures. wp_tag. wp_bind (mkskey _). iApply wp_mkskey.
iMod version_alloc as "[%γ cur_term]".
wp_pures. iRight. iExists _. iSplitR; eauto.
iDestruct "HokS" as "(#s_kS & _ & #sessW & status)".
iApply ("post" $! {| cst_ts := l; cst_key := Spec.tag (N.@"key") kS;
                     cst_name := γ;
                     cst_ok := in_honest kI kR T |}).
rewrite /client_state /=. iFrame. rewrite sterm_tag.
do 2!iSplitR => //.
iExists kS, ph, T. do 3!iSplitR => //.
case: in_honest; last by eauto.
iDestruct "status" as "(#p_kS & token & #session)".
iMod (term_meta_set _ _ γ N with "token") as "#meta"; eauto.
iModIntro. do 2!iSplit => //. iIntros "!> %kt #p_kS'".
rewrite (pterm_TKey kt) pterm_tag sterm_tag.
iDestruct "p_kS'" as "[?|[_ p_kS']]"; first by iApply "p_kS".
by iMod (wf_key_elim with "p_kS' key") as "#[]".
Qed.

Lemma wp_client_load E c kI kR s n t :
  ↑N ⊆ E →
  ↑cryptisN ⊆ E →
  channel c -∗
  ctx N -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  {{{ client_state kI kR s n t }}}
    Client.load N c (repr s) @ E
  {{{ t', RET (repr t');
      client_state kI kR s n t ∗
      ◇ ⌜cst_ok s → t' = t⌝ }}}.
Proof.
iIntros "% % #chan_c #ctx #p_ekI #p_ekR !> %Φ state post".
iDestruct "ctx" as "(_ & _ & ? & ? & _)".
rewrite /Client.load. wp_pures.
wp_bind (Client.get_ts _). iApply (wp_client_get_ts with "state").
iIntros "!> state". wp_pures. wp_bind (tint _). iApply wp_tint.
wp_pures. wp_bind (Client.get_sk _).
iApply (wp_client_get_sk with "state"). iIntros "!> state". wp_pures.
wp_tsenc. wp_pures.
iPoseProof (client_state_store_key with "state") as "#[s_k status]".
wp_bind (send _ _). iApply wp_send; eauto.
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
iPoseProof "status"
  as "(%kS' & %ph & %T & %e_kS & #hon & #sess & #meta & #? & #p_kS)".
iDestruct "p_t'" as "[[contra _] | succ]".
  iMod ("p_kS" $! Enc with "contra") as "{contra} #[]".
iDestruct "succ" as "(_ & #wf_t' & _)".
iDestruct "wf_t'" as "(%n' & %t' & %e & tP)".
iDestruct "state" as "(_ & _ & auth & _)".
case/Spec.of_list_inj: e => /Nat2Z.inj <- <- {n' t'}.
iModIntro.
iApply "tP".
- by iApply "status".
- by iApply version_auth_frag.
Qed.

End Verif.
