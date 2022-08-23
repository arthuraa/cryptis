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

Definition server_state kI kR s n t : iProp :=
  sst_ts s ↦ #n ∗
  sst_val s ↦ repr t ∗
  sterm (sst_key s) ∗
  pterm t ∗
  (if sst_ok s then version_frag (sst_name s) n t else True%I) ∗
  store_key N Resp kI kR (sst_key s) (sst_ok s) (sst_name s).

Lemma wp_server_get_ts E kI kR ss n t :
  {{{ server_state kI kR ss n t }}}
    Server.get_ts (repr ss) @ E
  {{{ RET #n; server_state kI kR ss n t }}}.
Proof.
iIntros "%Φ (ts & val & ?) post".
rewrite /Server.get_ts. wp_pures. wp_load. iApply "post".
by iFrame.
Qed.

Lemma wp_server_upd_val E kI kR ss n t n' t' :
  {{{ ▷ server_state kI kR ss n t ∗
      ▷ pterm t' ∗
      ▷ if sst_ok ss then version_frag (sst_name ss) n' t' else True%I }}}
    Server.upd_val (repr ss) #n' t' @ E
  {{{ RET #(); server_state kI kR ss n' t' }}}.
Proof.
iIntros "%Φ ((ts & val & ? & ? & #frag & key) & p_t' & #frag') post".
rewrite /Server.upd_val. wp_pures. wp_store. wp_pures. wp_store.
iApply "post". iFrame.
by case: sst_ok.
Qed.

Lemma wp_server_get_val E kI kR ss n t :
  {{{ server_state kI kR ss n t }}}
    Server.get_val (repr ss) @ E
  {{{ RET (repr t);
      pterm t ∗
      (if sst_ok ss then version_frag (sst_name ss) n t else True%I) ∗
      server_state kI kR ss n t }}}.
Proof.
iIntros "%Φ (ts & val & ? & #? & #frag & ?) post".
rewrite /Server.get_val. wp_pures. wp_load. iApply "post".
iFrame.
by eauto.
Qed.

Lemma wp_server_get_key E kI kR ss n t :
  {{{ server_state kI kR ss n t }}}
    Server.get_key (repr ss) @ E
  {{{ RET (repr (Spec.mkskey (sst_key ss)));
      server_state kI kR ss n t }}}.
Proof.
iIntros "%Φ ? post".
rewrite /Server.get_key. wp_pures. by iApply "post".
Qed.

Lemma store_predE kI kR ss n t (n' : nat) t' :
  server_state kI kR ss n t -∗
  ctx N -∗
  pterm (TEnc (sst_key ss) (Spec.tag (N.@"store") (Spec.of_list [TInt n'; t']))) -∗
  ▷ (server_state kI kR ss n t ∗
     pterm t' ∗
     if sst_ok ss then version_frag (sst_name ss) n' t' else True%I).
Proof.
iIntros "state #(? & ? & _ & _) #p_m".
iPoseProof (pterm_TEncE with "p_m [//]") as "{p_m} p_m".
iDestruct "state" as "(? & ? & #? & #p_t & #frag & key)".
iDestruct "key" as "(%kS & %ph & %T & %e_key & %e_ok & #sessW & #key)".
rewrite pterm_of_list /=.
iDestruct "p_m" as "[(p_key & _ & p_t' & _) | p_m]".
{ case e: sst_ok; last first.
    do 2?iSplit => //.
    iFrame. rewrite e. do 3!iSplit => //.
    iExists kS, _, T; iSplit => //.
    rewrite -e_ok e; iSplit => //.
    by iSplit => //.
  iDestruct "key" as "(#meta & #key & #contra)".
  iDestruct ("contra" with "p_key") as ">[]". }
iDestruct "p_m" as "(#p_m & s_t' & _)".
iDestruct "p_m" as "(%n'' & %t'' & %kI'' & %kR'' & %ok'' & %γ'' & >%e & p_m)".
case/Spec.of_list_inj: e => /Nat2Z.inj <- <- {n'' t''}.
iDestruct "p_m" as "(p_t' & >frag'' & p_m)".
case e: sst_ok; last first.
  iModIntro. do 2?iSplit => //.
  iFrame. iSplit => //. iSplit => //. rewrite e. iSplit => //.
  iExists kS, ph, T; iSplit => //.
  rewrite -e_ok e; iSplit => //.
  by iSplit => //.
iDestruct "key" as "(#meta & #key & #s_key)".
iModIntro.
iDestruct "p_m" as "(%kS''' & %ph''' & %T''' & %e_key''' & p_m)".
have {kS''' e_key'''} -> : kS''' = kS.
  rewrite e_key''' in e_key.
  by have [??] := Spec.tag_inj _ _ _ _ e_key.
iDestruct "p_m" as "(%e_ok''' & sessW''' & sess''')".
iDestruct (session_weak_session_key with "sessW''' key")
  as "(-> & -> & -> & ->)".
rewrite e_ok''' -e_ok e.
iDestruct "sess'''" as "(meta''' & _)".
iPoseProof (term_meta_agree with "meta''' meta") as "->".
iFrame. rewrite e.
do 4?iSplit => //.
iExists kS, ph, T. rewrite -e_ok e. do 5?iSplit => //.
Qed.

Lemma ack_storeI kS n :
  ctx N -∗
  sterm kS -∗
  pterm (TEnc kS (Spec.tag (N.@"ack_store") (TInt n))).
Proof.
iIntros "(_ & #ctx & _) #s_kS".
iApply pterm_TEncIS => //.
- by rewrite sterm_TKey.
- iModIntro. by iExists n.
- by rewrite sterm_TInt.
- by rewrite pterm_TInt; eauto.
Qed.

Lemma wp_server_handle_store E c kI kR ss n t m :
  ↑cryptisN ⊆ E →
  channel c -∗
  ctx N -∗
  pterm (TEnc (sst_key ss) (Spec.tag (N.@"store") m)) -∗
  {{{ server_state kI kR ss n t }}}
    Server.handle_store N c (repr ss) m @ E
  {{{ n' t' v, RET v; server_state kI kR ss n' t' }}}.
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
iPoseProof (store_predE with "state ctx p_m") as "(state & #p_t' & #frag)".
wp_bind (Server.upd_val _ _ _).
iApply (wp_server_upd_val with "[$]").
iIntros "!> state". wp_pures.
wp_bind (Server.get_key _).
iApply (wp_server_get_key with "[$]") => //.
iIntros "!> state". wp_tsenc. rewrite /=.
iApply wp_send => //.
  iModIntro. iApply ack_storeI => //.
  iPoseProof (pterm_sterm with "p_m") as "s_m".
  rewrite sterm_TEnc. by iDestruct "s_m" as "[??]".
iApply "post". by eauto.
Qed.

End Verif.
