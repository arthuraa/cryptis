From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta cryptis primitives tactics.
From cryptis Require Import role dh_auth.
From cryptis.store Require Import impl shared.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : conn_state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_connection_connect N E c kI kR dq n T :
  ↑cryptisN ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  dh_auth_ctx (N.@"auth") -∗
  public (TKey Dec kI) -∗
  public (TKey Dec kR) -∗
  {{{ ●H{dq|n} T }}}
    Connection.connect N c (TKey Enc kI) (TKey Dec kI) (TKey Dec kR)
    @ E
  {{{ cs, RET (repr cs);
    ●H{dq|n} T ∗
    is_conn_state cs 0 ∗
    ⌜si_init cs = kI⌝ ∗
    ⌜si_resp cs = kR⌝ ∗
    ⌜si_time cs = n⌝ ∗
    ⌜si_hon cs = T⌝ ∗
    ⌜cs_role cs = Init⌝ ∗
    gmeta_token (cs_name cs) (⊤ ∖ ↑nroot.@"dh_auth") }}}.
Proof.
iIntros "% #? #? #? #? #? % !> hon post".
wp_lam. wp_pures.
iCombine "hon post" as "I". iRevert "I".
iApply wp_do_until. iIntros "!> [hon post]".
wp_pures. wp_bind (initiator _ _ _ _ _).
iApply (wp_initiator with "[//] [//] [//] [] [] [hon]") => //.
iIntros "!> %res (hon & resP)".
case: res=> [kS|] /=; wp_pures; last by iLeft; iFrame; eauto.
wp_alloc ts as "ts". set  si := SessInfo _ _ _ _ _. wp_pures.
iDestruct "resP" as "(%γ & #m_kS & #sess & token & #p_kS)".
iRight. iModIntro. iExists _.  iSplit => //.
iApply ("post" $! (ConnState si ts γ Init)). iFrame => /=.
eauto.
Qed.

Lemma wp_connection_listen N E c kR dq n T :
  ↑cryptisN ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  dh_auth_ctx (N.@"auth") -∗
  public (TKey Dec kR) -∗
  {{{ ●H{dq|n} T }}}
    Connection.listen N c (TKey Enc kR) (TKey Dec kR)
    @ E
  {{{ cs, RET (TKey Dec (si_init cs), repr cs)%V;
    ●H{dq|n} T ∗
    is_conn_state cs 0 ∗
    ⌜si_resp cs = kR⌝ ∗
    ⌜si_time cs = n⌝ ∗
    ⌜si_hon cs = T⌝ ∗
    ⌜cs_role cs = Resp⌝ ∗
    gmeta_token (cs_name cs) (⊤ ∖ ↑nroot.@"dh_auth") }}}.
Proof.
iIntros "% #? #? #? #? % !> hon post".
wp_lam. wp_pures.
iCombine "hon post" as "I". iRevert "I".
iApply wp_do_until. iIntros "!> [hon post]".
wp_pures. wp_bind (responder _ _ _ _).
iApply (wp_responder with "[//] [//] [] [] [hon]") => //.
iIntros "!> %res (hon & resP)".
case: res=> [[vkI kS]|] /=; wp_pures; last by iLeft; iFrame; eauto.
wp_alloc ts as "ts".
iDestruct "resP" as "(%kI & %γ & -> & #p_vkI & #m_kS & #sess & token & #p_kS)".
set  si := SessInfo _ _ _ _ _. wp_pures.
iRight. iModIntro. iExists _.  iSplit => //.
iApply ("post" $! (ConnState si ts γ Resp)). iFrame => /=.
eauto.
Qed.

Lemma wp_connection_timestamp E cs (n : nat) :
  {{{ is_conn_state cs n }}}
    Connection.timestamp (repr cs) @ E
  {{{ RET #n; is_conn_state cs n }}}.
Proof.
rewrite /Connection.timestamp.
iIntros "%Φ (Hn & #sess & #? & #key) post".
wp_pures. wp_load. iApply "post". iModIntro. iFrame. by eauto.
Qed.

Lemma wp_connection_tick E cs (n : nat) :
  {{{ is_conn_state cs n }}}
    Connection.tick (repr cs) @ E
  {{{ RET #(); is_conn_state cs (S n) }}}.
Proof.
iIntros "%Ψ (Hn & #seas & #? & #key) post".
rewrite /Connection.tick; wp_pures; wp_load; wp_store.
iApply "post".
rewrite (_ : (n + 1)%Z = (S n)%nat :> Z); last by lia.
iFrame; eauto.
Qed.

Lemma wp_connection_session_key E cs n :
  {{{ is_conn_state cs n }}}
    Connection.session_key (repr cs) @ E
  {{{ RET (repr (Spec.mkskey (si_key cs)));
      is_conn_state cs n ∗
      session (cs_name cs) cs (cs_role cs) ∗
      minted (si_key cs) ∗
      □ (∀ kt, public (TKey kt (si_key cs)) ↔ ▷ session_fail cs) }}}.
Proof.
rewrite /Connection.session_key.
iIntros "%Φ (? & #? & #? & #?) post". wp_pures. iApply "post".
iModIntro. iFrame. iSplit => //; eauto.
Qed.

Lemma wp_connection_send N E c cs n m φ :
  ↑cryptisN ⊆ E →
  channel c -∗
  enc_pred N φ -∗
  public m -∗
  □ φ (si_key cs) m -∗
  {{{ is_conn_state cs n }}}
    Connection.send N c (repr cs) m @ E
  {{{ RET #(); is_conn_state cs n }}}.
Proof.
iIntros "%sub #chan #pred #public_m #inv !> %Φ conn post".
wp_lam. wp_pures.
wp_bind (Connection.session_key _).
iApply (wp_connection_session_key with "conn").
iIntros "!> (conn & #sess & #minted_k & #sec)". wp_pures.
wp_bind (tsenc _ _ _). iApply wp_tsenc. wp_pures.
iApply wp_send => //.
{ iApply public_TEncIS => //.
  - by rewrite minted_TKey.
  - by iApply public_minted.
  - by iIntros "!> !> _". }
by iApply "post".
Qed.

Lemma wp_connection_select_body φ v (handlers : list val) (Φ : val → iProp) E :
  ([∗ list] handler ∈ handlers,
    (φ -∗ WP (handler : val) v @ E {{ v',
           ⌜v' = NONEV⌝ ∗ φ ∨
           ∃ r, ⌜v' = SOMEV r⌝ ∗ Φ r }}))%I -∗
  φ -∗ WP Connection.select_body v (repr handlers) @ E {{ v',
      ⌜v' = NONEV⌝ ∗ φ ∨
      ∃ r, ⌜v' = SOMEV r⌝ ∗ Φ r }}.
Proof.
rewrite /= repr_list_unseal.
iIntros "wp_handlers inv".
iLöb as "IH" forall (handlers).
wp_rec; case: handlers=> [|handler handlers]; wp_pures; first by eauto.
rewrite /=. iDestruct "wp_handlers" as "[wp_handler wp_handlers]".
iSpecialize ("wp_handler" with "inv").
iSpecialize ("IH" with "wp_handlers").
wp_bind (handler _); iApply (wp_wand with "wp_handler").
iIntros "%v' [[-> inv] | (%r & -> & post)]"; wp_pures.
- by iApply "IH".
- iRight. iExists r. by iFrame.
Qed.

Lemma wp_connection_select_body' Φ φ v (handlers : list val) Ψ E :
  ([∗ list] handler ∈ handlers,
     (φ -∗ WP (handler : val) v @ E {{ v,
       ⌜v = NONEV⌝ ∗ φ ∨
       ∃ r, ⌜v = SOMEV r⌝ ∗ Φ r }}))%I -∗
  (φ -∗ Ψ NONEV) -∗
  (∀ r, Φ r -∗ Ψ (SOMEV r)) -∗
  φ -∗
  WP Connection.select_body v (repr handlers) @ E {{ Ψ }}.
Proof.
iIntros "wp post1 post2 inv".
iApply (wp_wand with "[wp inv] [post1 post2]").
- by iApply (wp_connection_select_body φ v handlers Φ with "[wp] inv").
- iIntros "%res [[-> ?]|(%r & -> & ?)]".
  + by iApply "post1".
  + by iApply "post2".
Qed.

Lemma wp_connection_make_handler φ Φ k (handler : namespace * expr) E :
  WP handler.2 @ E {{ f,
    □ ∀ m : term,
        public (TEnc k (Spec.tag handler.1 m)) -∗
        φ -∗
        WP (f : val) m @ E {{ v',
            ⌜v' = NONEV⌝ ∗ φ ∨
            ∃ r, ⌜v' = SOMEV r⌝ ∗ Φ r }}
  }} -∗
  WP Connection.make_handler handler @ E {{ f,
    □ ∀ m : term,
        public (TEnc k m) -∗
        φ -∗
        WP (f : val) m @ E {{ v',
          ⌜v' = NONEV⌝ ∗ φ ∨
          ∃ r, ⌜v' = SOMEV r⌝ ∗ Φ r }}
  }}.
Proof.
case: handler => N handler /=; iIntros "wp".
rewrite /Connection.make_handler. wp_pures.
wp_bind handler. iApply (wp_wand with "wp").
iIntros "%handler' #Hhandler'". wp_pures.
iIntros "!> !> %m #p_m inv". wp_pures.
wp_untag m; wp_pures.
- by iApply "Hhandler'".
- by iLeft; iFrame.
Qed.

Lemma wp_connection_make_handlers φ Φ k (handlers : list (namespace * expr)) E :
  ([∗ list] handler ∈ handlers,
      WP (handler.2 : expr) @ E {{ f, □ ∀ m : term,
        public (TEnc k (Spec.tag handler.1 m)) -∗
        φ -∗
        WP (f : val) m @ E {{ v,
            ⌜v = NONEV⌝ ∗ φ ∨
            ∃ r, ⌜v = SOMEV r⌝ ∗ Φ r }} }})%I -∗
  WP Connection.make_handlers handlers @ E {{ v',
    ∃ handlers' : list val, ⌜v' = repr handlers'⌝ ∗
      [∗ list] handler' ∈ handlers', □ ∀ m : term,
        public (TEnc k m) -∗
        φ -∗
        WP (handler' : val) m @ E {{ v,
          ⌜v = NONEV⌝ ∗ φ ∨
          ∃ r, ⌜v = SOMEV r⌝ ∗ Φ r }}
  }}.
Proof.
rewrite /= repr_list_unseal.
elim: handlers=> [|[N handler] handlers IH] //=.
  iIntros "_". wp_pures. iModIntro. iExists []. by rewrite /=.
iIntros "[wp_handler wp_handlers]".
wp_bind (Connection.make_handlers _).
iPoseProof (IH with "wp_handlers") as "wp_handlers". clear IH.
iApply (wp_wand with "wp_handlers [wp_handler]").
iIntros "%v' (%handlers' & -> & #Hhandlers')".
wp_bind (Connection.make_handler _).
iApply (wp_wand with "[wp_handler] [Hhandlers']").
{ iApply (wp_connection_make_handler _ _ _ (N, handler) with "wp_handler"). }
iIntros "%f #wp_f". wp_lam; wp_pures.
iExists (f :: handlers'). iSplitR => //=.
iModIntro. iSplit => //.
Qed.

Definition handler_correct φ Φ cs handler n E : iProp :=
  WP handler.2 @ E {{ f,
    ∃ Ψ, enc_pred handler.1 Ψ ∗
    □ ∀ m, minted m -∗
           □ ▷ (session_fail cs ∗ public m ∨ Ψ (si_key cs) m) -∗
           is_conn_state cs n -∗
           φ -∗
           WP (f : val) m @ E {{ v,
             ⌜v = NONEV⌝ ∗ is_conn_state cs n ∗ φ ∨
             ∃ r, ⌜v = SOMEV r⌝ ∗ Φ r }}
  }}%I.

Lemma wp_connection_select φ Φ (c : val) cs n (handlers : list (namespace * expr)) E :
  ↑cryptisN ⊆ E →
  channel c -∗
  ([∗ list] handler ∈ handlers, handler_correct φ Φ cs handler n E) -∗
  is_conn_state cs n -∗
  φ -∗
  WP Connection.select c (repr cs) handlers @ E {{ Φ }}.
Proof.
rewrite Connection.select_eq /Connection.select_def.
iIntros "%sub #chan_c wps conn inv".
wp_bind (Connection.make_handlers _).
iApply (wp_wand with "[wps]").
{ iApply (wp_connection_make_handlers
            (is_conn_state cs n ∗ φ) Φ (si_key cs)
           with "[wps]").
  iApply (big_sepL_impl with "wps").
  iIntros "!> % %handler _ wp".
  iApply (wp_wand with "wp").
  iIntros "%f #wp !> %m #p_m [conn inv]".
  iDestruct "wp" as "(%Ψ & #enc & #wp)".
  iAssert (minted m) as "#m_m".
  { rewrite public_minted minted_TEnc minted_tag.
    by iDestruct "p_m" as "[??]". }
  iPoseProof (public_TEncE with "p_m enc") as "{p_m} p_m".
  iAssert (□ ∀ kt, public (TKey kt (si_key cs)) ↔ ▷ session_fail cs)%I as "#p_kS".
  { by iDestruct "conn" as "(_ & _ & _ & #?)". }
  iApply ("wp" with "m_m [] conn inv").
  iDestruct "p_m" as "[[fail p_m]|(#inv & ?)]".
  - iSpecialize ("p_kS" with "fail"). by eauto.
  - by eauto. }
iIntros "% (%handlers' & -> & #Hhandlers')".
wp_pures.
wp_bind (Connection.session_key _).
iApply (wp_connection_session_key with "conn").
iIntros "!> (conn & #sess & #m_kS & #p_kS)".
wp_bind (untuple _).
iApply wp_untuple => /=.
wp_pures. iCombine "conn inv" as "I". iRevert "I". iApply wp_do_until.
iIntros "!> I". wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m #p_m". wp_pures.
wp_dec m; wp_pures; last by iLeft; iFrame.
iApply (wp_connection_select_body' Φ with "[] [] [] I").
- iApply (big_sepL_impl with "Hhandlers'").
  iIntros "!> %k %handler _ #Hhandler inv" => //.
  by iApply ("Hhandler" with "p_m inv").
- iIntros "[??]". iLeft. by iFrame.
- iIntros "%r Hr". iRight. iExists r. by eauto.
Qed.

Lemma wp_connection_recv N E c cs n (f : val) φ Φ Ψ :
  ↑cryptisN ⊆ E →
  channel c -∗
  enc_pred N Φ -∗
  □ (∀ m,
      is_conn_state cs n -∗
      φ -∗
      minted m -∗
      □ (session_fail cs ∗ public m ∨ Φ (si_key cs) m) -∗
      WP f m @ E {{ v, ⌜v = NONEV⌝ ∗ is_conn_state cs n ∗ φ ∨
                       ∃ v', ⌜v = SOMEV v'⌝ ∗ Ψ v' }}) -∗
  is_conn_state cs n -∗ φ -∗ WP Connection.recv N c (repr cs) f @ E {{ Ψ }}.
Proof.
iIntros "%sub #chan #pred #post conn inv".
wp_lam; wp_pures.
wp_bind (Connection.session_key _).
iApply (wp_connection_session_key with "conn").
iIntros "!> (conn & #sess & #minted_kS & #p_kS)".
wp_pures. iCombine "conn inv" as "I". iRevert "I".
iApply wp_do_until.
iIntros "!> (conn & inv)".
wp_pure _ credit:"c".
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m #p_m". wp_pures. wp_tsdec m; wp_pures; last by iLeft; iFrame.
iAssert (▷ □ (session_fail cs ∗ public m ∨ Φ (si_key cs) m))%I
  as "p_m'".
{ iDestruct (public_TEncE with "[//] [//]") as "{p_m} [[fail p_m]|p_m]".
  - iPoseProof ("p_kS" with "fail") as "{fail} fail".
    iModIntro. by eauto.
  - iDestruct "p_m" as "[p_m ?]".
    iModIntro. iModIntro. eauto. }
iMod (lc_fupd_elim_later with "c p_m'") as "{p_m'} #p_m'".
iApply ("post" with "conn inv").
{ rewrite public_minted minted_TEnc minted_tag.
  by iDestruct "p_m" as "[??]". }
by eauto.
Qed.

Lemma wp_connection_close E (c : val) cs n :
  {{{ is_conn_state cs n }}}
    Connection.close c (repr cs) @ E
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ (conn & _) post".
wp_lam; wp_pures.
wp_free.
by iApply "post".
Qed.

End Verif.
