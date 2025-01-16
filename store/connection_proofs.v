From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta cryptis primitives tactics.
From cryptis Require Import role iso_dh.
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

Lemma wp_connection_connect N c kI kR :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx (N.@"auth") -∗
  sign_key kI -∗
  public (TKey Open kR) -∗
  {{{ True }}}
    Connection.connect N c kI (TKey Open kR)
  {{{ cs, RET (repr cs);
    wf_sess_info cs ∗
    cs_ts cs ↦ #0 ∗
    ⌜si_init cs = kI⌝ ∗
    ⌜si_resp cs = kR⌝ ∗
    ⌜cs_role cs = Init⌝ ∗
    term_token (si_init_share cs) ⊤ }}}.
Proof.
iIntros "#? #? #? #? #? % !> _ post".
wp_lam. wp_pures. iRevert "post".
iApply wp_do_until. iIntros "!> post".
wp_pures.
wp_apply (wp_initiator with "[//] [//] [//] [] []") => //.
iIntros "%res resP".
case: res=> [kS|] /=; wp_pures; last by iLeft; iFrame; eauto.
iDestruct "resP"
  as "(%si & % & %e_kR & <- & #m_kS & #comp & token)".
case: e_kR => <-.
wp_alloc ts as "ts". wp_pures.
iRight. iModIntro. iExists _.  iSplit => //.
iApply ("post" $! (ConnState si ts Init)). iFrame => /=.
iPoseProof (senc_key_si_key with "[//] m_kS") as "#?".
do !iSplit => //.
Qed.

Lemma wp_connection_listen N c kR :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx (N.@"auth") -∗
  sign_key kR -∗
  {{{ True }}}
    Connection.listen N c kR
  {{{ cs, RET (TKey Open (si_init cs), repr cs)%V;
    wf_sess_info cs ∗
    cs_ts cs ↦ #0 ∗
    ⌜si_resp cs = kR⌝ ∗
    ⌜cs_role cs = Resp⌝ ∗
    term_token (si_resp_share cs) ⊤ }}}.
Proof.
iIntros "#? #? #? #? % !> _ post".
wp_lam. wp_pures. iRevert "post".
iApply wp_do_until. iIntros "!> post".
wp_pures.
wp_apply (wp_responder with "[//] [//] [] []") => //.
iIntros "%res resP".
case: res=> [[vkI kS]|] /=; wp_pures; last by iLeft; iFrame; eauto.
wp_alloc ts as "ts".
iDestruct "resP"
  as "(%si & -> & % & <- & #p_vkI & #m_kS & #comp & token)".
iPoseProof (senc_key_si_key with "[//] m_kS") as "?".
wp_pures.
iRight. iModIntro. iExists _.  iSplit => //.
iApply ("post" $! (ConnState si ts Resp)). iFrame => /=.
by do !iSplit => //; eauto.
Qed.

Lemma wp_connection_timestamp cs (n : nat) :
  {{{ cs_ts cs ↦ #n }}}
    Connection.timestamp (repr cs)
  {{{ RET #n; cs_ts cs ↦ #n }}}.
Proof.
rewrite /Connection.timestamp.
iIntros "%Φ Hn post".
wp_pures. wp_load. iApply "post". iModIntro. by iFrame.
Qed.

Lemma wp_connection_tick cs (n : nat) :
  {{{ cs_ts cs ↦ #n }}}
    Connection.tick (repr cs)
  {{{ RET #(); cs_ts cs ↦ #(S n) }}}.
Proof.
iIntros "%Ψ Hn post".
rewrite /Connection.tick; wp_pures; wp_load; wp_store.
iApply "post".
rewrite (_ : (n + 1)%Z = (S n)%nat :> Z); last by lia.
iFrame; eauto.
Qed.

Lemma wp_connection_session_key cs :
  {{{ True }}}
    Connection.session_key (repr cs)
  {{{ RET (repr (si_key cs)); True }}}.
Proof.
rewrite /Connection.session_key.
iIntros "%Φ _ post". wp_pures. iApply "post".
iModIntro. by iFrame.
Qed.

Lemma wp_connection_send N c cs m φ rl :
  channel c -∗
  seal_pred N (session_msg_pred φ rl) -∗
  public m -∗
  □ (session_failed_for_or cs (swap_role rl) True →
     session_failed_or cs (φ cs m)) -∗
  wf_conn_state cs -∗
  {{{ True }}}
    Connection.send N c (repr cs) m
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #pred #public_m #inv #conn !> %Φ _ post".
iDestruct "conn" as "((? & #? & ?) & _)".
wp_lam. wp_pures.
wp_apply (wp_connection_session_key _) => //.
iIntros "_". wp_pures.
wp_apply wp_senc. wp_pures.
iApply wp_send => //.
{ iApply public_TSealIS => //.
  - by rewrite minted_TKey.
  - iModIntro. iExists cs. do !iSplit => //.
  - by iApply public_minted.
  - by iIntros "!> !> _". }
by iApply "post".
Qed.

Lemma wp_connection_select_body φ v (handlers : list val) (Φ : val → iProp) :
  ([∗ list] handler ∈ handlers,
    (φ -∗ WP (handler : val) v {{ v',
           ⌜v' = NONEV⌝ ∗ φ ∨
           ∃ r, ⌜v' = SOMEV r⌝ ∗ Φ r }}))%I -∗
  φ -∗ WP Connection.select_body v (repr handlers) {{ v',
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

Lemma wp_connection_select_body' Φ φ v (handlers : list val) Ψ :
  ([∗ list] handler ∈ handlers,
     (φ -∗ WP (handler : val) v {{ v,
       ⌜v = NONEV⌝ ∗ φ ∨
       ∃ r, ⌜v = SOMEV r⌝ ∗ Φ r }}))%I -∗
  (φ -∗ Ψ NONEV) -∗
  (∀ r, Φ r -∗ Ψ (SOMEV r)) -∗
  φ -∗
  WP Connection.select_body v (repr handlers) {{ Ψ }}.
Proof.
iIntros "wp post1 post2 inv".
iApply (wp_wand with "[wp inv] [post1 post2]").
- by iApply (wp_connection_select_body φ v handlers Φ with "[wp] inv").
- iIntros "%res [[-> ?]|(%r & -> & ?)]".
  + by iApply "post1".
  + by iApply "post2".
Qed.

Lemma wp_connection_make_handler φ Φ k (handler : namespace * expr) :
  WP handler.2 {{ f,
    □ ∀ m : term,
        public (TSeal (TKey Seal k) (Spec.tag handler.1 m)) -∗
        φ -∗
        WP (f : val) m {{ v',
            ⌜v' = NONEV⌝ ∗ φ ∨
            ∃ r, ⌜v' = SOMEV r⌝ ∗ Φ r }}
  }} -∗
  WP Connection.make_handler handler {{ f,
    □ ∀ m : term,
        public (TSeal (TKey Seal k) m) -∗
        φ -∗
        WP (f : val) m {{ v',
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

Lemma wp_connection_make_handlers φ Φ k (handlers : list (namespace * expr)) :
  ([∗ list] handler ∈ handlers,
      WP (handler.2 : expr) {{ f, □ ∀ m : term,
        public (TSeal (TKey Seal k) (Spec.tag handler.1 m)) -∗
        φ -∗
        WP (f : val) m {{ v,
            ⌜v = NONEV⌝ ∗ φ ∨
            ∃ r, ⌜v = SOMEV r⌝ ∗ Φ r }} }})%I -∗
  WP Connection.make_handlers handlers {{ v',
    ∃ handlers' : list val, ⌜v' = repr handlers'⌝ ∗
      [∗ list] handler' ∈ handlers', □ ∀ m : term,
        public (TSeal (TKey Seal k) m) -∗
        φ -∗
        WP (handler' : val) m {{ v,
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

Definition handler_correct φ Φ cs handler n : iProp :=
  WP handler.2 {{ f,
    ∃ Ψ, seal_pred handler.1 (session_msg_pred Ψ (swap_role (cs_role cs))) ∗
    □ ∀ m, ▷ public m -∗
           □ ▷ session_failed_or cs (Ψ cs m) -∗
           wf_conn_state cs -∗
           release_token (cs_share cs) -∗
           cs_ts cs ↦ #n -∗
           φ -∗
           WP (f : val) m {{ v,
             ⌜v = NONEV⌝ ∗ cs_ts cs ↦ #n ∗ release_token (cs_share cs) ∗ φ ∨
             ∃ r, ⌜v = SOMEV r⌝ ∗ Φ r }}
  }}%I.

Lemma wp_connection_select φ Φ (c : val) cs n (handlers : list (namespace * expr)) :
  channel c -∗
  ([∗ list] handler ∈ handlers, handler_correct φ Φ cs handler n) -∗
  wf_conn_state cs -∗
  release_token (cs_share cs) -∗
  cs_ts cs ↦ #n -∗
  φ -∗
  WP Connection.select c (repr cs) handlers {{ Φ }}.
Proof.
rewrite Connection.select_eq /Connection.select_def.
iIntros "#chan_c wps #conn rel ts inv".
wp_bind (Connection.make_handlers _).
iApply (wp_wand with "[wps]").
{ iApply (wp_connection_make_handlers
            (cs_ts cs ↦ #n ∗ release_token (cs_share cs) ∗ φ) Φ (si_key cs)
           with "[wps]").
  iApply (big_sepL_impl with "wps").
  iIntros "!> % %handler _ wp".
  iApply (wp_wand with "wp").
  iIntros "%f #wp !> %m #p_m (ts & rel & inv)".
  iDestruct "wp" as "(%Ψ & #seal & #wp)".
  iAssert (minted m) as "#m_m".
  { rewrite public_minted minted_TSeal minted_tag.
    by iDestruct "p_m" as "[??]". }
  iAssert (□ ▷ (public m ∗ session_failed_or cs (Ψ cs m)))%I
    as "{p_m} #[p_m inv_m]".
  { iDestruct "conn" as "[(#? & #s_key & #sess) sess']".
    iDestruct (public_TSealE with "[//] [//]") as "{p_m} [[p_key p_m]|p_m]".
    - iSplitR => //.
      iSpecialize ("s_key" with "p_key").
      rewrite -bi.later_intuitionistically.
      iDestruct "s_key" as "{p_key} >p_key".
      iDestruct "sess'" as "(%failed & #[meta failed] & _)".
      case: failed; last first.
      { iDestruct ("failed" with "p_key") as "#contra".
        iModIntro.
        by iDestruct (release_token_released_session with "rel contra")
          as "[]". }
      iIntros "!> !>". iLeft.
      by case: (cs_role cs); [iLeft|iRight]; iSplit.
    - iDestruct "p_m" as "[#p_m _]".
      iModIntro. iModIntro. 
      iDestruct "p_m" as "(%si & %e_kS & #sess'' & inv_m)".
      iSplit => //. rewrite swap_roleK (session_agree e_kS).
      by iApply "inv_m". }
  iApply ("wp" with "p_m [//] conn rel ts inv"). }
iIntros "% (%handlers' & -> & #Hhandlers')".
wp_pures. wp_apply wp_connection_session_key => //. iIntros "_".
wp_pures. iCombine "ts rel inv" as "I". iRevert "I". iApply wp_do_until.
iIntros "!> I". wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m #p_m". wp_pures.
wp_apply wp_key.
wp_bind (open _ _). iApply wp_open.
case: Spec.openP; last by wp_pures; iLeft; iFrame.
move=> _ {}m [<-] ->. wp_pures.
iApply (wp_connection_select_body' Φ with "[] [] [] I").
- iApply (big_sepL_impl with "Hhandlers'").
  iIntros "!> %k %handler _ #Hhandler inv" => //.
  by iApply ("Hhandler" with "p_m inv").
- iIntros "(?&?&?)". iLeft. by iFrame.
- iIntros "%r Hr". iRight. iExists r. by eauto.
Qed.

Lemma wp_connection_recv N c cs n (f : val) φ Φ rl Ψ :
  channel c -∗
  seal_pred N (session_msg_pred Φ rl) -∗
  ⌜cs_role cs = swap_role rl⌝ -∗
  wf_conn_state cs -∗
  □ (∀ m,
      cs_ts cs ↦ #n -∗
      release_token (cs_share cs) -∗
      φ -∗
      public m -∗
      □ session_failed_or cs (Φ cs m) -∗
      WP f m {{ v, ⌜v = NONEV⌝ ∗
                   cs_ts cs ↦ #n ∗ release_token (cs_share cs) ∗ φ ∨
                   ∃ v', ⌜v = SOMEV v'⌝ ∗ Ψ v' }}) -∗
  cs_ts cs ↦ #n -∗ release_token (cs_share cs) -∗ φ -∗
  WP Connection.recv N c (repr cs) f {{ Ψ }}.
Proof.
iIntros "#chan #pred %e_rl #conn #post ts rel inv".
move/(f_equal swap_role): e_rl; rewrite swap_roleK => <- {rl}.
iPoseProof "conn" as "((#minted_kS & #s_key & #sess) & #sess')".
wp_lam; wp_pures.
wp_apply wp_connection_session_key => //. iIntros "_".
wp_pures. iCombine "ts rel inv" as "I". iRevert "I".
iApply wp_do_until.
iIntros "!> (ts & rel & inv)".
wp_pure _ credit:"c".
wp_pures. wp_apply wp_recv => //.
iIntros "%m #p_m". wp_pures. wp_sdec m; wp_pures; last by iLeft; iFrame.
iAssert (▷ □ (public m ∗ session_failed_or cs (Φ cs m)))%I
  as "{p_m} #p_m".
{ iDestruct (public_TSealE with "[//] [//]") as "{p_m} [[p_key p_m]|p_m]".
  - iSplitR => //.
    iSpecialize ("s_key" with "p_key").
    iDestruct "sess'" as "(%failed & #[meta failed] & _)".
    iDestruct "s_key" as "{p_key} >p_key".
    case: failed; last first.
    { iDestruct ("failed" with "p_key") as "#contra".
      iModIntro.
      by iDestruct (release_token_released_session with "rel contra")
        as "[]". }
    iIntros "!> !>". iLeft.
    by case: (cs_role cs); [iLeft|iRight]; iSplit.
  - iDestruct "p_m" as "[#p_m _]".
    iModIntro. iModIntro.
    iDestruct "p_m" as "(%si & %e_kS & p_m & inv_m)".
    iSplit => //.
    rewrite swap_roleK (session_agree e_kS). by iApply "inv_m". }
iMod (lc_fupd_elim_later with "c p_m") as "{p_m} [#p_m #inv_m]".
by iApply ("post" with "ts rel inv").
Qed.

Lemma wp_connection_close (c : val) cs n :
  {{{ cs_ts cs ↦ #n }}}
    Connection.close c (repr cs)
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ ts post".
wp_lam; wp_pures.
wp_free.
by iApply "post".
Qed.

End Verif.
