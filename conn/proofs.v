From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics.
From cryptis Require Import role iso_dh.
From cryptis.conn Require Import impl props.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Proofs.

Import Props Impl.

Section Proofs.

Context `{!cryptisGS Σ, !heapGS Σ, !connGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

(* MOVE *)
Lemma connected_public_key' kI kR cs n n0 kt :
  connected' kI kR cs false n n0 -∗
  public (TKey kt (si_key cs)) -∗
  ◇ compromised_session (cs_role cs) cs.
Proof.
iIntros "conn #p_k".
iPoseProof "conn" as "(_ & _ & #sess & rel & _)".
iDestruct "sess" as "(#? & #s_key & #sess)".
iPoseProof (senc_key_compromised_keyI with "s_key p_k") as "{p_k} p_k".
iPoseProof (senc_key_compromised_keyE with "s_key p_k") as "{p_k} >p_k".
by iApply session_compromised.
Qed.
(* /MOVE *)

Lemma public_sencE N rl si m φ :
  public (TSeal (TKey Seal (si_key si)) (Spec.tag N m)) -∗
  seal_pred N φ -∗
  wf_sess_info rl si -∗
  release_token (si_share_of rl si) -∗
  ▷ □ (compromised_session rl si ∗ public m ∨ φ (si_key si) m).
Proof.
iIntros "#p_m #Nφ #(_ & s_key & sess) rel".
iDestruct (public_TSealE with "[//] [//]") as "{p_m} [[p_key p_m]|p_m]".
- iPoseProof ("s_key" with "p_key") as "{p_key} >p_key".
  iPoseProof (session_compromised with "[//] p_key rel") as "#>?".
  iModIntro. iLeft. iModIntro. by do 2!iSplit => //.
- iDestruct "p_m" as "[#p_m _]". by eauto.
Qed.

Lemma or_sep1 (P Q R : iProp) : P ∨ Q -∗ P ∨ R -∗ P ∨ Q ∗ R.
Proof.
iIntros "[?|?] [?|?]"; eauto. iRight. by iFrame.
Qed.

Lemma or_sep2 (P Q R : iProp) :
  Persistent P →
  P ∨ Q ∗ R ⊢ (P ∨ Q) ∗ (P ∨ R).
Proof.
iIntros "% [#?|[Q R]]"; first by iSplitR; eauto.
by iSplitL "Q"; eauto.
Qed.

Lemma wp_connect P N c kI kR n :
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  sign_key kI -∗
  public (TKey Open kR) -∗
  {{{ client_disconnected N kI kR n ∗ (failure kI kR ∨ P) }}}
    Impl.connect N c kI (TKey Open kR)
  {{{ cs, RET (repr cs);
      connected kI kR cs n ∗
      (compromised_session Init cs ∨ P) ∗
      client_token N kI kR cs }}}.
Proof.
iIntros "#? #? #? #? #? % !> ((#server_clock & dis) & HP) post".
iPoseProof (or_sep1 with "dis HP") as "H".
rewrite bi.or_alt. iDestruct "H" as "(%failed & dis)".
wp_lam. wp_pure _ credit:"c1". wp_pure _ credit:"c2".
wp_pures. wp_bind (do_until _).
iAssert (if failed then failure kI kR else True)%I as "#?".
{ by case: failed. }
iCombine "dis post c1 c2" as "post". iApply (wp_frame_wand with "post").
wp_apply wp_do_until'. iModIntro.
wp_pures.
wp_apply (wp_initiator _ failed with "[//] [//] [] [] []") => //.
- by iApply ctx_iso_dh_ctx.
- case: failed => //. by eauto.
iIntros "%res resP".
case: res=> [kS|] /=; last by eauto.
iDestruct "resP"
  as "(%si & <- & %e_kR & <- & #m_kS & #sess & #comp & rel & token)".
case: e_kR => <- {kR}.
iRight. iExists _. iSplit => //.
iIntros "(dis & post & c1 & c2)".
wp_pures.
wp_alloc ts as "ts". wp_pures.
pose cs := State si ts Init.
iMod (term_meta_set' (N := isoN.@"beginning") n with "token")
  as "[#beginning token]"; first by solve_ndisj.
iPoseProof (term_token_drop (↑isoN.@"end") with "token")
  as "end"; first by solve_ndisj.
iAssert (|={⊤}=> compromised_session Init si ∨ conn_ready N si n ∗ P)%I
  with "[dis]" as ">conn_ready".
{ case: failed.
  - iModIntro. iLeft. by iApply "comp".
  - iDestruct "dis" as "[dis P]".
    iAssert (|={⊤}=> conn_ready N si n)%I with "[dis]" as ">#?".
    { iApply (escrowI with "dis"). iApply term_token_switch. }
    by eauto. }
rewrite or_sep2. iDestruct "conn_ready" as "[#conn_ready P]".
wp_apply wp_senc. wp_pures. wp_apply wp_send => //.
{ iDestruct "conn_ready" as "[(_ & p_k & _)|conn_ready]".
  - iApply public_TSealIP.
    + by iApply public_TKey; eauto.
    + by rewrite public_tag public_TInt.
  - iApply public_TSealIS.
    + by rewrite minted_TKey.
    + by iApply ctx_init.
    + iModIntro. iExists si. rewrite public_TInt.
      do 2!iSplit => //. iExists n. by eauto.
    + by rewrite minted_TInt.
    + rewrite public_TInt. by eauto. }
wp_pures. iApply ("post" $! cs).
iSplitR "end P".
- iExists 0, n. iFrame. iModIntro. do 5!iSplit => //.
  + iSplit => //. iSplit => //. by iApply senc_key_si_key.
  + by eauto.
- iFrame. by eauto.
Qed.

Lemma wp_listen N c :
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  {{{ True }}}
    listen c
  {{{ ga skA, RET (ga, TKey Open skA)%V;
      public ga ∗ public (TKey Open skA) }}}.
Proof.
iIntros "#? #? #? % !> _ post".
wp_lam. iApply (wp_frame_wand with "post"). wp_pures.
wp_apply wp_do_until'.
iModIntro. wp_pures.
wp_apply wp_responder_wait; eauto.
iIntros "%ga %vkA #(p_ga & #p_vkA)".
wp_pures. wp_apply wp_is_key.
case: Spec.is_keyP => [kt skA -> {vkA}|_]; wp_pures; last by eauto.
case: bool_decide_reflect => [e|_]; wp_pures; last by eauto.
case: kt => // in e *.
iModIntro. iRight. iExists _. iSplit => //.
iIntros "post". iApply "post". by eauto.
Qed.

Lemma wp_confirm P N c skA skB ga n :
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  {{{ public ga ∗ public (TKey Open skA) ∗ sign_key skB ∗
      server_disconnected N skA skB n ∗
      (failure skA skB ∨ P) }}}
    confirm N c skB (ga, TKey Open skA)%V
  {{{ cs, RET (repr cs);
      ⌜cs_role cs = Resp⌝ ∗
      ⌜si_init cs = skA⌝ ∗
      ⌜si_resp cs = skB⌝ ∗
      connected skA skB cs n ∗
      (compromised_session Resp cs ∨ P) ∗
      server_token N cs }}}.
Proof.
iIntros "#? #ctx #? !> %Φ (#p_ga & #p_vkA & #sign_skB & dis & P) post".
iPoseProof (or_sep1 with "dis P") as "dis".
rewrite bi.or_alt. iDestruct "dis" as "(%failed & dis)".
wp_lam. wp_pures.
iAssert (if failed then failure skA skB else True)%I
  as "#?".
{ by case: failed. }
wp_bind (do_until _).
iApply (wp_frame_wand with "post").
iApply (wp_frame_wand with "dis").
iApply wp_do_until'. iIntros "!>".
wp_pures.
iPoseProof (ctx_iso_dh_ctx with "[//]") as "#?".
iApply (wp_responder_accept _ failed).
{ do !iSplit => //. case: failed => //. by eauto. }
iIntros "!> %osi res". case: osi => [si|]; last by eauto.
iDestruct "res" as "(%e & <- & #m_k & #sess & #comp & rel & token)".
case: e => -> {skA}.
iRight. iExists _. iSplit => //.
iIntros "dis post".
wp_pures. wp_bind (do_until _).
iApply (wp_frame_wand with "post").
iApply (wp_frame_wand with "token").
iCombine "rel dis" as "I". iRevert "I".
iApply wp_do_until.
iIntros "!> [rel dis]".
wp_pures. wp_apply wp_recv => //. iIntros "%m #p_m". wp_pures.
wp_sdec m; last first.
{ iModIntro. iLeft. by iFrame. }
iModIntro. iRight. iExists _. iSplit => //. iIntros "token post".
wp_pures. wp_alloc ts as "ts". 
iPoseProof (ctx_init with "[//]") as "#?".
iPoseProof (senc_key_si_key with "ctx m_k") as "#?".
iPoseProof (public_sencE _ Resp with "p_m [//] [] rel") as "{p_m} #p_m".
{ do !iSplit => //. }
wp_pure _.
iMod (term_meta_set' (N:=isoN.@"beginning") n with "token")
  as "[#beginningB token]"; first by solve_ndisj.
rewrite (term_token_difference _ (↑isoN.@"begin")); last by solve_ndisj.
iDestruct "token" as "[begin token]".
iAssert (|={⊤}=>
  compromised_session Resp si ∨ P ∗
  term_meta (si_init_share si) (isoN.@"beginning") n ∗
  ∃ n0, clock N (si_init si) (si_resp si) n0 ∗
        clock N (si_init si) (si_resp si) n0)%I
  with "[dis begin]" as ">con".
{ iDestruct "p_m" as "#[[? _]|inv]"; first by eauto.
  iDestruct "inv" as "(%si' & %e & _ & inv)".
  rewrite -(session_agree e) {si' e}.
  iDestruct "inv" as "(%beginning & clock_ready & beginning & conn_ready)".
  case: failed.
  { iModIntro. iLeft. by iApply "comp". }
  iDestruct "dis" as "[dis P]".
  iDestruct "dis" as "[[-> never]|clockB]".
  { iMod (escrowE with "clock_ready never") as ">clockB"; eauto.
    iMod (escrowE with "conn_ready begin") as ">clockA"; eauto.
    iPoseProof (clock_agree with "clockA clockB") as "->".
    iModIntro. iRight. by iFrame. }
  iMod (escrowE with "conn_ready begin") as ">clockA"; eauto.
  iPoseProof (clock_agree with "clockA clockB") as "->".
  iModIntro. iRight. by iFrame. }
rewrite 2!or_sep2. iDestruct "con" as "(P & (#? & ?))".
wp_pures. iApply ("post" $! (State si ts Resp)).
iModIntro. iSplit => //=. iFrame. iSplit => //.
do !iSplit => //. iExists n. by do !iSplit => //.
Qed.

Lemma wp_timestamp kI kR cs b n n0 :
  {{{ connected' kI kR cs b n n0 }}}
    timestamp (repr cs)
  {{{ RET #n; connected' kI kR cs b n n0 }}}.
Proof.
rewrite /timestamp.
iIntros "%Φ Hn post".
iDestruct "Hn" as "(% & % & #? & ? & ? & #?)".
wp_pures. wp_load. iApply "post". iFrame.
iModIntro. by eauto 10.
Qed.

Lemma wp_tick kI kR cs n :
  {{{ connected kI kR cs n }}}
    tick (repr cs)
  {{{ RET #(); connected kI kR cs (S n) }}}.
Proof.
iIntros "%Ψ (%n' & %n0 & -> & #? & Hn) post".
iDestruct "Hn" as "(% & % & #? & ? & ? & #?)".
rewrite /tick; wp_pures; wp_load; wp_store.
iApply "post".
rewrite (_ : (n' + 1)%Z = (S n')%nat :> Z); last by lia.
iFrame; eauto 10.
Qed.

Lemma wp_session_key cs :
  {{{ True }}}
    session_key (repr cs)
  {{{ RET (repr (si_key cs)); True }}}.
Proof.
rewrite /session_key.
iIntros "%Φ _ post". wp_pures. iApply "post".
iModIntro. by iFrame.
Qed.

Lemma wp_write' kI kR cs b n1 n0 N c ts φ :
  channel c -∗
  seal_pred N (conn_pred φ) -∗
  ([∗ list] t ∈ ts, public t) -∗
  compromised_session (cs_role cs) cs ∨ □ φ kI kR cs (n1 + n0) ts -∗
  {{{ connected' kI kR cs b n1 n0 }}}
    write N c (repr cs) (repr ts)
  {{{ RET #(); connected' kI kR cs b n1 n0 }}}.
Proof.
iIntros "#chan #pred #p_ts #inv !> %Φ conn post".
iAssert (⌜kI = si_init cs⌝ ∗ ⌜kR = si_resp cs⌝)%I as "#[-> ->]".
{ by iDestruct "conn" as "(<- & <- & _)". }
wp_lam. wp_pures. wp_apply (wp_timestamp with "[$]").
iIntros "conn". wp_pures.
wp_apply wp_session_key => //. iIntros "_".
wp_pures. wp_apply wp_tint. wp_list. wp_term_of_list.
wp_pures. wp_apply wp_senc. wp_pures.
iAssert (wf_sess_info (cs_role cs) cs) as "#wf".
{ by iDestruct "conn" as "(? & ? & ? & ?)". }
iAssert (compromised_session (cs_role cs) cs ∨
           term_meta (si_init_share cs) (isoN.@"beginning") n0)%I
  as "#beginning".
{ by iDestruct "conn" as "(? & ? & ? & ? & ? & ?)". }
wp_apply (wp_send with "[//] [#]").
{ iDestruct "inv" as "[(_ & ? & _)|#inv]".
  { iModIntro. iApply public_TSealIP.
    + by iApply public_TKey; eauto.
    + rewrite public_tag public_of_list /= public_TInt. by eauto. }
  iDestruct "beginning" as "[(_ & ? & _)|beginning]".
  { iModIntro. iApply public_TSealIP.
    + by iApply public_TKey; eauto.
    + rewrite public_tag public_of_list /= public_TInt. by eauto. }
 iModIntro. iApply public_TSealIS; eauto.
 - rewrite minted_TKey. by iDestruct "wf" as "(? & ? & ?)".
 - iModIntro. iExists cs, n1, ts, n0. do !iSplit => //.
 - iApply public_minted.
   rewrite public_of_list /= public_TInt. by eauto.
 - rewrite public_of_list /= public_TInt. by eauto. }
by iApply "post".
Qed.

Lemma wp_write kI kR cs n N c ts φ :
  channel c -∗
  seal_pred N (conn_pred φ) -∗
  ([∗ list] t ∈ ts, public t) -∗
  compromised_session (cs_role cs) cs ∨ □ φ kI kR cs n ts -∗
  {{{ connected kI kR cs n }}}
    write N c (repr cs) (repr ts)
  {{{ RET #(); connected kI kR cs n }}}.
Proof.
iIntros "#chan #pred #p_ts #inv !> %Φ conn post".
iDestruct "conn" as "(%n' & %n0 & -> & #? & conn)".
wp_apply (wp_write' with "[//] [//] p_ts inv conn").
iIntros "conn". iApply "post". iExists n', n0. by eauto.
Qed.

Lemma wp_select_inner_body_aux φ v1 v2 (handlers : list val) (Φ : val → iProp) :
  ([∗ list] handler ∈ handlers,
    (φ -∗ WP (handler : val) v1 v2 {{ v',
           ⌜v' = NONEV⌝ ∗ φ ∨
           ∃ r, ⌜v' = SOMEV r⌝ ∗ Φ r }}))%I -∗
  φ -∗ WP select_inner_body v1 v2 (repr handlers) {{ v',
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
wp_bind (handler _ _); iApply (wp_wand with "wp_handler").
iIntros "%v' [[-> inv] | (%r & -> & post)]"; wp_pures.
- by iApply "IH".
- iRight. iExists r. by iFrame.
Qed.

Lemma wp_select_inner_body Φ φ v1 v2 (handlers : list val) Ψ :
  ([∗ list] handler ∈ handlers,
     (φ -∗ WP (handler : val) v1 v2 {{ v,
       ⌜v = NONEV⌝ ∗ φ ∨
       ∃ r, ⌜v = SOMEV r⌝ ∗ Φ r }}))%I -∗
  (φ -∗ Ψ NONEV) -∗
  (∀ r, Φ r -∗ Ψ (SOMEV r)) -∗
  φ -∗
  WP select_inner_body v1 v2 (repr handlers) {{ Ψ }}.
Proof.
iIntros "wp post1 post2 inv".
iApply (wp_wand with "[wp inv] [post1 post2]").
- by iApply (wp_select_inner_body_aux φ v1 v2 handlers Φ with "[wp] inv").
- iIntros "%res [[-> ?]|(%r & -> & ?)]".
  + by iApply "post1".
  + by iApply "post2".
Qed.

Lemma wp_open' N φ kI kR cs n n0 m :
  {{{ seal_pred N (conn_pred φ) ∗
      connected' kI kR cs false n n0 ∗
      public (TSeal (TKey Seal (si_key cs)) m) }}}
    open' N #n m
  {{{ res, RET res;
      connected' kI kR cs false n n0 ∗
      (⌜res = NONEV⌝ ∨
       ∃ ts, ⌜res = SOMEV (repr ts)⌝ ∗
             ([∗ list] t ∈ ts, public t) ∗
             □ (compromised_session (cs_role cs) cs ∨ φ kI kR cs (n + n0) ts)) }}}.
Proof.
iIntros "%Φ (#Φ & conn & #p_m) post".
rewrite /open'.
wp_pure _ credit:"c1".
wp_pure _ credit:"c2".
wp_pures.
wp_untag m; wp_pures; last by iApply "post"; eauto.
wp_list_of_term m; wp_pures; last by iApply "post"; eauto.
case: m => [|t ts].
{ rewrite repr_list_unseal. wp_pures. by iApply "post"; eauto. }
rewrite repr_list_unseal /= -repr_list_unseal.
wp_pures. wp_apply wp_to_int.
case: Spec.to_intP => [n' ->|_]; wp_pures; last by iApply "post"; eauto.
case: bool_decide_reflect => [[<-]|ne]; wp_pures; last by iApply "post"; eauto.
iPoseProof (public_sencE with "p_m [//] [#] [conn]") as "{p_m} #p_m".
- by iDestruct "conn" as "(? & ? & ? & ? & ?)".
- by iDestruct "conn" as "(? & ? & ? & ? & ?)".
iAssert (□ ▷ (([∗ list] t ∈ ts, public t) ∗
           (compromised_session (cs_role cs) cs ∨ φ kI kR cs (n + n0) ts)))%I
  as "#H".
{ iDestruct "conn" as "(<- & <- & ? & ? & ? & #beginning)".
  iIntros "!> !>".
  iDestruct "p_m" as "#[[comp p_m]|inv]".
  - rewrite public_of_list /=. iDestruct "p_m" as "[_ p_m]".
    iSplit => //. by eauto.
  - iDestruct "inv"
      as "(%si & %n'' & %ts' & %n0' & %e_k & %e_m & p_ts & beginning' & ?)".
    move/session_agree: e_k => <- {si}.
    case/Spec.of_list_inj: e_m => e_n <-.
    have <-: n = n'' by lia.
    iSplit => //.
    iDestruct "beginning" as "[?|beginning]"; eauto.
    iPoseProof (term_meta_agree with "beginning beginning'") as "->".
    iRight. by eauto. }
iMod (lc_fupd_elim_later_pers with "c1 H") as "{H} #[p_ts inv_ts]".
iModIntro. iApply "post". iFrame. iRight. by eauto.
Qed.

Definition make_handler_post φ ψ kI kR cs (handler : val) : iProp :=
  □ ∀ n1 n0 (m : term),
    public (TSeal (TKey Seal (si_key cs)) m) -∗
    term_meta (cs_share cs) (isoN.@"beginning") n0 -∗
    connected' kI kR cs false n1 n0 -∗
    φ (n1 + n0) -∗
    WP handler #n1 m {{ v,
      ⌜v = NONEV⌝ ∗ connected' kI kR cs false n1 n0 ∗ φ (n1 + n0) ∨
      ∃ r, ⌜v = SOMEV r⌝ ∗ ψ (n1 + n0) r }}.

Definition handler_correct_gen φ ψ kI kR cs handler : iProp :=
  WP handler.2 {{ f,
    ∃ Ψ, seal_pred handler.1 (conn_pred Ψ) ∗
    □ ∀ n ts,
      {{{ connected kI kR cs n ∗ φ n ∗
          ▷ ([∗ list] t ∈ ts, public t) ∗
          □ ▷ (compromised_session (cs_role cs) cs ∨ Ψ kI kR cs n ts) }}}
        (f : val) (repr ts)
      {{{ v, RET v;
         ⌜v = NONEV⌝ ∗ connected kI kR cs n ∗ φ n ∨
         ∃ r, ⌜v = SOMEV r⌝ ∗ ψ n r }}}
  }}%I.

Lemma wp_make_handler φ ψ kI kR cs (handler : namespace * expr) :
  handler_correct_gen φ ψ kI kR cs handler -∗
  WP make_handler handler {{ make_handler_post φ ψ kI kR cs }}.
Proof.
case: handler => N handler /=; iIntros "wp".
rewrite make_handler_eq /make_handler_def. wp_pures.
wp_bind handler. iApply (wp_wand with "wp").
iIntros "%v_handler #(%φ' & #? & #wp)". wp_pures.
iIntros "!> !> %n1 %n0 %m #p_m #beg conn inv". wp_pures.
wp_apply (wp_open' with "[$conn]"); eauto.
iIntros "%res (conn & [->|(%ts & -> & #p_ts & #inv_ts)])"; wp_pures.
{ iLeft. by iFrame. }
wp_apply ("wp" with "[$inv conn]").
{ iFrame. iSplit; eauto. }
iIntros "%res [(-> & conn & inv)|?]"; last by eauto.
iLeft. iFrame. iSplit => //.
iDestruct "conn" as "(%n1' & %n0' & %e & #beg' & conn)".
iPoseProof (term_meta_agree with "beg beg'") as "<-".
by have <- : n1 = n1' by lia.
Qed.

Lemma wp_make_handlers φ ψ kI kR cs handlers :
  ([∗ list] handler ∈ handlers,
    handler_correct_gen φ ψ kI kR cs handler) -∗
  WP make_handlers handlers {{ v',
    ∃ handlers : list val, ⌜v' = repr handlers⌝ ∗
      [∗ list] handler ∈ handlers,
        make_handler_post φ ψ kI kR cs handler }}.
Proof.
rewrite /= !repr_list_unseal.
elim: handlers=> [|[N handler] handlers IH] //=.
  iIntros "_". wp_pures. iModIntro. iExists []. by rewrite /=.
iIntros "[wp_handler wp_handlers]".
wp_bind (make_handlers _).
iPoseProof (IH with "wp_handlers") as "wp_handlers". clear IH.
iApply (wp_wand with "wp_handlers [wp_handler]").
iIntros "%v' (%handlers' & -> & #Hhandlers')".
wp_bind (make_handler _).
iApply (wp_wand with "[wp_handler] [Hhandlers']").
{ iApply (wp_make_handler _ _ _ _ _ (N, handler) with "wp_handler"). }
iIntros "%f #wp_f". wp_lam; wp_pures.
iExists (f :: handlers'). iSplitR => //=.
iModIntro. iSplit => //.
Qed.

Lemma wp_select_outer_body φ ψ (c : val) kI kR cs (handlers : list val) :
  channel c -∗
  ([∗ list] handler ∈ handlers,
    make_handler_post φ ψ kI kR cs handler) -∗
  ∀ n n0,
  term_meta (cs_share cs) (isoN.@"beginning") n0 -∗
  connected' kI kR cs false n n0 -∗
  φ (n + n0) -∗
  WP select_outer_body c (repr cs) (repr handlers) {{ ψ (n + n0) }}.
Proof.
iIntros "#chan_c #wps %n %n0 #beg conn inv".
wp_lam. wp_pures. wp_apply (wp_timestamp with "conn"). iIntros "conn".
wp_pures. wp_apply wp_session_key => //. iIntros "_".
wp_pures. iCombine "conn inv" as "I". iRevert "I". iApply wp_do_until.
iIntros "!> I". wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m #p_m". wp_pures.
wp_apply wp_key.
wp_bind (open _ _). iApply wp_open.
case: Spec.openP; last by wp_pures; iLeft; iFrame.
move=> _ {}m [<-] ->. wp_pures.
iApply (wp_select_inner_body (ψ (n + n0)) with "[] [] [] I").
- iApply (big_sepL_impl with "wps").
  iIntros "!> %k %handler _ #Hhandler (conn & inv)" => //.
  by iApply ("Hhandler" with "p_m [//] conn inv").
- iIntros "(?&?)". iLeft. by iFrame.
- iIntros "%r Hr". iRight. iExists r. by eauto.
Qed.

Lemma wp_select
  φ ψ (c : val) kI kR cs (handlers : list (namespace * expr)) :
  channel c -∗
  ([∗ list] handler ∈ handlers,
    handler_correct_gen φ ψ kI kR cs handler) -∗
  ∀ n, connected kI kR cs n -∗
  φ n -∗
  WP select c (repr cs) handlers {{ ψ n }}.
Proof.
rewrite select_eq /select_def.
iIntros "#chan_c wps %n (%n' & %n0 & -> & #beg & conn) inv".
wp_bind (make_handlers _). iApply (wp_wand with "[wps]").
{ wp_apply (wp_make_handlers with "wps"). }
iIntros "%res (%v_handlers & -> & #wps)".
by wp_apply (wp_select_outer_body with "[] [] [] conn inv").
Qed.

Lemma wp_read N c kI kR cs n φ :
  channel c -∗
  seal_pred N (conn_pred φ) -∗
  {{{ connected kI kR cs n }}}
    read N c (repr cs)
  {{{ ts, RET (repr (ts : list term));
      connected kI kR cs n ∗
      ([∗ list] t ∈ ts, public t) ∗
      □ (compromised_session (cs_role cs) cs ∨ φ kI kR cs n ts) }}}.
Proof.
iIntros "#? #NΦ !> %Ψ conn post".
wp_lam. wp_pures. rewrite !subst_select /=.
wp_apply (wp_select
  (λ n, (∀ ts, connected kI kR cs n ∗
          ([∗ list] t ∈ ts, public t) ∗
          □ (compromised_session (cs_role cs) cs ∨ φ kI kR cs n ts) -∗
          Ψ (repr ts)))%I with "[] [] conn post") => //.
rewrite /= /handler_correct_gen /=. iSplit => //. wp_pures.
iModIntro. iExists _; iSplit; eauto.
iModIntro. clear n.
iIntros "%n %ts !> %Φ (conn & post1 & #p_ts & #inv_ts) post2".
wp_pures. iModIntro.
iApply "post2". iRight. iExists _. iSplit => //.
iApply "post1". iFrame. by eauto.
Qed.

Lemma wp_free (c : val) cs n :
  {{{ cs_ts cs ↦ #n }}}
    free c (repr cs)
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ ts post".
wp_lam; wp_pures.
wp_free.
by iApply "post".
Qed.

Lemma wp_close N c kI kR cs n :
  channel c -∗
  ctx N -∗
  {{{ connected kI kR cs n ∗ client_token N kI kR cs }}}
    close N c (repr cs)
  {{{ RET #();
      client_disconnected N kI kR n ∗
      public (si_key cs) }}}.
Proof.
iIntros "#chan_c (_ & _ & #close & #ack & _)".
iIntros "!> %Φ [conn token] post".
iPoseProof (connected_keyE with "conn") as "[-> ->]".
wp_lam. wp_pures.
wp_apply (@wp_nil term).
wp_apply (wp_write with "[//] [] [] [] [$]") => //.
{ iRight. iModIntro. by eauto. }
iIntros "conn". wp_pures.
wp_apply (wp_read with "[//] [] [$]") => //.
iIntros "%ts (conn & _ & #inv)".
wp_pures.
iAssert (|={⊤}=>
  ⌜cs_role cs = Init⌝ ∗
  client_disconnected N (si_init cs) (si_resp cs) n ∗
  (compromised_session Init cs ∨ released (si_resp_share cs)))%I
  with "[token]" as ">(%e_rl & dis & #relR)".
{ iDestruct "token" as "(-> & #server & end)".
  iDestruct "inv" as "[fail|[inv #rel]]".
  { iModIntro. do !iSplit => //; eauto.
    iLeft. by iApply session_failed_failure. }
  iMod (escrowE with "inv end") as ">c1" => //.
  iModIntro. iFrame. do !iSplit => //. by eauto. }
iDestruct "conn" as "(% & % & _ & _ & _ & _ & #wf & rel & ts & _)".
iDestruct "wf" as "(_ & _ & #sec & _)".
iMod (release with "rel") as "#relI".
rewrite /cs_share e_rl /=.
wp_apply (wp_free with "[$]"). iIntros "_".
iApply "post". iFrame.
iDestruct "relR" as "[(_ & ? & _)|relR]"; eauto.
iApply "sec". iSplit => //.
Qed.

Definition handler_loop_post φ skI skR cs n res : iProp :=
  ⌜res = #true⌝ ∗ ∃ n', connected skI skR cs n' ∗ φ n'.

Definition handler_correct φ skI skR cs handler : iProp :=
  handler_correct_gen φ (handler_loop_post φ skI skR cs)
           skI skR cs handler.

Definition handler_loop_post_gen φ N skI skR cs n res : iProp :=
  ⌜res = #true⌝ ∗
    (∃ n', connected skI skR cs n' ∗ server_token N cs ∗ φ n') ∨
  ⌜res = #false⌝ ∗
    ∃ n', server_disconnected N skI skR n' ∗ φ n'.

Lemma wp_handle_loop c N skI skR cs n φ ψ handlers :
  channel c -∗
  ([∗ list] handler ∈ handlers,
    make_handler_post
      (λ n, server_token N cs ∗ φ n)
      (handler_loop_post_gen φ N skI skR cs)
      skI skR cs handler) -∗
  connected skI skR cs n -∗
  server_token N cs -∗
  φ n -∗
  (∀ n', server_disconnected N skI skR n' ∗ φ n' -∗ ψ #()) -∗
  WP handle_loop c (repr cs) (repr handlers) {{ ψ }}.
Proof.
iIntros "#chan_c #wps conn token inv post".
iApply (wp_frame_wand with "post").
iLöb as "IH" forall (n).
iDestruct "conn" as "(%n1 & %n0 & -> & #beg & conn)".
wp_rec. wp_pures. iCombine "token inv" as "inv".
iPoseProof (wp_select_outer_body with "chan_c wps beg conn inv") as "wp".
wp_bind (select_outer_body _ _ _). iApply (wp_wand with "wp").
iIntros "% [(-> & %n' & conn & token & inv)|(-> & %n' & dis)]".
- wp_pures. by iApply ("IH" with "conn token inv").
- wp_pures. iModIntro. iIntros "post". by iApply "post".
Qed.

Lemma wp_handle
  φ ψ (c : val) skI skR cs n N (handlers : list (namespace * expr)) :
  channel c -∗
  ctx N -∗
  ([∗ list] handler ∈ handlers, handler_correct φ skI skR cs handler) -∗
  connected skI skR cs n -∗
  server_token N cs -∗
  φ n -∗
  (∀ n', server_disconnected N skI skR n' ∗ φ n' -∗ ψ #()) -∗
  WP handle N c (repr cs) handlers {{ ψ }}.
Proof.
iIntros "#chan_c #ctx wps conn token inv post".
rewrite handle_eq /handle_def.
iAssert ([∗ list] handler ∈ handlers, handler_correct_gen
           (λ n, server_token N cs ∗ φ n)
           (handler_loop_post_gen φ N skI skR cs)
           skI skR cs handler)%I with "[wps]" as "wps".
{ iApply (big_sepL_impl with "wps").
  iIntros "!> % % _ wp".
  rewrite /handler_correct_gen.
  iApply (wp_wand with "wp").
  iIntros "%v_handler (%ψ' & #? & #wp)".
  iExists ψ'. iSplit => //.
  iIntros "!> %n' %ts !> %ψ'' (conn & (token & inv) & #p_ts & #inv_ts)".
  iIntros "post". iApply ("wp" with "[$conn $inv]"); eauto.
  iIntros "!> %res [(-> & conn & inv)|(%v & -> & -> & %n'' & conn & inv)]".
  - iApply "post". iLeft. by iFrame.
  - iApply "post". iRight. iExists _. iSplit => //.
    iLeft. by iFrame. }
iAssert (handler_correct_gen
           (λ n, server_token N cs ∗ φ n)
           (handler_loop_post_gen φ N skI skR cs)
           skI skR cs (N.@"conn".@"close",
             handle_close N c (repr cs)))%I as "wp_close".
{ iPoseProof (ctx_close with "ctx") as "#?".
  iPoseProof (ctx_ack_close with "ctx") as "#?".
  rewrite /handler_correct_gen /handle_close. wp_pures.
  iModIntro. iExists _. iSplit => //.
  iIntros "!> %n' %ts !> %ψ' (conn & (token & inv) & _ & _) post". wp_pures.
  iPoseProof (connected_keyE skI skR cs n' with "conn") as "%e".
  iDestruct "conn" as "(%n1 & %n0 & -> & _ & conn)".
  iAssert (⌜cs_role cs = Resp⌝)%I as "%e_rl".
  { by iDestruct "token" as "[??]". }
  iAssert (|==> (connected' skI skR cs true n1 n0 ∗
             released (si_resp_share cs)))%I
    with "[conn]" as ">[conn #rel]".
  { iDestruct "conn" as "(<- & <- & ? & rel & ts & ?)".
    iMod (release with "rel") as "#rel".
    iModIntro. iFrame. rewrite /cs_share /= e_rl. by eauto. }
  iAssert (|={⊤}=>
    server_disconnected N skI skR (n1 + n0) ∗
    (compromised_session Resp cs ∨
     □ ack_close_pred N skI skR cs (n1 + n0) [TInt 0]))%I
  with "[token]" as ">(dis & #?)".
  { rewrite /server_disconnected.
    case: e => -> ->.
    iDestruct "token" as "[_ token]".
    iDestruct "token" as "[#fail|(%n'' & c1 & c2)]".
    { iModIntro. rewrite -session_failed_failure.
      iSplit => //; eauto. }
    iMod (clock_update N (n1 + n0) with "c1 c2") as "[c1 c2]".
    iAssert (|={⊤}=> conn_closed N cs (n1 + n0))%I with "[c2]" as ">#?".
    { iApply (escrowI with "c2"). iApply term_token_switch. }
    iModIntro.
    iFrame. iRight. iModIntro. by iSplit. }
  wp_list. rewrite -e_rl.
  wp_apply (wp_write' with "[//] [] [] [//] [$]") => //.
  - by rewrite /= public_TInt.
  iIntros "conn". wp_pures.
  iDestruct "conn" as "(_ & _ & _ & _ & ts & _)".
  wp_apply (wp_free with "[$]"). iIntros "_". wp_pures.
  iModIntro. iApply "post". iRight. iExists _. iSplit => //.
  iRight. iSplit => //. iExists (n1 + n0). by iFrame. }
iPoseProof (wp_make_handlers with "wps") as "wp".
wp_bind (make_handlers _). iApply (wp_wand with "wp").
iIntros "%res (%handlers' & -> & #wps')".
wp_pures. rewrite !subst_make_handler /=.
iPoseProof (wp_make_handler with "wp_close") as "{wp_close} wp_close".
wp_bind (make_handler _). iApply (wp_wand with "wp_close").
iIntros "%v_close {wp_close} #wp_close".
wp_bind (_ :: _)%E.
wp_apply (@wp_cons val _ _ _ _ v_close).
iApply (wp_handle_loop with "[//] [] conn token inv").
{ by rewrite /=; iSplit => //. }
by [].
Qed.

End Proofs.

End Proofs.
