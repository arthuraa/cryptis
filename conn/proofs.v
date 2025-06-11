From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics.
From cryptis Require Import role iso_dh.
From cryptis.conn Require Import impl props.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Proofs.

Import Props Impl.

Record handler := Handler {
  handler_val : val;
}.

Instance repr_handler : Repr handler := handler_val.

Section Proofs.

Context `{!cryptisGS Σ, !heapGS Σ, !connGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : state).
Implicit Types kI kR kS t : term.
Implicit Types n m : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_connect P N c kI kR :
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  sign_key kI -∗
  public (TKey Open kR) -∗
  {{{ failure kI kR ∨ P }}}
    Impl.connect N c kI (TKey Open kR)
  {{{ cs, RET (repr cs);
      connected kI kR Init cs ∗
      (compromised_session Init cs ∨ P) ∗
      release_token (si_init_share cs) ∗
      term_token (si_init_share cs) (↑isoN.@"conn") }}}.
Proof.
iIntros "#? #? #? #? #? % !> HP post".
rewrite bi.or_alt. iDestruct "HP" as "(%failed & HP)".
wp_lam. wp_pure _ credit:"c1". wp_pure _ credit:"c2".
wp_pures. wp_bind (do_until _).
iAssert (if failed then failure kI kR else True)%I as "#?".
{ by case: failed. }
iCombine "HP post c1 c2" as "post". iApply (wp_frame_wand with "post").
wp_apply wp_do_until'. iModIntro.
wp_pures.
wp_apply (wp_initiator _ failed with "[//] [//] [] [] []") => //.
- case: failed => //. by eauto.
iIntros "%res resP".
case: res=> [kS|] /=; last by eauto.
iDestruct "resP"
  as "(%si & <- & %e_kR & <- & #m_kS & #sess & #comp & rel & token)".
case: e_kR => <- {kR}.
iRight. iExists _. iSplit => //.
iIntros "(dis & post & c1 & c2)".
wp_pures.
wp_alloc ts as "ts"; try lia. wp_pures. rewrite /=.
pose cs := State si ts Init.
iMod (received_alloc si Init with "token") as "[received token]";
  first solve_ndisj.
iApply ("post" $! cs).
iModIntro. iFrame.
iSplit.
{ do 5!iSplit => //. by iApply senc_key_si_key. }
iSplitR "token".
{ case: failed; eauto. iLeft. by iApply "comp". }
iApply (term_token_drop with "token"). solve_ndisj.
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

Lemma wp_confirm P N c skA skB ga :
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  {{{ public ga ∗ public (TKey Open skA) ∗ sign_key skB ∗
      (failure skA skB ∨ P) }}}
    confirm N c skB (ga, TKey Open skA)%V
  {{{ cs, RET (repr cs);
      connected skA skB Resp cs ∗
      (compromised_session Resp cs ∨ P) ∗
      release_token (si_resp_share cs) ∗
      term_token (si_resp_share cs) (↑isoN.@"conn") }}}.
Proof.
iIntros "#? #ctx #? !> %Φ (#p_ga & #p_vkA & #sign_skB & P) post".
rewrite bi.or_alt. iDestruct "P" as "(%failed & P)".
wp_lam. wp_pures.
iAssert (if failed then failure skA skB else True)%I
  as "#?".
{ by case: failed. }
wp_bind (do_until _).
iApply (wp_frame_wand with "post").
iApply (wp_frame_wand with "P").
iApply wp_do_until'. iIntros "!>".
wp_pures.
iPoseProof (ctx_iso_dh_ctx with "[//]") as "#?".
iApply (wp_responder_accept _ failed).
{ do !iSplit => //. case: failed => //. by eauto. }
iIntros "!> %osi res". case: osi => [si|]; last by eauto.
iDestruct "res" as "(%e & <- & #m_k & #sess & #comp & rel & token)".
case: e => -> {skA}.
iRight. iExists _. iSplit => //.
iIntros "P post".
wp_pures.
wp_alloc ts as "ts"; first lia.
wp_pures.
iMod (received_alloc si Resp with "token") as "[received token]";
  first solve_ndisj.
iApply ("post" $! (State si ts Resp)).
iModIntro. iFrame. do 6?iSplit => //.
{ by iApply senc_key_si_key. }
iSplitR "token".
{ case: failed; eauto. iLeft. by iApply "comp". }
iApply (term_token_drop with "token"). solve_ndisj.
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

Lemma wp_write kI kR rl cs N c ts φ :
  channel c -∗
  seal_pred N (conn_pred rl φ) -∗
  ([∗ list] t ∈ ts, public t) -∗
  {{{ connected kI kR rl cs ∗
      (public (si_key cs) ∨ φ kI kR cs ts) }}}
    write c (repr cs) (Tag N) (repr ts)
  {{{ RET #(); connected kI kR rl cs }}}.
Proof.
iIntros "#chan #pred #p_ts !> %Φ (conn & inv) post".
iDestruct "conn" as "(<- & <- & <- & #sess & %n & %m & counters & recv)".
wp_lam. wp_pures.
wp_lam. wp_pures.
wp_apply wp_session_key => //. iIntros "_".
wp_pures.
wp_apply (wp_load_offset with "counters") => //.
iIntros "counters".
wp_apply wp_tint. wp_list. wp_term_of_list.
wp_pures. wp_apply wp_senc. wp_pures.
iAssert (|={⊤}=> public (si_key cs) ∨
                   conn_pred (cs_role cs) φ
                     (si_key cs) (Spec.of_list (TInt n :: ts)))%I
  with "[inv]" as ">#p_t".
{ iDestruct "inv" as "[#?|inv]"; first by eauto.
  iRight. iExists cs, n, ts. do 3!iSplitR => //.
  by iApply escrow_received. }
wp_apply (wp_send with "[//] [#]").
{ iDestruct "p_t" as "[p_t|inv_t]".
  { iApply public_TSealIP.
    - rewrite public_TKey; eauto.
    - rewrite public_tag public_of_list /= public_TInt; eauto. }
 iApply public_TSealIS; eauto.
 - rewrite minted_TKey. by iDestruct "sess" as "(? & ? & ?)".
 - iApply public_minted.
   rewrite public_of_list /= public_TInt. by eauto.
 - rewrite public_of_list /= public_TInt. by eauto. }
wp_pures.
wp_apply (wp_load_offset with "counters") => //.
iIntros "counters". wp_pures.
wp_apply (wp_store_offset with "counters") => //=.
rewrite (_ : (_ + _)%Z = S n); last by lia.
iIntros "counters". iApply "post". iFrame. by eauto.
Qed.

Lemma wp_try_open N φ kI kR rl cs t :
  {{{ seal_pred N (conn_pred (swap_role rl) φ) ∗
      connected kI kR rl cs ∗
      public (TSeal (TKey Seal (si_key cs)) t) }}}
    try_open (repr cs) (Tag N) t
  {{{ res, RET res;
      connected kI kR rl cs ∗
      (⌜res = NONEV⌝ ∨
       ∃ ts, ⌜res = SOMEV (repr ts)⌝ ∗
             ([∗ list] t ∈ ts, public t) ∗
             (public (si_key cs) ∨ φ kI kR cs ts)) }}}.
Proof.
iIntros "%Φ (#Φ & conn & #p_t) post".
rewrite /try_open.
wp_pure _ credit:"c1".
wp_pure _ credit:"c2".
wp_pures.
wp_untag t; wp_pures; last by iApply "post"; iFrame; eauto.
wp_list_of_term t; wp_pures; last by iApply "post"; iFrame; eauto.
iDestruct "conn" as "(<- & <- & <- & #sess & %n & %m & counters & recv)".
wp_lam. wp_pures. wp_apply (wp_load_offset with "counters") => //.
iIntros "counters".
wp_pures.
case: t => [|t ts].
{ rewrite repr_list_unseal; wp_pures.
  iApply "post". iFrame. iModIntro. iSplit; eauto. }
rewrite repr_list_unseal /= -repr_list_unseal.
wp_pures. wp_apply wp_to_int.
case: Spec.to_intP => [n' ->|_]; wp_pures; last first.
{ iApply "post". iFrame. iModIntro. iSplit; eauto. }
case: bool_decide_reflect => [[<-]|ne]; wp_pures; last first.
{ iApply "post". iFrame. iModIntro. iSplit; eauto. }
iPoseProof (public_sencE with "p_t [//] [#]") as "{p_t} #p_t" => //.
rewrite (_ : (m + 1)%Z = S m); last by lia.
wp_lam. wp_pures.
iAssert (|={⊤}=> ▷ (([∗ list] t ∈ ts, public t) ∗
           received_auth cs (cs_role cs) (S m) ∗
           (public (si_key cs) ∨ φ (si_init cs) (si_resp cs) cs ts)))%I
  with "[recv]" as ">H".
{ rewrite public_of_list /=.
  iDestruct "p_t" as "#[(? & _ & ?)|inv]".
  { iMod (received_update with "recv") as "[recv _]".
    iIntros "!> !>". iFrame. iSplit => //. eauto. }
  iDestruct "inv" as "(%si & %m' & %ts' & %e_k & %e_t & p_ts & inv)".
  move/session_agree: e_k => <- {si}.
  case/Spec.of_list_inj: e_t => e_m <-.
  have <-: m = m' by lia.
  rewrite swap_roleK.
  iMod (escrowE with "inv recv") as "{inv} [inv recv]";
    first by solve_ndisj.
  iIntros "!> !>". by iFrame. }
wp_apply (wp_store_offset with "counters") => //=. iIntros "counters".
iDestruct "H" as "(#? & received & inv)".
wp_pures. iApply "post". iFrame.
iModIntro. iSplit; eauto.
Qed.

Definition wf_handler Φ Ψ kI kR rl cs (h : handler) : iProp :=
  □ ∀ t,
    {{{ public (TSeal (TKey Seal (si_key cs)) t) ∗
        connected kI kR rl cs ∗ Φ }}}
      repr h (repr cs) t
    {{{ ov, RET (repr ov);
        match ov : option val with
        | Some v => Ψ v
        | None => connected kI kR rl cs ∗ Φ
        end
    }}}.

Instance persistent_wf_handler Φ Ψ kI kR rl cs h :
  Persistent (wf_handler Φ Ψ kI kR rl cs h).
Proof. apply _. Qed.

Lemma wp_select Φ Ψ kI kR rl cs c hs :
  channel c -∗
  ([∗ list] h ∈ hs, wf_handler Φ Ψ kI kR rl cs h) -∗
  (connected kI kR rl cs ∗ Φ) -∗
  WP select c (repr cs) (repr hs) {{ Ψ }}.
Proof.
iIntros "#chan_c #wp_handlers inv".
wp_lam; wp_pures. wp_apply wp_session_key => //. iIntros "_".
wp_pures. iRevert "inv". iApply wp_do_until.
iIntros "!> inv". wp_pures.
wp_apply wp_recv => //. iIntros "%t #p_t". wp_pures.
wp_apply wp_key. wp_bind (open _ _). iApply wp_open.
case: Spec.openP; last by wp_pures; iLeft; iFrame.
move=> _ {}t [<-] ->. wp_pures.
wp_apply (wp_scan_list (wf_handler Φ Ψ kI kR rl cs)); last first.
{ iSplit => //. iLeft. by iFrame. }
iIntros "!> %h !> %Ξ ([(_ & inv)|(% & % & ?)] & #wp_handler)" => //.
iIntros "post". wp_pures. wp_apply ("wp_handler" with "[$]").
iIntros "%ov ov". iApply "post". case: ov => [v|]; eauto.
Qed.

Lemma wp_handle Φ Ψ kI kR rl cs φ (N : namespace) (f : val) :
  {{{
    seal_pred N (conn_pred (swap_role rl) φ) ∗
    □ (∀ (ts : list term),
      {{{ connected kI kR rl cs ∗ Φ ∗
          ▷ ([∗ list] t ∈ ts, public t) ∗
          ▷ (public (si_key cs) ∨ φ kI kR cs ts) }}}
        f (repr cs) (repr ts)
      {{{ v, RET v; Ψ v }}})
  }}}
    handle (Tag N) f
  {{{ h, RET (repr h); wf_handler Φ Ψ kI kR rl cs h }}}.
Proof.
iIntros "%Ξ [#? #wp] post". wp_lam. wp_pures.
iIntros "!>". iApply ("post" $! (Handler _)). clear Ξ.
iIntros "!> %t !> %Ξ (#p_t & conn & inv) post". wp_pures.
wp_apply (wp_try_open with "[$conn]"); eauto.
iIntros "%res (conn & [->|(%ts & -> & #p_ts & inv_ts)])"; wp_pures.
{ iApply ("post" $! None). by iFrame. }
wp_apply ("wp" with "[$inv $conn $inv_ts]") => //.
iIntros "%res ?". wp_pures. iModIntro. by iApply ("post" $! (Some res)). 
Qed.

Lemma wp_read N c kI kR rl cs φ :
  channel c -∗
  seal_pred N (conn_pred (swap_role rl) φ) -∗
  {{{ connected kI kR rl cs }}}
    read c (repr cs) (Tag N)
  {{{ ts, RET (repr (ts : list term));
      connected kI kR rl cs ∗
      ([∗ list] t ∈ ts, public t) ∗
      (public (si_key cs) ∨ φ kI kR cs ts) }}}.
Proof.
iIntros "#? #Nφ !> %Φ conn post".
wp_lam. wp_pures.
pose (Ψ := λ v,
  (∃ ts : list term,
    ⌜v = repr ts⌝ ∗
    connected kI kR rl cs ∗
    ([∗ list] t ∈ ts, public t) ∗
    (public (si_key cs) ∨ φ kI kR cs ts))%I).
iApply (wp_wand _ _ _ Ψ with "[conn]"); last first.
{ iIntros "% (%ts & -> & ?)". by iApply "post". }
clear Φ. wp_apply (wp_handle True Ψ kI kR rl cs).
{ iSplit => //.
  iIntros "!> %ts !> %Ξ (conn & _ & #p_ts & inv_ts) post".
  wp_pures. iModIntro. iApply "post". iFrame. by eauto. }
iIntros "%h #h_p". wp_list.
wp_apply (wp_select True%I Ψ with "[//] [] [$conn]") => //=.
by eauto.
Qed.

Lemma wp_free (c : val) kI kR rl cs :
  {{{ connected kI kR rl cs }}}
    free c (repr cs)
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ conn post".
iDestruct "conn" as "(? & ? & ? & ? & % & % & ts & ?)".
rewrite !array_cons array_nil.
iDestruct "ts" as "(sent & recv & _)".
wp_lam; wp_pures.
wp_free. wp_pures.
wp_free.
by iApply "post".
Qed.

End Proofs.

End Proofs.
