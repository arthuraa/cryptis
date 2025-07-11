From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh.
From cryptis.examples.conn Require Import impl props.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Proofs.

Import Props.

Record handler := Handler {
  handler_val : val;
}.

Instance repr_handler : Repr handler := handler_val.

Section Proofs.

Context `{!cryptisGS Σ, !heapGS Σ, !connGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : state).
Implicit Types kS t : term.
Implicit Types skI skR : sign_key.
Implicit Types n m : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_channel cs :
  {{{ True }}}
    Impl.channel (repr cs)
  {{{ RET (cs_chan cs); True }}}.
Proof.
iIntros "% _ post". wp_lam. wp_pures. by iApply "post".
Qed.

Lemma wp_connect P c skI skR :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx -∗
  minted skI -∗
  minted skR -∗
  {{{ failure skI skR ∨ P }}}
    Impl.connect c skI (Spec.pkey skR)
  {{{ cs, RET (repr cs);
      connected skI skR Init cs ∗
      (compromised_session Init cs ∨ P) ∗
      release_token (si_init_share cs) ∗
      term_token (si_init_share cs) (⊤ ∖ ↑iso_dhN ∖ ↑connN) }}}.
Proof.
iIntros "#? #? #? #? #? % !> HP post".
rewrite bi.or_alt. iDestruct "HP" as "(%failed & HP)".
wp_lam. wp_pure _ credit:"c1". wp_pure _ credit:"c2".
wp_pures. wp_bind (do_until _).
iAssert (if failed then failure skI skR else True)%I as "#?".
{ by case: failed. }
iCombine "HP post c1 c2" as "post". iApply (wp_frame_wand with "post").
wp_apply wp_do_until'. iModIntro.
wp_pures.
wp_apply (wp_initiator failed with "[//] [//] [] [] []") => //.
iIntros "%res resP".
case: res=> [kS|] /=; last by eauto.
iDestruct "resP"
  as "(%si & <- & %e_kR & <- & #m_kS & #sess & #comp & rel & token)".
move: e_kR => <-.
iRight. iExists _. iSplit => //.
iIntros "(dis & post & c1 & c2)".
wp_pures.
wp_alloc ts as "ts"; try lia. wp_pures. rewrite /=.
pose cs := State si ts c Init.
iMod (received_alloc si Init with "token") as "[received token]";
  first solve_ndisj.
iApply ("post" $! cs).
iModIntro. iFrame.
iSplit.
{ do 6!iSplit => //. }
iSplitR "token".
{ case: failed; eauto. iLeft. by iApply "comp". }
iApply (term_token_drop with "token"). solve_ndisj.
Qed.

Lemma wp_listen c :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx -∗
  {{{ True }}}
    Impl.listen c
  {{{ ga skI, RET (ga, Spec.pkey skI)%V;
      public ga ∗ minted skI }}}.
Proof.
iIntros "#? #? #? % !> _ post". wp_lam.
wp_apply wp_responder_wait; eauto.
Qed.

Lemma wp_confirm P c skI skR ga :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx -∗
  {{{ public ga ∗ minted skI ∗ minted skR ∗
      (failure skI skR ∨ P) }}}
    Impl.confirm c skR (ga, Spec.pkey skI)%V
  {{{ cs, RET (repr cs);
      connected skI skR Resp cs ∗
      (compromised_session Resp cs ∨ P) ∗
      release_token (si_resp_share cs) ∗
      term_token (si_resp_share cs) (⊤ ∖ ↑iso_dhN ∖ ↑connN) }}}.
Proof.
iIntros "#? #ctx #? !> %Φ (#p_ga & #p_pkA & #sign_skB & P) post".
rewrite bi.or_alt. iDestruct "P" as "(%failed & P)".
wp_lam. wp_pures.
iAssert (if failed then failure skI skR else True)%I
  as "#?".
{ by case: failed. }
wp_bind (do_until _).
iApply (wp_frame_wand with "post").
iApply (wp_frame_wand with "P").
iApply wp_do_until'. iIntros "!>".
wp_pures.
iApply (wp_responder_accept failed).
{ do !iSplit => //. }
iIntros "!> %osi res". case: osi => [si|]; last by eauto.
iDestruct "res" as "(%e & <- & #m_k & #sess & #comp & rel & token)".
rewrite -{}e {skI}.
iRight. iExists _. iSplit => //.
iIntros "P post".
wp_pures.
wp_alloc ts as "ts"; first lia.
wp_pures.
iMod (received_alloc si Resp with "token") as "[received token]";
  first solve_ndisj.
iApply ("post" $! (State si ts c Resp)).
iModIntro. iFrame. do 7?iSplit => //.
iSplitR "token".
{ case: failed; eauto. iLeft. by iApply "comp". }
iApply (term_token_drop with "token"). solve_ndisj.
Qed.

Lemma wp_session_key cs :
  {{{ True }}}
    Impl.session_key (repr cs)
  {{{ RET (repr (si_key cs)); True }}}.
Proof.
rewrite /Impl.session_key.
iIntros "%Φ _ post". wp_pures. iApply "post".
iModIntro. by iFrame.
Qed.

Lemma wp_send skI skR rl cs N ts φ :
  senc_pred N (conn_pred rl φ) -∗
  ([∗ list] t ∈ ts, public t) -∗
  {{{ connected skI skR rl cs ∗
      (public (si_key cs) ∨ φ skI skR cs ts) }}}
    Impl.send (repr cs) (Tag N) (repr ts)
  {{{ RET #(); connected skI skR rl cs }}}.
Proof.
iIntros "#pred #p_ts !> %Φ (conn & inv) post".
iDestruct "conn" as "(<- & <- & <- & #chan & #sess & %n & %m & counters & recv)".
wp_lam. wp_pures.
wp_apply wp_channel => //. iIntros "_". wp_pures.
wp_lam. wp_pures.
wp_apply wp_session_key => //. iIntros "_".
wp_pures.
wp_apply (wp_load_offset with "counters") => //.
iIntros "counters".
wp_apply wp_tint. wp_list. wp_term_of_list.
iAssert (public (Spec.of_list (TInt n :: ts))) as "?".
{ by rewrite public_of_list /= public_TInt; eauto. }
iAssert (|={⊤}=> public (si_key cs) ∨
                   conn_pred (cs_role cs) φ
                     (si_key cs) (Spec.of_list (TInt n :: ts)))%I
  with "[inv]" as ">#p_t".
{ iDestruct "inv" as "[#?|inv]"; first by eauto.
  iRight. iExists cs, n, ts. do 3!iSplitR => //.
  by iApply escrow_received. }
wp_pures. wp_apply wp_senc; eauto.
- by iDestruct "sess" as "(?&?)".
- by iDestruct "p_t" as "[p_t|inv_t]"; eauto.
iIntros "%t #?". wp_pures. wp_apply wp_send => //. wp_pures.
wp_apply (wp_load_offset with "counters") => //.
iIntros "counters". wp_pures.
wp_apply (wp_store_offset with "counters") => //=.
rewrite (_ : (_ + _)%Z = S n); last by lia.
iIntros "counters". iApply "post". iFrame. by eauto.
Qed.

Lemma wp_try_open N φ skI skR rl cs t :
  {{{ senc_pred N (conn_pred (swap_role rl) φ) ∗
      connected skI skR rl cs ∗
      public (TSeal (si_key cs) t) }}}
    Impl.try_open (repr cs) (Tag N) t
  {{{ res, RET res;
      connected skI skR rl cs ∗
      (⌜res = NONEV⌝ ∨
       ∃ ts, ⌜res = SOMEV (repr ts)⌝ ∗
             ([∗ list] t ∈ ts, public t) ∗
             (public (si_key cs) ∨ φ skI skR cs ts)) }}}.
Proof.
Arguments si_key : simpl never.
iIntros "%Φ (#Φ & conn & #p_t) post".
rewrite /Impl.try_open.
wp_pure _ credit:"c1".
wp_pure _ credit:"c2".
wp_pures.
wp_untag t; wp_pures; last by iApply "post"; iFrame; eauto.
wp_list_of_term t; wp_pures; last by iApply "post"; iFrame; eauto.
iDestruct "conn"
  as "(<- & <- & <- & #chan & #sess & %n & %m & counters & recv)".
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
iPoseProof (public_sencE with "p_t [//]") as "{p_t} #p_t" => //.
rewrite (_ : (m + 1)%Z = S m); last by lia.
wp_lam. wp_pures.
iAssert (|={⊤}=> ▷ (([∗ list] t ∈ ts, public t) ∗
           received_auth cs (cs_role cs) (S m) ∗
           (public (si_key cs) ∨ φ (si_init cs) (si_resp cs) cs ts)))%I
  with "[recv]" as ">H".
{ rewrite public_of_list /= minted_of_list /=.
  iDestruct "p_t" as "#(m_t & [fail|#inv] & #p_t)".
  { iMod (received_update with "recv") as "[recv _]".
    iDestruct ("p_t" with "fail") as "[_ ?]".
    iIntros "!> !>". iFrame. iSplit => //. eauto. }
  iDestruct "inv" as "(%si & %m' & %ts' & %e_k & %e_t & p_ts & inv)".
  move/term_of_senc_key_inj/session_agree: e_k => <- {si}.
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

Definition wf_handler Φ Ψ skI skR rl cs (h : handler) : iProp :=
  □ ∀ t,
    {{{ public (TSeal (si_key cs) t) ∗
        connected skI skR rl cs ∗ Φ }}}
      repr h (repr cs) t
    {{{ ov, RET (repr ov);
        match ov : option val with
        | Some v => Ψ v
        | None => connected skI skR rl cs ∗ Φ
        end
    }}}.

Instance persistent_wf_handler Φ Ψ skI skR rl cs h :
  Persistent (wf_handler Φ Ψ skI skR rl cs h).
Proof. apply _. Qed.

Lemma wp_select Φ Ψ skI skR rl cs hs :
  ([∗ list] h ∈ hs, wf_handler Φ Ψ skI skR rl cs h) -∗
  (connected skI skR rl cs ∗ Φ) -∗
  WP Impl.select (repr cs) (repr hs) {{ Ψ }}.
Proof.
iIntros "#wp_handlers [conn inv]".
iPoseProof (connected_channel with "conn") as "#?".
iCombine "conn inv" as "inv".
wp_lam; wp_pures. wp_apply wp_session_key => //. iIntros "_".
wp_pures. iRevert "inv". iApply wp_do_until.
iIntros "!> inv". wp_pures.
wp_apply wp_channel => //. iIntros "_".
wp_apply wp_recv => //. iIntros "%t #p_t". wp_pures.
wp_bind (open _ _). iApply wp_open.
case: Spec.openP; last by wp_pures; iLeft; iFrame.
move=> _ {}t /Spec.open_key_sencK -> ->. wp_pures.
wp_apply (wp_scan_list (wf_handler Φ Ψ skI skR rl cs)); last first.
{ iSplit => //. iLeft. by iFrame. }
iIntros "!> %h !> %Ξ ([(_ & inv)|(% & % & ?)] & #wp_handler)" => //.
iIntros "post". wp_pures. wp_apply ("wp_handler" with "[$]").
iIntros "%ov ov". iApply "post". case: ov => [v|]; eauto.
Qed.

Lemma wp_handle Φ Ψ skI skR rl cs φ (N : namespace) (f : val) :
  {{{
    senc_pred N (conn_pred (swap_role rl) φ) ∗
    □ (∀ (ts : list term),
      {{{ connected skI skR rl cs ∗ Φ ∗
          ▷ ([∗ list] t ∈ ts, public t) ∗
          ▷ (public (si_key cs) ∨ φ skI skR cs ts) }}}
        f (repr cs) (repr ts)
      {{{ v, RET v; Ψ v }}})
  }}}
    Impl.handle (Tag N) f
  {{{ h, RET (repr h); wf_handler Φ Ψ skI skR rl cs h }}}.
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

Lemma wp_recv N skI skR rl cs φ :
  senc_pred N (conn_pred (swap_role rl) φ) -∗
  {{{ connected skI skR rl cs }}}
    Impl.recv (repr cs) (Tag N)
  {{{ ts, RET (repr (ts : list term));
      connected skI skR rl cs ∗
      ([∗ list] t ∈ ts, public t) ∗
      (public (si_key cs) ∨ φ skI skR cs ts) }}}.
Proof.
iIntros "#Nφ !> %Φ conn post".
wp_lam. wp_pures.
pose (Ψ := λ v,
  (∃ ts : list term,
    ⌜v = repr ts⌝ ∗
    connected skI skR rl cs ∗
    ([∗ list] t ∈ ts, public t) ∗
    (public (si_key cs) ∨ φ skI skR cs ts))%I).
iApply (wp_wand _ _ _ Ψ with "[conn]"); last first.
{ iIntros "% (%ts & -> & ?)". by iApply "post". }
clear Φ. wp_apply (wp_handle True Ψ skI skR rl cs).
{ iSplit => //.
  iIntros "!> %ts !> %Ξ (conn & _ & #p_ts & inv_ts) post".
  wp_pures. iModIntro. iApply "post". iFrame. by eauto. }
iIntros "%h #h_p". wp_list.
wp_apply (wp_select True%I Ψ with "[] [$conn]") => //=.
by eauto.
Qed.

Lemma wp_free kI kR rl cs :
  {{{ connected kI kR rl cs }}}
    Impl.free (repr cs)
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ conn post".
iDestruct "conn" as "(? & ? & ? & ? & ? & % & % & ts & ?)".
rewrite !array_cons array_nil.
iDestruct "ts" as "(sent & recv & _)".
wp_lam; wp_pures.
wp_free. wp_pures.
wp_free.
by iApply "post".
Qed.

End Proofs.

End Proofs.
