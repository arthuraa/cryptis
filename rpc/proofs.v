From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics.
From cryptis Require Import role iso_dh conn.
From cryptis.rpc Require Import impl props.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Proofs.

Import Props Impl.

Section Proofs.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !rpcGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : Conn.state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_connect P N c kI kR n :
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  sign_key kI -∗
  public (TKey Open kR) -∗
  {{{ client_disconnected N kI kR n ∗ (Conn.failure kI kR ∨ P) }}}
    Impl.connect N c kI (TKey Open kR)
  {{{ cs, RET (repr cs);
      client_connected N kI kR cs n ∗
      (compromised_session Init cs ∨ P) }}}.
Proof.
iIntros "#? #? #? #? #? % !> (clock & P) post".
iPoseProof (or_sep1 with "clock P") as "P".
wp_lam; wp_pures.
iPoseProof (Props.ctx_conn_ctx with "[//]") as "?".
iApply wp_fupd.
wp_apply (Conn.wp_connect with "[//] [//] [//] [//] [//] P").
iIntros "%cs (connected & P & rel & token)".
iMod (term_meta_set (isoN.@"conn".@"beg") n with "token")
  as "#meta"; first solve_ndisj.
iDestruct (or_sep2 with "P") as "[clock P]".
iApply "post". by iFrame.
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
wp_lam. iApply Conn.wp_listen => //.
by iApply Props.ctx_conn_ctx.
Qed.

Lemma wp_confirm P N c skA skB ga n :
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  {{{ public ga ∗ public (TKey Open skA) ∗ sign_key skB ∗
      server_disconnected N skA skB n ∗
      (Conn.failure skA skB ∨ P) }}}
    confirm N c skB (ga, TKey Open skA)%V
  {{{ cs, RET (repr cs);
      server_connected N skA skB cs n ∗
      (compromised_session Resp cs ∨ P) }}}.
Proof.
iIntros "#? #ctx #? !> %Φ (#p_ga & #p_vkA & #sign_skB & dis & P) post".
iPoseProof (or_sep1 with "dis P") as "dis".
wp_lam; wp_pures.
iPoseProof (Props.ctx_conn_ctx with "[//]") as "?".
iApply wp_fupd.
wp_apply (Conn.wp_confirm (server_clock N skA skB n ∗ P)
           with "[//] [//] [//] [$dis]").
{ by eauto. }
iIntros "%cs (conn & dis & rel & token)".
iMod (term_meta_set (isoN.@"conn".@"beg") n with "token")
  as "#meta"; first solve_ndisj.
iDestruct (or_sep2 with "dis") as "[dis P]".
iApply "post". by iFrame.
Qed.

Lemma wp_call N s φ ψ kI kR c cs n (ts : list term) :
  {{{ channel c ∗ cryptis_ctx ∗ ctx N ∗
      ([∗ list] t ∈ ts, public t) ∗
      rpc_pred N s φ ψ ∗
      client_connected N kI kR cs n ∗
      (compromised_session Init cs ∨ φ kI kR cs n ts) }}}
    call N s c (repr cs) (repr ts)
  {{{ ts', RET (repr ts');
      client_connected N kI kR cs (S n) ∗
      (compromised_session Init cs ∨ ψ kI kR cs n ts') ∗
      ([∗ list] t ∈ ts', public t) }}}.
Proof.
iIntros "%Φ (#? & #? & #? & #p_ts & #(? & ?) & conn & inv) post".
iDestruct "conn" as "(conn & rel & clock)".
wp_lam. wp_pure _ credit:"c". wp_pures.
iAssert (|==>
  compromised_session Init cs ∨
  client_clock N kI kR (S n) ∗ tick N kI kR n)%I
  with "[clock]" as ">clock".
{ iDestruct "clock" as "[?|[clock tock]]"; eauto.
  iMod (tock_tick with "clock tock") as "(_ & ?)"; eauto. }
rewrite or_sep2. iDestruct "clock" as "[clock tick]".
wp_apply (Conn.wp_write with "[//] [] [] [$conn tick inv]"); eauto.
{ iDestruct "inv" as "[(_ & ? & _)|inv]"; first by eauto.
  iDestruct "tick" as "[(_ & ? & _)|tick]"; first by eauto.
  iRight. iExists n. by iFrame. }
iIntros "conn". wp_pures. iApply wp_fupd.
wp_apply (Conn.wp_read with "[//] [] [$conn]"); eauto.
iIntros "%ts' (conn & p_ts' & inv)".
iApply "post". iDestruct "inv" as "[#inv|inv]".
{ iAssert (public (TKey Open (si_key cs))) as "?".
  { iApply public_TKey. by eauto. }
  iPoseProof (Conn.connected_public_key with "conn rel [//]") as "#>?".
  iFrame. iModIntro. iSplitR; eauto. }
iDestruct "inv" as "(%m & tock & inv)".
iFrame. iDestruct "clock" as "[#?|clock]".
{ iModIntro. iSplitL; eauto. }
iPoseProof (client_clock_tock with "clock tock") as "%e".
case: e => <-.
iModIntro. iSplitR "inv"; eauto.
iRight. iFrame.
Qed.

Definition wf_handler Φ kI kR cs N h : iProp :=
  Conn.wf_handler
    (∃ n,
        release_token (si_resp_share cs) ∗ Φ n ∗
        (compromised_session Resp cs ∨ server_clock N kI kR n))%I
    (λ r, ∃ n,
      ⌜r = #true⌝ ∗ Φ n ∗
      Conn.connected kI kR Resp cs ∗
      (compromised_session Resp cs ∨ server_clock N kI kR n) ∗
      release_token (si_resp_share cs) ∨
      ⌜r = #false⌝ ∗ Φ n ∗
      (compromised_session Resp cs ∨ server_clock N kI kR n) ∗
      public (si_key cs))%I
    kI kR Resp cs h.

Lemma wp_handle Φ N s φ₁ φ₂ kI kR c cs (f : val) :
  {{{
    channel c ∗
    rpc_pred N s φ₁ φ₂ ∗
    ctx N ∗
    □ (∀ n (ts : list term),
      {{{ ▷ ([∗ list] t ∈ ts, public t) ∗
          ▷ (compromised_session Resp cs ∨ φ₁ kI kR cs n ts) ∗
          Φ n }}}
        f (repr ts)
      {{{ ts', RET (repr ts');
          match ts' with
          | Some ts' => ([∗ list] t ∈ ts', public t) ∗
                        (compromised_session Resp cs ∨ φ₂ kI kR cs n ts')
          | None => True
          end ∗
          Φ (S n) }}})
  }}}
    handle N s c f
  {{{ h, RET (repr h); wf_handler Φ kI kR cs N h }}}.
Proof.
iIntros "%Ψ (#chan_c & (#? & #?) & #ctx & #wp_f) post".
iPoseProof (ctx_error with "[//]") as "#?".
wp_lam; wp_pures.
iApply Conn.wp_handle; last by eauto.
iSplit => //. clear Ψ.
iIntros "!> %ts !> %Ψ (conn & I & #p_ts & inv_ts) post".
iDestruct "I" as "(%n & rel & I & clock)". wp_pures.
iAssert (Conn.connected kI kR Resp cs ∗
         release_token (si_resp_share cs) ∗
         ◇ (compromised_session Resp cs ∨ call_pred N φ₁ kI kR cs ts))%I
  with "[conn rel inv_ts]" as "(conn & rel & >inv_ts)".
{ iDestruct "inv_ts" as "[#fail|inv_ts]"; last by iFrame.
  iAssert (public (TKey Open (si_key cs))) as "?".
  { iApply public_TKey. by eauto. }
  iPoseProof (Conn.connected_public_key with "conn rel [//]") as "#H".
  iFrame. iMod "H" as "?". by eauto. }
iAssert (|==>
           compromised_session Resp cs ∨
           server_clock N kI kR (S n) ∗
           φ₁ kI kR cs n ts ∗
           tock N kI kR (S n))%I
    with "[clock inv_ts]" as ">H".
{ iDestruct "clock" as "[?|clockS]"; first by eauto.
  iDestruct "inv_ts" as "[?|inv_ts]"; first by eauto.
  iDestruct "inv_ts" as "(%m & clockC & inv)".
  iMod (tick_tock with "clockS clockC") as "(-> & clockS & clockC)".
  iModIntro. iRight. by iFrame. }
iPoseProof (or_sep2 with "H") as "[clockS H]".
iPoseProof (or_sep2 with "H") as "[inv clockC]".
wp_apply ("wp_f" with "[$]"). iIntros "%ts' (inv_ts' & inv)".
case: ts' => [ts'|]; wp_pures; last first.
{ wp_list.
  wp_apply (Conn.wp_write with "[//] [] [] [$conn]") => //.
  { by rewrite /= public_TInt. }
  { by iRight. }
  iIntros "conn". wp_pures.
  iApply "post". iModIntro. iExists (S n). iLeft. by iFrame. }
iDestruct "inv_ts'" as "(#p_ts' & inv_ts')".
wp_apply (Conn.wp_write with "[//] [] [] [inv_ts' clockC $conn]") => //.
{ iDestruct "inv_ts'" as "[(_ & ? & _)|inv_ts']"; first by eauto.
  iDestruct "clockC" as "[(_ & ? & _)|clockC]"; first by eauto.
  iRight. iExists n. iFrame. }
iIntros "conn". wp_pures. iApply "post". iModIntro.
iExists (S n). iLeft. by iFrame.
Qed.

Lemma wp_handle_close Φ N c kI kR cs :
  {{{ channel c ∗ ctx N }}}
    handle_close N c
  {{{ h, RET (repr h); wf_handler Φ kI kR cs N h }}}.
Proof.
iIntros "%Ψ (#chan_c & #ctx) post". wp_lam; wp_pures.
wp_apply Conn.wp_handle; last by eauto. clear Ψ.
iPoseProof (ctx_close with "ctx") as "#?".
iPoseProof (ctx_ack_close with "ctx") as "#?".
iSplit => //.
iIntros "!> %ts !> %Ψ (conn & inv & #p_ts & #inv_ts) post".
iDestruct "inv" as "(%n & rel & inv & clockS)". wp_pures.
iMod (release with "rel") as "#relS".
iPoseProof (Conn.connected_released_session with "conn") as "#s_k".
iAssert (|==> public (si_key cs))%I as ">#p_k".
{ iDestruct "inv_ts" as "[?|relC]"; first by eauto.
  iIntros "!>". iApply "s_k". by iSplit. }
wp_pures. wp_list.
wp_apply (Conn.wp_write with "[//] [] [] [$conn]") => //.
- by rewrite /= public_TInt.
- by iLeft.
iIntros "conn". wp_pures. wp_apply (Conn.wp_free with "[$conn]").
iIntros "_". wp_pures. iApply "post".
iExists n. iModIntro. iFrame. iRight. by eauto.
Qed.

Lemma wp_server Φ N kI kR c cs n handlers :
  {{{ channel c ∗ ctx N ∗
      server_connected N kI kR cs n ∗ Φ n ∗
      [∗ list] h ∈ handlers, wf_handler Φ kI kR cs N h }}}
    server N c (repr cs) (repr handlers)
  {{{ RET #(); ∃ n', server_disconnected N kI kR n' ∗
                     public (si_key cs) ∗ Φ n' }}}.
Proof.
iLöb as "IH" forall (n).
iIntros "%Ψ (#chan_c & #ctx & conn & inv & #handlers) post".
iDestruct "conn" as "(conn & rel & clockS)".
iPoseProof (Conn.connected_keyE with "conn") as "#(-> & -> & _)".
wp_rec. wp_pures. wp_apply (wp_handle_close Φ N _ _ _ cs); eauto.
iIntros "%hc #wp_hc". wp_list.
iAssert ([∗ list] h ∈ (hc :: handlers), wf_handler Φ _ _ cs N h)%I
  as "#wp".
{ rewrite /=; iSplit => //. eauto. }
iClear "wp_hc". wp_bind (Conn.select _ _ _).
iApply (wp_wand with "[inv conn rel clockS]").
{ wp_apply (Conn.wp_select with "chan_c wp [$conn $rel $inv $clockS]"). }
iIntros "%res (%n' & Hres)".
iDestruct "Hres" as "[(-> & Hres)|(-> & Hres)]".
- iDestruct "Hres" as "(inv & conn & clockS & rel)". wp_pures.
  wp_apply ("IH" with "[$inv $clockS $rel $conn]") => //.
  by do !iSplit => //.
- iDestruct "Hres" as "(inv & clockS & rel)". wp_pures.
  iApply "post". iExists n'. iFrame. iModIntro.
  iDestruct "clockS" as "[?|clockS]"; last by iRight.
  iLeft. by iApply Conn.session_failed_failure.
Qed.

Lemma wp_close N c kI kR cs n :
  {{{ channel c ∗ ctx N ∗ client_connected N kI kR cs n }}}
    close N c (repr cs)
  {{{ RET #(); client_disconnected N kI kR n ∗ public (si_key cs) }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & conn) post".
iDestruct "conn" as "(conn & rel & clockC)".
iPoseProof (Conn.connected_keyE with "conn") as "#(-> & -> & _)".
wp_lam. wp_pures. wp_list.
iMod (release with "rel") as "#relC".
iPoseProof (ctx_close with "[//]") as "#?".
iPoseProof (ctx_ack_close with "[//]") as "#?".
wp_apply (Conn.wp_write with "[//] [] [] [$conn]") => //.
{ rewrite /= public_TInt. by eauto. }
{ by iRight. }
iIntros "conn". wp_pures.
wp_apply (Conn.wp_read with "[//] [] [$]"); eauto.
iIntros "%ts (conn & _ & #inv)".
wp_pures. wp_apply (Conn.wp_free with "[$conn]"). iIntros "_".
iApply "post". iDestruct "inv" as "[#p_k|[]]".
iSplit => //. iDestruct "clockC" as "[#comp|clockC]".
+ iLeft. by iApply Conn.session_failed_failure.
+ by iRight.
Qed.

End Proofs.

End Proofs.
