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
iApply "post". iFrame.
iModIntro. iExists n. iSplit => //. by iPureIntro; lia.
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
iApply "post". iFrame. iExists n. iModIntro. iSplit; eauto. iPureIntro. lia.
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
iDestruct "conn" as "(%n1 & %n0 & -> & conn & #beg & rel & clock)".
wp_lam; wp_pures.
wp_apply (Conn.wp_write with "[//] [] [] [$conn clock inv]"); eauto.
{ iDestruct "inv" as "[?|inv]"; first by eauto.
  iDestruct "clock" as "[?|clock]"; first by eauto.
  iRight. iExists n0. by iFrame. }
iIntros "conn". wp_pures.
wp_apply (Conn.wp_read with "[//] [] [$conn $rel]"); eauto.
iIntros "%ts' (conn & rel & p_ts' & inv)".
iApply "post". iFrame. iDestruct "inv" as "[#inv|inv]".
{ iSplitR; eauto. iExists n0. iSplit; first by iPureIntro; lia.
  iSplit => //. by eauto. }
iDestruct "inv" as "(%n0' & #beg' & clock & inv)".
iPoseProof (term_meta_agree with "beg beg'") as "<-".
iFrame. iExists n0.
have -> : S (n0 + n1) = (n0 + S n1)%nat by lia.
iFrame. by eauto.
Qed.

Definition handler Φ kI kR cs N (handler : val) : iProp :=
  Conn.handler
    (λ n1 m, ∃ n0,
      ⌜m = n1⌝ ∗
      term_meta (si_resp_share cs) (isoN.@"conn".@"beg") n0 ∗
      Φ (n0 + n1) ∗
      (compromised_session Resp cs ∨ server_clock N kI kR (n0 + n1)))%I
    (λ n1 m r, ∃ n0,
      ⌜m = n1⌝ ∗
      term_meta (si_resp_share cs) (isoN.@"conn".@"beg") n0 ∗
      (⌜r = #true⌝ ∗
       Φ (S (n0 + n1)) ∗
       Conn.connected kI kR Resp cs (S n1) (S n1) ∗
       (compromised_session Resp cs ∨ server_clock N kI kR (S (n0 + n1))) ∗
       release_token (si_resp_share cs) ∨
       ⌜r = #false⌝ ∗
       Φ (n0 + n1) ∗
       (compromised_session Resp cs ∨ server_clock N kI kR (n0 + n1)) ∗
       released (si_resp_share cs)))%I
    kI kR Resp cs handler.

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
  {{{ h, RET h; handler Φ kI kR cs N h }}}.
Proof.
iIntros "%Ψ (#chan_c & (#? & #?) & #ctx & #wp_f) post".
iPoseProof (ctx_error with "[//]") as "#?".
wp_lam; wp_pures.
iApply (wp_wand with "[] post"). clear Ψ.
iApply Conn.wp_handle; last first.
{ iIntros "!> %h wp". iApply "wp". }
iSplit => //.
iIntros "!> %n1 %m %ts !> %Ψ (conn & rel & I & #p_ts & inv_ts) post".
iDestruct "I" as "(%n0 & -> & #begS & I & clock)". wp_pures.
iAssert (|==>
           compromised_session Resp cs ∨
           server_clock N kI kR (S (n0 + n1)) ∗
           φ₁ kI kR cs (n0 + n1) ts ∗
           term_meta (si_init_share cs) (isoN.@"conn".@"beg") n0 ∗
           client_clock N kI kR (S (n0 + n1)))%I
    with "[clock inv_ts]" as ">H".
{ iDestruct "clock" as "[?|clockS]"; first by eauto.
  iDestruct "inv_ts" as "[?|inv_ts]"; first by eauto.
  iDestruct "inv_ts" as "(%n0' & #begC & clockC & inv)".
  iMod (clocks_update with "clockC clockS") as "(%e_n' & clockS & clockC)".
  have <- : n0 = n0' by lia.
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
  iApply "post". iModIntro. iExists n0. do !iSplit => //. iLeft. by iFrame. }
iDestruct "inv_ts'" as "(#p_ts' & inv_ts')".
wp_apply (Conn.wp_write with "[//] [] [] [inv_ts' clockC $conn]") => //.
{ iDestruct "inv_ts'" as "[?|inv_ts']"; first by eauto.
  iDestruct "clockC" as "[?|[#begC clockC]]"; first by eauto.
  iRight. iExists n0. iFrame.
  have -> : n0 + S n1 = S (n0 + n1) by lia. by iFrame. }
iIntros "conn". wp_pures. iApply "post". iModIntro.
iExists n0. do !iSplit => //. iFrame. iLeft. by iFrame.
Qed.

Lemma wp_handle_close Φ N c kI kR cs :
  {{{ channel c ∗ ctx N }}}
    handle_close N c
  {{{ h, RET h; handler Φ kI kR cs N h }}}.
Proof.
iIntros "%Ψ (#chan_c & #ctx) post". wp_lam; wp_pures.
iApply (wp_wand with "[] post"). clear Ψ.
wp_apply Conn.wp_handle; last first.
{ iIntros "% wp". iApply "wp". }
iPoseProof (ctx_close with "ctx") as "#?".
iPoseProof (ctx_ack_close with "ctx") as "#?".
iSplit => //.
iIntros "!> %n1 %m %ts !> %Ψ (conn & rel & inv & #p_ts & inv_ts) post".
iDestruct "inv" as "(%n0 & -> & #begS & inv & clockS)". wp_pures.
iAssert (|==>
           compromised_session Resp cs ∨
           server_clock N kI kR (n0 + n1) ∗
           term_meta (si_init_share cs) (isoN.@"conn".@"beg") n0 ∗
           client_clock N kI kR (n0 + n1))%I
    with "[clockS inv_ts]" as ">H".
{ iDestruct "clockS" as "[?|clockS]"; first by eauto.
  iDestruct "inv_ts" as "[?|inv_ts]"; first by eauto.
  iDestruct "inv_ts" as "(%n0' & #begC & clockC)".
  iPoseProof (clocks_agree with "clockC clockS") as "%e_n'".
  have <- : n0 = n0' by lia.
  iModIntro. iRight. by iFrame. }
wp_pures.
iPoseProof (or_sep2 with "H") as "[clockS clockC]".
iMod (release with "rel") as "#rel".
wp_list.
wp_apply (Conn.wp_write with "[//] [] [] [clockC $conn]") => //.
- by rewrite /= public_TInt.
- iDestruct "clockC" as "[?|[#begC clockC]]"; first by eauto.
  iRight. iExists n0. iFrame. by eauto.
iIntros "conn". wp_pures. wp_apply (Conn.wp_free with "[$conn]").
iIntros "_". wp_pures. iApply "post".
iExists n0. iModIntro. do !iSplit => //.
iFrame. iRight. iFrame. by eauto.
Qed.

Lemma wp_server Φ N kI kR c cs n handlers :
  {{{ channel c ∗ ctx N ∗
      server_connected N kI kR cs n ∗ Φ n ∗
      [∗ list] h ∈ handlers, handler Φ kI kR cs N h }}}
    server N c (repr cs) (repr handlers)
  {{{ RET #(); ∃ n', server_disconnected N kI kR n' ∗ Φ n' }}}.
Proof.
iLöb as "IH" forall (n).
iIntros "%Ψ (#chan_c & #ctx & conn & inv & #handlers) post".
iDestruct "conn" as "(%n1 & %n0 & -> & conn & #beg & rel & clockS)".
iPoseProof (Conn.connected_keyE with "conn") as "#(-> & -> & _)".
wp_rec. wp_pures. wp_apply (wp_handle_close Φ N _ _ _ cs); eauto.
iIntros "%hc #wp_hc". wp_apply (@wp_cons val _ _ _ _ hc).
iAssert ([∗ list] h ∈ (hc :: handlers), handler Φ _ _ cs N h)%I
  as "#wp".
{ rewrite /=; iSplit => //. eauto. }
iClear "wp_hc". wp_bind (Conn.select _ _ _).
iApply (wp_wand with "[inv conn rel clockS]").
{ wp_apply (Conn.wp_select with "chan_c wp [$conn $rel $inv $clockS]").
  by eauto. }
iIntros "%res (%n0' & _ & #beg' & Hres)".
iPoseProof (term_meta_agree with "beg beg'") as "<-".
iDestruct "Hres" as "[(-> & Hres)|(-> & Hres)]".
- iDestruct "Hres" as "(inv & conn & clockS & rel)". wp_pures.
  wp_apply ("IH" with "[$inv $clockS $rel $conn]") => //.
  do !iSplit => //. iExists n0. iSplit => //.
  iPureIntro. lia.
- iDestruct "Hres" as "(inv & clockS & rel)". wp_pures.
  iApply "post". iExists (n0 + n1). iFrame. iModIntro.
  iDestruct "clockS" as "[?|clockS]"; last by iRight.
  iLeft. by iApply Conn.session_failed_failure.
Qed.

Lemma wp_close N c kI kR cs n :
  {{{ channel c ∗ ctx N ∗ client_connected N kI kR cs n }}}
    close N c (repr cs)
  {{{ RET #(); client_disconnected N kI kR n ∗ public (si_key cs) }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & conn) post".
iDestruct "conn" as "(%n1 & %n0 & -> & conn & #beg & rel & clockC)".
iPoseProof (Conn.connected_keyE with "conn") as "#(-> & -> & _)".
wp_lam. wp_pures. wp_list.
iPoseProof (Conn.connected_released_session with "conn") as "#p_k".
iPoseProof (ctx_close with "[//]") as "#?".
iPoseProof (ctx_ack_close with "[//]") as "#?".
wp_apply (Conn.wp_write with "[//] [] [] [$conn clockC]") => //.
{ rewrite /= public_TInt. by eauto. }
{ iDestruct "clockC" as "[?|clockC]"; eauto.
  iRight. iExists n0. by iFrame. }
iIntros "conn". wp_pures.
wp_apply (Conn.wp_read with "[//] [] [$]") => //.
iIntros "%ts (conn & rel & _ & inv)".
wp_pures. iMod (release with "rel") as "#relC".
wp_apply (Conn.wp_free with "[$conn]"). iIntros "_".
iApply "post". iDestruct "inv" as "[#comp|inv]".
- iSplit.
  + iLeft. by iApply Conn.session_failed_failure.
  + by iDestruct "comp" as "(_ & ? & _)".
- iDestruct "inv" as "(%n0' & #beg' & clockC & #relS)".
  iPoseProof (term_meta_agree with "beg beg'") as "<-".
  iSplit.
  + by iRight.
  + iApply "p_k". by iSplit.
Qed.

End Proofs.

End Proofs.
