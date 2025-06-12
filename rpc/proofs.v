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

Lemma wp_connect P c kI kR :
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  sign_key kI -∗
  public (TKey Open kR) -∗
  {{{ Conn.failure kI kR ∨ P }}}
    Impl.connect c kI (TKey Open kR)
  {{{ cs, RET (repr cs);
      client_connected kI kR cs ∗
      (compromised_session Init cs ∨ P) }}}.
Proof.
iIntros "#? #? #? #? #? % !> P post".
wp_lam; wp_pures.
iPoseProof (Props.ctx_conn_ctx with "[//]") as "?".
iApply wp_fupd.
wp_apply (Conn.wp_connect with "[//] [//] [//] [//] [//] P").
iIntros "%cs (connected & P & rel & token)".
iApply "post". by iFrame.
Qed.

Lemma wp_listen c :
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  {{{ True }}}
    listen c
  {{{ ga skA, RET (ga, TKey Open skA)%V;
      public ga ∗ public (TKey Open skA) }}}.
Proof.
iIntros "#? #? #? % !> _ post".
wp_lam. iApply Conn.wp_listen => //.
by iApply Props.ctx_conn_ctx.
Qed.

Lemma wp_confirm P c skA skB ga :
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  {{{ public ga ∗ public (TKey Open skA) ∗ sign_key skB ∗
      (Conn.failure skA skB ∨ P) }}}
    confirm c skB (ga, TKey Open skA)%V
  {{{ cs, RET (repr cs);
      server_connected skA skB cs ∗
      (compromised_session Resp cs ∨ P) }}}.
Proof.
iIntros "#? #ctx #? !> %Φ (#p_ga & #p_vkA & #sign_skB & P) post".
wp_lam; wp_pures.
iPoseProof (Props.ctx_conn_ctx with "[//]") as "?".
iApply wp_fupd.
wp_apply (Conn.wp_confirm P with "[//] [//] [//] [$P]").
{ by eauto. }
iIntros "%cs (conn & dis & rel & token)".
iApply "post". by iFrame.
Qed.

Lemma wp_call N s φ ψ kI kR c cs (ts : list term) :
  {{{ channel c ∗ cryptis_ctx ∗ ctx ∗
      ([∗ list] t ∈ ts, public t) ∗
      rpc_pred N s φ ψ ∗
      client_connected kI kR cs ∗
      (compromised_session Init cs ∨ φ kI kR cs ts) }}}
    call N s c (repr cs) (repr ts)
  {{{ ts', RET (repr ts');
      client_connected kI kR cs ∗
      (compromised_session Init cs ∨ ψ kI kR cs ts') ∗
      ([∗ list] t ∈ ts', public t) }}}.
Proof.
iIntros "%Φ (#? & #? & #? & #p_ts & #(? & ?) & conn & inv) post".
iDestruct "conn" as "(conn & rel)".
wp_lam. wp_pure _ credit:"c". wp_pures.
wp_apply (Conn.wp_write with "[//] [] [] [$conn inv]"); eauto.
{ iDestruct "inv" as "[(_ & ? & _)|inv]"; first by eauto. by iRight. }
iIntros "conn". wp_pures. iApply wp_fupd.
wp_apply (Conn.wp_read with "[//] [] [$conn]"); eauto.
iIntros "%ts' (conn & p_ts' & inv)".
iApply "post". iDestruct "inv" as "[#inv|inv]".
{ iAssert (public (TKey Open (si_key cs))) as "?".
  { iApply public_TKey. by eauto. }
  iPoseProof (Conn.connected_public_key with "conn rel [//]") as "#>?".
  iFrame. iModIntro. by eauto. }
by iFrame.
Qed.

Definition wf_handler Φ kI kR cs h : iProp :=
  Conn.wf_handler
    (release_token (si_resp_share cs) ∗ Φ)%I
    (λ r,
      ⌜r = #true⌝ ∗ Φ ∗
      Conn.connected kI kR Resp cs ∗
      release_token (si_resp_share cs) ∨
      ⌜r = #false⌝ ∗ Φ ∗
      public (si_key cs))%I
    kI kR Resp cs h.

Lemma wp_handle Φ N s φ₁ φ₂ kI kR c cs (f : val) :
  {{{
    channel c ∗
    rpc_pred N s φ₁ φ₂ ∗
    ctx ∗
    □ (∀ (ts : list term),
      {{{ ▷ ([∗ list] t ∈ ts, public t) ∗
          ▷ (compromised_session Resp cs ∨ φ₁ kI kR cs ts) ∗
          Φ }}}
        f (repr ts)
      {{{ ts', RET (repr ts');
          match ts' with
          | Some ts' => ([∗ list] t ∈ ts', public t) ∗
                        (compromised_session Resp cs ∨ φ₂ kI kR cs ts')
          | None => True
          end ∗
          Φ }}})
  }}}
    handle N s c f
  {{{ h, RET (repr h); wf_handler Φ kI kR cs h }}}.
Proof.
iIntros "%Ψ (#chan_c & (#? & #?) & #ctx & #wp_f) post".
iPoseProof (ctx_error with "[//]") as "#?".
wp_lam; wp_pures.
iApply Conn.wp_handle; last by eauto.
iSplit => //. clear Ψ.
iIntros "!> %ts !> %Ψ (conn & I & #p_ts & inv_ts) post".
iDestruct "I" as "(rel & I)". wp_pures.
iAssert (Conn.connected kI kR Resp cs ∗
         release_token (si_resp_share cs) ∗
         ◇ (compromised_session Resp cs ∨ φ₁ kI kR cs ts))%I
  with "[conn rel inv_ts]" as "(conn & rel & >inv_ts)".
{ iDestruct "inv_ts" as "[#fail|inv_ts]"; last by iFrame.
  iAssert (public (TKey Open (si_key cs))) as "?".
  { iApply public_TKey. by eauto. }
  iPoseProof (Conn.connected_public_key with "conn rel [//]") as "#H".
  iFrame. iMod "H" as "?". by eauto. }
wp_apply ("wp_f" with "[$]"). iIntros "%ts' (inv_ts' & inv)".
case: ts' => [ts'|]; wp_pures; last first.
{ wp_list.
  wp_apply (Conn.wp_write with "[//] [] [] [$conn]") => //.
  { by rewrite /= public_TInt. }
  { by iRight. }
  iIntros "conn". wp_pures.
  iApply "post". iModIntro. iLeft. by iFrame. }
iDestruct "inv_ts'" as "(#p_ts' & inv_ts')".
wp_apply (Conn.wp_write with "[//] [] [] [inv_ts' $conn]") => //.
{ iDestruct "inv_ts'" as "[(_ & ? & _)|inv_ts']"; first by eauto.
  by eauto. }
iIntros "conn". wp_pures. iApply "post". iModIntro.
iLeft. by iFrame.
Qed.

Lemma wp_handle_close Φ c kI kR cs :
  {{{ channel c ∗ ctx }}}
    handle_close c
  {{{ h, RET (repr h); wf_handler Φ kI kR cs h }}}.
Proof.
iIntros "%Ψ (#chan_c & #ctx) post". wp_lam; wp_pures.
wp_apply Conn.wp_handle; last by eauto. clear Ψ.
iPoseProof (ctx_close with "ctx") as "#?".
iPoseProof (ctx_ack_close with "ctx") as "#?".
iSplit => //.
iIntros "!> %ts !> %Ψ (conn & inv & #p_ts & #inv_ts) post".
iDestruct "inv" as "(rel & inv)". wp_pures.
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
iModIntro. iFrame. iRight. by eauto.
Qed.

Lemma wp_server Φ kI kR c cs handlers :
  {{{ channel c ∗ ctx ∗
      server_connected kI kR cs ∗ Φ ∗
      [∗ list] h ∈ handlers, wf_handler Φ kI kR cs h }}}
    server c (repr cs) (repr handlers)
  {{{ RET #(); public (si_key cs) ∗ Φ }}}.
Proof.
iLöb as "IH".
iIntros "%Ψ (#chan_c & #ctx & conn & inv & #handlers) post".
iDestruct "conn" as "(conn & rel)".
iPoseProof (Conn.connected_keyE with "conn") as "#(-> & -> & _)".
wp_rec. wp_pures. wp_apply (wp_handle_close Φ _ _ _ cs); eauto.
iIntros "%hc #wp_hc". wp_list.
iAssert ([∗ list] h ∈ (hc :: handlers), wf_handler Φ _ _ cs h)%I
  as "#wp".
{ rewrite /=; iSplit => //. eauto. }
iClear "wp_hc". wp_bind (Conn.select _ _ _).
iApply (wp_wand with "[inv conn rel]").
{ wp_apply (Conn.wp_select with "chan_c wp [$conn $rel $inv]"). }
iIntros "%res Hres".
iDestruct "Hres" as "[(-> & Hres)|(-> & Hres)]".
- iDestruct "Hres" as "(inv & conn & rel)". wp_pures.
  wp_apply ("IH" with "[$inv $rel $conn]") => //.
  by do !iSplit => //.
- iDestruct "Hres" as "(inv & rel)". wp_pures.
  iApply "post". by iFrame.
Qed.

Lemma wp_close c kI kR cs :
  {{{ channel c ∗ ctx ∗ client_connected kI kR cs }}}
    close c (repr cs)
  {{{ RET #(); public (si_key cs) }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & conn) post".
iDestruct "conn" as "(conn & rel)".
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
iApply "post". by iDestruct "inv" as "[#p_k|[]]".
Qed.

End Proofs.

End Proofs.
