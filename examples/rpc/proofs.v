From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh conn.
From cryptis.examples.rpc Require impl.
From cryptis.examples.rpc.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !rpcGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : Conn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_connect P c skI skR :
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  minted skI -∗
  minted skR -∗
  {{{ Conn.failure skI skR ∨ P }}}
    impl.connect c skI (Spec.pkey skR)
  {{{ cs, RET (repr cs);
      client_connected skI skR cs ∗
      (compromised_session Init cs ∨ P) }}}.
Proof.
iIntros "#? #? #? #? #? % !> P post".
wp_lam; wp_pures.
iPoseProof (ctx_conn_ctx with "[//]") as "?".
iApply wp_fupd.
wp_apply (Conn.wp_connect with "[//] [//] [//] [] [] P"); eauto.
iIntros "%cs (connected & P & rel & token)".
iMod (resp_pred_token_alloc with "token") as "(t1 & t2 & token)";
  first solve_ndisj.
iApply ("post" $! cs). iFrame. iModIntro. iRight. by iFrame.
Qed.

Lemma wp_listen c :
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  {{{ True }}}
    impl.listen c
  {{{ ga skI, RET (ga, Spec.pkey skI)%V;
      public ga ∗ minted skI }}}.
Proof.
iIntros "#? #? #? % !> _ post".
wp_lam. iApply Conn.wp_listen => //.
by iApply ctx_conn_ctx.
Qed.

Lemma wp_confirm P c skI skR ga :
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  {{{ public ga ∗ minted skI ∗ minted skR ∗
      (Conn.failure skI skR ∨ P) }}}
    impl.confirm c skR (ga, Spec.pkey skI)%V
  {{{ cs, RET (repr cs);
      server_connected skI skR cs ∗
      (compromised_session Resp cs ∨ P) }}}.
Proof.
iIntros "#? #ctx #? !> %Φ (#p_ga & #m_skI & #m_skR & P) post".
wp_lam; wp_pures.
iPoseProof (ctx_conn_ctx with "[//]") as "?".
iApply wp_fupd.
wp_apply (Conn.wp_confirm P with "[//] [//] [//] [$P]").
{ by eauto. }
iIntros "%cs (conn & dis & rel & token)".
iApply "post". by iFrame.
Qed.

Lemma wp_call N φ ψ skI skR cs (ts : list term) :
  {{{ cryptis_ctx ∗ ctx ∗
      ([∗ list] t ∈ ts, public t) ∗
      rpc N φ ψ ∗
      client_connected skI skR cs ∗
      (compromised_session Init cs ∨ φ skI skR cs ts) }}}
    impl.call (repr cs) (Tag N) (repr ts)
  {{{ ts', RET (repr ts');
      client_connected skI skR cs ∗
      (compromised_session Init cs ∨ ψ skI skR cs ts ts') ∗
      ([∗ list] t ∈ ts', public t) }}}.
Proof.
iIntros "%Φ (#? & #? & #p_ts & #? & conn & inv) post".
iDestruct "conn" as "(conn & rel & resp_pred)".
iAssert (|==>
  (compromised_session Init cs ∨ resp_pred_token cs (ψ skI skR cs ts)) ∗
  (compromised_session Init cs ∨
     resp_pred_token cs (ψ skI skR cs ts) ∗
     φ skI skR cs ts))%I
  with "[resp_pred inv]" as ">[resp_pred inv]".
{ rewrite -or_sep2.
  iDestruct "resp_pred" as "[#fail|(t1 & t2)]"; eauto.
  iMod (resp_pred_token_update _ _ _ (ψ skI skR cs ts)
         with "t1 t2") as "[t1 t2]".
  iDestruct "inv" as "[#fail|inv]"; eauto.
  iModIntro. iRight. by iFrame. }
wp_lam. wp_pure _ credit:"c". wp_pures.
wp_apply (Conn.wp_send with "[] [] [$conn inv]"); eauto.
{ iDestruct "inv" as "[(_ & ? & _)|inv]"; first by eauto. iRight.
  by iFrame. }
iIntros "conn". wp_pures. iApply wp_fupd.
wp_apply (Conn.wp_recv with "[] [$conn]"); eauto.
{ by iApply ctx_resp. }
iIntros "%ts' (conn & p_ts' & inv)".
iApply "post".
iDestruct "inv" as "[#inv|inv]".
{ iPoseProof (Conn.connected_public_key with "conn rel [//]") as "#>?".
  iFrame. iModIntro. iSplitL; by eauto. }
iDestruct "resp_pred" as "[#fail|t1]".
{ iFrame. iModIntro. iSplitL; eauto. }
iDestruct "inv" as "(%ψ' & t2 & inv)".
iPoseProof (resp_pred_token_agree with "t1 t2") as "#E".
iSpecialize ("E" $! ts').
iMod (lc_fupd_elim_later_pers with "c E") as "{E} #E".
iRewrite "E".
iMod (resp_pred_token_update _ _ _ (λ _, False%I)
       with "t1 t2") as "ts".
by iFrame.
Qed.

Definition wf_handler Φ skI skR cs h : iProp :=
  Conn.wf_handler
    (release_token (si_resp_share cs) ∗ Φ)%I
    (λ r,
      ⌜r = #true⌝ ∗ Φ ∗
      Conn.connected skI skR Resp cs ∗
      release_token (si_resp_share cs) ∨
      ⌜r = #false⌝ ∗ Φ ∗
      public (si_key cs))%I
    skI skR Resp cs h.

Lemma wp_handle Φ N φ₁ φ₂ skI skR cs (f : val) :
  {{{
    rpc N φ₁ φ₂ ∗
    ctx ∗
    □ (∀ (ts : list term),
      {{{ ▷ ([∗ list] t ∈ ts, public t) ∗
          ▷ (compromised_session Resp cs ∨ φ₁ skI skR cs ts) ∗
          Φ }}}
        f (repr ts)
      {{{ ts', RET (repr ts');
          match ts' with
          | Some ts' => ([∗ list] t ∈ ts', public t) ∗
                        (compromised_session Resp cs ∨ φ₂ skI skR cs ts ts')
          | None => True
          end ∗
          Φ }}})
  }}}
    impl.handle (Tag N) f
  {{{ h, RET (repr h); wf_handler Φ skI skR cs h }}}.
Proof.
iIntros "%Ψ (#? & #ctx & #wp_f) post".
iPoseProof (ctx_error with "[//]") as "#?".
wp_lam; wp_pures.
iApply Conn.wp_handle; last by eauto.
iSplit => //. clear Ψ.
iIntros "!> %ts !> %Ψ (conn & I & #p_ts & inv_ts) post".
iDestruct "I" as "(rel & I)". wp_pures.
iAssert (Conn.connected skI skR Resp cs ∗
         release_token (si_resp_share cs) ∗
         ◇ (compromised_session Resp cs ∨
              resp_pred_token cs (φ₂ skI skR cs ts) ∗
              φ₁ skI skR cs ts))%I
  with "[conn rel inv_ts]" as "(conn & rel & >inv_ts)".
{ iDestruct "inv_ts" as "[#fail|inv_ts]"; last by iFrame.
  iPoseProof (Conn.connected_public_key with "conn rel [//]") as "#H".
  iFrame. iMod "H" as "?". by eauto. }
rewrite or_sep2. iDestruct "inv_ts" as "[resp_pred inv_ts]".
wp_apply ("wp_f" with "[$]"). iIntros "%ts' (inv_ts' & inv)".
case: ts' => [ts'|]; wp_pures; last first.
{ wp_list.
  wp_apply (Conn.wp_send with "[] [] [$conn]") => //.
  { by rewrite /= public_TInt. }
  { by iRight. }
  iIntros "conn". wp_pures.
  iApply "post". iModIntro. iLeft. by iFrame. }
iDestruct "inv_ts'" as "(#p_ts' & inv_ts')".
wp_apply (Conn.wp_send with "[] [] [inv_ts' resp_pred $conn]") => //.
{ by iApply ctx_resp. }
{ iDestruct "inv_ts'" as "[(_ & ? & _)|inv_ts']"; first by eauto.
  iDestruct "resp_pred" as "[(_ & ? & _)|resp_pred]"; first by eauto.
  iRight. iExists _. iFrame. }
iIntros "conn". wp_pures. iApply "post". iModIntro.
iLeft. by iFrame.
Qed.

Lemma wp_handle_close Φ skI skR cs :
  {{{ ctx }}}
    impl.handle_close
  {{{ h, RET (repr h); wf_handler Φ skI skR cs h }}}.
Proof.
iIntros "%Ψ #ctx post".
wp_apply Conn.wp_handle; last by eauto. clear Ψ.
iPoseProof (ctx_close with "ctx") as "#?".
iPoseProof (ctx_resp with "ctx") as "#?".
iSplit => //.
iIntros "!> %ts !> %Ψ (conn & inv & #p_ts & inv_ts) post".
iDestruct "inv" as "(rel & inv)". wp_pures.
iMod (release with "rel") as "#relS".
iPoseProof (Conn.connected_released_session with "conn") as "#s_k".
iAssert (|==> public (si_key cs))%I with "[inv_ts]" as ">#p_k".
{ iDestruct "inv_ts" as "[?|[_ relC]]"; first by eauto.
  iIntros "!>". iApply "s_k". by iSplit. }
wp_pures. wp_list.
wp_apply (Conn.wp_send with "[] [] [$conn]") => //.
- by rewrite /= public_TInt.
- by iLeft.
iIntros "conn". wp_pures. wp_apply (Conn.wp_free with "[$conn]").
iIntros "_". wp_pures. iApply "post".
iModIntro. iFrame. iRight. by eauto.
Qed.

Lemma wp_server Φ skI skR cs handlers :
  {{{ ctx ∗
      server_connected skI skR cs ∗ Φ ∗
      [∗ list] h ∈ handlers, wf_handler Φ skI skR cs h }}}
    impl.server (repr cs) (repr handlers)
  {{{ RET #(); public (si_key cs) ∗ Φ }}}.
Proof.
iLöb as "IH".
iIntros "%Ψ (#ctx & conn & inv & #handlers) post".
iDestruct "conn" as "(conn & rel)".
iPoseProof (Conn.connected_keyE with "conn") as "#(-> & -> & _)".
wp_rec. wp_pures. wp_apply (wp_handle_close Φ _ _ cs); eauto.
iIntros "%hc #wp_hc". wp_list.
iAssert ([∗ list] h ∈ (hc :: handlers), wf_handler Φ _ _ cs h)%I
  as "#wp".
{ rewrite /=; iSplit => //. eauto. }
iClear "wp_hc". wp_bind (Conn.select _ _).
iApply (wp_wand with "[inv conn rel]").
{ wp_apply (Conn.wp_select with "wp [$conn $rel $inv]"). }
iIntros "%res Hres".
iDestruct "Hres" as "[(-> & Hres)|(-> & Hres)]".
- iDestruct "Hres" as "(inv & conn & rel)". wp_pures.
  wp_apply ("IH" with "[$inv $rel $conn]") => //.
  by do !iSplit => //.
- iDestruct "Hres" as "(inv & rel)". wp_pures.
  iApply "post". by iFrame.
Qed.

Lemma wp_close skI skR cs :
  {{{ ctx ∗ client_connected skI skR cs }}}
    impl.close (repr cs)
  {{{ RET #(); public (si_key cs) }}}.
Proof.
iIntros "%Φ (#ctx & conn) post".
iDestruct "conn" as "(conn & rel & resp_pred)".
iPoseProof (Conn.connected_keyE with "conn") as "#(-> & -> & _)".
wp_lam. wp_pures. wp_list.
iMod (release with "rel") as "#relC".
iPoseProof (ctx_close with "[//]") as "#?".
iPoseProof (ctx_resp with "[//]") as "#?".
rewrite or_sep2. iDestruct "resp_pred" as "[t1 t2]".
wp_apply (Conn.wp_send with "[] [] [$conn t2]") => //.
{ rewrite /= public_TInt. by eauto. }
{ iDestruct "t2" as "[(_ & ? & _)|?]"; first by eauto.
  iRight. by iFrame. }
iIntros "conn". wp_pures.
wp_apply (Conn.wp_recv with "[] [$]"); eauto.
iIntros "%ts (conn & _ & inv)". wp_pure _ credit:"c".
wp_pures. iApply wp_fupd.
wp_apply (Conn.wp_free with "[$conn]"). iIntros "_".
iApply "post".
iDestruct "t1" as "[(_ & ? & _)|t1]"; eauto.
iDestruct "inv" as "[#p_k|(% & t2 & inv)]"; eauto.
iPoseProof (resp_pred_token_agree with "t1 t2") as "#E".
iSpecialize ("E" $! ts). iMod (lc_fupd_elim_later_pers with "c E") as "{E} #E".
iAssert False%I as "[]".
by iRewrite "E".
Qed.

End Proofs.
