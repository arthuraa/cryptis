From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn conn.
From cryptis.examples.rpc Require impl.
From cryptis.examples.rpc.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record handler := Handler {
  handler_val : val;
}.

Instance repr_handler : Repr handler := handler_val.

Section Proofs.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ, !rpcGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Notation rpcN := (nroot.@"rpc").

Lemma wp_connect P c skI skR :
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  minted skI -∗
  minted skR -∗
  {{{ GenConn.failure skI skR ∨ P }}}
    impl.connect c skI (Spec.pkey skR)
  {{{ cs, RET (repr cs);
      client_connected skI skR cs ∗
      (compromised cs ∨ P) }}}.
Proof.
iIntros "#? #? [#? #?] #? #? % !> P post".
wp_lam; wp_pures. iApply wp_fupd.
wp_apply (Conn.wp_connect with "[] [P]"); eauto 10.
iIntros "%cs (connected & P & rel & token)".
iMod (resp_pred_token_alloc with "token") as "(t1 & t2 & token)";
  first solve_ndisj.
iApply ("post" $! cs).
iPoseProof (Conn.connected_public_key_or with "connected rel P")
  as "(connected & rel & >P)".
iFrame. iModIntro. iRight. by iFrame.
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
iIntros "#? #? [#? #?] % !> _ post".
wp_lam. by iApply Conn.wp_listen.
Qed.

Lemma wp_confirm P c skI skR ga :
  channel c -∗
  cryptis_ctx -∗
  ctx -∗
  {{{ public ga ∗ minted skI ∗ minted skR ∗
      (GenConn.failure skI skR ∨ P) }}}
    impl.confirm c skR (ga, Spec.pkey skI)%V
  {{{ cs, RET (repr cs);
      server_connected skI skR cs ∗
      (compromised cs ∨ P) }}}.
Proof.
iIntros "#? #ctx1 [#? #ctx2] !> %Φ (#p_ga & #m_skI & #m_skR & P) post".
wp_lam; wp_pures. iApply wp_fupd.
wp_apply (Conn.wp_confirm P with "[] [$P]").
- eauto.
- eauto.
iIntros "%cs (conn & dis & rel & token)".
iPoseProof (Conn.connected_public_key_or with "conn rel dis")
  as "(conn & rel & >dis)".
iApply "post". by iFrame.
Qed.

Lemma wp_call_gen N φ ψ skI skR cs t :
  {{{ cryptis_ctx ∗ ctx ∗ public t ∗
      rpc_pred N φ ψ ∗
      connected skI skR Init cs ∗
      client_tokens cs ∗
      (public (si_key cs) ∨ φ skI skR cs t) }}}
    impl.call (repr cs) (Tag N) t
  {{{ t', RET (repr t');
      connected skI skR Init cs ∗
      client_tokens cs ∗
      (public (si_key cs) ∨ ψ skI skR cs t t') ∗
      public t' }}}.
Proof.
iIntros "%Φ (#? & #ctx & #p_t & #N & conn & resp_pred & inv) post".
iDestruct "ctx" as "[? ctx]".
iAssert (|==>
  (public (si_key cs) ∨ resp_pred_token cs N t) ∗
  (public (si_key cs) ∨
     resp_pred_token cs N t ∗ φ skI skR cs t))%I
  with "[resp_pred inv]" as ">[resp_pred inv]".
{ rewrite -or_sep2.
  iDestruct "resp_pred" as "[#fail|(t1 & t2)]"; eauto.
  iMod (resp_pred_token_update cs N t with "t1 t2") as "[t1 t2]".
  iDestruct "inv" as "[#fail|inv]"; eauto.
  iModIntro. iRight. by iFrame. }
wp_lam. wp_pure _ credit:"c". wp_pures. wp_tag.
wp_apply (Conn.wp_send with "[] [] [$conn inv]"); eauto.
{ by rewrite public_tag. }
{ iDestruct "inv" as "[?|[??]]"; first by eauto. iRight.
  iExists N, t, φ, ψ. iSplit => //. by iFrame. }
iIntros "conn". wp_pures. iApply wp_fupd.
wp_apply (Conn.wp_recv with "[] [$conn]"); eauto.
iIntros "%t' (conn & p_t' & inv)".
iApply "post".
iDestruct "inv" as "[#inv|inv]".
{ iFrame. iModIntro. iSplitL; iLeft; by eauto. }
iDestruct "resp_pred" as "[#fail|t1]".
{ iFrame. iModIntro. iSplitL; iLeft; by eauto. }
iDestruct "inv" as "(%N' & %t₀ & %φ' & %ψ' & #N' & inv & t2)".
iPoseProof (resp_pred_token_agree with "t1 t2") as "[<- <-]".
iPoseProof (rpc_pred_agree with "N N'") as "[_ E]".
iMod (lc_fupd_elim_later_pers with "c E") as "{E} #E".
iRewrite ("E" $! skI skR cs t t').
iMod (resp_pred_token_update _ rpcN (TInt 0)
       with "t1 t2") as "t".
by iFrame.
Qed.

Lemma wp_call N φ ψ skI skR cs t :
  {{{ cryptis_ctx ∗ ctx ∗ public t ∗
      rpc_pred N φ ψ ∗
      client_connected skI skR cs ∗
      (compromised cs ∨ φ skI skR cs t) }}}
    impl.call (repr cs) (Tag N) t
  {{{ t', RET (repr t');
      client_connected skI skR cs ∗
      (compromised cs ∨ ψ skI skR cs t t') ∗
      public t' }}}.
Proof.
iIntros "%Φ (#? & #ctx & #p_t & #N & (conn & rel & tok) & inv) post".
rewrite [in (_ ∨ φ _ _ _ _)%I]compromised_public.
iApply wp_fupd.
wp_apply (wp_call_gen with "[$conn $tok $inv]"); first by eauto.
iIntros "%t' (conn & tok & res & #p_t')".
iDestruct (Conn.connected_public_key_or with "conn rel res")
  as "(conn & rel & >res)".
iModIntro. iApply "post". by iFrame.
Qed.

Definition wf_handler Φ skI skR cs (h : handler) : iProp :=
  □ ∀ t,
    {{{ public t ∗
        (public (si_key cs) ∨ rpc_msg_pred skI skR cs Init t) ∗
        server_connected skI skR cs ∗
        Φ }}}
      repr h (repr cs) t
    {{{ ob, RET (repr ob);
        match ob : option bool with
        | Some true =>
            Φ ∗ server_connected skI skR cs
        | Some false => Φ ∗ public (si_key cs)
        | None =>
            Φ ∗ server_connected skI skR cs ∗
            (public (si_key cs) ∨ rpc_msg_pred skI skR cs Init t)
        end
    }}}.

Typeclasses Opaque wf_handler.

Instance persistent_wf_handler Φ skI skR cs h :
  Persistent (wf_handler Φ skI skR cs h).
Proof. rewrite /wf_handler. apply _. Qed.

Lemma wp_handle_gen Φ N φ ψ skI skR cs (f : val) :
  {{{
    rpc_pred N φ ψ ∗
    ctx ∗
    □ (∀ t : term,
      {{{ ▷ public t ∗
          ▷ (compromised cs ∨ φ skI skR cs t) ∗
          release_token (si_resp_share cs) ∗
          Φ }}}
        f (repr t)
      {{{ ores, RET (repr ores);
          match ores : option (bool * term) with
          | Some (continue, t') =>
              public t' ∗
              if continue then
                (public (si_key cs) ∨ ψ skI skR cs t t') ∗
                release_token (si_resp_share cs)
              else public (si_key cs) ∨ released_session cs
          | None => release_token (si_resp_share cs)
          end ∗
          Φ }}})
  }}}
    impl.handle_gen (Tag N) f
  {{{ h, RET (repr h); wf_handler Φ skI skR cs h }}}.
Proof.
iIntros "%Ξ (#N & #ctx & #wp) post". wp_lam. wp_pures.
iDestruct "ctx" as "(#? & #?)".
iIntros "!>". iApply ("post" $! (Handler _)). clear Ξ.
rewrite /wf_handler.
iIntros "!> %t !> %Ξ (#p_t & inv_t & (conn & rel) & inv) post".
wp_pure _ credit:"c1".
wp_pures. wp_untag t; wp_pures; last by iApply ("post" $! None); iFrame.
iAssert (|={⊤}=> (
  connected skI skR Resp cs ∗
  release_token (si_resp_share cs) ∗
  (public (si_key cs) ∨ resp_pred_token cs N t ∗ φ skI skR cs t)))%I
  with "[c1 conn rel inv_t]" as ">(conn & rel & inv_t)".
{ iDestruct "inv_t" as "[#fail|inv_t]".
  { iPoseProof (Conn.connected_public_key with "conn rel fail") as "#>?".
    iFrame. by eauto. }
  iFrame.
  iDestruct "inv_t" as "(%N' & %t' & %φ' & %ψ' & %e & #N' & inv_t & token)".
  case/Spec.tag_inj: e => /Tag_inj <- <- {N' t'}.
  iPoseProof (rpc_pred_agree with "N N'") as "[E _]".
  iMod (lc_fupd_elim_later_pers with "c1 E") as "{E} #E".
  iRewrite ("E" $! skI skR cs t). iRight. by iFrame. }
rewrite public_tag or_sep2. iDestruct "inv_t" as "[t inv_t]".
iPoseProof (Conn.connected_public_key_or with "conn rel inv_t")
  as "(conn & rel & >inv_t)".
wp_apply ("wp" with "[$inv $rel inv_t]").
{ iSplit => //. }
iIntros ([[continue t']|]) "[res inv]"; wp_pures; last first.
{ by iApply ("post" $! (Some true)); iFrame. }
iDestruct "res" as "(#p_t' & inv_t')".
iPoseProof (Conn.connected_released_session with "conn") as "#sess".
iAssert ((if continue then (public (si_key cs) ∨ ψ skI skR cs t t')
          else public (si_key cs)) ∗
         (if continue then release_token (si_resp_share cs) else public (si_key cs)))%I
  with "[inv_t']" as "[inv_t' rel]".
{ case: continue; eauto.
  iDestruct "inv_t'" as "[?|inv_t']"; eauto.
  iSplit; iApply "sess"; eauto. }
wp_apply (Conn.wp_send with "[] p_t' [$conn t inv_t']"); eauto.
{ iDestruct "t" as "[?|t]"; eauto.
  case: continue; eauto.
  iDestruct "inv_t'" as "[?|inv_t']"; eauto.
  iRight. iExists _, _, _, _. iFrame. by iFrame "#". }
iIntros "conn". wp_pures.
case: continue; wp_pures.
- by iApply ("post" $! (Some true)); iFrame.
- wp_apply (Conn.wp_free with "conn"). iIntros "_". wp_pures.
  iApply ("post" $! (Some false)). by eauto.
Qed.

Lemma wp_handle Φ N φ ψ skI skR cs (f : val) :
  {{{
    rpc_pred N φ ψ ∗
    ctx ∗
    □ (∀ t : term,
      {{{ ▷ public t ∗
          ▷ (compromised cs ∨ φ skI skR cs t) ∗
          Φ }}}
        f (repr t)
      {{{ ot', RET (repr ot');
          match ot' : option term with
          | Some t' =>
              public t' ∗
              (compromised cs ∨ ψ skI skR cs t t')
          | None => True
          end ∗
          Φ }}})
  }}}
    impl.handle (Tag N) f
  {{{ h, RET (repr h); wf_handler Φ skI skR cs h }}}.
Proof.
iIntros "%Ξ (#N & #ctx & #wp) post". wp_lam. wp_pures.
iApply wp_handle_gen; last by eauto.
do 2![iSplit; eauto]. clear Ξ.
iIntros "!> %t %Ξ !> (#p_t & inv_t & rel & inv) post".
wp_pures.
wp_apply ("wp" with "[$inv_t $inv]") => //.
iIntros ([t'|]) "[ot' inv]"; wp_pures; last by iApply ("post" $! None); iFrame.
iApply ("post" $! (Some (true, t'))). iClear "wp".
rewrite compromised_public. by iFrame.
Qed.

Lemma wp_handle_close Φ skI skR cs :
  {{{ ctx }}}
    impl.handle_close
  {{{ h, RET (repr h); wf_handler Φ skI skR cs h }}}.
Proof.
iIntros "%Ξ #ctx post".
wp_apply wp_handle_gen; last by eauto.
iSplit; first by iDestruct "ctx" as "[??]".
iSplit; eauto. clear Ξ.
iIntros "!> %t %Ξ !> (#p_t & #inv_t & rel & inv) post".
iMod (release with "rel") as "#?".
wp_pures. iApply ("post" $! (Some (false, _))). iFrame.
iModIntro. iSplit; eauto.
rewrite compromised_public.
iDestruct "inv_t" as "[?|inv_t]"; eauto.
iRight. by iSplit.
Qed.

Lemma wp_select Φ skI skR cs handlers :
  {{{ ctx ∗
      server_connected skI skR cs ∗
      Φ ∗
      [∗ list] h ∈ handlers, wf_handler Φ skI skR cs h }}}
    impl.select (repr cs) (repr handlers)
  {{{ ob, RET (repr ob);
      match ob with
      | Some false => Φ ∗ public (si_key cs)
      | _ => Φ ∗ server_connected skI skR cs
      end }}}.
Proof.
iIntros "%Ψ (#ctx & (conn & rel) & inv & #wp_handlers) post".
wp_lam. wp_pures. iPoseProof "ctx" as "[??]".
wp_apply (Conn.wp_recv with "[//] [$]").
iIntros "%m (conn & #p_m & inv_m)". wp_pures.
wp_apply (wp_handle_close Φ skI skR cs); eauto.
iIntros "%h #wp_h". wp_list. wp_pures.
iApply (wp_wand _ _ _ (λ v,
  ∃ ob : option bool,
    ⌜v = repr ob⌝ ∗
    match ob with
    | Some true => Φ ∗ server_connected skI skR cs
    | Some false => Φ ∗ public (si_key cs)
    | None => Φ ∗ server_connected skI skR cs ∗
              (public (si_key cs) ∨ rpc_msg_pred skI skR cs Init m)
    end) with "[rel inv conn inv_m] [post]")%I; last first.
{ iIntros "% (% & -> & H)". iApply "post".
  case: ob => [[]|]; eauto.
  by iDestruct "H" as "(?&?&?)"; iFrame. }
clear Ψ.
wp_apply (wp_scan_list (wf_handler Φ skI skR cs) with "[]"); last first.
{ iSplit => //=; eauto. iExists None. by iFrame. }
iClear "wp_handlers wp_h". clear h.
iIntros "!> %h %Ψ !> ((%ob & %e & inv) & #wp_h) post".
case: ob => [[]|] //= in e *.
iDestruct "inv" as "(inv & (conn & rel) & inv_m)".
wp_pures. rewrite /wf_handler.
iApply ("wp_h" with "[$conn $rel $inv_m $inv]") => //.
iIntros "!> %ob H".
have -> : repr ob = repr (((λ b : bool, #b) <$> ob)).
  by case: ob => [[]|].
iApply "post". iExists ob. iFrame.
by case: ob => [[]|].
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
wp_rec. wp_pures. wp_apply (wp_select with "[$conn inv]").
{ by iFrame "#". }
iIntros "%ob H". wp_pures.
case: ob => [[]|]; wp_pures.
- iDestruct "H" as "[inv server]".
  by iApply ("IH" with "[$] post").
- iDestruct "H" as "[inv #?]". iApply "post". by iFrame.
- iDestruct "H" as "[inv server]".
  by iApply ("IH" with "[$] post").
Qed.

Lemma wp_close skI skR cs :
  {{{ cryptis_ctx ∗ ctx ∗ client_connected skI skR cs }}}
    impl.close (repr cs)
  {{{ RET #(); public (si_key cs) }}}.
Proof.
iIntros "%Φ (#? & #ctx & conn & rel & tok) post".
iMod (release with "rel") as "#rel". wp_lam.
iPoseProof "ctx" as "[? ?]".
wp_apply (wp_call_gen with "[$conn $tok]").
{ rewrite public_TInt. do ![iSplit; eauto]. }
iIntros "% (conn & tok & [#? | []] & _)".
wp_pures. wp_apply (Conn.wp_free with "conn"). iIntros "_".
by iApply "post".
Qed.

End Proofs.
