From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta cryptis primitives tactics.
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
Lemma wp_do_until' E (f : val) (φ : val → iProp) :
  □ WP f #() @ E {{ v, ⌜v = NONEV⌝ ∨ (∃ v', ⌜v = SOMEV v'⌝ ∗ φ v') }} -∗
  WP do_until f @ E {{ φ }}.
Proof.
iIntros "#wp_f".
iAssert True%I as "I" => //.
iRevert "I".
iApply wp_do_until.
iIntros "!> _".
iApply wp_wand; eauto.
iIntros "%v [->|post]"; eauto.
Qed.

Lemma connected_public_key kI kR cs n n0 kt :
  connected kI kR cs n n0 -∗
  public (TKey kt (si_key cs)) -∗
  ▷ session_failed cs true.
Proof.
iIntros "conn #p_k".
iPoseProof "conn" as "(_ & _ & #sess & _ & rel & _ & #failed & _)".
iDestruct "sess" as "(#? & #s_key & #sess)".
iPoseProof (senc_key_compromised_keyI with "s_key p_k") as "{p_k} p_k".
iPoseProof (senc_key_compromised_keyE with "s_key p_k") as "{p_k} >p_k".
iDestruct "failed" as "(%failed & failed)".
case: failed => //.
iDestruct "failed" as "[[_ #s_k] _]".
iPoseProof ("s_k" with "p_k") as "{p_k} >p_k".
by iDestruct (release_token_released_session with "rel p_k") as "[]".
Qed.
(* /MOVE *)

Lemma public_sencE N cs m φ rl failed :
  public (TSeal (TKey Seal (si_key cs)) (Spec.tag N m)) -∗
  seal_pred N (session_msg_pred φ rl) -∗
  ⌜cs_role cs = swap_role rl⌝ -∗
  wf_sess_info cs -∗
  session_failed_for cs (cs_role cs) failed -∗
  release_token (cs_share cs) -∗ ▷ □ ∃ failed' : bool,
  ⌜failed → failed'⌝ ∗
  (session_failed cs failed' ∗ public m ∗ (⌜failed'⌝ ∨ φ cs m)).
Proof.
iIntros "#p_m #Nφ %e_rl #(_ & s_key & sess) #failed rel".
iDestruct (public_TSealE with "[//] [//]") as "{p_m} [[p_key p_m]|p_m]".
- iExists failed. iSplitR => //.
  case: failed.
  + do !iModIntro. iSplit; eauto.
    by case: (cs_role cs); [iLeft|iRight].
  + iSpecialize ("s_key" with "p_key").
    iDestruct "failed" as "#[meta #failed]".
    iDestruct "s_key" as "{p_key} >p_key".
    iDestruct ("failed" with "p_key") as "#contra".
    iModIntro.
    by iDestruct (release_token_released_session with "rel contra")
      as "[]".
- iDestruct "p_m" as "[#p_m _]".
  iModIntro. iModIntro.
  iDestruct "p_m" as "(%si & %failed' & %e_kS & p_m & failed' & inv_m)".
  rewrite e_rl -(session_agree e_kS).
  iPoseProof (session_failedI' with "failed' failed") as "failed''".
  iExists (failed' || failed).
  rewrite Bool.orb_comm. iSplit; first by case: failed.
  do 2!iSplit => //.
  rewrite Bool.orb_comm. case: failed' => /=; eauto.
  iDestruct "inv_m" as "[[]|inv_m]".
  by eauto.
Qed.

Lemma wp_connect N c kI kR n failed :
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  sign_key kI -∗
  public (TKey Open kR) -∗
  {{{ client_disconnected N kI kR n failed }}}
    Impl.connect N c kI (TKey Open kR)
  {{{ cs, RET (repr cs);
      connected kI kR cs 0 n ∗
      client_token N kI kR cs }}}.
Proof.
iIntros "#? #? #? #? #? % !> dis post".
wp_lam. wp_pure _ credit:"c1". wp_pure _ credit:"c2".
wp_pures. wp_bind (do_until _).
iCombine "dis post c1 c2" as "post". iApply (wp_frame_wand with "post").
wp_apply wp_do_until'. iModIntro.
wp_pures.
wp_apply (wp_initiator with "[//] [//] [] [] []") => //.
{ by iApply ctx_iso_dh_ctx. }
iIntros "%res resP".
case: res=> [kS|] /=; last by eauto.
iDestruct "resP"
  as "(%si & <- & %e_kR & <- & #m_kS & #comp & rel & token)".
case: e_kR => <- {kR}.
iRight. iExists _. iSplit => //.
iIntros "(dis & post & c1 & c2)".
wp_pures.
wp_alloc ts as "ts". wp_pures.
pose cs := State si ts Init.
iMod (client_connectingI N (cs := cs) with "[//] [$] [] [$] [$]")
  as "(%failed' & %le_failed & connecting & #beginning & #ready)" => //.
{ rewrite /wf_sess_info. iSplit => //. iSplit => //.
  by iApply senc_key_si_key. }
iAssert (server_clock_ready N (si_init si) (si_resp si)) as "#?".
{ by iDestruct "connecting" as "(? & ?)". }
iAssert (wf_sess_info cs) as "#?".
{ by iDestruct "connecting" as "(? & ? & ?)". }
iPoseProof (client_connecting_failed with "connecting")
  as "#failedI".
wp_apply wp_senc. wp_pures. wp_apply wp_send => //.
{ iApply public_TSealIS.
  - by rewrite minted_TKey.
  - by iApply ctx_init.
  - iModIntro. iExists si, failed'. rewrite public_TInt.
    do 3!iSplit => //.
    iDestruct "ready" as "[fail|ready]"; eauto.
    iRight. iExists n. by eauto.
  - by rewrite minted_TInt.
  - rewrite public_TInt. by eauto. }
wp_pures.
iCombine "post ts connecting" as "post".
iApply (wp_frame_wand with "post").
wp_bind (do_until _).
iRevert "rel". iApply wp_do_until. iIntros "!> rel".
wp_pures. wp_apply wp_recv => //.
iIntros "%m #p_m". wp_pures.
wp_sdec m; last by eauto.
iPoseProof (ctx_ack_init with "[//]") as "?".
iPoseProof (public_sencE _ cs with "p_m [//] [//] [//] failedI rel")
  as "{p_m} #p_m".
iModIntro. iRight. iExists _. iSplit => //. wp_pures.
iIntros "!> (post & ts & connecting)".
iDestruct "p_m" as "#(%failed'' & %le_failed'' & failed'' & p_m & ack)".
iDestruct "connecting" as "(_ & _ & _ & end & _)".
iApply ("post" $! cs).
iFrame. do !iSplit => //; eauto.
Qed.

Lemma wp_listen N c kR :
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  sign_key kR -∗
  {{{ True }}}
    listen N c kR
  {{{ cs, RET (TKey Open (si_init cs), repr cs)%V;
      incoming_connection N kR cs }}}.
Proof.
iIntros "#? #? #? #? % !> _ post".
wp_lam. wp_pures. iApply (wp_frame_wand with "post").
wp_apply wp_do_until'. iIntros "!>".
wp_pures.
wp_apply (wp_responder with "[//] [//] [] []") => //.
{ by iApply ctx_iso_dh_ctx. }
iIntros "%res resP".
case: res=> [[vkI kS]|] /=; last by iLeft; iFrame; eauto.
iRight. iExists _. iSplit => //. wp_pures.
wp_alloc ts as "ts".
iDestruct "resP"
  as "(%si & -> & % & <- & #p_vkI & #m_kS & #comp & rel & token)".
iPoseProof (senc_key_si_key with "[//] m_kS") as "?".
wp_pures. wp_bind (do_until _).
iCombine "ts rel token" as "I". iApply (wp_frame_wand with "I").
wp_apply wp_do_until'. iIntros "!>". wp_pures.
wp_apply wp_recv => //. iIntros "%m #p_m".
wp_pures. wp_sdec m; try by iLeft.
pose cs := State si ts Resp.
iPoseProof (ctx_init with "[//]") as "#?".
iIntros "!>". iRight. iExists _. iSplitR => //.
iIntros "(ts & rel & token)".
wp_pure _ credit:"c".
wp_pures.
iModIntro.
iIntros "post". iApply ("post" $! cs).
iAssert (wf_sess_info cs) as "#sess".
{ by do !iSplit => //. }
iFrame. do !iSplit => //.
iIntros "%failed rel #failed".
iPoseProof (public_sencE _ cs with "p_m [//] [//] [//] failed rel")
  as "{p_m} #p_m".
iMod (lc_fupd_elim_later with "c p_m") as "{p_m} #p_m".
iDestruct "p_m" as "(%failed' & %le_failed' & #failed' & p_m & inv)".
iModIntro. iExists failed'. do !iSplit => //.
iDestruct "inv" as "[?|inv]"; eauto.
Qed.

Lemma session_failed_session_failed_for si rl failed failed' :
  session_failed_for si rl failed -∗
  session_failed si failed' -∗
  ⌜failed → failed'⌝.
Proof.
iIntros "#failed #failed'".
case: failed' => //.
case: failed  => //.
iDestruct "failed'" as "[failed1 failed2]".
case: rl.
- by iPoseProof (session_failed_for_agree with "failed failed1") as "%".
- by iPoseProof (session_failed_for_agree with "failed failed2") as "%".
Qed.

Lemma wp_confirm N c kR cs n0 failed :
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  {{{ incoming_connection N kR cs ∗
      server_disconnected N (si_init cs) kR n0 failed }}}
    confirm N c (repr cs)
  {{{ RET #();
      ⌜cs_role cs = Resp⌝ ∗
      □ (⌜failed⌝ -∗ session_failed cs true) ∗
      connected (si_init cs) kR cs 0 n0 ∗
      server_token N cs }}}.
Proof.
iIntros "#? #? #? !> %Φ [inc dis] post".
iAssert (⌜cs_role cs = Resp⌝)%I as "%e_rl".
{ by iDestruct "inc" as "(_ & _ & _ & ? & _)". }
wp_lam. wp_pures.
wp_apply wp_senc. wp_pures.
iMod (server_connect with "dis inc") as "(#? & con & ?)".
iAssert (public (TSeal (TKey Seal (si_key cs))
                   (Spec.tag (N.@"conn".@"ack_init") (TInt 0))))
  as "#?".
{ iPoseProof (ctx_ack_init with "[//]") as "?".
  iDestruct "con"
    as "(_ & <- & #sess & (%failed'' & #failed'') & ? & ? & #failed & #beginning)".
  rewrite e_rl.
  iApply public_TSealIS => //.
  - rewrite minted_TKey. by iDestruct "sess" as "(? & _)".
  - iModIntro. iExists cs. iExists failed''.
    rewrite public_TInt. do !iSplit => //. by eauto.
  - by rewrite minted_TInt.
  - by rewrite public_TInt; eauto. }
wp_apply (wp_send with "[]") => //.
iApply "post". iFrame. by eauto.
Qed.

Lemma wp_timestamp kI kR cs n n0 :
  {{{ connected kI kR cs n n0 }}}
    timestamp (repr cs)
  {{{ RET #n; connected kI kR cs n n0 }}}.
Proof.
rewrite /timestamp.
iIntros "%Φ Hn post".
iDestruct "Hn" as "(% & % & #? & #? & ? & ? & #? & #?)".
wp_pures. wp_load. iApply "post". iFrame.
iModIntro. by eauto 10.
Qed.

Lemma wp_tick kI kR cs n n0 :
  {{{ connected kI kR cs n n0 }}}
    tick (repr cs)
  {{{ RET #(); connected kI kR cs (S n) n0 }}}.
Proof.
iIntros "%Ψ Hn post".
iDestruct "Hn" as "(% & % & #? & #? & ? & ? & #? & #?)".
rewrite /tick; wp_pures; wp_load; wp_store.
iApply "post".
rewrite (_ : (n + 1)%Z = (S n)%nat :> Z); last by lia.
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

Lemma wp_write kI kR cs n n0 N c ts φ :
  channel c -∗
  seal_pred N (conn_pred φ) -∗
  ([∗ list] t ∈ ts, public t) -∗
  session_failed cs true ∨ □ φ kI kR cs (n + n0) ts -∗
  {{{ connected kI kR cs n n0 }}}
    write N c (repr cs) (repr ts)
  {{{ RET #(); connected kI kR cs n n0 }}}.
Proof.
iIntros "#chan #pred #p_ts #inv !> %Φ conn post".
wp_lam. wp_pures. wp_apply (wp_timestamp with "[$]").
iIntros "conn". wp_pures.
wp_apply wp_session_key => //. iIntros "_".
wp_pures. wp_apply wp_tint. wp_list. wp_term_of_list.
wp_pures. wp_apply wp_senc. wp_pures.
wp_apply (wp_send with "[//] [#]").
{ iPoseProof (conn_predI _ _ _ _ _ φ with "conn p_ts [inv]") as "#?".
  { iModIntro. iDestruct "inv" as "[?|#?]"; eauto. }
  iApply (public_TSealIS with "[#] [//] [//]").
  - rewrite minted_TKey.
    by iDestruct "conn" as "(_ & _ & (? & ? & ?) & _)".
  - iApply public_minted. rewrite public_of_list /=.
    rewrite public_TInt. by eauto.
  - iIntros "!> !> _".
    rewrite public_of_list /= public_TInt. by eauto. }
by iApply "post".
Qed.

Lemma wp_select_body φ v1 v2 (handlers : list val) (Φ : val → iProp) :
  ([∗ list] handler ∈ handlers,
    (φ -∗ WP (handler : val) v1 v2 {{ v',
           ⌜v' = NONEV⌝ ∗ φ ∨
           ∃ r, ⌜v' = SOMEV r⌝ ∗ Φ r }}))%I -∗
  φ -∗ WP select_body v1 v2 (repr handlers) {{ v',
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

Lemma wp_select_body' Φ φ v1 v2 (handlers : list val) Ψ :
  ([∗ list] handler ∈ handlers,
     (φ -∗ WP (handler : val) v1 v2 {{ v,
       ⌜v = NONEV⌝ ∗ φ ∨
       ∃ r, ⌜v = SOMEV r⌝ ∗ Φ r }}))%I -∗
  (φ -∗ Ψ NONEV) -∗
  (∀ r, Φ r -∗ Ψ (SOMEV r)) -∗
  φ -∗
  WP select_body v1 v2 (repr handlers) {{ Ψ }}.
Proof.
iIntros "wp post1 post2 inv".
iApply (wp_wand with "[wp inv] [post1 post2]").
- by iApply (wp_select_body φ v1 v2 handlers Φ with "[wp] inv").
- iIntros "%res [[-> ?]|(%r & -> & ?)]".
  + by iApply "post1".
  + by iApply "post2".
Qed.

Lemma wp_make_handler φ Φ k n (handler : namespace * expr) :
  WP handler.2 {{ f,
    □ ∀ ts,
        let m := Spec.tag handler.1 (Spec.of_list (TInt n :: ts)) in
        public (TSeal (TKey Seal k) m) -∗
        φ -∗
        WP (f : val) (repr ts) {{ v',
            ⌜v' = NONEV⌝ ∗ φ ∨
            ∃ r, ⌜v' = SOMEV r⌝ ∗ Φ r }}
  }} -∗
  WP make_handler handler {{ f,
    □ ∀ (m : term),
        public (TSeal (TKey Seal k) m) -∗
        φ -∗
        WP (f : val) #n m {{ v',
          ⌜v' = NONEV⌝ ∗ φ ∨
          ∃ r, ⌜v' = SOMEV r⌝ ∗ Φ r }}
  }}.
Proof.
case: handler => N handler /=; iIntros "wp".
rewrite /make_handler. wp_pures.
wp_bind handler. iApply (wp_wand with "wp").
iIntros "%handler' #Hhandler'". wp_pures.
iIntros "!> !> %m #p_m inv". wp_pures.
wp_untag m; wp_pures; last by iLeft; iFrame.
wp_list_of_term m; wp_pures; last by iLeft; iFrame.
case: m => [|t ts].
{ rewrite repr_list_unseal. wp_pures. by iLeft; iFrame. }
rewrite repr_list_unseal /= -repr_list_unseal.
wp_pures. wp_apply wp_to_int.
case: Spec.to_intP => [n' ->|_]; wp_pures; last by iLeft; iFrame.
case: bool_decide_reflect => [[<-]|ne]; wp_pures; last by iLeft; iFrame.
by iApply "Hhandler'" => //.
Qed.

Lemma wp_make_handlers φ Φ k n (handlers : list (namespace * expr)) :
  ([∗ list] handler ∈ handlers,
      WP (handler.2 : expr) {{ f, □ ∀ ts,
        let m := Spec.tag handler.1 (Spec.of_list (TInt n :: ts)) in
        public (TSeal (TKey Seal k) m) -∗
        φ -∗
        WP (f : val) (repr ts) {{ v,
            ⌜v = NONEV⌝ ∗ φ ∨
            ∃ r, ⌜v = SOMEV r⌝ ∗ Φ r }} }})%I -∗
  WP make_handlers handlers {{ v',
    ∃ handlers' : list val, ⌜v' = repr handlers'⌝ ∗
      [∗ list] handler' ∈ handlers', □ ∀ (m : term),
        public (TSeal (TKey Seal k) m) -∗
        φ -∗
        WP (handler' : val) #n m {{ v,
          ⌜v = NONEV⌝ ∗ φ ∨
          ∃ r, ⌜v = SOMEV r⌝ ∗ Φ r }}
  }}.
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
{ rewrite -repr_list_unseal.
  iApply (wp_make_handler _ _ _ _ (N, handler) with "wp_handler"). }
iIntros "%f #wp_f". wp_lam; wp_pures.
iExists (f :: handlers'). iSplitR => //=.
iModIntro. iSplit => //.
Qed.

Definition handler_correct φ Φ kI kR cs n n0 handler : iProp :=
  WP handler.2 {{ f,
    ∃ Ψ, seal_pred handler.1 (conn_pred Ψ) ∗
    □ ∀ ts,
      connected kI kR cs n n0 -∗
      ▷ ([∗ list] t ∈ ts, public t) -∗
      □ ▷ (session_failed cs true ∨ Ψ kI kR cs (n + n0) ts) -∗
      φ -∗
      WP (f : val) (repr ts) {{ v,
        ⌜v = NONEV⌝ ∗ connected kI kR cs n n0 ∗ φ ∨
        ∃ r, ⌜v = SOMEV r⌝ ∗ Φ r }}
  }}%I.

Lemma wp_select
  φ Φ (c : val) kI kR cs n n0 (handlers : list (namespace * expr)) :
  channel c -∗
  ([∗ list] handler ∈ handlers,
    handler_correct φ Φ kI kR cs n n0 handler) -∗
  connected kI kR cs n n0 -∗
  φ -∗
  WP select c (repr cs) handlers {{ Φ }}.
Proof.
rewrite select_eq /select_def.
iIntros "#chan_c wps conn inv".
wp_bind (make_handlers _).
iApply (wp_wand with "[wps]").
{ iApply (wp_make_handlers
            (connected kI kR cs n n0 ∗ φ)
            Φ (si_key cs)
           with "[wps]").
  iApply (big_sepL_impl with "wps").
  iIntros "!> %k %handler _ wp".
  iApply (wp_wand with "wp").
  iIntros "%f #wp !> %ts #p_m [conn φ]".
  iDestruct "wp" as "(%Ψ & #seal & #wp)".
  iAssert (□ ▷ (([∗ list] t ∈ ts, public t) ∗
           (session_failed cs true ∨ Ψ kI kR cs (n + n0) ts)))%I
    as "#[p_ts inv_ts]".
  { iDestruct (public_TSealE with "[//] [//]") as "{p_m} [[p_key p_m]|p_m]".
    - rewrite public_of_list /=.
      iDestruct "p_m" as "[_ p_ts]". iSplitR => //.
      rewrite -bi.later_intuitionistically.
      iPoseProof (connected_public_key with "conn p_key") as "#failed".
      by eauto.
    - iDestruct "p_m" as "[#p_m _]".
      rewrite -bi.later_intuitionistically.
      iModIntro.
      iPoseProof (conn_predE with "conn p_m") as "[#? #?]".
      iModIntro. by eauto. }
  iApply ("wp" with "conn p_ts inv_ts [$]"). }
iIntros "% (%handlers' & -> & #Hhandlers')".
wp_pures. wp_apply (wp_timestamp with "conn"). iIntros "conn".
wp_pures. wp_apply wp_session_key => //. iIntros "_".
wp_pures. iCombine "conn inv" as "I". iRevert "I". iApply wp_do_until.
iIntros "!> I". wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m #p_m". wp_pures.
wp_apply wp_key.
wp_bind (open _ _). iApply wp_open.
case: Spec.openP; last by wp_pures; iLeft; iFrame.
move=> _ {}m [<-] ->. wp_pures.
iApply (wp_select_body' Φ with "[] [] [] I").
- iApply (big_sepL_impl with "Hhandlers'").
  iIntros "!> %k %handler _ #Hhandler inv" => //.
  by iApply ("Hhandler" with "p_m inv").
- iIntros "(?&?)". iLeft. by iFrame.
- iIntros "%r Hr". iRight. iExists r. by eauto.
Qed.

Lemma wp_read N c kI kR cs n n0 φ :
  channel c -∗
  seal_pred N (conn_pred φ) -∗
  {{{ connected kI kR cs n n0 }}}
    read N c (repr cs)
  {{{ ts, RET (repr (ts : list term));
      connected kI kR cs n n0 ∗
      ([∗ list] t ∈ ts, public t) ∗
      □ (session_failed cs true ∨ φ kI kR cs (n + n0) ts) }}}.
Proof.
iIntros "#? #NΦ !> %Ψ conn post".
wp_lam. wp_pures. rewrite !subst_select /=.
iRevert "post".
iApply (wp_select with "[//] [] conn").
rewrite /= /handler_correct /=. iSplit => //. wp_pures.
iModIntro. iExists _. iSplit => //.
iIntros "!> %ts conn #p_ts #inv_ts post".
wp_pures. iModIntro. iRight. iExists _. iSplit => //.
iApply "post". by iFrame; eauto.
Qed.

Lemma wp_close (c : val) cs n :
  {{{ cs_ts cs ↦ #n }}}
    close c (repr cs)
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ ts post".
wp_lam; wp_pures.
wp_free.
by iApply "post".
Qed.

End Proofs.

End Proofs.
