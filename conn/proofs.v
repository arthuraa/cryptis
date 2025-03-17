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

Section Proofs.

Context `{!cryptisGS Σ, !heapGS Σ, !connGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : state).
Implicit Types kI kR kS t : term.
Implicit Types n m : nat.
Implicit Types γ : gname.
Implicit Types v : val.

(* MOVE *)
Lemma connected_public_key kI kR rl cs n m kt :
  connected kI kR rl cs n m -∗
  release_token (si_share_of rl cs) -∗
  public (TKey kt (si_key cs)) -∗
  ◇ compromised_session rl cs.
Proof.
iIntros "conn rel #p_k".
iPoseProof "conn" as "(_ & _ & <- & #sess & _)".
iDestruct "sess" as "(#? & #s_key & #sess)".
iPoseProof (senc_key_compromised_keyI with "s_key p_k") as "{p_k} p_k".
iPoseProof (senc_key_compromised_keyE with "s_key p_k") as "{p_k} >p_k".
by iApply session_compromised.
Qed.
(* /MOVE *)

Lemma public_sencE N rl si t φ :
  public (TSeal (TKey Seal (si_key si)) (Spec.tag (Tag N) t)) -∗
  seal_pred N φ -∗
  wf_sess_info rl si -∗
  release_token (si_share_of rl si) -∗
  ▷ □ (compromised_session rl si ∗ public t ∨ φ (si_key si) t).
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

Lemma wp_connect P N c kI kR :
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  sign_key kI -∗
  public (TKey Open kR) -∗
  {{{ failure kI kR ∨ P }}}
    Impl.connect N c kI (TKey Open kR)
  {{{ cs, RET (repr cs);
      connected kI kR Init cs 0 0 ∗
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

Lemma wp_confirm P N c skA skB ga n :
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  {{{ public ga ∗ public (TKey Open skA) ∗ sign_key skB ∗
      (failure skA skB ∨ P) }}}
    confirm N c skB (ga, TKey Open skA)%V
  {{{ cs, RET (repr cs);
      connected skA skB Resp cs 0 0 ∗
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

Lemma wp_get_sent kI kR rl cs n m :
  {{{ connected kI kR rl cs n m }}}
    !#(cs_ts cs +ₗ 0%nat)
  {{{ RET #n; connected kI kR rl cs n m }}}.
Proof.
iIntros "% (<- & <- & <- & #sess & counters & recv) post".
wp_apply (wp_load_offset with "counters") => //.
iIntros "counters". iApply "post". by iFrame; eauto.
Qed.

Lemma wp_get_received kI kR rl cs n m :
  {{{ connected kI kR rl cs n m }}}
    !#(cs_ts cs +ₗ 1%nat)
  {{{ RET #m; connected kI kR rl cs n m }}}.
Proof.
iIntros "% (<- & <- & <- & #sess & counters & recv) post".
wp_apply (wp_load_offset with "counters") => //.
iIntros "counters". iApply "post". by iFrame; eauto.
Qed.

Lemma wp_set_sent kI kR rl cs n m (p : nat) :
  {{{ connected kI kR rl cs n m }}}
    #(cs_ts cs +ₗ 0%nat) <- #p
  {{{ RET #(); connected kI kR rl cs p m }}}.
Proof.
iIntros "% (<- & <- & <- & #sess & counters & recv) post".
wp_apply (wp_store_offset with "counters") => //=.
iIntros "counters". iApply "post". by iFrame; eauto.
Qed.

Lemma wp_write kI kR rl cs n m N c ts φ :
  channel c -∗
  seal_pred N (conn_pred rl φ) -∗
  ([∗ list] t ∈ ts, public t) -∗
  {{{ connected kI kR rl cs n m ∗
      (compromised_session rl cs ∨ φ kI kR cs n ts) }}}
    write (Tag N) c (repr cs) (repr ts)
  {{{ RET #(); connected kI kR rl cs (S n) m }}}.
Proof.
iIntros "#chan #pred #p_ts !> %Φ (conn & inv) post".
iDestruct "conn" as "(<- & <- & <- & #sess & counters & recv)".
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
{ iDestruct "inv" as "[#(_ & ? & _)|inv]"; first by eauto.
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

Lemma wp_try_open N φ kI kR rl cs n m t :
  {{{ seal_pred N (conn_pred (swap_role rl) φ) ∗
      connected kI kR rl cs n m ∗
      release_token (si_share_of rl cs) ∗
      public (TSeal (TKey Seal (si_key cs)) t) }}}
    try_open (Tag N) (repr cs) t
  {{{ res, RET res;
      release_token (si_share_of rl cs) ∗
      (⌜res = NONEV⌝ ∗
       connected kI kR rl cs n m ∨
       ∃ ts, ⌜res = SOMEV (repr ts)⌝ ∗
             ([∗ list] t ∈ ts, public t) ∗
             connected kI kR rl cs n (S m) ∗
             (compromised_session rl cs ∨ φ kI kR cs m ts)) }}}.
Proof.
iIntros "%Φ (#Φ & conn & rel & #p_t) post".
rewrite /try_open.
wp_pure _ credit:"c1".
wp_pure _ credit:"c2".
wp_pures.
wp_untag t; wp_pures; last by iApply "post"; iFrame; eauto.
wp_list_of_term t; wp_pures; last by iApply "post"; iFrame; eauto.
wp_lam. wp_pures.
wp_apply (wp_get_received with "conn"). iIntros "conn".
wp_pures.
case: t => [|t ts].
{ rewrite repr_list_unseal; wp_pures.
  by iApply "post"; iFrame; iLeft; iFrame. }
rewrite repr_list_unseal /= -repr_list_unseal.
wp_pures. wp_apply wp_to_int.
case: Spec.to_intP => [n' ->|_]; wp_pures; last first.
{ by iApply "post"; iFrame; iLeft; iFrame. }
case: bool_decide_reflect => [[<-]|ne]; wp_pures; last first.
{ by iApply "post"; iFrame; iLeft; iFrame. }
iPoseProof (public_sencE with "p_t [//] [#] [$]") as "{p_t} #p_t".
- by iDestruct "conn" as "(? & ? & <- & ? & ?)".
rewrite (_ : (m + 1)%Z = S m); last by lia.
wp_lam. wp_pures.
iDestruct "conn" as "(<- & <- & <- & #sess & ts & received)".
iAssert (|={⊤}=> ▷ (([∗ list] t ∈ ts, public t) ∗
           received_auth cs (cs_role cs) (S m) ∗
           (compromised_session (cs_role cs) cs ∨
              φ (si_init cs) (si_resp cs) cs m ts)))%I
  with "[received]" as ">H".
{ rewrite public_of_list /=.
  iDestruct "p_t" as "#[(? & _ & ?)|inv]".
  { iMod (received_update with "received") as "[received _]".
    iIntros "!> !>". iFrame. iSplit => //. eauto. }
  iDestruct "inv"
      as "(%si & %m' & %ts' & %e_k & %e_t & p_ts & inv)".
  move/session_agree: e_k => <- {si}.
  case/Spec.of_list_inj: e_t => e_m <-.
  have <-: m = m' by lia.
  rewrite swap_roleK.
  iMod (escrowE with "inv received") as "{inv} [inv received]";
    first by solve_ndisj.
  iIntros "!> !>". by iFrame. }
wp_apply (wp_store_offset with "ts") => //=. iIntros "ts".
iDestruct "H" as "(#? & received & inv)".
wp_pures. iApply "post". iFrame.
iModIntro. iRight. iExists ts. iFrame.
do !iSplit => //.
Qed.

Definition make_handler_post φ ψ kI kR rl cs (handler : val) : iProp :=
  □ ∀ n m (t : term),
    public (TSeal (TKey Seal (si_key cs)) t) -∗
    connected kI kR rl cs n m -∗
    release_token (si_share_of rl cs) -∗
    φ n m -∗
    WP handler (repr cs) t {{ v,
      ⌜v = NONEV⌝ ∗
        connected kI kR rl cs n m ∗
        release_token (si_share_of rl cs) ∗ φ n m ∨
      ∃ r, ⌜v = SOMEV r⌝ ∗ ψ n m r }}.

Definition handler_correct_gen φ ψ kI kR rl cs handler : iProp :=
  ∃ N f, ⌜handler = (Tag N, f)%V⌝ ∗
  ∃ Ψ, seal_pred N (conn_pred (swap_role rl) Ψ) ∗
  □ ∀ n m ts,
    {{{ connected kI kR rl cs n (S m) ∗
        release_token (si_share_of rl cs) ∗
        φ n m ∗
        ▷ ([∗ list] t ∈ ts, public t) ∗
        ▷ (compromised_session rl cs ∨ Ψ kI kR cs m ts) }}}
      (f : val) (repr ts)
    {{{ v, RET v; ψ n m v }}}.

Lemma wp_make_handler φ ψ kI kR rl cs handler :
  handler_correct_gen φ ψ kI kR rl cs handler -∗
  WP make_handler handler {{ make_handler_post φ ψ kI kR rl cs }}.
Proof.
iIntros "(%N & %f & -> & %φ' & #? & #wp)".
wp_lam. wp_pures.
iIntros "!> !> %n %m %t #p_t conn recv inv". wp_pures.
wp_apply (wp_try_open with "[$conn $recv]"); eauto.
iIntros "%res (rel & [(-> & conn)|(%ts & -> & #p_ts & conn & inv_ts)])"; wp_pures.
{ iLeft. by iFrame. }
wp_apply ("wp" with "[$inv $conn $rel $inv_ts]") => //.
iIntros "%res ?". wp_pures. iModIntro. iRight. by eauto.
Qed.

Lemma wp_make_handlers φ ψ kI kR rl cs (handlers : list val) :
  ([∗ list] handler ∈ handlers,
    handler_correct_gen φ ψ kI kR rl cs handler) -∗
  WP make_handlers (repr handlers) {{ v',
    ∃ handlers : list val, ⌜v' = repr handlers⌝ ∗
      [∗ list] handler ∈ handlers,
        make_handler_post φ ψ kI kR rl cs handler }}.
Proof.
rewrite /= !repr_list_unseal.
elim: handlers=> [|handler handlers IH] //=.
  iIntros "_". wp_rec. wp_pures. iModIntro. iExists []. by rewrite /=.
iIntros "[wp_handler wp_handlers]". wp_rec; wp_pures.
wp_bind (make_handlers _).
iPoseProof (IH with "wp_handlers") as "wp_handlers". clear IH.
iApply (wp_wand with "wp_handlers [wp_handler]").
iIntros "%v' (%handlers' & -> & #Hhandlers')".
wp_bind (make_handler _).
iApply (wp_wand with "[wp_handler] [Hhandlers']").
{ iApply (wp_make_handler _ _ _ _ _ _ handler with "wp_handler"). }
clear handler.
iIntros "%handler #wp_handler". wp_lam; wp_pures.
iExists (handler :: handlers'). iSplitR => //=.
iModIntro. iSplit => //.
Qed.

Lemma wp_select_outer_body φ ψ (c : val) kI kR rl cs (handlers : list val) :
  channel c -∗
  ([∗ list] handler ∈ handlers,
    make_handler_post φ ψ kI kR rl cs handler) -∗
  ∀ n m,
  connected kI kR rl cs n m -∗
  release_token (si_share_of rl cs) -∗
  φ n m -∗
  WP select_outer_body c (repr cs) (repr handlers) {{ ψ n m }}.
Proof.
iIntros "#chan_c #wps %n %m conn rel inv".
wp_lam. wp_pures. wp_apply wp_session_key => //. iIntros "_".
wp_pures. iCombine "conn rel inv" as "I". iRevert "I". iApply wp_do_until.
iIntros "!> I". wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%t #p_t". wp_pures.
wp_apply wp_key. wp_bind (open _ _). iApply wp_open.
case: Spec.openP; last by wp_pures; iLeft; iFrame.
move=> _ {}t [<-] ->. wp_pures.
iApply (wp_select_inner_body (ψ n m) with "[] [] [] I").
- iApply (big_sepL_impl with "wps").
  iIntros "!> %k %handler _ #Hhandler (conn & rel & inv)" => //.
  by iApply ("Hhandler" with "p_t conn rel inv").
- iIntros "(?&?)". iLeft. by iFrame.
- iIntros "%r Hr". iRight. iExists r. by eauto.
Qed.

Lemma wp_select φ ψ (c : val) kI kR rl cs (handlers : list val) :
  channel c -∗
  ([∗ list] handler ∈ handlers,
    handler_correct_gen φ ψ kI kR rl cs handler) -∗
  ∀ n m, connected kI kR rl cs n m -∗
  release_token (si_share_of rl cs) -∗
  φ n m -∗
  WP select c (repr cs) (repr handlers) {{ ψ n m }}.
Proof.
iIntros "#chan_c wps %n %m conn rel inv".
wp_lam; wp_pures.
wp_bind (make_handlers _). iApply (wp_wand with "[wps]").
{ wp_apply (wp_make_handlers with "wps"). }
iIntros "%res (%v_handlers & -> & #wps)".
by wp_apply (wp_select_outer_body with "[] [] conn rel inv").
Qed.

Lemma wp_read N c kI kR rl cs n m φ :
  channel c -∗
  seal_pred N (conn_pred (swap_role rl) φ) -∗
  {{{ connected kI kR rl cs n m ∗
      release_token (si_share_of rl cs) }}}
    read (Tag N) c (repr cs)
  {{{ ts, RET (repr (ts : list term));
      connected kI kR rl cs n (S m) ∗
      release_token (si_share_of rl cs) ∗
      ([∗ list] t ∈ ts, public t) ∗
      (compromised_session rl cs ∨ φ kI kR cs m ts) }}}.
Proof.
iIntros "#? #NΦ !> %Ψ [conn rel] post".
wp_lam. wp_pures.
wp_apply (@wp_nil val). wp_apply (wp_cons _ (Tag N, λ: "ts", "ts")%V).
wp_apply (
  wp_select
  (λ n m, (∀ ts, connected kI kR rl cs n (S m) ∗
            release_token (si_share_of rl cs) ∗
            ([∗ list] t ∈ ts, public t) ∗
            (compromised_session rl cs ∨ φ kI kR cs m ts) -∗
            Ψ (repr ts)))%I
  (λ _ _, Ψ)%I
  with "[//] [] conn rel post") => //.
rewrite /= /handler_correct_gen /=. iSplit => //.
iExists _, _; iSplit => //.
iExists _; iSplit; eauto.
iModIntro. clear n m.
iIntros "%n %m %ts !> %Φ (conn & rel & post1 & #p_ts & inv_ts) post2".
wp_pures. iModIntro.
iApply "post2". iApply "post1". iFrame. by eauto.
Qed.

Lemma wp_free (c : val) cs n m :
  {{{ cs_ts cs ↦∗ [ #n; #m ] }}}
    free c (repr cs)
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ ts post". rewrite !array_cons array_nil.
iDestruct "ts" as "(sent & recv & _)".
wp_lam; wp_pures.
wp_free. wp_pures.
wp_free.
by iApply "post".
Qed.

(*
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
*)

End Proofs.

End Proofs.
