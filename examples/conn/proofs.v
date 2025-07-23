From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh.
From cryptis.examples.conn Require impl.
From cryptis.examples.conn.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation connN := (nroot.@"conn").

Section Proofs.

Context `{!cryptisGS Σ, !heapGS Σ, !connGS Σ, !iso_dhGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : state).
Implicit Types kS t : term.
Implicit Types skI skR : sign_key.
Implicit Types n m : nat.
Implicit Types γ : gname.
Implicit Types v : val.
Implicit Types (N : namespace).

Lemma wp_channel cs :
  {{{ True }}}
    impl.channel (repr cs)
  {{{ RET (cs_chan cs); True }}}.
Proof.
iIntros "% _ post". wp_lam. wp_pures. by iApply "post".
Qed.

Lemma wp_connect P c skI skR N φ ψ :
  channel c ∗
  cryptis_ctx ∗
  ctx N φ ψ ∗
  minted skI ∗
  minted skR -∗
  {{{ (failure skI skR ∨ P) }}}
    impl.connect c skI (Spec.pkey skR) (Tag N)
  {{{ cs, RET (repr cs);
      connected skI skR φ Init cs ∗
      (compromised_session Init cs ∨ P ∗ ψ Init (si_resp_share cs)) ∗
      release_token (si_init_share cs) ∗
      term_token (si_init_share cs) (⊤ ∖ ↑iso_dhN ∖ ↑connN) }}}.
Proof.
iIntros "(#? & #? & ([#? #?] & #?) & #? & #?) % !> HP post".
rewrite bi.or_alt. iDestruct "HP" as "(%failed & HP)".
wp_lam. wp_pure _ credit:"c1". wp_pure _ credit:"c2".
wp_pures. wp_bind (do_until _).
iAssert (if failed then failure skI skR else True)%I as "#?".
{ by case: failed. }
iCombine "HP post c1 c2" as "post". iApply (wp_frame_wand with "post").
iApply wp_do_until'. iIntros "!>". wp_pures.
wp_apply (wp_initiator failed with "[//] [//] [] [//] [] [] [] []") => //.
iIntros "%res resP".
case: res=> [kS|] /=; last by eauto.
iDestruct "resP"
  as "(%si & <- & %e_kR & <- & #m_kS & #sess & #comp & rel & token & res)".
move: e_kR => <-.
iRight. iExists _. iSplit => //.
iIntros "(dis & post & c1 & c2)".
wp_pures.
wp_alloc ts as "ts"; try lia. wp_pures. rewrite /=.
pose cs := State si ts c Init.
iMod (received_alloc si Init with "token") as "[received token]";
  first solve_ndisj.
iApply ("post" $! cs).
rewrite /conn_init_pred or_sep2.
iDestruct "res" as "[res1 res2]".
iModIntro. iFrame.
iSplit.
{ do 6!iSplit => //. }
iSplitR "token"; last first.
{ iApply (term_token_drop with "token"). solve_ndisj. }
iDestruct "res2" as "[?|res2]"; eauto.
case: failed; [|iRight]; iFrame.
iLeft. by iApply "comp".
Qed.

Lemma wp_listen c N φ ψ :
  channel c -∗
  cryptis_ctx -∗
  ctx N φ ψ -∗
  {{{ True }}}
    impl.listen c
  {{{ ga skI, RET (ga, Spec.pkey skI)%V;
      public ga ∗ minted skI }}}.
Proof.
iIntros "#? #? [[#? _] _] % !> _ post". wp_lam.
wp_apply wp_responder_wait; eauto.
Qed.

Lemma wp_confirm P ψ c skI skR ga N φ :
  channel c -∗
  cryptis_ctx -∗
  ctx N φ ψ -∗
  {{{ public ga ∗ minted skI ∗ minted skR ∗
      □ (∀ gb, term_token gb (↑iso_dhN.@"res" ∖ ↑iso_dhN.@"res".@"pred") ={⊤}=∗
               ψ Init gb ∗ ψ Resp gb) ∗
      (failure skI skR ∨ P) }}}
    impl.confirm c skR (Tag N) (ga, Spec.pkey skI)%V
  {{{ cs, RET (repr cs);
      connected skI skR φ Resp cs ∗
      (compromised_session Resp cs ∨ P) ∗
      release_token (si_resp_share cs) ∗
      term_token (si_resp_share cs) (⊤ ∖ ↑iso_dhN ∖ ↑connN) ∗
      ψ Resp (si_resp_share cs) }}}.
Proof.
iIntros "#? #ctx [[#? #?] #?] !> %Φ (#p_ga & #p_pkA & #sign_skB & #mk & P) post".
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
iApply (wp_responder_accept failed (λ gb, conn_msg_pred φ gb ∗ ψ Resp gb))%I.
{ do !iSplit => //.
  iIntros "%gb token".
  iMod (term_pred_alloc _ (N := iso_dhN.@"res".@"pred")
          (λ '(skI, skR, si, rl, t), φ skI skR si rl t) with "token")
    as "[#pred token]"; try solve_ndisj.
  iAssert (conn_msg_pred φ gb) as "#?".
  { iModIntro. iIntros "% % %". iApply ("pred" $! (_, _, _)). }
  iMod ("mk" with "token") as "[init resp]". iFrame. by eauto. }
iIntros "!> %osi res". case: osi => [kS|]; last by eauto.
iDestruct "res"
  as "(%si & <- & <- & -> & #m_k & #sess & #comp & rel & token & msg & res)".
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
    impl.session_key (repr cs)
  {{{ RET (repr (si_key cs)); True }}}.
Proof.
rewrite /impl.session_key.
iIntros "%Φ _ post". wp_pures. iApply "post".
iModIntro. by iFrame.
Qed.

Lemma wp_role cs :
  {{{ True }}}
    impl.role (repr cs)
  {{{ RET (repr (cs_role cs)); True }}}.
Proof.
iIntros "%Φ _ post". wp_lam. wp_pures. by iApply "post".
Qed.

Lemma wp_send skI skR rl cs t N φ ψ :
  ctx N φ ψ -∗
  public t -∗
  {{{ connected skI skR φ rl cs ∗
      (public (si_key cs) ∨ φ skI skR cs rl t) }}}
    impl.send (repr cs) t
  {{{ RET #(); connected skI skR φ rl cs }}}.
Proof.
iIntros "[[_ #pred] _] #p_ts !> %Φ (conn & inv) post".
iDestruct "conn"
  as "(<- & <- & <- & #chan & #sess & #msg & %n & %m & counters & recv)".
wp_lam. wp_pures.
wp_apply wp_channel => //. iIntros "_". wp_pures.
wp_lam. wp_pures.
wp_apply wp_session_key => //. iIntros "_".
wp_pures.
wp_list.
wp_apply (wp_load_offset with "counters") => //.
iIntros "counters".
wp_apply wp_tint. wp_list. wp_apply wp_role => //. iIntros "_".
wp_apply wp_tint. wp_list. wp_term_of_list.
set msg := Spec.of_list _.
iAssert (public msg) as "#?".
{ rewrite public_of_list /= !public_TInt. by eauto. }
iAssert (|={⊤}=> (public (si_key cs) ∨ conn_pred (si_key cs) msg))%I
  with "[inv]" as ">#p_t".
{ iDestruct "inv" as "[#?|inv]"; first by eauto.
  iDestruct "msg" as "[(_ & ? & _)|msg]"; eauto.
  iSpecialize ("msg" with "inv").
  iRight. iExists cs, (cs_role cs), n, t.
  do 3!iSplitR => //.
  by iApply escrow_received. }
wp_pures. wp_apply wp_senc; eauto.
- by iDestruct "sess" as "(?&?)".
- by iDestruct "p_t" as "[p_t|inv_t]"; eauto.
iIntros "% #?". wp_pures. wp_apply wp_send => //. wp_pures.
wp_apply (wp_load_offset with "counters") => //.
iIntros "counters". wp_pures.
wp_apply (wp_store_offset with "counters") => //=.
rewrite (_ : (_ + _)%Z = S n); last by lia.
iIntros "counters". iApply "post". iFrame. by eauto 10.
Qed.

Ltac recv_failure :=
  iLeft; iFrame; eauto 10.

Lemma wp_recv skI skR rl cs N φ ψ :
  ctx N φ ψ -∗
  {{{ connected skI skR φ rl cs }}}
    impl.recv (repr cs)
  {{{ t, RET (repr t);
      connected skI skR φ rl cs ∗
      public t ∗
      (public (si_key cs) ∨ φ skI skR cs (swap_role rl) t) }}}.
Proof.
iIntros "[[_ #Nφ] _] !> %Φ conn post".
wp_lam.
iPoseProof (connected_channel with "conn") as "#?".
wp_apply wp_channel => //. iIntros "_". wp_pures.
wp_apply wp_role => //. iIntros "_". wp_pures.
wp_apply wp_session_key => //. iIntros "_". wp_pures.
iApply (wp_frame_wand with "post").
iRevert "conn". iApply wp_do_until.
iIntros "!> conn". wp_pure _ credit:"c1".
wp_apply wp_recv => //. iIntros "%t #p_t". wp_pure _ credit:"c2". wp_pures.
iDestruct "conn"
  as "(<- & <- & <- & #chan & #sess & #msg & %n & %m & counters & recv)".
wp_lam. wp_pures. wp_apply wp_sdec => //. iSplit; last first.
{ wp_pures. iLeft. iFrame. by eauto 10. }
iClear "p_t" => {t}. iIntros "%t #m_t #inv_t #s_t". wp_pures.
wp_list_of_term t; wp_pures; last by recv_failure.
wp_list_match => [rl' r' {}t ->|_]; wp_pures; last by recv_failure.
wp_apply wp_to_int.
case: Spec.to_intP => [ {}rl' ->|_]; wp_pures; last by recv_failure.
wp_apply wp_to_int.
case: Spec.to_intP => [ {}r' ->|_]; wp_pures; last by recv_failure.
case: bool_decide_reflect => [?|ne]; wp_pures; first by recv_failure.
wp_apply (wp_load_offset with "counters") => //. iIntros "counters".
wp_pures. case: bool_decide_reflect => [[<-]|_]; wp_pures; last by recv_failure.
wp_apply (wp_load_offset with "counters") => //. iIntros "counters".
wp_pures. rewrite (_ : (m + 1)%Z = S m); last by lia.
wp_apply (wp_store_offset with "counters") => //=. iIntros "counters".
iAssert (|={⊤}=> public t ∗
           received_auth cs (cs_role cs) (S m) ∗
           (public (si_key cs) ∨
              φ (si_init cs) (si_resp cs) cs (swap_role (cs_role cs)) t))%I
  with "[recv c1 c2]" as "{inv_t} >(p_t & recv & inv_t)".
{ iDestruct "inv_t" as "[fail|#inv]".
  { iMod (received_update with "recv") as "[recv _]".
    iDestruct ("s_t" with "fail") as "p_t".
    rewrite public_of_list /=. iDestruct "p_t" as "(_ & _ & p_t & _)".
    iFrame. by eauto. }
  iDestruct "inv" as "(%si & %rl'' & %m' & %t' & %e_k & %e_t & p_ts & inv)".
  move/term_of_senc_key_inj/session_agree: e_k => <- {si}.
  case/Spec.of_list_inj: e_t => -> e_m <- {rl'} in ne *.
  have <-: m = m' by lia.
  have {ne} -> : rl'' = swap_role (cs_role cs).
    rewrite /repr_role in ne.
    case: rl'' (cs_role cs) => [] [] /= in ne *; congruence.
  rewrite swap_roleK.
  iMod (escrowE with "inv recv") as "{inv} [inv recv]";
    first by solve_ndisj.
  iFrame.
  iCombine "inv recv" as "I".
  iMod (lc_fupd_elim_later with "c1 I") as "[inv recv]".
  iFrame. iSplitR; eauto.
  iDestruct "msg" as "[(_ & ? & _)|msg]"; eauto.
  iSpecialize ("msg" with "inv").
  iMod (lc_fupd_elim_later with "c2 msg") as "msg".
  by eauto. }
wp_pures. iModIntro. iRight. iExists _. iSplit => //.
iIntros "post". iApply "post". iFrame. by eauto 10.
Qed.

Lemma wp_free kI kR φ rl cs :
  {{{ connected kI kR φ rl cs }}}
    impl.free (repr cs)
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ conn post".
iDestruct "conn" as "(? & ? & ? & ? & ? & ? & % & % & ts & ?)".
rewrite !array_cons array_nil.
iDestruct "ts" as "(sent & recv & _)".
wp_lam; wp_pures.
wp_free. wp_pures.
wp_free.
by iApply "post".
Qed.

End Proofs.
