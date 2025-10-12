From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par ticket_lock assert.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.lib Require Import term_set.
From cryptis.examples.nsl Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Section NSL.

Context `{!heapGS Σ, !cryptisGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : aenc_key).

Record sess_info : Type := SessInfo {
  si_init : aenc_key;
  si_resp : aenc_key;
  si_init_share : term;
  si_resp_share : term;
}.

Definition si_key si :=
  SEncKey (Spec.of_list [Spec.pkey (si_init si);
                         Spec.pkey (si_resp si);
                         si_init_share si;
                         si_resp_share si]).

Lemma nsl_session_agree si1 si2 :
  si_key si1 = si_key si2 → si1 = si2.
Proof.
case: si1=>>; case: si2=>>; case.
by case/Spec.of_list_inj
   => /Spec.aenc_pkey_inj <- /Spec.aenc_pkey_inj <- <- <-.
Qed.

Definition msg1_pred skR m1 : iProp := ∃ nI skI,
  ⌜m1 = Spec.of_list [nI; Spec.pkey skI]⌝ ∧
  (public nI ↔ ▷ (public skI ∨ public skR)).

Definition msg2_pred skI m2 : iProp := ∃ nI nR skR,
  ⌜m2 = Spec.of_list [nI; nR; Spec.pkey skR]⌝ ∧
  (public nR ↔ ▷ (public skI ∨ public skR)).

Definition msg3_pred skR nR : iProp := True.

Definition nsl_ctx : iProp :=
  aenc_pred (nslN.@"m1") msg1_pred ∧
  aenc_pred (nslN.@"m2") msg2_pred ∧
  aenc_pred (nslN.@"m3") msg3_pred.

Lemma nsl_alloc E1 E2 :
  ↑nslN ⊆ E1 →
  seal_pred_token AENC E1 ={E2}=∗
  nsl_ctx ∗
  seal_pred_token AENC (E1 ∖ ↑nslN).
Proof.
iIntros (sub1) "t1".
rewrite (seal_pred_token_difference _ (↑nslN) E1) //.
iDestruct "t1" as "[t1 t1']". iFrame.
iMod (aenc_pred_set (N := nslN.@"m1") msg1_pred with "t1")
  as "[#H1 t1]"; try solve_ndisj.
iMod (aenc_pred_set (N := nslN.@"m2") msg2_pred with "t1")
  as "[#H2 t1]"; try solve_ndisj.
iMod (aenc_pred_set (N := nslN.@"m3") msg3_pred with "t1")
  as "[#H3 t1]"; try solve_ndisj.
iModIntro; iFrame; do !iSplit => //.
Qed.

Global Instance nsl_ctx_persistent : Persistent nsl_ctx.
Proof. apply _. Qed.

Definition session_NSL skI skR si : iProp :=
  ⌜skI = si_init si⌝ ∗ ⌜skR = si_resp si⌝ ∗
  minted (si_key si) ∗
  □ (public (si_key si) ↔ ▷ (public skI ∨ public skR)).

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); eauto.

Lemma wp_init c skI skR :
  channel c ∗
  cryptis_ctx ∗
  nsl_ctx ∗
  minted skI ∗
  minted skR -∗
  {{{ True }}}
    init c skI (Spec.pkey skR)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session_NSL skI skR si ∗
        term_token (si_init_share si) (⊤ ∖ ↑nslN) }}}.
Proof.
iIntros "(#chan_c & #ctx & #(?&?&?) & #m_skI & #m_skR) !> %Ψ _ Hpost".
iAssert (public (Spec.pkey skI)) as "?". { by iApply public_aenc_key. }
iAssert (public (Spec.pkey skR)) as "?". { by iApply public_aenc_key. }
rewrite /init. wp_pures. wp_apply wp_pkey. wp_pures.
wp_apply (wp_mk_nonce (λ _, public skI ∨ public skR)%I (λ _, False)%I) => //.
iIntros "%nI _ #m_nI #s_nI _ token".
rewrite (term_token_difference _ (↑nslN)) //.
iDestruct "token" as "[_ token]".
rewrite bi.intuitionistic_intuitionistically.
wp_pures. wp_list. wp_term_of_list. wp_apply wp_aenc => /=; eauto.
- by rewrite minted_of_list /= minted_pkey; eauto.
- iRight. iSplit.
  + iModIntro. iExists _. by eauto.
  + iIntros "!> #p_skR". rewrite public_of_list /=. do !iSplit => //.
    iApply "s_nI". by eauto.
iIntros "%m1 #p_m1". wp_pures.
wp_apply wp_send => //.
wp_pures. wp_apply wp_recv => //. iIntros "%m2 #p_m2".
wp_apply wp_adec => //. iSplit; last protocol_failure.
iClear "p_m2" => {m2}. iIntros "%m2 #m_m2 #inv_m2".
wp_list_of_term m2; last protocol_failure.
wp_list_match => [nI' nR pkR' {m2} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nI'.
wp_eq_term e; last protocol_failure; subst pkR'.
rewrite minted_of_list public_of_list /=.
iDestruct "m_m2" as "(_ & m_nR & _)".
iAssert (public nR ↔ ▷ (public skI ∨ public skR))%I as "s_nR".
{ iDestruct "inv_m2" as "[(p_nI & p_nR & _)|[#inv_m2 _]]".
  - iSpecialize ("s_nI" with "p_nI"). by iSplit; eauto.
  - iDestruct "inv_m2" as "(%nI' & %nR' & %skR' & %e & s_nR)".
    by case/Spec.of_list_inj: e => _ <- /Spec.aenc_pkey_inj <-. }
wp_pures. wp_apply wp_aenc; eauto.
{ iRight. iSplit => //. iIntros "!> #p_skR".
  iApply "s_nR". by eauto. }
iIntros "%m3 #p_m3". wp_pures. wp_apply wp_send => //.
wp_pures. wp_list. wp_term_of_list. wp_apply wp_derive_senc_key.
set sess_key := Spec.of_list [Spec.pkey skI; _; _; _].
wp_pures.
iApply ("Hpost" $! (Some (SEncKey sess_key))). iModIntro.
iRight. iExists (SessInfo skI skR nI nR). iFrame.
do !iSplit => //.
{ rewrite minted_senc minted_of_list /= !minted_pkey; eauto. }
rewrite public_senc_key public_of_list /=.
iModIntro. iSplit.
- iIntros "(_ & _ & _ & p_nR & _)". by iApply "s_nR".
- iIntros "#fail". by do !iSplit => //; [iApply "s_nI"|iApply "s_nR"].
Qed.

Lemma wp_resp c skR :
  channel c ∗
  cryptis_ctx ∗
  nsl_ctx ∗
  minted skR -∗
  {{{ True }}}
    resp c skR
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI si,
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session_NSL skI skR si ∗
        term_token (si_resp_share si) (⊤ ∖ ↑nslN)
  }}}.
Proof.
iIntros "(#chan_c & #ctx & #(?&?&?) & #aencR) !> %Ψ _ Hpost".
iAssert (public (Spec.pkey skR)) as "?". { by iApply public_aenc_key. }
rewrite /resp. wp_pures. wp_apply wp_pkey. wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#p_m1".
wp_apply wp_adec => //. iSplit; last protocol_failure.
iClear "p_m1" => {m1}. iIntros "%m1 #m_m1 #inv_m1".
wp_list_of_term m1; last protocol_failure.
wp_list_match => [nI pkI {m1} ->|_]; last protocol_failure.
rewrite minted_of_list /= public_of_list /=.
iDestruct "m_m1" as "(m_nI & m_pkI & _)".
wp_apply wp_is_aenc_key => //. iSplit; last protocol_failure.
iIntros "%skI -> #m_skI {m_pkI}". wp_pures.
iAssert (▷ (public skI ∨ public skR) → public nI)%I as "s_nI".
{ iDestruct "inv_m1" as "[(? & _)|[#inv_m1 _]]"; eauto.
  iIntros "#fail".
  iDestruct "inv_m1" as "(%nI' & %skI' & %e & s_nI)".
  case/Spec.of_list_inj: e => <- /Spec.aenc_pkey_inj <-.
  by iApply "s_nI". }
wp_apply (wp_mk_nonce_freshN
           ∅
           (λ _, public skI ∨ public skR)%I
           (λ _, False)%I
           (λ nR, {[nR; SEncKey (Spec.of_list [Spec.pkey skI; Spec.pkey skR; nI; nR]) : term]})) => //.
- by iIntros "% %".
- iIntros "%nR".
  rewrite big_sepS_union_pers !big_sepS_singleton minted_senc minted_of_list.
  rewrite /= !minted_pkey.
  iSplit => //; iModIntro; first by iSplit; iIntros "?".
  iSplit; last by iIntros "(_ & _ & _ & ? & _)".
  by iIntros "#m_nR"; do !iSplit => //.
iIntros "%nR _ %nonce #m_nR #s_nR _ tokens".
rewrite bi.intuitionistic_intuitionistically.
set sess_key := SEncKey (Spec.of_list [_; _; _; _]).
have ? : nR ≠ sess_key.
  by move=> e; rewrite e keysE in nonce.
rewrite big_sepS_union; last set_solver.
rewrite !big_sepS_singleton. iDestruct "tokens" as "[nR_token sk_token]".
rewrite (term_token_difference _ (↑nslN)) //.
iDestruct "nR_token" as "[_ nR_token]". wp_pures.
wp_list. wp_term_of_list.
wp_apply wp_aenc; eauto.
- by rewrite minted_of_list /= minted_pkey; eauto.
- iRight. iSplit.
  + iExists nI, nR, skR. by eauto.
  + iIntros "!> #p_skI". rewrite public_of_list /=.
    do !iSplit => //; [iApply "s_nI"|iApply "s_nR"]; eauto.
iIntros "%m2 #p_m2". wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_recv => //.
iIntros "%m3 #p_m3".
wp_apply wp_adec => //. iSplit; last protocol_failure.
iClear "p_m3" => {m3}. iIntros "%m3 _ _". wp_pures.
wp_eq_term e; last protocol_failure; subst m3.
wp_pures. wp_list. wp_term_of_list. wp_apply wp_derive_senc_key.
wp_pures. iApply ("Hpost" $! (Some (Spec.pkey skI, sess_key))).
iModIntro. iRight. iExists skI, (SessInfo skI skR nI nR). iFrame.
do !iSplit => //=.
{ rewrite minted_senc minted_of_list /= !minted_pkey; eauto. }
rewrite public_senc_key public_of_list /=.
iModIntro. iSplit.
- iIntros "(_ & _ & _ & #p_nR & _)". by iApply "s_nR".
- iIntros "#fail". rewrite !public_aenc_key.
  by do !iSplit => //; [iApply "s_nI"|iApply "s_nR"].
Qed.

End NSL.
