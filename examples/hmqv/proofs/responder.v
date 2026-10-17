From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.lib Require Import dh hmqv.
From cryptis.examples.hmqv Require Import impl.
From cryptis.examples.hmqv.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !hmqvGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (rl : role) (t X_a : term).
Implicit Types (p_a p_b x_a x_b : nonce).
Implicit Types (si : sess_info) (osi : option sess_info).
Implicit Types (N : namespace).

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); eauto.

Lemma wp_responder_listen c :
  {{{ channel c ∗ cryptis_ctx }}}
    responder_listen c
  {{{ X_a P_a, RET (X_a, P_a); public X_a ∗ public P_a }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx) post". wp_lam. wp_pures.
iApply (wp_frame_wand with "post").
wp_apply wp_do_until'. iIntros "!>".
wp_pures. wp_apply wp_recv => //.
iIntros "%m1 #p_m1". wp_pures.
wp_list_of_term m1; wp_pures; last by eauto.
wp_list_match => [X_a P_a ->|_]; wp_pures; last by eauto.
rewrite public_of_list /=. iDestruct "p_m1" as "(#p_Xa & #p_Pa & _)".
iModIntro. iRight. iExists _; iSplit => //.
iIntros "post". iApply "post". by iSplit.
Qed.

Lemma wp_responder_confirm c p_a p_b X_a N φ ψ :
  {{{ channel c ∗ cryptis_ctx ∗
      hmqv_ctx ∗ hmqv_pred N φ ∗
      public X_a ∗ hmqv_key p_a ∗ hmqv_key p_b ∗
      (∀ x_b,
          let si := resp_si p_a X_a p_b x_b in
          secret x_b -∗
          term_token (si_resp_share si) (↑hmqvN.@"res") ={⊤}=∗
          φ p_a p_b si Init ∗ ψ x_b) }}}
    responder_confirm c p_b (TExp g p_b) X_a (TExp g p_a) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ x_b,
        let si := resp_si p_a X_a p_b x_b in
        ⌜r = Some (si_key si, TNonce x_b)⌝ ∗
        session Resp p_a p_b si ∗
        release_token (si_resp_share si) ∗
        term_token (si_resp_share si) (⊤ ∖ ↑hmqvN) ∗
        ψ x_b ∗
        (public (si_key si) ∨ φ p_a p_b si Resp) }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & #(Hm2 & Hm3 & Hkey) & #N_φ &
             #p_Xa & #key_a & #key_b & hook) Hpost".
iPoseProof "key_a" as "[#m_pa #pred_a]".
iPoseProof "key_b" as "[#m_pb #pred_b]".
iPoseProof (hmqv_key_public with "key_a") as "#p_Pa".
iPoseProof (hmqv_key_public with "key_b") as "#p_Pb".
iPoseProof (public_minted with "p_Xa") as "#m_Xa".
iAssert (public g) as "#p_g"; first by rewrite public_TInt.
wp_lam. wp_pures.
(* The ephemeral is a [secret] of its owner. *)
iMod pending_alloc as (γ) "pend".
wp_apply (wp_mk_nonce_freshN ∅ (λ _, shot γ 1)%I dh_key_share
            (λ x, {[TExp g x]})) => //.
- by iIntros "% %contra".
- iIntros "%x"; rewrite big_sepS_singleton; iModIntro; iSplit.
  + iIntros "#?"; by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
  + rewrite (minted_TExp x) //; by iIntros "[_ ?]".
iIntros "%x_b _ #m_xb #s_xb #pred_xb _ tok_Xb".
rewrite big_sepS_singleton.
have Nm_xb : negb (is_mul (TNonce x_b)) by [].
iAssert (□ (public x_b ↔ ▷ shot γ 1))%I as "#s_xb'".
{ iModIntro; iSplit.
  - iIntros "#p". iDestruct ("s_xb" with "p") as "#s". iNext.
    by iDestruct "s" as "#s".
  - iIntros "#s". iApply "s_xb". iNext. by iModIntro. }
iPoseProof (secret_alloc with "s_xb' pend") as "s".
iAssert (hmqv_key x_b) as "#key_xb"; first by iSplit.
set X_b := TExp g x_b.
set si := resp_si p_a X_a p_b x_b.
iAssert (public X_b) as "#p_Xb";
  first by iApply (public_dh_share gNX gNm gNi Nm_xb with "p_g m_xb pred_xb").
iDestruct (release_tokenI with "tok_Xb") as "[tok_rel tok_Xb]";
  first solve_ndisj.
iDestruct (term_token_difference X_b (↑hmqvN.@"ready") with "tok_Xb")
  as "[tok_ready tok_Xb]"; first solve_ndisj.
iDestruct (term_token_difference X_b (↑hmqvN.@"res") with "tok_Xb")
  as "[tok_res tok_Xb]"; first solve_ndisj.
iDestruct (term_token_drop (⊤ ∖ ↑hmqvN) with "tok_Xb") as "tok_Xb";
  first solve_ndisj.
iMod ("hook" $! x_b with "s tok_res") as "[gift ψ]".
iMod (hmqv_ready_alloc N p_a p_b si Init with "[//] gift") as "#ready".
wp_pures. wp_apply wp_texp. rewrite -/X_b. wp_pures.
wp_apply wp_hmqv_ke. wp_pures.
set σ := hmqv_K hmqvN "resp" "init" p_b x_b (TExp g p_b) X_b (TExp g p_a) X_a.
iAssert (minted σ) as "#m_σ".
{ iApply minted_hmqv_K => //; by iApply public_minted. }
wp_list. wp_apply wp_H. wp_list. wp_term_of_list.
wp_apply wp_send => //.
{ rewrite public_of_list /=. do !iSplit => //.
  iApply (public_THashIS with "Hm2 [] []").
  - iApply minted_of_list => /=. do !iSplit => //. by iApply minted_Tag.
  - iNext; iModIntro. iExists p_a, X_a, p_b, x_b, N. by do !iSplit => //. }
wp_pures. wp_apply wp_recv => //. iIntros "%A_a #p_Aa".
wp_pures. wp_list. wp_apply wp_H.
wp_eq_term e; last by protocol_failure.
subst A_a.
iAssert (public (Spec.of_list [σ; Tag N])
         ∨ ▷ □ m3_pred (Spec.of_list [σ; Tag N]))%I as "#auth".
  by iDestruct (public_THashE with "Hm3 p_Aa") as "[? | [_ ?]]"; eauto.
wp_pures.
iAssert (minted (si_key si)) as "#m_k"; first by iApply minted_si_key.
(* A valid [A_a] was either forged -- then the key is public, so the
   initiator's long-term key or the responder's whole state leaked -- or
   produced by the honest initiator, which vouches for its ephemeral and hands
   over the escrowed resources. *)
iAssert (|={⊤}=>
           session Resp p_a p_b si ∗
           (public (si_key si) ∨ ▷ φ p_a p_b si Resp))%I
  with "[tok_ready]" as ">(#sess & res)".
{ iDestruct "auth" as "[#p_t | #auth]".
  - iEval (rewrite public_of_list /=) in "p_t".
    iDestruct "p_t" as "[#p_σ _]".
    iDestruct (@public_hmqv_K_forged _ _ _ hmqvN g "resp" "init" p_b x_b p_a
                 (TExp g p_b) X_b X_a gNX gNm gNi tags'
                 with "key_b key_xb key_a p_σ") as "#comp".
    iAssert (public (si_key si)) as "#p_k"; first by iApply public_si_key.
    iModIntro.
    iSplit; last by iLeft.
    do 2!(iSplit; first by []).
    iSplit => //.
    iSplit; first by iIntros "!> _".
    iLeft. iDestruct "comp" as "[?|[? ?]]"; first by iLeft.
    iRight. iSplit => //. iExists x_b. by iSplit.
  - iDestruct "auth"
      as "(%p_a' & %x_a' & %p_b' & %X_b' & %N' & %e' & #key_xa & #ready_a)".
    move: e' => /Spec.of_list_inj [] eσ /Tag_inj eN.
    subst N'.
    have [epb [epa [eXa eXb]]] :=
      @hmqv_K_inj' hmqvN g "resp" "init" p_b x_b p_a p_b' x_a' p_a' X_a X_b'
                   gNX gNm gNi tags' eσ.
    subst p_a' p_b' X_a X_b'.
    iPoseProof (honest_session_ok p_a p_b x_a' x_b
                  with "Hkey key_a key_b key_xa key_xb m_k")
      as "#[ok1 ok2]".
    have e_si : init_si p_a x_a' p_b X_b = si.
      by rewrite /si /X_b init_resp_si.
    iMod ("ready_a" with "N_φ tok_ready") as "res".
    iEval (rewrite e_si) in "res".
    iModIntro.
    iSplit; last by iRight.

    do 2!(iSplit; first by []).
    iSplit => //.
    iSplit; first by iApply "ok2".
    by iRight. }
wp_pures. wp_list. wp_apply wp_H.
wp_apply wp_derive_senc_key. wp_pures.
iApply ("Hpost" $! (Some (si_key si, TNonce x_b))). iModIntro.
iRight. iExists x_b. iFrame "tok_rel tok_Xb ψ res".
iSplit; first by [].
by iApply "sess".
Qed.

Lemma wp_responder_confirm_weak c p_a p_b X_a N :
  {{{ channel c ∗ cryptis_ctx ∗
      hmqv_ctx ∗ hmqv_pred N (λ _ _ _ _, True)%I ∗
      public X_a ∗ hmqv_key p_a ∗ hmqv_key p_b }}}
    responder_confirm c p_b (TExp g p_b) X_a (TExp g p_a) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ x_b,
        let si := resp_si p_a X_a p_b x_b in
        ⌜r = Some (si_key si, TNonce x_b)⌝ ∗
        session_weak Resp p_a p_b si ∗
        term_token (si_resp_share si) (⊤ ∖ ↑hmqvN) }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & #? & #? & #p_Xa & #key_a & #key_b) Hpost".
iApply wp_fupd. wp_apply (wp_responder_confirm _ _ _ _ _ _ (λ _, True%I)).
{ do !iSplit => //. by iIntros "%x_b _ _ !>". }
iIntros "%r [->|Hr]"; first by iApply ("Hpost" $! None); eauto.
iDestruct "Hr" as "(%x_b & -> & #sess & rel & tok & _ & _)".
iMod (unrelease Resp with "rel") as "#un". iModIntro.
iApply ("Hpost" $! (Some (si_key (resp_si p_a X_a p_b x_b), TNonce x_b))).
iRight. iExists x_b. iFrame. iSplit => //.
by iApply unreleased_session_weak.
Qed.
End Verif.
