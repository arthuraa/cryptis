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

Implicit Types (rl : role) (t : term).
Implicit Types (p_a p_b x_a x_b : nonce).
Implicit Types (si : sess_info).
Implicit Types (N : namespace).

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); eauto.

Lemma wp_initiator c p_a p_b N φ ψ :
  channel c ∗
  cryptis_ctx ∗
  hmqv_ctx ∗
  hmqv_pred N φ ∗
  hmqv_key p_a ∗
  hmqv_key p_b -∗
  {{{ ∀ x_a X_b,
        let si := init_si p_a x_a p_b X_b in
        secret x_a -∗
        term_token (si_init_share si) (↑hmqvN.@"res") ={⊤}=∗
        φ p_a p_b si Resp ∗ ψ x_a }}}
    initiator c p_a (TExp g p_a) (TExp g p_b) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ x_a X_b,
        let si := init_si p_a x_a p_b X_b in
        ⌜r = Some (si_key si, TNonce x_a)⌝ ∗
        session Init p_a p_b si ∗
        release_token (si_init_share si) ∗
        term_token (si_init_share si) (⊤ ∖ ↑hmqvN) ∗
        ψ x_a ∗
        (public (si_key si) ∨ φ p_a p_b si Init)
  }}}.
Proof.
rewrite /initiator.
iIntros "(#chan_c & #ctx & #(Hm2 & Hm3 & Hkey) & #N_φ & #key_a & #key_b)".
iIntros "!> %Ψ hook Hpost".
iPoseProof "key_a" as "[#m_pa #pred_a]".
iPoseProof "key_b" as "[#m_pb #pred_b]".
iPoseProof (hmqv_key_public with "key_a") as "#p_Pa".
iPoseProof (hmqv_key_public with "key_b") as "#p_Pb".
iAssert (public g) as "#p_g"; first by rewrite public_TInt.
wp_pures.
(* The ephemeral is a [secret] of its owner. *)
iMod pending_alloc as (γ) "pend".
wp_apply (wp_mk_nonce_freshN ∅ (λ _, shot γ 1)%I dh_key_share
            (λ x, {[TExp g x]})) => //.
- by iIntros "% %contra".
- iIntros "%x"; rewrite big_sepS_singleton; iModIntro; iSplit.
  + iIntros "#?"; by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
  + rewrite (minted_TExp x) //; by iIntros "[_ ?]".
iIntros "%x_a _ #m_xa #s_xa #pred_xa _ tok_Xa".
rewrite big_sepS_singleton.
have Nm_xa : negb (is_mul (TNonce x_a)) by [].
iAssert (□ (public x_a ↔ ▷ shot γ 1))%I as "#s_xa'".
{ iModIntro; iSplit.
  - iIntros "#p". iDestruct ("s_xa" with "p") as "#s". iNext.
    by iDestruct "s" as "#s".
  - iIntros "#s". iApply "s_xa". iNext. by iModIntro. }
iPoseProof (secret_alloc with "s_xa' pend") as "s".
iAssert (hmqv_key x_a) as "#key_xa"; first by iSplit.
set X_a := TExp g x_a.
iAssert (public X_a) as "#p_Xa";
  first by iApply (public_dh_share gNX gNm gNi Nm_xa with "p_g m_xa pred_xa").
iDestruct (release_tokenI with "tok_Xa") as "[tok_rel tok_Xa]";
  first solve_ndisj.
iDestruct (term_token_difference X_a (↑hmqvN.@"ready") with "tok_Xa")
  as "[tok_ready tok_Xa]"; first solve_ndisj.
iDestruct (term_token_difference X_a (↑hmqvN.@"res") with "tok_Xa")
  as "[tok_res tok_Xa]"; first solve_ndisj.
iDestruct (term_token_drop (⊤ ∖ ↑hmqvN) with "tok_Xa") as "tok_Xa";
  first solve_ndisj.
wp_pures. wp_apply wp_texp. rewrite -/X_a. wp_pures.
wp_list. wp_term_of_list.
wp_apply wp_send => //.
{ rewrite public_of_list /=. by do !iSplit => //. }
wp_pures. wp_apply wp_recv => //.
iIntros "%m2 #p_m2".
wp_list_of_term m2; last by protocol_failure.
wp_pures. wp_list_match => [X_b A_b -> {m2}|]; last by protocol_failure.
rewrite public_of_list /=. iDestruct "p_m2" as "(#p_Xb & #p_Ab & _)".
iPoseProof (public_minted with "p_Xb") as "#m_Xb".
wp_pures. wp_apply wp_hmqv_ke. wp_pures.
set σ := hmqv_K hmqvN "init" "resp" p_a x_a (TExp g p_a) X_a (TExp g p_b) X_b.
pose si := init_si p_a x_a p_b X_b.
wp_list. wp_apply wp_H.
wp_eq_term e'; last by protocol_failure.
subst A_b.
iAssert (public (Spec.of_list [σ; Tag N])
         ∨ ▷ □ m2_pred (Spec.of_list [σ; Tag N]))%I as "#auth".
  by iDestruct (public_THashE with "Hm2 p_Ab") as "[? | [_ ?]]"; eauto.
wp_pures.
iAssert (minted σ) as "#m_σ".
{ iApply minted_hmqv_K => //; by iApply public_minted. }
iAssert (minted (si_key si)) as "#m_k"; first by iApply minted_si_key.
(* A valid [A_b] was either forged -- then the key is public, so the
   responder's long-term key or the initiator's whole state leaked -- or
   produced by the honest responder, which vouches for its ephemeral and hands
   over the escrowed resources. *)
iAssert (|={⊤}=>
           session Init p_a p_b si ∗
           (public (si_key si) ∨ ▷ φ p_a p_b si Init))%I
  with "[tok_ready]" as ">(#sess & res)".
{ iDestruct "auth" as "[#p_t | #auth]".
  - iEval (rewrite public_of_list /=) in "p_t".
    iDestruct "p_t" as "[#p_σ _]".
    iDestruct (@public_hmqv_K_forged _ _ _ hmqvN g "init" "resp" p_a x_a p_b
                 (TExp g p_a) X_a X_b gNX gNm gNi tags
                 with "key_a key_xa key_b p_σ") as "#comp".
    iAssert (public (si_key si)) as "#p_k"; first by iApply public_si_key.
    iModIntro.
    iSplit; last by iLeft.
    do 2!(iSplit; first by []).
    iSplit => //.
    iSplit; first by iIntros "!> _".
    iLeft. iDestruct "comp" as "[?|[? ?]]"; first by iLeft.
    iRight. iSplit => //. iExists x_a. by iSplit.
  - iDestruct "auth"
      as "(%p_a' & %X_a' & %p_b' & %x_b' & %N' & %e' & #key_xb & #ready)".
    move: e' => /Spec.of_list_inj [] eσ /Tag_inj eN.
    subst N'.
    have [epa [epb [eXb eXa]]] :=
      @hmqv_K_inj' hmqvN g "init" "resp" p_a x_a p_b p_a' x_b' p_b' X_b X_a'
                   gNX gNm gNi tags eσ.
    subst p_a' p_b' X_b X_a'.
    have e_si : si = resp_si p_a (TExp g x_a) p_b x_b'.
      by rewrite /si init_resp_si.
    iEval (rewrite e_si) in "m_k".
    rewrite e_si.
    iPoseProof (honest_session_ok p_a p_b x_a x_b'
                  with "Hkey key_a key_b key_xa key_xb m_k")
      as "#[ok1 ok2]".
    iMod ("ready" with "N_φ tok_ready") as "res".
    iModIntro.
    iSplit; last by iRight.
    do 2!(iSplit; first by []).
    iSplit => //.
    iSplit; first by iApply "ok2".
    by iRight. }
iMod ("hook" $! x_a X_b with "s tok_res") as "[gift ψ]".
iMod (hmqv_ready_alloc N p_a p_b si Resp with "[//] gift") as "#ready_b".
wp_list. wp_apply wp_H.
wp_apply wp_send => //.
{ iApply (public_THashIS with "Hm3 [] []").
  - iApply minted_of_list => /=. do !iSplit => //. by iApply minted_Tag.
  - iNext; iModIntro. iExists p_a, x_a, p_b, X_b, N. by do !iSplit => //. }
wp_pures. wp_list. wp_apply wp_H.
wp_apply wp_derive_senc_key. wp_pures.
iApply ("Hpost" $! (Some (si_key si, TNonce x_a))).
iRight. iExists x_a, X_b. iFrame. iModIntro.
by do !iSplit => //.
Qed.

Lemma wp_initiator_weak c p_a p_b N :
  channel c ∗
  cryptis_ctx ∗
  hmqv_ctx ∗
  hmqv_pred N (λ _ _ _ _, True)%I ∗
  hmqv_key p_a ∗
  hmqv_key p_b -∗
  {{{ True }}}
    initiator c p_a (TExp g p_a) (TExp g p_b) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ x_a X_b,
        let si := init_si p_a x_a p_b X_b in
        ⌜r = Some (si_key si, TNonce x_a)⌝ ∗
        session_weak Init p_a p_b si ∗
        term_token (si_init_share si) (⊤ ∖ ↑hmqvN)
  }}}.
Proof.
iIntros "(#chan_c & #ctx & #? & #? & #key_a & #key_b) !> %Ψ _ Hpost".
iApply wp_fupd.
wp_apply (wp_initiator _ _ _ _ _ (λ _, True%I)) => //; first iFrame "#".
{ by iIntros "%x_a %X_b _ _ !>". }
iIntros "%r [->|Hr]"; first by iApply ("Hpost" $! None); eauto.
iDestruct "Hr" as "(%x_a & %X_b & -> & #sess & rel & tok & _ & _)".
iMod (unrelease Init with "rel") as "#un". iModIntro.
iApply ("Hpost" $! (Some (si_key (init_si p_a x_a p_b X_b), TNonce x_a))).
iRight. iExists x_a, X_b. iFrame. iSplit => //.
by iApply unreleased_session_weak.
Qed.
End Verif.
