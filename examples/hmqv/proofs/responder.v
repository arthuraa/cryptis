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

Lemma wp_responder_confirm c p_a p_b X_a N φ :
  {{{ channel c ∗ cryptis_ctx ∗
      hmqv_ctx ∗ hmqv_pred N φ ∗
      public X_a ∗ hmqv_key p_a ∗ hmqv_key p_b ∗
      (∀ x_b,
          let si := resp_si p_a X_a p_b x_b in
          term_token (si_resp_share si) (↑hmqvN.@"res") ={⊤}=∗
           φ p_a p_b si Init ∗ φ p_a p_b si Resp) }}}
    responder_confirm c p_b (TExp g p_b) X_a (TExp g p_a) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        ⌜resp_session si⌝ ∗
        session p_a p_b si ∗
        release_token (si_resp_share si) ∗
        term_token (si_resp_share si) (⊤ ∖ ↑hmqvN) ∗
        φ p_a p_b si Resp }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & #(Hm2 & Hm3 & Hkey) & #N_φ &
             #p_Xa & #key_a & #key_b & res) Hpost".
iPoseProof "key_a" as "[#m_pa #pred_a]".
iPoseProof "key_b" as "[#m_pb #pred_b]".
iPoseProof (hmqv_key_public with "key_a") as "#p_Pa".
iPoseProof (hmqv_key_public with "key_b") as "#p_Pb".
iPoseProof (public_minted with "p_Xa") as "#m_Xa".
iAssert (public g) as "#p_g"; first by rewrite public_TInt.
wp_lam. wp_pures.
wp_eq_term e_ab; first by protocol_failure.
have p_a_b : p_a ≠ p_b by move=> e; apply: e_ab; rewrite e.
wp_pures.
(* The fresh ephemeral comes with a token on the responder's share;
   freshness against the peer's share keeps the two ephemerals apart. *)
wp_apply (wp_mk_nonce_freshN {[X_a]} (λ _, False)%I dh_key_share
            (λ x, {[TExp g x]})) => //.
- by iIntros "%"; rewrite elem_of_singleton; iIntros "->".
- iIntros "%x"; rewrite big_sepS_singleton; iModIntro; iSplit.
  + iIntros "#?"; by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
  + rewrite (minted_TExp x) //; by iIntros "[_ ?]".
iIntros "%x_b %fresh_b #m_xb #s_xb #pred_xb _ tok_Xb".
rewrite big_sepS_singleton.
have Nm_xb : negb (is_mul (TNonce x_b)) by [].
have X_a_xb : X_a ≠ TExp g x_b.
  move=> e; apply: (fresh_b X_a); first by rewrite elem_of_singleton.
  rewrite e; apply: subterm_exps.
  by rewrite exps_TExp_expN // factors_Nmul // list_elem_of_singleton.
iPoseProof (eph_seed_intro with "s_xb pred_xb") as "#eph_b".
set X_b := TExp g x_b.
set si := resp_si p_a X_a p_b x_b.
iAssert (public X_b) as "#p_Xb";
  first by iApply (public_dh_share gNX gNm gNi Nm_xb with "p_g m_xb pred_xb").
iDestruct (release_tokenI with "tok_Xb") as "[tok_rel tok_Xb]";
  first solve_ndisj.
iDestruct (term_token_difference X_b (↑hmqvN.@"res") with "tok_Xb")
  as "[tok_res tok_Xb]"; first solve_ndisj.
iDestruct (term_token_drop (⊤ ∖ ↑hmqvN) with "tok_Xb") as "tok_Xb";
  first solve_ndisj.
iMod ("res" $! x_b with "tok_res") as "[res_I res_R]".
iMod (hmqv_ready_alloc N p_a p_b si with "[//] res_I") as "#ready".
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
iAssert (public (Spec.of_list [σ]) ∨ ▷ □ m3_pred (Spec.of_list [σ]))%I
  as "#auth".
  by iDestruct (public_THashE with "Hm3 p_Aa") as "[? | [_ ?]]"; eauto.
wp_pures.
iAssert (minted (si_key si)) as "#m_k"; first by iApply minted_si_key.
(* A valid [A_a] was either forged -- then the key is public, so a long-term
   key leaked -- or produced by the honest initiator, which vouches for its
   ephemeral. *)
iAssert (session p_a p_b si) as "#sess".
{ iDestruct "auth" as "[#p_t | #auth]".
  - iEval (rewrite public_of_list /=) in "p_t".
    iDestruct "p_t" as "[#p_σ _]".
    iDestruct (@public_hmqv_K_static _ _ _ hmqvN g "resp" "init" p_b x_b p_a
                 (TExp g p_b) X_b X_a gNX gNm gNi tags' (not_eq_sym p_a_b)
                 with "pred_b pred_a p_σ") as "#comp".
    iAssert (public (si_key si)) as "#p_k"; first by iApply public_si_key.
    do 2!(iSplit; first by []).
    iSplit => //.
    iSplit; first by iIntros "!> _".
    iLeft. iDestruct "comp" as "[c|c]"; [by iRight | by iLeft].
  - iDestruct "auth" as "(%p_a' & %x_a' & %p_b' & %X_b' & %e' & #eph_a)".
    move: e' => /Spec.of_list_inj [] eσ.
    have [epb [epa [eXa eXb]]] :=
      @hmqv_K_inj' hmqvN g "resp" "init" p_b x_b p_a p_b' x_a' p_a' X_a X_b'
                   gNX gNm gNi tags' eσ.
    subst p_a' p_b' X_a X_b'.
    have x_a_b : x_a' ≠ x_b by move=> e'; apply: X_a_xb; rewrite e'.
    iPoseProof (honest_session_ok p_a p_b x_a_b with "Hkey eph_a eph_b m_k")
      as "#[ok1 ok2]".
    do 2!(iSplit; first by []).
    iSplit => //.
    iSplit; first by iApply "ok2".
    by iRight. }
wp_pures. wp_list. wp_apply wp_H.
wp_apply wp_derive_senc_key. wp_pures.
iApply ("Hpost" $! (Some (si_key si))). iModIntro.
iRight. iExists si. iFrame "tok_rel tok_Xb res_R".
iSplit; first by [].
iSplit; first by iPureIntro; exists p_a, X_a, p_b, x_b.
by iApply "sess".
Qed.

Lemma wp_responder_confirm_weak c p_a p_b X_a N :
  {{{ channel c ∗ cryptis_ctx ∗
      hmqv_ctx ∗ hmqv_pred N (λ _ _ _ _, True)%I ∗
      public X_a ∗ hmqv_key p_a ∗ hmqv_key p_b }}}
    responder_confirm c p_b (TExp g p_b) X_a (TExp g p_a) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session_weak p_a p_b si ∗
        term_token (si_resp_share si) (⊤ ∖ ↑hmqvN) }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & #? & #? & #p_Xa & #key_a & #key_b) Hpost".
iApply wp_fupd. wp_apply wp_responder_confirm.
{ do !iSplit => //. by iIntros "%x_b _ !>". }
iIntros "%osi [->|Hsi]"; first by iApply ("Hpost" $! None); eauto.
iDestruct "Hsi" as "(%si & -> & _ & #sess & rel & tok & _)".
iMod (unrelease Resp with "rel") as "#un". iModIntro.
iApply ("Hpost" $! (Some (si_key si))). iRight. iFrame. iSplit => //.
by iApply unreleased_session_weak.
Qed.

End Verif.
