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

(** What the responder keeps between its two messages. *)
Definition resp_state N P_a X_a p_b x_b : iProp :=
  ⌜P_a ≠ one⌝ ∗ ⌜si_secret (resp_si P_a X_a p_b x_b) ≠ one⌝ ∗
  ephemeral x_b ∗ usage (TExp g x_b) N ∗
  term_token (TExp g x_b) (↑hmqvN.@"ready") ∗
  term_token (TExp g x_b) (↑hmqvN.@"compromised").

(** The responder answers whatever long-term key [P_a] it is given.  The hook
    runs only if the responder answers, so a caller that lends it [R] gets [R]
    back otherwise. *)
Lemma wp_responder_accept c P_a X_a p_b N φ ρ ψ R :
  {{{ channel c ∗ cryptis_ctx ∗
      hmqv_ctx ∗ hmqv_pred N φ ρ ∗
      public P_a ∗ public X_a ∗ hmqv_key p_b ∗
      (R ∧
       ∀ x_b,
          let si := resp_si P_a X_a p_b x_b in
          term_token (si_resp_share si) (⊤ ∖ ↑hmqvN) ={⊤}=∗
          φ si Init ∗ ψ si) }}}
    responder_accept c p_b (TExp g p_b) X_a P_a (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∗ R ∨
      ∃ x_b, let si := resp_si P_a X_a p_b x_b in
        ⌜r = Some (si_secret si)⌝ ∗
        resp_state N P_a X_a p_b x_b ∗ ψ si }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & #(Hm2 & Hm3 & Hkey) & #N_φ &
             #p_Pa & #p_Xa & #key_b & hook) Hpost".
iPoseProof "key_b" as "[#m_pb #pred_b]".
iPoseProof (hmqv_key_public with "key_b") as "#p_Pb".
wp_lam. wp_pures.
wp_eq_term eP; wp_pures.
  by iApply ("Hpost" $! None); iLeft; iDestruct "hook" as "[$ _]".
wp_apply (wp_mk_ephemeral with "ctx").
iIntros "%x_b #eph_xb #p_Xb tok_ready tok_use tok_comp tok_Xb".
iPoseProof "eph_xb" as "[#key_xb _]".
iPoseProof "key_xb" as "[#m_xb _]".
set X_b := TExp g x_b.
wp_pures. wp_apply wp_texp. rewrite -/X_b. wp_pures.
wp_apply wp_hmqv_ke. wp_pures.
pose si := resp_si P_a X_a p_b x_b.
set σ := hmqv_K hmqvN "resp" "init" p_b x_b (TExp g p_b) X_b P_a X_a.
wp_eq_term eσ; wp_pures.
  by iApply ("Hpost" $! None); iLeft; iDestruct "hook" as "[$ _]".
iDestruct "hook" as "[_ hook]".
iMod ("hook" $! x_b with "tok_Xb") as "[gift ψ]".
iMod (hmqv_ready_alloc N si Init with "N_φ gift") as "#ready".
iMod (term_meta_set (hmqvN.@"usage") N with "tok_use") as "#use"; first done.
iAssert (minted σ) as "#m_σ".
{ iApply minted_hmqv_K => //; by iApply public_minted. }
wp_list. wp_apply wp_H. wp_list. wp_term_of_list.
wp_apply wp_send => //.
{ rewrite public_of_list /=. do !iSplit => //.
  iApply (public_THashIS with "Hm2 [] []").
  - iApply minted_of_list => /=. do !iSplit => //. by iApply minted_Tag.
  - iNext; iModIntro. iExists P_a, X_a, p_b, x_b, N. by do !iSplit => //. }
wp_pures. iApply ("Hpost" $! (Some σ)). iModIntro.
iRight. iExists x_b. iSplit => //. iFrame "eph_xb use". iFrame. by iSplit.
Qed.

Lemma wp_responder_finish c P_a X_a p_b x_b N φ ρ :
  let si := resp_si P_a X_a p_b x_b in
  {{{ channel c ∗ cryptis_ctx ∗
      hmqv_ctx ∗ hmqv_pred N φ ρ ∗
      public P_a ∗ public X_a ∗ hmqv_key p_b ∗ resp_state N P_a X_a p_b x_b }}}
    responder_finish c (si_secret si) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨
      ⌜r = Some (si_key si)⌝ ∗
      session ρ Resp si ∗
      (compromised Resp si ∨ φ si Resp) }}}.
Proof.
move=> si.
iIntros "%Φ (#chan_c & #ctx & #(Hm2 & Hm3 & Hkey) & #N_φ & #p_Pa & #p_Xa &
             #key_b & (%nPa & %nσ & #eph_xb & #use & tok_ready & tok_comp))
         Hpost".
iPoseProof "key_b" as "[#m_pb _]".
iPoseProof "eph_xb" as "[#key_xb #s_xb]".
iPoseProof "key_xb" as "[#m_xb _]".
iPoseProof (hmqv_key_public with "key_b") as "#p_Pb".
iPoseProof (hmqv_key_public with "key_xb") as "#p_Xb".
set σ := si_secret si.
iAssert (minted σ) as "#m_σ".
{ iApply minted_hmqv_K => //; by iApply public_minted. }
iAssert (minted (si_key si)) as "#m_k"; first by iApply minted_si_key.
wp_lam. wp_pures. wp_apply wp_recv => //. iIntros "%A_a #p_Aa".
wp_pures. wp_list. wp_apply wp_H.
wp_eq_term e; last by protocol_failure.
subst A_a.
iAssert (public (Spec.of_list [σ; Tag N])
         ∨ ▷ □ m3_pred (Spec.of_list [σ; Tag N]))%I as "#auth".
  by iDestruct (public_THashE with "Hm3 p_Aa") as "[? | [_ ?]]"; eauto.
wp_pures.
(* A valid [A_a] was either forged, so the key is public, or produced by an
   honest initiator, which vouches for its keys and hands over the escrowed
   resources. *)
iAssert (|={⊤}=>
           session ρ Resp si ∗ (compromised Resp si ∨ ▷ φ si Resp))%I
  with "[tok_ready tok_comp]" as ">[#sess res]".
{ iDestruct "auth" as "[#p_t | #auth]".
  - iEval (rewrite public_of_list /=) in "p_t".
    iDestruct "p_t" as "[#p_σ _]".
    iMod (term_meta_set (hmqvN.@"compromised") true with "tok_comp")
      as "#comp"; first done.
    iAssert (public (si_key si)) as "#p_k"; first by iApply public_si_key.
    iModIntro. iSplit; last by iLeft.
    iSplit; first done. iSplit; first by iIntros "!> _".
    iLeft. iSplit; first done. iSplit; first done.
    iIntros "!> %p_a %e #key_a". rewrite /si /= in e. subst P_a.
    iDestruct (@public_hmqv_K_forged _ _ _ hmqvN g "resp" "init" p_b x_b p_a
                 (TExp g p_b) (TExp g x_b) X_a gNX gNm tags'
                 with "key_b key_xb key_a p_σ") as "[#p|[_ #x]]".
    + by iModIntro.
    + by iDestruct ("s_xb" with "x") as ">[]".
  - iDestruct "auth" as "(%p_a & %x_a & %P_b' & %X_b' & %N' & %e' & %nPb' &
                          #key_a & #eph_xa & #ready_a)".
    move: e' => /Spec.of_list_inj [] eσ /Tag_inj eN.
    subst N'.
    have [ePa [eXa [ePb eXb]]] := hmqv_K_inj' gNX gNm tags' nPa nPb' nσ eσ.
    subst P_b' X_b' P_a X_a.
    have e_si : init_si p_a x_a (TExp g p_b) (TExp g x_b) = si.
      by rewrite /si init_resp_si.
    iMod (term_meta_set (hmqvN.@"compromised") false with "tok_comp")
      as "#ncomp"; first done.
    iMod ("ready_a" with "N_φ tok_ready") as "res".
    iEval (rewrite e_si) in "res".
    iPoseProof (honest_session N φ ρ p_a p_b x_a x_b
                  with "Hkey N_φ key_a key_b eph_xa eph_xb use m_k")
      as "[#rel #ok]".
    iModIntro. iSplit; last by iRight.
    iSplit; first done. iSplit; first done.
    iRight. iSplit; last done.
    iIntros "!> #c".
    by iDestruct (term_meta_agree with "c ncomp") as %?. }
wp_pures. wp_apply wp_session_key. wp_pures.
iApply ("Hpost" $! (Some (si_key si))). iModIntro.
iRight. iFrame "res". by iSplit.
Qed.

Lemma wp_responder_confirm c P_a X_a p_b N φ ρ ψ :
  {{{ channel c ∗ cryptis_ctx ∗
      hmqv_ctx ∗ hmqv_pred N φ ρ ∗
      public P_a ∗ public X_a ∗ hmqv_key p_b ∗
      (∀ x_b,
          let si := resp_si P_a X_a p_b x_b in
          term_token (si_resp_share si) (⊤ ∖ ↑hmqvN) ={⊤}=∗
          φ si Init ∗ ψ si) }}}
    responder_confirm c p_b (TExp g p_b) X_a P_a (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ x_b,
        let si := resp_si P_a X_a p_b x_b in
        ⌜r = Some (si_key si)⌝ ∗
        session ρ Resp si ∗ ψ si ∗
        (compromised Resp si ∨ φ si Resp) }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & #? & #N_φ & #p_Pa & #p_Xa & #key_b & hook)
         Hpost".
wp_lam. wp_pures.
wp_apply (wp_responder_accept _ _ _ _ _ _ _ ψ True%I with "[hook]").
{ iFrame "#". by iSplit. }
iIntros "%r [[-> _]|(%x_b & -> & state & ψ)]"; wp_pures.
  by iApply ("Hpost" $! None); iLeft.
wp_apply (wp_responder_finish with "[$state]"); first by iFrame "#".
iIntros "%r [->|(-> & #sess & res)]".
- iApply ("Hpost" $! None). by iLeft.
- iApply "Hpost". iRight. iExists x_b. by iFrame "∗ #".
Qed.
End Verif.
