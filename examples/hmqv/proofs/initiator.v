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
  by intros; wp_pures; iApply ("Hpost" $! None); iLeft;
     iDestruct "hook" as "[$ _]".

(* The hook runs only if the session succeeds, so a caller that lends it [R]
   gets [R] back otherwise.  The long-term key [P_b] used for the peer need
   not be vetted: the guarantees about the key hold for whoever owns [P_b], if
   anyone does. *)
Lemma wp_initiator c p_a P_b N φ ψ R :
  channel c ∗
  cryptis_ctx ∗
  hmqv_ctx ∗
  hmqv_pred N φ ∗
  hmqv_key p_a ∗
  public P_b -∗
  {{{ R ∧
      ∀ x_a X_b,
        secret x_a -∗
        term_token (TExp g x_a) (↑hmqvN.@"res") ={⊤}=∗
        (∀ p_b, ⌜P_b = TExp g p_b⌝ →
           φ p_a p_b (init_si p_a x_a p_b X_b) Resp) ∗
        ψ x_a X_b }}}
    initiator c p_a (TExp g p_a) P_b (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∗ R ∨ ∃ (k : senc_key) x_a X_b,
        ⌜r = Some (k, TNonce x_a)⌝ ∗
        release_token (TExp g x_a) ∗
        term_token (TExp g x_a) (⊤ ∖ ↑hmqvN) ∗
        ψ x_a X_b ∗
        ∀ p_b, ⌜P_b = TExp g p_b⌝ → hmqv_key p_b -∗
          let si := init_si p_a x_a p_b X_b in
          ⌜k = si_key si⌝ ∗
          session Init p_a p_b si ∗
          (public (si_key si) ∨ φ p_a p_b si Init)
  }}}.
Proof.
rewrite /initiator.
iIntros "(#chan_c & #ctx & #(Hm2 & Hm3 & Hkey) & #N_φ & #key_a & #p_Pb)".
iIntros "!> %Ψ hook Hpost".
iPoseProof "key_a" as "[#m_pa _]".
iPoseProof (hmqv_key_public with "key_a") as "#p_Pa".
wp_pures.
wp_eq_term eP; first by protocol_failure.
wp_pures. wp_apply (wp_mk_ephemeral with "ctx").
iIntros "%x_a s #key_xa #p_Xa tok_rel tok_ready tok_res tok_Xa".
iPoseProof "key_xa" as "[#m_xa _]".
set X_a := TExp g x_a.
wp_pures. wp_apply wp_texp. rewrite -/X_a. wp_pures.
wp_list. wp_term_of_list.
wp_apply wp_send => //.
{ rewrite public_of_list /=. by do !iSplit => //. }
wp_pures. wp_apply wp_recv => //.
iIntros "%m2 #p_m2".
wp_list_of_term m2; last by protocol_failure.
wp_pures. wp_list_match => [X_b A_b -> {m2}|]; last by protocol_failure.
rewrite public_of_list /=. iDestruct "p_m2" as "(#p_Xb & #p_Ab & _)".
wp_pures. wp_apply wp_hmqv_ke. wp_pures.
set σ := hmqv_K hmqvN "init" "resp" p_a x_a (TExp g p_a) X_a P_b X_b.
wp_eq_term nσ; first by protocol_failure.
wp_pures.
wp_list. wp_apply wp_H.
wp_eq_term e'; last by protocol_failure.
subst A_b.
iAssert (public (Spec.of_list [σ; Tag N])
         ∨ ▷ □ m2_pred (Spec.of_list [σ; Tag N]))%I as "#auth".
  by iDestruct (public_THashE with "Hm2 p_Ab") as "[? | [_ ?]]"; eauto.
wp_pures.
iAssert (minted σ) as "#m_σ".
{ iApply minted_hmqv_K => //; by iApply public_minted. }
(* A valid [A_b] was either forged, so the key is public, or produced by an
   honest responder, which owns [P_b], vouches for its ephemeral and hands over
   the escrowed resources. *)
iAssert (|={⊤}=>
           public σ ∨ ∃ p_b x_b,
             ⌜P_b = TExp g p_b⌝ ∗ ⌜X_b = TExp g x_b⌝ ∗ hmqv_key x_b ∗
             ▷ φ p_a p_b (resp_si p_a X_a p_b x_b) Init)%I
  with "[tok_ready]" as ">res".
{ iDestruct "auth" as "[#p_t | #auth]".
  - iEval (rewrite public_of_list /=) in "p_t".
    iDestruct "p_t" as "[#p_σ _]". by iLeft.
  - iDestruct "auth" as "(%P_a' & %X_a' & %p_b & %x_b & %N' & %e' &
                          %nPa' & #key_xb & #ready)".
    move: e' => /Spec.of_list_inj [] eσ /Tag_inj eN.
    subst N'.
    have [ePb [eXb [ePa eXa]]] := hmqv_K_inj' gNX gNm tags eP nPa' nσ eσ.
    subst P_a' X_a'.
    iSpecialize ("ready" $! p_a with "[//]").
    iMod ("ready" with "N_φ tok_ready") as "res".
    iModIntro. iRight. iExists p_b, x_b.
    do 2!(iSplit; first done). by iFrame "key_xb res". }
iDestruct "hook" as "[_ hook]".
iMod ("hook" $! x_a X_b with "s tok_res") as "[gift ψ]".
iMod (hmqv_ready_alloc_resp N p_a x_a P_b X_b with "[//] gift")
  as "#ready_b".
wp_list. wp_apply wp_H.
wp_apply wp_send => //.
{ iApply (public_THashIS with "Hm3 [] []").
  - iApply minted_of_list => /=. do !iSplit => //. by iApply minted_Tag.
  - iNext; iModIntro. iExists p_a, x_a, P_b, X_b, N. by do !iSplit => //. }
wp_pures. wp_apply wp_session_key. wp_pures.
iApply ("Hpost" $! (Some (_, TNonce x_a))).
iRight. iExists _, x_a, X_b. iFrame "tok_rel tok_Xa ψ". iModIntro.
iSplit; first done.
iIntros "%p_b %ePb #key_b". subst P_b.
iAssert (minted (si_key (init_si p_a x_a p_b X_b))) as "#m_k".
{ by iApply minted_si_key. }
iSplit; first done.
iDestruct "res" as "[#p_σ | (%p_b' & %x_b & %e_pb & -> & #key_xb & res)]".
- iDestruct (@public_hmqv_K_forged _ _ _ hmqvN g "init" "resp" p_a x_a p_b
               (TExp g p_a) X_a X_b gNX gNm tags
               with "key_a key_xa key_b p_σ") as "#comp".
  iAssert (public (si_key (init_si p_a x_a p_b X_b))) as "#p_k".
  { by iApply public_si_key. }
  iSplit; last by iLeft.
  do 2!(iSplit; first by []).
  iSplit => //.
  iSplit; first by iIntros "!> _".
  iLeft. iDestruct "comp" as "[?|[? ?]]"; first by iLeft.
  iRight. iSplit => //. iExists x_a. by iSplit.
- move/TExp_g_inj: e_pb => e_pb; subst p_b'.
  rewrite init_resp_si.
  iPoseProof (honest_session_ok p_a p_b x_a x_b
                with "Hkey key_a key_b key_xa key_xb m_k")
    as "#[ok1 ok2]".
  iSplit; last by iRight.
  do 2!(iSplit; first by []).
  iSplit => //.
  iSplit; first by iApply "ok2".
  by iRight.
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
wp_apply (wp_initiator _ _ _ _ _ (λ _ _, True%I) True%I) => //.
{ iFrame "#". by iApply hmqv_key_public. }
{ iSplit => //. iIntros "%x_a %X_b _ _ !>". by iSplit. }
iIntros "%r [[-> _]|Hr]"; first by iApply ("Hpost" $! None); eauto.
iDestruct "Hr" as "(%k & %x_a & %X_b & -> & rel & tok & _ & sess)".
iDestruct ("sess" $! p_b with "[//] key_b") as "(-> & #sess & _)".
iMod (unrelease Init (init_si p_a x_a p_b X_b) with "rel") as "#un".
iModIntro.
iApply ("Hpost" $! (Some (si_key (init_si p_a x_a p_b X_b), TNonce x_a))).
iRight. iExists x_a, X_b. iFrame. iSplit => //.
by iApply unreleased_session_weak.
Qed.
End Verif.
