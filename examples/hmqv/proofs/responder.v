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
Definition resp_state (x_b : nonce) : iProp :=
  hmqv_key x_b ∗ term_token (TExp g x_b) (↑hmqvN.@"ready").

(** The responder answers whatever long-term key [P_a] it is given; its gift is
    for the owner of [P_a], if there is one.  The hook runs only if the
    responder answers, so a caller that lends it [R] gets [R] back otherwise. *)
Lemma wp_responder_accept c P_a X_a p_b N φ ψ R :
  {{{ channel c ∗ cryptis_ctx ∗
      hmqv_ctx ∗ hmqv_pred N φ ∗
      public P_a ∗ public X_a ∗ hmqv_key p_b ∗
      (R ∧
       ∀ x_b,
          secret x_b -∗
          term_token (TExp g x_b) (↑hmqvN.@"res") ={⊤}=∗
          (∀ p_a, ⌜P_a = TExp g p_a⌝ →
             φ p_a p_b (resp_si p_a X_a p_b x_b) Init) ∗
          ψ x_b) }}}
    responder_accept c p_b (TExp g p_b) X_a P_a (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∗ R ∨
      ∃ x_b, ⌜r = Some (resp_secret P_a X_a p_b x_b, TNonce x_b)⌝ ∗
        resp_state x_b ∗
        release_token (TExp g x_b) ∗
        term_token (TExp g x_b) (⊤ ∖ ↑hmqvN) ∗
        ψ x_b }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & #(Hm2 & Hm3 & Hkey) & #N_φ &
             #p_Pa & #p_Xa & #key_b & hook) Hpost".
iPoseProof "key_b" as "[#m_pb #pred_b]".
iPoseProof (hmqv_key_public with "key_b") as "#p_Pb".
wp_lam. wp_pures.
wp_eq_term eP; wp_pures.
  by iApply ("Hpost" $! None); iLeft; iDestruct "hook" as "[$ _]".
wp_apply (wp_mk_ephemeral with "ctx").
iIntros "%x_b s #key_xb #p_Xb tok_rel tok_ready tok_res tok_Xb".
iPoseProof "key_xb" as "[#m_xb _]".
set X_b := TExp g x_b.
wp_pures. wp_apply wp_texp. rewrite -/X_b. wp_pures.
wp_apply wp_hmqv_ke. wp_pures.
set σ := hmqv_K hmqvN "resp" "init" p_b x_b (TExp g p_b) X_b P_a X_a.
wp_eq_term eσ; wp_pures.
  by iApply ("Hpost" $! None); iLeft; iDestruct "hook" as "[$ _]".
iDestruct "hook" as "[_ hook]".
iMod ("hook" $! x_b with "s tok_res") as "[gift ψ]".
iMod (hmqv_ready_alloc_any_init N P_a X_a p_b x_b with "[//] gift")
  as "#ready".
iAssert (minted σ) as "#m_σ".
{ iApply minted_hmqv_K => //; by iApply public_minted. }
wp_list. wp_apply wp_H. wp_list. wp_term_of_list.
wp_apply wp_send => //.
{ rewrite public_of_list /=. do !iSplit => //.
  iApply (public_THashIS with "Hm2 [] []").
  - iApply minted_of_list => /=. do !iSplit => //. by iApply minted_Tag.
  - iNext; iModIntro. iExists P_a, X_a, p_b, x_b, N. by do !iSplit => //. }
wp_pures. iApply ("Hpost" $! (Some (σ, TNonce x_b))). iModIntro.
iRight. iExists x_b. iSplit => //. by iFrame "key_xb ∗ #".
Qed.

Lemma wp_responder_finish c p_a p_b X_a x_b N φ :
  let si := resp_si p_a X_a p_b x_b in
  {{{ channel c ∗ cryptis_ctx ∗
      hmqv_ctx ∗ hmqv_pred N φ ∗
      public X_a ∗ hmqv_key p_a ∗ hmqv_key p_b ∗ resp_state x_b }}}
    responder_finish c (si_secret si) (TNonce x_b) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨
      ⌜r = Some (si_key si, TNonce x_b)⌝ ∗
      session Resp p_a p_b si ∗
      (public (si_key si) ∨ φ p_a p_b si Resp) }}}.
Proof.
move=> si.
iIntros "%Φ (#chan_c & #ctx & #(Hm2 & Hm3 & Hkey) & #N_φ &
             #p_Xa & #key_a & #key_b & [#key_xb tok_ready]) Hpost".
iPoseProof "key_b" as "[#m_pb _]".
iPoseProof "key_xb" as "[#m_xb _]".
iPoseProof (hmqv_key_public with "key_a") as "#p_Pa".
iPoseProof (hmqv_key_public with "key_b") as "#p_Pb".
iPoseProof (hmqv_key_public with "key_xb") as "#p_Xb".
set σ := si_secret si.
iAssert (minted σ) as "#m_σ".
{ iApply minted_hmqv_K => //; by iApply public_minted. }
wp_lam. wp_pures. wp_apply wp_recv => //. iIntros "%A_a #p_Aa".
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
                 (TExp g p_b) (TExp g x_b) X_a gNX gNm tags'
                 with "key_b key_xb key_a p_σ") as "#comp".
    iAssert (public (si_key si)) as "#p_k"; first by iApply public_si_key.
    iModIntro.
    iSplit; last by iLeft.
    do 2!(iSplit; first by []).
    iSplit => //.
    iSplit; first by iIntros "!> _".
    iLeft. iDestruct "comp" as "[?|[? ?]]"; first by iLeft.
    iRight. iSplit => //. iExists x_b. by iSplit.
  - iDestruct "auth" as "(%p_a' & %x_a' & %P_b' & %X_b' & %N' & %e' & %nPb' &
                          #key_xa & #ready_a)".
    move: e' => /Spec.of_list_inj [] eσ /Tag_inj eN.
    subst N'.
    have nσ : resp_secret (TExp g p_a) X_a p_b x_b ≠ one.
      exact: hmqv_K_neq_unit gNX gNm.
    have nK : init_secret p_a' x_a' P_b' X_b' ≠ one by rewrite -eσ.
    have [ePb [eXb [/TExp_g_inj epa eXa]]] :=
      hmqv_K_inj' gNX gNm tags nPb' (@TExp_g_neq_one p_a) nK (eq_sym eσ).
    subst p_a' P_b' X_a X_b'.
    iSpecialize ("ready_a" $! p_b with "[//]").
    iPoseProof (honest_session_ok p_a p_b x_a' x_b
                  with "Hkey key_a key_b key_xa key_xb m_k")
      as "#[ok1 ok2]".
    have e_si : init_si p_a x_a' p_b (TExp g x_b) = si.
      by rewrite /si init_resp_si.
    iMod ("ready_a" with "N_φ tok_ready") as "res".
    iEval (rewrite e_si) in "res".
    iModIntro.
    iSplit; last by iRight.
    do 2!(iSplit; first by []).
    iSplit => //.
    iSplit; first by iApply "ok2".
    by iRight. }
wp_pures. wp_apply wp_session_key. wp_pures.
iApply ("Hpost" $! (Some (si_key si, TNonce x_b))). iModIntro.
iRight. iFrame "res". by iSplit.
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
iIntros "%Φ (#chan_c & #ctx & #? & #N_φ & #p_Xa & #key_a & #key_b & hook)
         Hpost".
wp_lam. wp_pures.
wp_apply (wp_responder_accept _ (TExp g p_a) _ _ _ _ ψ True%I with "[hook]").
{ iFrame "#". iSplitR; first by iApply hmqv_key_public.
  iSplit => //.
  iIntros "%x_b s tok". iMod ("hook" with "s tok") as "[gift $]".
  iIntros "!> %p_a' %e". by move/TExp_g_inj: e => <-. }
iIntros "%r [[-> _]|(%x_b & -> & state & rel & tok & ψ)]"; wp_pures.
  by iApply ("Hpost" $! None); iLeft.
wp_apply (wp_responder_finish with "[$state]"); first by iFrame "#".
iIntros "%r [->|(-> & #sess & res)]".
- iApply ("Hpost" $! None). by iLeft.
- iApply "Hpost". iRight. iExists x_b. by iFrame "∗ #".
Qed.

(** With a peer that need not be honest, the key comes with no guarantee. *)
Lemma wp_responder_confirm_any c P_a X_a p_b N φ ψ :
  {{{ channel c ∗ cryptis_ctx ∗
      hmqv_ctx ∗ hmqv_pred N φ ∗
      public P_a ∗ public X_a ∗ hmqv_key p_b ∗
      (∀ x_b,
          secret x_b -∗
          term_token (TExp g x_b) (↑hmqvN.@"res") ={⊤}=∗
          (∀ p_a, ⌜P_a = TExp g p_a⌝ →
             φ p_a p_b (resp_si p_a X_a p_b x_b) Init) ∗
          ψ x_b) }}}
    responder_confirm c p_b (TExp g p_b) X_a P_a (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨
      ∃ (k : senc_key) x_b, ⌜r = Some (k, TNonce x_b)⌝ ∗ ψ x_b }}}.
Proof.
iIntros "%Φ (#chan_c & #ctx & #? & #? & #? & #? & #? & hook) Hpost".
wp_lam. wp_pures.
wp_apply (wp_responder_accept _ _ _ _ _ _ _ True%I with "[hook]").
{ iFrame "#". by iSplit. }
iIntros "%r [[-> _]|(%x_b & -> & _ & _ & _ & ψ)]"; wp_pures.
  by iApply ("Hpost" $! None); iLeft.
wp_lam. wp_pures. wp_apply wp_recv => //. iIntros "%A_a _".
wp_pures. wp_list. wp_apply wp_H.
wp_eq_term e; last by protocol_failure.
wp_pures. wp_apply wp_session_key. wp_pures.
iApply ("Hpost" $! (Some (_, TNonce x_b))). iRight. iExists _, x_b. by iFrame.
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
