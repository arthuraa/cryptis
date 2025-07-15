From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.examples.iso_dh Require Import impl.
From cryptis.examples.iso_dh.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !iso_dhGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : sign_key).
Implicit Types (failed : bool).
Implicit Types (si : sess_info).
Implicit Types (N : namespace).

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Definition nonce_secrecy failed a : iProp :=
  if failed then True%I
  else (∃ gb, term_meta a (nroot.@"resp_share") gb ∗
                released (TExp (TInt 0) a) ∗
                released gb)%I.

Lemma nonce_secrecy_set failed a gb :
  term_meta a (nroot.@"resp_share") gb ⊢
  nonce_secrecy failed a ↔ ⌜failed⌝ ∨ released (TExp (TInt 0) a) ∧ released gb.
Proof.
iIntros "#meta"; iSplit.
- case: failed; eauto.
  iIntros "(%gb' & #meta' & #rel_a & #rel_b)". iRight.
  iPoseProof (term_meta_agree with "meta meta'") as "->".
  by iSplit.
- case: failed; eauto.
  iIntros "[[]|[#? #?]]". iExists gb. by eauto.
Qed.

Lemma wp_initiator failed c skI skR N φ data :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx -∗
  iso_dh_pred N φ -∗
  minted skI -∗
  minted skR -∗
  (if failed then public skI ∨ public skR else True) -∗
  public data -∗
  {{{ φ data }}}
    initiator c skI (Spec.pkey skR) (Tag N) data
  {{{ okS, RET (repr okS);
      if okS is Some kS then ∃ si,
        ⌜si_init si = skI⌝ ∗
        ⌜si_resp si = skR⌝ ∗
        ⌜si_key si = kS⌝ ∗
        minted kS ∗
        session Init si ∗
        □ (⌜failed⌝ → compromised_session Init si) ∗
        release_token (si_init_share si) ∗
        term_token (si_init_share si) (⊤ ∖ ↑iso_dhN)
      else φ data
 }}}.
Proof.
rewrite /initiator.
set pkI := Spec.pkey skI.
iIntros "#chan_c #ctx #(? & ?) #N_φ".
iIntros "#m_skI #m_skR #failed #p_data %Ψ !> inv_data Hpost".
wp_pures. wp_apply wp_pkey. wp_pures. rewrite -/pkI.
wp_apply (wp_mk_nonce_freshN ∅
            (nonce_secrecy failed)
            iso_dh_key_share
            (λ a, {[a; TExp (TInt 0) a]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%a".
  rewrite big_sepS_union_pers !big_sepS_singleton minted_TExp minted_TInt /=.
  rewrite bi.True_and.
  iSplit; iIntros "!>"; iSplit; eauto; by iIntros "(_ & ?)".
iIntros "%a %fresh %nonce #m_a #s_a #a_pred token".
set ga := TExp (TInt 0) a.
have ?: a ≠ ga.
  by move=> contra; rewrite contra is_nonce_TExp in nonce.
rewrite big_sepS_union; last by set_solver.
rewrite !big_sepS_singleton.
iDestruct "token" as "[token_a token_ga]".
iPoseProof (release_tokenI with "token_ga") as "[token_rel token_ga]" => //.
rewrite (term_token_difference ga (↑iso_dhN.@"failed")); last solve_ndisj.
iDestruct "token_ga" as "[failed_token token_ga]".
wp_pures. wp_apply wp_mk_keyshare => //. rewrite -/ga.
iIntros "_". wp_pures. wp_list. wp_term_of_list.
wp_pure _ credit:"H1".
wp_pure _ credit:"H2".
iAssert (public ga) as "p_ga".
{ iApply public_TExp_iff; eauto.
  rewrite minted_TInt.
  iRight. do 2![iSplit => //].
  iApply "a_pred". iModIntro. iModIntro.
  by rewrite /iso_dh_key_share exps_TExpN. }
wp_apply wp_send => //.
{ rewrite public_of_list /=. do 2?[iSplit => //].
  by iApply public_verify_key. }
wp_pure _ credit:"H3".
wp_pures. wp_apply wp_recv => //.
iIntros "%m2 #p_m2".
wp_apply wp_verify; eauto; iSplit; last by protocol_failure.
iIntros "{p_m2}" => {m2}. iIntros "%m2 #p_m2 #inv".
set pkR := Spec.pkey skR.
wp_pures. wp_list_of_term m2; last by protocol_failure.
wp_pures. wp_list_match => [ga' gb pkI' -> {m2}|]; last by protocol_failure.
wp_eq_term e; last by protocol_failure. subst ga'.
wp_pures. wp_eq_term e; last by protocol_failure. subst pkI'.
rewrite public_of_list /=. iDestruct "p_m2" as "(_ & p_gb & _)".
iPoseProof (public_minted with "p_gb") as "m_gb".
wp_pures. wp_bind (texp _ _). iApply wp_texp.
wp_pures. wp_list. wp_term_of_list. wp_pures.
set gab := TExp gb a.
set seed := Spec.of_list [pkI; pkR; ga; gb; gab].
pose si := SessInfo skI skR ga gb gab.
wp_pures. wp_list. wp_term_of_list.
iMod (term_meta_set' (N := nroot.@"resp_share") gb
       with "token_a") as "[#meta token_a]" => //.
iAssert (public a ↔ ▷ (⌜failed⌝ ∨ released_session si))%I as "{s_a} s_a".
{ iApply (bi.iff_trans _ (▷ □ nonce_secrecy failed a)).
  iSplit => //. rewrite !bi.intuitionistic_intuitionistically.
  iApply bi.later_iff. iApply (nonce_secrecy_set with "meta"). }
iAssert (▷ (⌜failed⌝ ∨ released_session si) → public (si_key si))%I as "s_k1".
{ iIntros "#released".
  rewrite public_senc_key public_of_list /=.
  do !iSplit => //; try by iApply sign_key_public.
  - by iApply public_verify_key.
  - by iApply public_verify_key.
  - iApply public_TExp => //. by iApply "s_a". }
iAssert (|={⊤}=>
           □ (⌜failed⌝ → compromised_session Init si) ∗
           ∃ failed,
             term_meta ga (iso_dhN.@"failed") failed ∗
             if failed then public (si_init si) ∨ public (si_resp si)
             else □ (public (si_key si) → ▷ released_session si))%I
  with "[token_a failed_token H3]" as "{inv} > #[comp s_k2]".
{ case: failed.
  { iMod (term_meta_set (iso_dhN.@"failed") true with "failed_token")
      as "#?"; first by solve_ndisj.
    iModIntro. iSplit.
    { iIntros "!> _". do !iSplit => //.
      iApply "s_k1". by eauto. }
    iExists true. iSplit => //. }
  iDestruct "inv" as "[comp|#inv]".
  { iMod (term_meta_set (iso_dhN.@"failed") true with "failed_token")
      as "#?"; first by solve_ndisj.
    iModIntro. iSplit; first by iIntros "!> []".
    iExists true. iSplit => //. by eauto. }
  iMod (lc_fupd_elim_later_pers with "H3 inv") as "{inv} #inv".
  iDestruct "inv" as "(%ga' & %b & %pkI' & %e_m2 & s_b & pred_b)".
  case/Spec.of_list_inj: e_m2 => <- -> /Spec.sign_pkey_inj <- {ga' gb pkI'}
    in gab seed si *.
  iDestruct "s_b" as "[?|s_b]".
  { iMod (term_meta_set (iso_dhN.@"failed") true with "failed_token")
      as "#?"; first by solve_ndisj.
    iModIntro.
    iSplit; first by iIntros "!> []".
    iExists true. by eauto. }
  iMod (term_meta_set (iso_dhN.@"failed") false with "failed_token")
    as "#?"; first by solve_ndisj.
  rewrite !TExp_TExpN TExpC2 in gab seed si *.
  iIntros "!>".
  iSplit; first by iIntros "!> []".
  iExists false. iSplit => //. iIntros "!> {s_k1} #p_k".
  rewrite public_senc_key public_of_list /=.
  iDestruct "p_k" as "(_ & _ & _ & _ & p_gab & _)".
  rewrite bi.False_or.
  by iPoseProof (public_dh_secret' b a with "[//] [//] [//] [//] [//]") as ">?".
}
iMod (iso_dh_ready_alloc gb with "[//] inv_data") as "#?".
wp_pures. wp_apply wp_sign; eauto.
{ rewrite public_of_list /=. do ![iSplit => //].
  - by iApply public_verify_key.
  - by rewrite public_Tag; eauto. }
{ iRight. iExists a, gb, skR, _, _. iModIntro.
  iDestruct "s_k2" as "(%failed' & ? & s_k2)".
  iSplit => //. case: failed'; by eauto. }
iIntros "%m3 #p_m3". wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_derive_senc_key.
set k := SEncKey _.
iAssert (minted k) as "#m_k".
{ rewrite minted_senc minted_of_list /=.
  rewrite !minted_TExp /= minted_TInt.
  rewrite !minted_pkey. by do !iSplit => //. }
wp_pures. iApply ("Hpost" $! (Some k)).
iExists si. iFrame. do !iSplitR => //.
- iIntros "!> !> #rel". iApply "s_k1". by eauto.
iApply (term_token_drop with "token_ga"). solve_ndisj.
Qed.

Lemma wp_initiator_weak c skI skR N :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx -∗
  iso_dh_pred N (λ _, True)%I -∗
  minted skI -∗
  minted skR -∗
  {{{ True }}}
    initiator c skI (Spec.pkey skR) (Tag N) (TInt 0)
  {{{ okS, RET (repr okS);
      if okS is Some kS then ∃ si,
        ⌜si_init si = skI⌝ ∗
        ⌜si_resp si = skR⌝ ∗
        ⌜si_key si = kS⌝ ∗
        minted kS ∗
        ((public (si_init si) ∨ public (si_resp si))
          ∨ □ (public kS ↔ ▷ False)) ∗
        term_token (si_init_share si) (⊤ ∖ ↑iso_dhN)
      else True
 }}}.
Proof.
iIntros "#chan_c #ctx #? #? #m_skI #m_skR %Ψ !> _ Hpost".
iApply wp_fupd. wp_apply (wp_initiator false) => //.
{ by rewrite public_TInt. }
iIntros "%okS HkS". case: okS => [kS|]; last by iApply ("Hpost" $! None).
iDestruct "HkS" as "(%si & <- & <- & <- & #? & #sess & #? & rel & tok)".
iMod (unrelease with "rel") as "#un". iModIntro.
iApply ("Hpost" $! (Some (si_key si))).
iExists si. iFrame. do !iSplit => //.
iDestruct "sess" as "(#? & %failed & #failed & #comp)".
case: failed; first by eauto.
iRight. iApply (unreleased_key_secrecy Init) => //.
iModIntro. by iSplit.
Qed.

End Verif.
