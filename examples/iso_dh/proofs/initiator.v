From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.lib Require Import dh.
From cryptis.examples.iso_dh Require Import impl.
From cryptis.examples.iso_dh.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !iso_dhGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : sign_key).
Implicit Types (si : sess_info).
Implicit Types (N : namespace).
Implicit Types (φ : sess_info → role → iProp) (ρ : sess_info → iProp).

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iLeft;
     iDestruct "hook" as "[$ _]".

(** The secrecy of the initiator's DH exponent: compromise makes it public, and
    so does the release of the session, once the responder's share is known. *)
Definition init_secrecy ρ skI skR (a : nonce) : iProp :=
  let ga := TExp (TInt 0) a in
  term_meta ga (iso_dhN.@"compromised") true ∨
  ∃ gb, term_meta ga (iso_dhN.@"resp_share") gb ∗
        ρ (SessInfo skI skR ga gb (TExp gb a)).

(* The hook runs only if the session succeeds, so a caller that lends it [R]
   gets [R] back otherwise. *)
Lemma wp_initiator c skI skR N φ ρ ψ R :
  channel c ∗
  cryptis_ctx ∗
  iso_dh_ctx ∗
  iso_dh_pred N φ ρ ∗
  minted skI ∗
  minted skR -∗
  {{{ R ∧
      ∀ (a : nonce) gb,
        let si := SessInfo skI skR (TExp (TInt 0) a) gb (TExp gb a) in
        term_token (si_init_share si) (⊤ ∖ ↑iso_dhN) ={⊤}=∗
        φ si Resp ∗ ψ si }}}
    initiator c skI (Spec.pkey skR) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∗ R ∨ ∃ (a : nonce) gb,
        let si := SessInfo skI skR (TExp (TInt 0) a) gb (TExp gb a) in
        ⌜r = Some (si_key si)⌝ ∗
        session ρ Init si ∗ ψ si ∗
        (compromised Init si ∨ φ si Init)
  }}}.
Proof.
rewrite /initiator.
set pkI := Spec.pkey skI.
iIntros "(#chan_c & #ctx & #(? & ?) & #N_φ & #m_skI & #m_skR)".
iIntros "!> %Ψ hook Hpost".
wp_pures. wp_apply wp_pkey. wp_pures. rewrite -/pkI.
wp_apply (wp_mk_nonce_freshN ∅ (init_secrecy ρ skI skR) dh_key_share
            (λ a, {[TExp (TInt 0) a]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%a".
  rewrite big_sepS_singleton minted_TExp //. rewrite minted_TInt bi.True_and.
  iIntros "!>"; iSplit; eauto; by iIntros "(_ & ?)".
iIntros "%a %fresh #m_a #s_a #a_pred _ token_ga".
have Nm_a : negb (is_mul (TNonce a)) by [].
(* [dh.v] takes the generator as a parameter; ISO-DH always uses [TInt 0]. *)
have NInt : negb (is_exp (TInt 0)) by [].
have NIntM : negb (is_gmul (TInt 0)) by [].
iAssert (public (TInt 0)) as "#p_g"; first by rewrite public_TInt.
set ga := TExp (TInt 0) a.
rewrite !big_sepS_singleton.
rewrite (term_token_difference ga (↑iso_dhN)) //.
iDestruct "token_ga" as "[token_N token_ga]".
iDestruct (term_token_difference ga (↑iso_dhN.@"compromised") with "token_N")
  as "[comp_token token_N]"; first solve_ndisj.
iDestruct (term_token_difference ga (↑iso_dhN.@"resp_share") with "token_N")
  as "[share_token token_N]"; first solve_ndisj.
iDestruct (term_token_difference ga (↑iso_dhN.@"ready") with "token_N")
  as "[ready_token _]"; first solve_ndisj.
wp_pures. wp_apply wp_mk_keyshare => //. rewrite -/ga.
iIntros "_". wp_pures. wp_list. wp_term_of_list.
wp_pure _ credit:"H1".
wp_pure _ credit:"H2".
iAssert (public ga) as "p_ga";
  first by iApply (public_dh_share NInt NIntM Nm_a).
wp_apply wp_send => //.
{ rewrite public_of_list /=. do 2?[iSplit => //].
  by iApply public_verify_key. }
wp_pures. wp_apply wp_recv => //.
iIntros "%m2 #p_m2".
wp_apply wp_verify; eauto; iSplit; last by protocol_failure.
iIntros "{p_m2}" => {m2}. iIntros "%m2 #p_m2 #inv".
set pkR := Spec.pkey skR.
wp_pures. wp_list_of_term m2; last by protocol_failure.
wp_pures. wp_list_match => [ga' gb pkI' N' -> {m2}|]; last by protocol_failure.
wp_eq_term e; last by protocol_failure. subst ga'.
wp_pures. wp_eq_term e; last by protocol_failure. subst pkI'.
wp_pures. wp_eq_term e; last by protocol_failure. subst N'.
rewrite public_of_list /=. iDestruct "p_m2" as "(_ & p_gb & _)".
iPoseProof (public_minted with "p_gb") as "m_gb".
wp_pures. wp_bind (texp _ _). iApply wp_texp.
wp_pures. wp_list. wp_term_of_list. wp_pures.
set gab := TExp gb a.
pose si := SessInfo skI skR ga gb gab.
wp_pures. wp_list. wp_term_of_list.
iMod (term_meta_set (iso_dhN.@"resp_share") gb with "share_token")
  as "#meta" => //.
iAssert (□ (public a ↔ ▷ □ (compromised Init si ∨ ρ si)))%I
  as "{s_a} #s_a".
{ iModIntro. iSplit.
  - iIntros "#p_a". iDestruct ("s_a" with "p_a") as "#H". iNext.
    iDestruct "H" as "#[c|(%gb' & #meta' & #r)]"; iModIntro; first by iLeft.
    iPoseProof (term_meta_agree with "meta meta'") as "%e".
    by subst gb'; iRight.
  - iIntros "#H". iApply "s_a". iNext.
    iDestruct "H" as "#[c|r]"; iModIntro; first by iLeft.
    iRight. iExists gb. by iSplit. }
iAssert (□ (▷ □ (compromised Init si ∨ ρ si) → public (si_key si)))%I
  as "#s_k1".
{ iIntros "!> #H".
  rewrite public_senc_key public_of_list /=.
  do !iSplit => //; try by iApply sign_key_public.
  - by iApply public_verify_key.
  - by iApply public_verify_key.
  - iApply public_TExp => //. by iApply "s_a". }
iAssert (minted (si_key si)) as "#m_k".
{ rewrite minted_senc minted_of_list /= !minted_pkey.
  do !iSplit => //; by iApply all_minted_TExp; rewrite ?minted_TInt; iSplit. }
(* A valid signature on [m2] was either forged, so the initiator gives up and
   publishes its exponent, or produced by the honest responder, which vouches
   for its share and hands over the escrowed resources. *)
iAssert (|={⊤}=>
           session ρ Init si ∗ (compromised Init si ∨ φ si Init) ∗
           ((public skI ∨ public skR) ∨
            ∃ φ' ρ', usage gb N ∗ iso_dh_pred N φ' ρ' ∗
              □ (public (si_key si) → ▷ □ ρ' si)))%I
  with "[comp_token ready_token H2]" as "> (#sess & res & #s_k2)".
{ iDestruct "inv" as "[#comp|#inv]".
  - iMod (term_meta_set (iso_dhN.@"compromised") true with "comp_token")
      as "#c"; first solve_ndisj.
    iAssert (public (si_key si)) as "#p_k".
    { iApply "s_k1". iModIntro. iModIntro. by iLeft. }
    iModIntro. iSplit.
    + iSplit; first done. iSplit; first by iIntros "!> _".
      iLeft. iSplit; first done. by iSplit; first iRight.
    + iSplit; first by iLeft. by iLeft; iRight.
  - iDestruct "inv"
      as "(%ga' & %b & %skI' & %N' & %φ' & %ρ' & %e_m2 & #N_φ' & #s_b
           & #pred_b & #use & #ready)".
    have Nm_b : negb (is_mul (TNonce b)) by [].
    case/Spec.of_list_inj: e_m2
        => <- -> /Spec.sign_pkey_inj <- /Tag_inj <- {ga' gb skI' N'}
      in gab si *.
    rewrite TExpC in gab si *.
    iMod (term_meta_set (iso_dhN.@"compromised") false with "comp_token")
      as "#nc"; first solve_ndisj.
    iAssert (□ (¬ compromised Init si))%I as "#nc'".
    { iIntros "!> #c". by iDestruct (term_meta_agree with "c nc") as %?. }
    iDestruct (iso_dh_pred_agree with "N_φ N_φ'") as "[_ #ρ_eq]".
    iSpecialize ("ρ_eq" $! si).
    iAssert (□ (public a ↔ ▷ □ ρ si))%I as "#s_a'".
    { iModIntro. iSplit.
      - iIntros "#p_a". iDestruct ("s_a" with "p_a") as "#H". iNext.
        iDestruct "H" as "#[c|r]"; last done.
        by iDestruct ("nc'" with "c") as "[]".
      - iIntros "#r". iApply "s_a". iNext. iModIntro. by iRight. }
    iAssert (□ (public b ↔ ▷ □ ρ si))%I as "#s_b'".
    { iModIntro. iSplit.
      - iIntros "#p_b". iDestruct ("s_b" with "p_b") as "#H". iNext.
        by iRewrite "ρ_eq".
      - iIntros "#r". iApply "s_b". iNext. iRewrite "ρ_eq" in "r".
        by iModIntro. }
    iAssert (□ (public (si_key si) → ▷ □ ρ si))%I as "#ok".
    { iIntros "!> #p_k".
      rewrite public_senc_key public_of_list /=.
      iDestruct "p_k" as "(_ & _ & _ & _ & p_gab & _)".
      iEval (rewrite /gab TExpC TExpA) in "p_gab".
      iApply (@public_dh_secret' _ _ _ (TInt 0) (TNonce b) (TNonce a) _
                NInt NIntM Nm_b Nm_a with "s_b' pred_b s_a' a_pred p_gab"). }
    iMod ("ready" with "N_φ ready_token") as "res".
    iMod (lc_fupd_elim_later with "H2 res") as "res".
    iModIntro. iSplit.
    + iSplit; first done.
      iSplit; first by iIntros "!> #r"; iApply "s_k1"; iNext; iModIntro; iRight.
      by iRight; iSplit.
    + iSplitL "res"; first by iRight.
      iRight. iExists φ', ρ'. iSplit; first done. iSplit; first done.
      iIntros "!> #p_k". iDestruct ("ok" with "p_k") as "#r". iNext.
      by iRewrite -"ρ_eq". }
iDestruct "hook" as "[_ hook]".
iMod ("hook" $! a gb with "token_ga") as "[gift ψ]".
iMod (iso_dh_ready_alloc N si Resp with "N_φ gift") as "#ready_R".
wp_pures. wp_apply wp_sign; eauto.
{ rewrite public_of_list /=. do ![iSplit => //].
  by iApply public_verify_key. }
{ iRight. iModIntro. iExists a, gb, skR. iSplit => //.
  iDestruct "s_k2" as "[?|(%φ' & %ρ' & #use & #N_φ' & #ok)]"; first by iLeft.
  iRight. iExists N, φ', ρ'. by do !iSplit. }
iIntros "%m3 #p_m3". wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_derive_senc_key.
wp_pures. iApply ("Hpost" $! (Some (si_key si))).
iRight. iExists a, gb. iFrame. iModIntro. by iSplit.
Qed.

End Verif.
