From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.examples.nsl_dh Require Import impl.
From cryptis.examples.nsl_dh.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !nsl_dhGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : aenc_key).
Implicit Types (failed : bool).
Implicit Types (si : sess_info).
Implicit Types (N : namespace).

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); eauto.

Definition nonce_secrecy a : iProp :=
  term_meta (TExp (TInt 0) a) (nsl_dhN.@"failed") true ∨
  ∃ gb, term_meta (TExp (TInt 0) a) (nsl_dhN.@"resp_share") gb ∗
          released (TExp (TInt 0) a) ∗
          released gb.

Lemma nonce_secrecy_set a gb :
  term_meta (TExp (TInt 0) a) (nsl_dhN.@"resp_share") gb ⊢
  nonce_secrecy a ↔
  term_meta (TExp (TInt 0) a) (nsl_dhN.@"failed") true ∨
  released (TExp (TInt 0) a) ∧ released gb.
Proof.
iIntros "#meta"; iSplit.
- iIntros "[#?|Ha]"; eauto.
  iDestruct "Ha" as "(%gb' & #meta' & #rel_a & #rel_b)". iRight.
  iPoseProof (term_meta_agree with "meta meta'") as "->".
  by iSplit.
- rewrite /nonce_secrecy. iIntros "[#?|[#? #?]]"; eauto.
Qed.

Lemma wp_initiator_send failed c skI skR N φ :
  channel c ∗
  cryptis_ctx ∗
  nsl_dh_ctx ∗
  nsl_dh_pred N φ ∗
  minted skI ∗
  minted skR ∗
  (if failed then public skI ∨ public skR else True) -∗
  {{{ True }}}
    initiator_send c skI (Spec.pkey skR) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ a gb,
        let ga := TExp (TInt 0) a in
        let si := SessInfo skI skR ga gb (TExp gb a) in
        ⌜r = Some (a, ga, gb)⌝ ∗
        session skI skR si ∗
        □ (⌜failed⌝ → public (si_key si)) ∗
        release_token (si_init_share si) ∗
        term_token (si_init_share si) (⊤ ∖ ↑nsl_dhN) ∗
        (public (si_key si) ∨ φ skI skR si Init)
  }}}.
Proof. Admitted.

Lemma wp_initiator_confirm c skI skR a gb φ :
  let ga := TExp (TInt 0) a in
  let si := SessInfo skI skR ga gb (TExp gb a) in
  channel c ∗
  cryptis_ctx ∗
  nsl_dh_ctx ∗
  minted skI ∗
  minted skR ∗
  session skI skR si -∗
  {{{ □ (⌜false⌝ → public (si_key si)) ∗
      release_token (si_init_share si) ∗
      term_token (si_init_share si) (⊤ ∖ ↑nsl_dhN) ∗
      (public (si_key si) ∨ φ skI skR si Init) }}}
    initiator_confirm c skI (Spec.pkey skR) a ga gb
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨
        ⌜r = Some (si_key si)⌝ ∗
        session skI skR si ∗
        release_token (si_init_share si) ∗
        term_token (si_init_share si) (⊤ ∖ ↑nsl_dhN) ∗
        (public (si_key si) ∨ φ skI skR si Init)
  }}}.
Proof. Admitted.

Lemma wp_initiator failed c skI skR N φ :
  channel c ∗
  cryptis_ctx ∗
  nsl_dh_ctx ∗
  nsl_dh_pred N φ ∗
  minted skI ∗
  minted skR ∗
  (if failed then public skI ∨ public skR else True) -∗
  {{{ True }}}
    initiator c skI (Spec.pkey skR) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session skI skR si ∗
        □ (⌜failed⌝ → public (si_key si)) ∗
        release_token (si_init_share si) ∗
        term_token (si_init_share si) (⊤ ∖ ↑nsl_dhN) ∗
        (public (si_key si) ∨ φ skI skR si Init)
  }}}.
Proof. Admitted.

Lemma wp_initiator_weak c skI skR N :
  channel c ∗
  cryptis_ctx ∗
  nsl_dh_ctx ∗
  nsl_dh_pred N (λ _ _ _ _, True)%I ∗
  minted skI ∗
  minted skR -∗
  {{{ True }}}
    initiator c skI (Spec.pkey skR) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session_weak skI skR si ∗
        term_token (si_init_share si) (⊤ ∖ ↑nsl_dhN)
  }}}.
Proof. Admitted.

End Verif.
