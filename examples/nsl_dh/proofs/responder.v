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

Implicit Types (rl : role) (t pkI pkR ga kS : term).
Implicit Types (skI skR : aenc_key).
Implicit Types (failed : bool).
Implicit Types (si : sess_info) (osi : option sess_info).
Implicit Types (N : namespace) (data : term).
Implicit Types (ores : option (term * term)).

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); eauto.

Lemma wp_responder_listen c skR :
  {{{ channel c ∗ cryptis_ctx ∗ nsl_dh_ctx ∗ minted skR }}}
    responder_listen c skR
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ ga skI,
        ⌜r = Some (ga, Spec.pkey skI)⌝ ∗
        public ga ∗ minted skI }}}.
Proof. Admitted.

Lemma wp_responder_confirm failed c skR skI ga N φ :
  {{{ channel c ∗ cryptis_ctx ∗
      nsl_dh_ctx ∗ nsl_dh_pred N φ ∗
      public ga ∗ minted skI ∗ minted skR ∗
      (∀ b,
          let gb := TExp (TInt 0) b in
          let gab := TExp ga b in
          let si := SessInfo skI skR ga gb gab in
          term_token (si_resp_share si) (↑nsl_dhN.@"res") ={⊤}=∗
           φ (si_init si) (si_resp si) si Init ∗
           φ (si_init si) (si_resp si) si Resp) ∗
      if failed then public skR else True }}}
    responder_confirm c skR ga (Spec.pkey skI) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_key si)⌝ ∗
        session skI skR si ∗
        □ (⌜failed⌝ → public (si_key si)) ∗
        release_token (si_resp_share si) ∗
        term_token (si_resp_share si) (⊤ ∖ ↑nsl_dhN) ∗
        φ skI skR si Resp }}}.
Proof. Admitted.

Lemma wp_responder failed c skR N φ :
  {{{ channel c ∗ cryptis_ctx ∗
      nsl_dh_ctx ∗ nsl_dh_pred N φ ∗
      minted skR ∗
      (∀ skI ga b,
          let gb := TExp (TInt 0) b in
          let gab := TExp ga b in
          let si := SessInfo skI skR ga gb gab in
          term_token (si_resp_share si) (↑nsl_dhN.@"res") ={⊤}=∗
           φ (si_init si) (si_resp si) si Init ∗
           φ (si_init si) (si_resp si) si Resp) ∗
      if failed then public skR else True }}}
    responder c skR (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI si,
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session skI skR si ∗
        □ (⌜failed⌝ → public (si_key si)) ∗
        release_token (si_resp_share si) ∗
        term_token (si_resp_share si) (⊤ ∖ ↑nsl_dhN) ∗
        φ skI skR si Resp }}}.
Proof. Admitted.

Lemma wp_responder_simple c skR N :
  {{{ channel c ∗ cryptis_ctx ∗
      nsl_dh_ctx ∗ nsl_dh_pred N (λ _ _ _ _, True)%I ∗ minted skR }}}
    responder c skR (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI si,
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session skI skR si ∗
        release_token (si_resp_share si) ∗
        term_token (si_resp_share si) (⊤ ∖ ↑nsl_dhN) }}}.
Proof. Admitted.

Lemma wp_responder_weak c skR N :
  channel c ∗ cryptis_ctx ∗ nsl_dh_ctx ∗
  nsl_dh_pred N (λ _ _ _ _, True)%I ∗ minted skR -∗
  {{{ True }}}
    responder c skR (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ skI si,
        ⌜r = Some (Spec.pkey skI, si_key si)⌝ ∗
        session_weak skI skR si ∗
        term_token (si_resp_share si) (⊤ ∖ ↑nsl_dhN) }}}.
Proof. Admitted.

End Verif.
