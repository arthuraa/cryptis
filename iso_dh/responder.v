From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.iso_dh Require Import shared.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).
Implicit Types (γ γa γb : gname) (ok : bool).
Implicit Types (ts : nat) (T : gset term).
Implicit Types (si : sess_info).

Variable N : namespace.

Definition responder : val := λ: "c" "skR",
  let: "vkR" := vkey "skR" in
  let: "m1" := recv "c" in
  bind: "m1" := list_of_term "m1" in
  list_match: ["ga"; "vkI"] := "m1" in
  let: "b" := mknonce #() in
  let: "gb" := mkkeyshare "b" in
  let: "m2" := sign (N.@"m2") "skR" (term_of_list ["ga"; "gb"; "vkI"]) in
  send "c" "m2";;
  bind: "m3" := verify (N.@"m3") "vkI" (recv "c") in
  bind: "m3" := list_of_term "m3" in
  list_match: ["ga'"; "gb'"; "vkR'"] := "m3" in
  guard: eq_term "ga" "ga'" && eq_term "gb" "gb'" && eq_term "vkR" "vkR'" in
  let: "gab" := texp "ga" "b" in
  let: "secret" := term_of_list ["vkI"; "vkR"; "ga"; "gb"; "gab"] in
  SOME ("vkI", derive_key "secret").

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_responder c kR :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx N -∗
  public (TKey Open kR) -∗
  {{{ True }}}
    responder c kR
  {{{ okS,
      RET (repr okS);
      if okS is Some (vkI, kS) then ∃ si,
        ⌜vkI = TKey Open (si_init si)⌝ ∗
        ⌜si_resp si = kR⌝ ∗
        ⌜si_key si = kS⌝ ∗
        public vkI ∗
        minted kS ∗
        □ (∀ kt, public (TKey kt kS) ↔ ◇ public kS) ∗
        (public (TKey Seal (si_init si)) ∨ □ (◇ public kS ↔ ▷ False)) ∗
        term_token (si_resp_share si) ⊤
      else True
 }}}.
Proof.
set vkR := TKey Open kR.
iIntros "#chan_c #? (#? & #?) #p_vkR !> %Φ _ Hpost".
wp_lam. wp_pures. wp_apply wp_vkey. wp_pures.
wp_apply wp_recv => //. iIntros "%m1 #p_m1". wp_pures.
wp_list_of_term m1; last by protocol_failure.
wp_pures. wp_list_match => [ga vkI -> {m1}|]; last by protocol_failure.
rewrite public_of_list /=.
iDestruct "p_m1" as "(p_ga & p_vkI & _)".
wp_pures.
wp_apply (wp_mknonce_freshN ∅
          (λ _, False%I)
          iso_dh_pred
          (λ b, {[TExp (TInt 0) b]}))
       => //.
- iIntros "%". rewrite elem_of_empty. iIntros "[]".
- iIntros "%b".
  rewrite big_sepS_singleton minted_TExp minted_TInt /= bi.True_and.
  iModIntro. by iApply bi.equiv_iff.
iIntros "%b _ _ #m_b #p_b #dh_gb token".
set gb := TExp (TInt 0) b.
set gab := TExp ga b.
rewrite big_sepS_singleton.
iAssert (public gb) as "#p_gb".
{ iApply public_TExp_iff; eauto.
  rewrite minted_TInt. iRight. do ![iSplit => //].
  iApply "dh_gb". iPureIntro. by rewrite exps_TExpN. }
wp_pure _ credit:"H1".
wp_pure _ credit:"H2".
wp_apply wp_mkkeyshare => //.
iIntros "_". wp_pures. wp_list. wp_term_of_list.
wp_apply wp_sign. wp_pures.
wp_apply wp_send => //.
{ iApply public_TSealIS => //.
  - by rewrite public_minted !minted_TKey.
  - iModIntro.
    iExists ga, b, vkI.  by do ![iSplitL => //].
  - rewrite minted_of_list /= minted_TExp minted_TInt /=.
    rewrite !public_minted !minted_TKey. by do ![iSplitL => //].
  - iIntros "!> _". rewrite public_of_list /=.
    by eauto. }
wp_pures. wp_apply wp_recv => //. iIntros "%m3 #p_m3".
wp_apply wp_verify. case: Spec.decP; last by protocol_failure.
move=> kI {}m3 e_vkI ->.
rewrite {}e_vkI {vkI}. set vkI := TKey Open kI.
wp_pures. wp_list_of_term m3; last by protocol_failure.
wp_list_match => [ga' gb' vkR' -> {m3}|]; last by protocol_failure.
wp_eq_term e; last by protocol_failure. subst ga'.
wp_eq_term e; last by protocol_failure. subst gb'.
wp_eq_term e; last by protocol_failure. subst vkR'.
wp_pure _ credit:"H3".
wp_apply wp_texp.
wp_pure _ credit:"H4".
iPoseProof (public_TSealE with "p_m3 [//]") as "{p_m3} p_m3".
rewrite public_of_list /=.
wp_pures. wp_list. wp_term_of_list.
wp_pures. pose si := SessInfo kI kR ga gb gab.
wp_apply wp_derive_key. rewrite -[Spec.derive_key _]/(si_key si).
iAssert (|={⊤}=> public (TKey Seal kI) ∨ □ (◇ public (si_key si) ↔ ▷ False))%I
  with "[H4]" as "> #i_m3".
{ iDestruct "p_m3" as "[(p_skI & _) | (#i_m3 & _ & _)]"; first by eauto.
  iMod (lc_fupd_elim_later_pers with "H4 i_m3") as "{i_m3} #i_m3".
  iDestruct "i_m3" as "(%a & %gb' & %kR' & %e_m3 & p_a & pred_a)".
  case/Spec.of_list_inj: e_m3 => -> _ _ {ga gb' kR'} in gb gab si *.
  rewrite TExp_TExpN TExpC2 in gab si *.
  iIntros "!>". iRight. iIntros "!>".
  iApply (bi.iff_trans _ (◇ public gab)).
  iSplit; last by iApply public_dh_secret.
  rewrite public_derive_key public_of_list /=.
  iSplit; first by iIntros "(_ & _ & _ & _ & p_sk & _)".
  iIntros "#>p_gab !>". by do !iSplit. }
iAssert (minted (si_key si)) as "#m_kS".
{ rewrite minted_derive_key !minted_of_list /= !minted_TExp minted_TInt.
  by do !iSplit => //; iApply public_minted. }
iAssert (minted kI) as "#m_kI".
{ iApply minted_TKey. by iApply public_minted. }
wp_pures.
iApply ("Hpost" $! (Some (TKey Open kI, si_key si))).
iModIntro. iExists si. do !iSplit => //.
iIntros "!> %kt".
rewrite public_derive_key.
iApply public_key_derive_key => //.
by rewrite minted_derive_key.
Qed.

End Verif.
