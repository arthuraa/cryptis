From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.dh_auth Require Import shared.

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

Definition responder : val := λ: "c" "vkR" "skR",
  let: "m1" := recv "c" in
  bind: "m1" := list_of_term "m1" in
  list_match: ["ga"; "vkI"] := "m1" in
  bind: "kt" := is_key "vkI" in
  assert: "kt" = repr Dec in
  let: "b" := mknonce #() in
  let: "gb" := mkkeyshare "b" in
  let: "m2" := tenc (N.@"m2") "skR" (term_of_list ["ga"; "gb"; "vkI"]) in
  send "c" "m2";;
  bind: "m3" := tdec (N.@"m3") "vkI" (recv "c") in
  bind: "m3" := list_of_term "m3" in
  list_match: ["ga'"; "gb'"; "vkR'"] := "m3" in
  assert: eq_term "ga" "ga'" && eq_term "gb" "gb'" && eq_term "vkR" "vkR'" in
  let: "gab" := texp "ga" "b" in
  let: "secret" := term_of_list ["ga"; "gb"; "gab"] in
  let: "kS" := tag (nroot.@"keys".@"sym") "secret" in
  SOME ("vkI", mkskey "kS").

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_responder c kR dq n :
  channel c -∗
  cryptis_ctx -∗
  dh_auth_ctx N -∗
  public (TKey Dec kR) -∗
  {{{ ●Ph{dq} n }}}
    responder c (TKey Dec kR) (TKey Enc kR)
  {{{ okS,
      RET (repr ((λ p, pair p.1 (Spec.mkskey p.2)) <$> okS));
      ●Ph{dq} n ∗
      if okS is Some (vkI, kS) then ∃ kI,
        let si := SessInfo kI kR kS n in
        ⌜vkI = TKey Dec kI⌝ ∗
        public vkI ∗
        minted kS ∗
        □ (∀ kt, public (TKey kt kS) ↔ ▷ session_fail si) ∗
        session si ∗
        term_token kS (↑nroot.@"server")
      else True
 }}}.
Proof.
iIntros "#chan_c #? (#? & #?) #p_vkR !> %Φ phase_auth Hpost".
wp_lam. wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m1 #p_m1". wp_pures.
wp_list_of_term m1; last by protocol_failure.
wp_pures. wp_list_match => [ga vkI -> {m1}|]; last by protocol_failure.
rewrite public_of_list /=.
iDestruct "p_m1" as "(p_ga & p_vkI & _)".
iPoseProof (public_minted with "p_ga") as "m_ga".
iMod (minted_atI with "[//] phase_auth m_ga")
  as "[phase_auth #ma_ga]"; first by solve_ndisj.
wp_bind (is_key _). iApply wp_is_key.
case: Spec.is_keyP => [kt kI -> {vkI}|]; last by protocol_failure.
wp_pures. case: kt => //=; first by protocol_failure.
wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce_freshN ∅
          (λ _, public_at n (TKey Enc kI) ∨
                public_at n (TKey Enc kR))%I
          dh_auth_pred
          (λ b, {[Spec.tag (nroot.@"keys".@"sym")
                    (Spec.of_list [ga; TExp (TInt 0) [b]; Spec.texp ga b])]}))
       => //.
- iIntros "%". rewrite elem_of_empty. iIntros "[]".
- iIntros "%b".
  rewrite big_sepS_singleton minted_tag minted_of_list /=.
  rewrite minted_TExp minted_TInt /=.
  iModIntro. iSplit.
  + iIntros "#?". do !iSplit => //.
    by iApply minted_texp => //.
  + by iIntros "(_ & (_ & ? & _) & _)".
iIntros "%b _ #m_b #p_b #dh_gb token".
rewrite big_sepS_singleton.
set gb := TExp (TInt 0) [b].
set gab := Spec.texp ga b.
set kS := Spec.tag _ _.
rewrite (term_token_difference _ (↑nroot.@"client")) //.
iDestruct "token" as "[client token]".
iMod (escrowI cryptisN _ (term_token ga ⊤) (term_token kS (↑nroot.@"client"))
       with "client []") as "#client".
{ iExists (term_meta ga nroot ()). iSplit.
  - iIntros "!> [token #meta]".
    by iDestruct (term_meta_token with "token meta") as "[]".
  - iIntros "!> token".
    by iMod (term_meta_set nroot () with "token") as "#meta". }
rewrite (term_token_difference _ (↑nroot.@"server") (_ ∖ _)); last solve_ndisj.
iDestruct "token" as "[server token]".
iMod (term_meta_set (nroot.@"info") (kI, kR, n) with "token") as "#info".
  solve_ndisj.
iAssert (public gb) as "#p_gb".
{ iApply public_TExp1. rewrite minted_TInt.
  do ![iSplit => //].
  iRight. iApply "dh_gb". iIntros "!> !> %g %ts %e".
  case/TExp_inj: e => _ perm.
  by rewrite -(Permutation_length perm). }
wp_pure _ credit:"H1".
wp_pure _ credit:"H2".
wp_bind (mkkeyshare _). iApply wp_mkkeyshare => //.
iIntros "!> _". wp_pures. wp_list. wp_term_of_list. wp_tenc.
iPoseProof (phase_auth_frag with "phase_auth") as "#phaseR".
wp_pures. wp_bind (send _ _). iApply wp_send => //.
{ iModIntro.
  iApply public_TEncIS => //.
  - by rewrite public_minted !minted_TKey.
  - iModIntro.
    iExists ga, b, kI, n.  by do ![iSplitL => //].
  - rewrite minted_of_list /= minted_TExp minted_TInt /=.
    rewrite !public_minted !minted_TKey. by do ![iSplitL => //].
  - iIntros "!> _". rewrite public_of_list /=.
    by eauto. }
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m3 #p_m3".
wp_tdec m3; last by protocol_failure.
wp_pures. wp_list_of_term m3; last by protocol_failure.
wp_list_match => [ga' gb' vkR' -> {m3}|]; last by protocol_failure.
wp_eq_term e; last by protocol_failure. subst ga'.
wp_eq_term e; last by protocol_failure. subst gb'.
wp_eq_term e; last by protocol_failure. subst vkR'.
wp_pure _ credit:"H3".
wp_bind (texp _ _). iApply wp_texp.
wp_pure _ credit:"H4".
iPoseProof (public_TEncE with "p_m3 [//]") as "{p_m3} p_m3".
rewrite public_of_list /=.
wp_pures. wp_list. wp_term_of_list.
wp_pures. wp_tag. rewrite -/kS. pose si := SessInfo kI kR kS n.
iAssert ( |={⊤}=> ●Ph{dq} n ∗
  □ (session_fail si ∨
  ∃ a,
    ⌜ga = TExp (TInt 0) [a]⌝ ∗
    (public a ↔ ▷ □ session_fail si) ∗
    (∀ t, dh_pred a t ↔ ▷ □ dh_auth_pred t)))%I
  with "[phase_auth H3 H4]"
  as "{p_m3} > [phase_auth #i_m3]".
{ iDestruct "p_m3" as "[(p_skI & _) | (#i_m3 & _ & _)]".
  { iMod (public_atI with "[//] H3 phase_auth p_skI")
      as "[phase_auth #comp]" => //; try by solve_ndisj.
    iFrame. iLeft. iIntros "!> !>". by iLeft. }
  iMod (lc_fupd_elim_later_pers with "H4 i_m3") as "{i_m3} #i_m3".
  iDestruct "i_m3" as "(%a & %gb' & %kR' & %n' & %e_m3 &
                        p_a & pred_a & i_m3)".
  case/Spec.of_list_inj: e_m3 => -> <- <- {ga gb' kR'} in gb gab kS si *.
  iDestruct "i_m3" as "[i_m3 | i_m3]".
  { iPoseProof (public_at_public with "i_m3") as "i_m3'".
    iMod (public_atI with "[//] H3 phase_auth i_m3'")
      as "[phase_auth #comp]" => //; try by solve_ndisj.
    iFrame. iIntros "!> !>". iLeft. by iRight. }
  rewrite Spec.texpA TExpC2 -(Spec.texpA _ [a] b) -/gab -/kS.
  iPoseProof (term_meta_agree with "info i_m3") as "{i_m3} %e".
  case: e => <- {n'}.
  iFrame. iIntros "!> !>".
  iRight. iExists a. by do ![iSplitL => //]. }
iAssert (minted kS) as "#m_kS".
{ iApply minted_tag.
  rewrite minted_of_list /=. do !iSplit => //.
  - by iApply public_minted.
  - iApply minted_texp => //. }
iAssert (minted kI) as "#m_kI".
{ iApply minted_TKey. by iApply public_minted. }
wp_pures. wp_bind (mkskey _). iApply wp_mkskey. wp_pures.
iAssert (□ (∀ kt, public (TKey kt kS) ↔ ▷ session_fail si))%I
  as "#sec_sk".
{ iIntros "!> %kt". iSplit; last first.
  { iIntros "#comp". iApply public_TKey. iLeft.
    iApply public_tag.
    rewrite public_of_list /=.
    do !iSplit => //.
    iApply public_texp => //.
    iApply "p_b". eauto. }
  iIntros "#p_sk".
  iPoseProof (public_sym_keyE with "[//] p_sk") as ">p_kS".
  iDestruct "i_m3" as "[compromise|i_m3]" => //.
  iDestruct "i_m3" as "(%a & -> & p_a & pred_a)".
  rewrite Spec.texpA TExpC2 in gab kS si *.
  rewrite public_of_list /=.
  iDestruct "p_kS" as "(_ & _ & p_kS & _)".
  rewrite /gab public_TExp2.
  iDestruct "p_kS" as "[[_ p_b'] | [ [_ p_a'] | (_ & contra & _)]]".
  - iPoseProof ("p_b" with "p_b'") as "?". by eauto.
  - iPoseProof ("p_a" with "p_a'") as "{p_a} p_a". by eauto.
  + iPoseProof ("pred_a" with "contra") as ">%contra".
    by have := contra _ _ eq_refl. }
iApply ("Hpost" $! (Some (TKey Dec kI, kS))).
iFrame. iModIntro. iExists kI. by do !iSplit => //.
Qed.

End Verif.
