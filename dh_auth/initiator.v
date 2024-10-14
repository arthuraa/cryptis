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

Definition initiator : val := λ: "c" "vkI" "skI" "vkR",
  let: "a"    := mknonce #() in
  let: "ga"   := mkkeyshare "a" in
  let: "m1"   := term_of_list ["ga"; "vkI"] in
  send "c" "m1";;
  bind: "m2"   := tdec (N.@"m2") "vkR" (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["ga'"; "gb"; "vkI'"] := "m2" in
  assert: eq_term "ga" "ga'" && eq_term "vkI" "vkI'" in
  let: "gab" := texp "gb" "a" in
  let: "secret" := term_of_list ["ga"; "gb"; "gab"] in
  let: "kS" := tag (nroot.@"keys".@"sym") "secret" in
  let: "m3" := tenc (N.@"m3") "skI" (term_of_list ["ga"; "gb"; "vkR"]) in
  send "c" "m3";;
  SOME (mkskey "kS").

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_initiator c kI kR dq n T :
  channel c -∗
  cryptis_ctx -∗
  dh_auth_ctx N -∗
  public (TKey Dec kI) -∗
  public (TKey Dec kR) -∗
  {{{ ●H{dq|n} T }}}
    initiator c (TKey Dec kI) (TKey Enc kI) (TKey Dec kR)
  {{{ okS, RET (repr (Spec.mkskey <$> okS));
      ●H{dq|n} T ∗
      if okS is Some kS then
        let si := SessInfo kI kR kS n T in
        minted kS ∗
        □ (∀ kt, public (TKey kt kS) ↔ ▷ session_fail si) ∗
        (session_fail si ∨ session si ∗ term_token kS (↑nroot.@"client"))
      else True
 }}}.
Proof.
rewrite /initiator.
iIntros "#chan_c #ctx #(? & ?) #p_kI #p_kR %Ψ !> hon Hpost".
iMod (minted_at_list with "[//] hon") as "[hon list]" => //.
wp_pures.
iDestruct "list" as "(%M & #m_M & #minted_at_M)".
wp_bind (mknonce _).
iApply (wp_mknonce_freshN M
          (λ _, public_at n (TKey Enc kI) ∨
                public_at n (TKey Enc kR))%I
          dh_auth_pred
          (λ a, {[TExp (TInt 0) [a]]})) => //.
- iIntros "% ?". rewrite big_sepS_forall. by iApply "m_M".
- iIntros "%a". rewrite big_sepS_singleton minted_TExp minted_TInt /=.
  iIntros "!>"; iSplit; eauto.
  by iIntros "(_ & ? & _)".
iIntros "%a %fresh #m_a #p_a #a_pred token".
rewrite big_sepS_singleton.
iPoseProof (honest_auth_frag with "hon") as "#honI".
wp_pures. wp_bind (mkkeyshare _). iApply wp_mkkeyshare => //.
iIntros "!> _". wp_pures. wp_list. wp_term_of_list.
wp_pure _ credit:"H1".
wp_pure _ credit:"H2".
iAssert (public (TExp (TInt 0) [a])) as "p_ga".
{ iApply public_TExp1.
  rewrite minted_TInt. do 2![iSplit => //].
  iRight. iApply "a_pred". iModIntro. iModIntro.
  iIntros "%g %ks %e".
  case/TExp_inj: e => _ perm.
  by rewrite -(Permutation_length perm). }
wp_bind (send _ _). iApply wp_send => //.
{ rewrite public_of_list /=. iModIntro.
  do 2?[iSplit => //]. }
wp_pure _ credit:"H3".
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m2 #p_m2". wp_tdec m2; last by protocol_failure.
wp_pures. wp_list_of_term m2; last by protocol_failure.
wp_pures. wp_list_match => [ga' gb vkI' -> {m2}|]; last by protocol_failure.
wp_eq_term e; last by protocol_failure. subst ga'.
wp_pures. wp_eq_term e; last by protocol_failure. subst vkI'.
iAssert (public gb)%I as "#p_gb".
{ iPoseProof (public_TEncE with "p_m2 [//]") as "[p|p]".
  - rewrite public_of_list /=.
    by iDestruct "p" as "(_ & _ & ? & _)".
  - iDestruct "p" as "(_ & _ & #p)".
    iSpecialize ("p" with "p_kR").
    rewrite public_of_list /=.
    by iDestruct "p" as "(_ & ? & ? & _)". }
iPoseProof (public_minted with "p_m2") as "m_m2".
rewrite minted_TEnc minted_tag minted_of_list /=.
iDestruct "m_m2" as "(_ & _ & m_gb & _)".
wp_pures. wp_bind (texp _ _). iApply wp_texp.
wp_pures. wp_list. wp_term_of_list. wp_pures.
set secret := Spec.of_list [TExp (TInt 0) [a]; gb; Spec.texp gb a].
wp_tag.
set kS := Spec.tag (nroot.@"keys".@"sym") _. wp_pures.
wp_pures. wp_list. wp_term_of_list. wp_tenc.
iAssert ( |={⊤}=>
    ●H{dq|n} T ∗
    (public_at n (TKey Enc kR) ∧ ⌜TKey Enc kR ∉ T⌝ ∨
    ∃ b,
     ⌜gb = TExp (TInt 0) [b]⌝ ∗
     □ (public b ↔ ▷ □ (public_at n (TKey Enc kI) ∨
                        public_at n (TKey Enc kR))) ∗
     term_meta kS (nroot.@"info") (kI, kR, n) ∗
     term_token kS (↑nroot.@"client")))%I
  with "[hon token H3]"
  as "{p_m2} > (hon & p_m2)".
{ iPoseProof (public_TEncE with "p_m2 [//]") as "{p_m2} p_m2".
  iDestruct "p_m2" as "[[comp _]  | (#i_m2 & _ & _)]".
  { iMod (public_atI with "[ctx] [H3] [hon] [comp]")
      as "[hon #comp']" => //; try solve_ndisj.
    iPoseProof (honest_frag_public_at with "honI comp'") as "%" => //.
    iFrame. eauto. }
  iMod (lc_fupd_elim_later_pers with "H3 i_m2") as "{i_m2} #i_m2".
  iDestruct "i_m2"
    as "(%ga & %b & %kI' & %n' & %T' & %e_m2 &
         m_ga & ? & _ & honR & escrow & pred_b)".
  case/Spec.of_list_inj: e_m2 => <- -> <- {ga gb kI'} in secret kS *.
  iPoseProof (honest_auth_frag_agree with "hon honR") as "[% %]".
  case: (decide (n' < n)) => [contra|?].
  { iPoseProof ("minted_at_M" with "[//] m_ga") as "%ga_M".
    move/(_ _ ga_M)/subtermsP: fresh.
    rewrite subterms_TExp /= !elem_of_union => fresh.
    case: fresh.
    right. right. left. apply/subtermsP. apply/STRefl. }
  have ? : n' = n by lia. subst n'.
  iPoseProof (honest_frag_agree with "honR honI") as "->".
  iMod (escrowE with "escrow token") as ">token" => //.
  rewrite /kS /secret !Spec.texpA TExpC2. iFrame.
  iModIntro. iRight. iExists b. by do !iSplit => //.
}
set m3 := Spec.tenc _ _ _.
iAssert (public m3) as "#p_m3".
{ iApply (public_TEncIS with "[] [//] [#]") => //.
  - by rewrite !public_minted !minted_TKey.
  - iExists a, gb, kR, n, T. do 4![iSplitR => //].
    iDestruct "p_m2" as "[[#? _]|p_m2]"; eauto.
    iDestruct "p_m2" as "(%b & % & #? & #? & _)".
    iRight. by eauto.
  - rewrite minted_of_list /= minted_TExp /= minted_TInt minted_TKey.
    rewrite !public_minted !minted_TKey. by do ![iSplitL => //].
  - iIntros "!> _".
    rewrite public_of_list /=.
    by do ![iSplit => //]. }
wp_pures. wp_bind (send _ _). iApply wp_send => //.
wp_pures. wp_bind (mkskey _). iApply wp_mkskey.
pose si := SessInfo kI kR kS n T.
iAssert (minted kS) as "#?".
{ rewrite minted_tag minted_of_list /= minted_TExp /= minted_TInt.
  do !iSplit => //.
  iApply minted_texp => //. }
iAssert (□ (∀ kt, public (TKey kt kS) ↔ ▷ session_fail si))%I as "#sec_sk".
{ iIntros "%kt". iSplitL; last first.
  { iIntros "!> #comp".
    rewrite (public_TKey kt) public_tag. iLeft.
    rewrite public_of_list /=. do !iSplit => //.
    iApply public_texp => //.
    iApply "p_a". eauto. }
  iDestruct "p_m2" as "[[#? %comp]|p_m2]".
  { iIntros "!> _ !>". by iRight. }
  iDestruct "p_m2" as "(%b & -> & #p_b & #p_m2 & _)".
  iIntros "!> #p_sk".
  iPoseProof (public_sym_keyE with "[//] p_sk") as "{p_sk} >p_sk".
  rewrite Spec.texpA in secret kS si *.
  rewrite /secret public_of_list /= public_TExp2.
  iDestruct "p_sk" as "(_ & _ & p_sk & _)".
  iDestruct "p_sk" as "[[_ #p_b'] | [[_ p_a'] | (_ & a_pred' & _)]]".
  + iPoseProof ("p_b" with "p_b'") as "{p_b} p_b". by eauto.
  + iPoseProof ("p_a" with "p_a'") as "hon'". by eauto.
  + iPoseProof ("a_pred" with "a_pred'") as ">%contra".
    by have := contra _ _ eq_refl. }
wp_pures. iApply ("Hpost" $! (Some kS)). iFrame.
rewrite -[SessInfo _ _ _ _ _]/si.
iSplitR => //.
iSplitR => //.
iDestruct "p_m2" as "[[#fail _]|p_m2]".
{ iLeft. by iRight. }
iDestruct "p_m2" as "(%b & -> & #p_b & #p_m2 & token)".
iRight. iFrame. iModIntro. by iSplit.
Qed.

End Verif.
