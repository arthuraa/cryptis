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

Definition initiator : val := λ: "c" "skI" "vkR",
  let: "vkI"  := vkey "skI" in
  let: "a"    := mknonce #() in
  let: "ga"   := mkkeyshare "a" in
  let: "m1"   := term_of_list ["ga"; "vkI"] in
  send "c" "m1";;
  bind: "m2"   := verify (N.@"m2") "vkR" (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["ga'"; "gb"; "vkI'"] := "m2" in
  guard: eq_term "ga" "ga'" && eq_term "vkI" "vkI'" in
  let: "gab" := texp "gb" "a" in
  let: "secret" := term_of_list ["vkI"; "vkR"; "ga"; "gb"; "gab"] in
  let: "m3" := sign (N.@"m3") "skI" (term_of_list ["ga"; "gb"; "vkR"]) in
  send "c" "m3";;
  SOME (derive_key "secret").

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_initiator c kI kR :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx N -∗
  public (TKey Open kI) -∗
  public (TKey Open kR) -∗
  {{{ True }}}
    initiator c kI (TKey Open kR)
  {{{ okS, RET (repr okS);
      if okS is Some kS then ∃ si,
        ⌜si_init si = kI⌝ ∗
        ⌜si_resp si = kR⌝ ∗
        ⌜si_key si = kS⌝ ∗
        minted kS ∗
        □ (∀ kt, public (TKey kt kS) ↔ ◇ public kS) ∗
        (public (TKey Seal kR) ∨ □ (◇ public kS ↔ ▷ False)) ∗
        term_token (si_init_share si) ⊤
      else True
 }}}.
Proof.
rewrite /initiator.
set vkI := TKey Open kI.
set vkR := TKey Open kR.
iIntros "#chan_c #ctx #(? & ?) #p_kI #p_kR %Ψ !> phase Hpost".
wp_pures. wp_apply wp_vkey. wp_pures. rewrite -/vkI.
wp_apply (wp_mknonce_freshN ∅
            (λ _, False%I)
            iso_dh_pred
            (λ a, {[TExp (TInt 0) a]})) => //.
- iIntros "% ?". by rewrite elem_of_empty.
- iIntros "%a". rewrite big_sepS_singleton minted_TExp minted_TInt /=.
  iIntros "!>"; iSplit; eauto.
  by iIntros "(_ & ?)".
iIntros "%a %fresh %nonce #m_a #s_a #a_pred token".
set ga := TExp (TInt 0) a.
rewrite big_sepS_singleton.
wp_pures. wp_apply wp_mkkeyshare => //. rewrite -/ga.
iIntros "_". wp_pures. wp_list. wp_term_of_list.
wp_pure _ credit:"H1".
wp_pure _ credit:"H2".
iAssert (public ga) as "p_ga".
{ iApply public_TExp_iff; eauto.
  rewrite minted_TInt.
  iRight. do 2![iSplit => //].
  iApply "a_pred". iModIntro. iModIntro.
  by rewrite /iso_dh_pred exps_TExpN. }
wp_apply wp_send => //.
{ rewrite public_of_list /=. do 2?[iSplit => //]. }
wp_pure _ credit:"H3".
wp_pures. wp_apply wp_recv => //.
iIntros "%m2 #p_m2".
wp_verify m2; last by protocol_failure.
wp_pures. wp_list_of_term m2; last by protocol_failure.
wp_pures. wp_list_match => [ga' gb vkI' -> {m2}|]; last by protocol_failure.
wp_eq_term e; last by protocol_failure. subst ga'.
wp_pures. wp_eq_term e; last by protocol_failure. subst vkI'.
iAssert (public gb)%I as "#p_gb".
{ iPoseProof (public_TSealE with "p_m2 [//]") as "[p|p]".
  - rewrite public_of_list /=.
    by iDestruct "p" as "(_ & _ & ? & _)".
  - iDestruct "p" as "(_ & _ & #p)".
    iSpecialize ("p" with "p_kR").
    rewrite public_of_list /=.
    by iDestruct "p" as "(_ & ? & ? & _)". }
iPoseProof (public_minted with "p_m2") as "m_m2".
rewrite minted_TSeal minted_tag minted_of_list /=.
iDestruct "m_m2" as "(_ & _ & m_gb & _)".
wp_pures. wp_bind (texp _ _). iApply wp_texp.
wp_pures. wp_list. wp_term_of_list. wp_pures.
set gab := TExp gb a.
set seed := Spec.of_list [vkI; vkR; ga; gb; gab].
set secret := Spec.derive_key seed.
wp_pures. wp_list. wp_term_of_list. wp_apply wp_sign. wp_pures.
iAssert (|={⊤}=> public (TKey Seal kR) ∨ □ (◇ public secret ↔ ▷ False))%I
  with "[H3]"
  as "{p_m2} > #p_m2".
{ iPoseProof (public_TSealE with "p_m2 [//]") as "{p_m2} p_m2".
  iDestruct "p_m2" as "[[comp _]  | (#i_m2 & _ & _)]"; first by eauto.
  iMod (lc_fupd_elim_later_pers with "H3 i_m2") as "{i_m2} #i_m2".
  iDestruct "i_m2" as "(%ga' & %b & %kI' & %e_m2 & s_b & pred_b)".
  case/Spec.of_list_inj: e_m2 => _ -> _ {ga' gb kI'} in gab seed secret *.
  rewrite !TExp_TExpN TExpC2 in gab seed secret *.
  iIntros "!>". iRight. iIntros "!>".
  rewrite public_derive_key public_of_list /=.
  iApply (bi.iff_trans _ (◇ public gab)).
  iSplit; last by iApply public_dh_secret.
  iSplit; last by iIntros "#?"; do !iSplit.
  by iIntros ">(_ & _ & _ & _ & ? & _)". }
set m3 := Spec.enc _ _ _.
iAssert (public m3) as "#p_m3".
{ iApply (public_TSealIS with "[] [//] [#]") => //.
  - by rewrite !public_minted !minted_TKey.
  - iExists a, gb, kR. by do 3![iSplitR => //].
  - rewrite minted_of_list /= minted_TExp /= minted_TInt minted_TKey.
    rewrite !public_minted !minted_TKey. by do ![iSplitL => //].
  - iIntros "!> _".
    rewrite public_of_list /=.
    by do ![iSplit => //]. }
wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_derive_key.
pose si := SessInfo kI kR ga gb gab.
iAssert (minted seed) as "#m_seed".
{ rewrite minted_of_list /= !minted_TExp /= minted_TInt.
  by do !iSplit => //; iApply public_minted. }
wp_pures. iApply ("Hpost" $! (Some secret)).
iExists si. iFrame. do !iSplitR => //.
  by rewrite minted_derive_key.
iIntros "!> !> %kt".
rewrite public_derive_key.
by iApply public_key_derive_key.
Qed.

End Verif.
