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

Lemma wp_responder c skR :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx N -∗
  sign_key skR -∗
  {{{ True }}}
    responder c skR
  {{{ okS,
      RET (repr okS);
      if okS is Some (vkI, kS) then ∃ si,
        ⌜vkI = TKey Open (si_init si)⌝ ∗
        ⌜si_resp si = skR⌝ ∗
        ⌜si_key si = kS⌝ ∗
        public vkI ∗
        minted kS ∗
        key_secrecy si ∗
        release_token (si_resp_share si) ∗
        term_token (si_resp_share si) (↑isoN)
      else True
 }}}.
Proof.
set vkR := TKey Open skR.
iIntros "#chan_c #? (#? & #?) #sign_kR !> %Φ _ Hpost".
wp_lam. wp_pures. wp_apply wp_vkey. wp_pures.
wp_apply wp_recv => //. iIntros "%m1 #p_m1". wp_pures.
wp_list_of_term m1; last by protocol_failure.
wp_pures. wp_list_match => [ga vkI -> {m1}|]; last by protocol_failure.
rewrite public_of_list /=.
iDestruct "p_m1" as "(p_ga & p_vkI & _)".
wp_pures.
wp_apply (wp_mknonce_freshN ∅
          (λ b, released ga ∧ released (TExp (TInt 0) b))%I
          iso_dh_pred
          (λ b, {[TExp (TInt 0) b]}))
       => //.
- iIntros "%". rewrite elem_of_empty. iIntros "[]".
- iIntros "%b".
  rewrite big_sepS_singleton minted_TExp minted_TInt /= bi.True_and.
  iModIntro. by iApply bi.equiv_iff.
iIntros "%b _ _ #m_b #s_b #dh_gb token".
rewrite bi.intuitionistic_intuitionistically.
set gb := TExp (TInt 0) b.
set gab := TExp ga b.
rewrite big_sepS_singleton.
iDestruct (release_tokenI with "token") as "[token_rel token]" => //.
iPoseProof (term_token_drop (↑isoN) with "token")
  as "token"; first solve_ndisj.
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
{ iApply public_signIS => //.
  - iModIntro.
    iExists ga, b, vkI.  by do ![iSplitL => //].
  - rewrite public_of_list /=. by do !iSplit => //. }
wp_pures. wp_apply wp_recv => //. iIntros "%m3 #p_m3".
wp_apply wp_verify. case: Spec.decP; last by protocol_failure.
move=> skI {}m3 e_vkI ->.
rewrite {}e_vkI {vkI}. set vkI := TKey Open skI.
wp_pures. wp_list_of_term m3; last by protocol_failure.
wp_list_match => [ga' gb' vkR' -> {m3}|]; last by protocol_failure.
wp_eq_term e; last by protocol_failure. subst ga'.
wp_eq_term e; last by protocol_failure. subst gb'.
wp_eq_term e; last by protocol_failure. subst vkR'.
wp_pure _ credit:"H3".
wp_apply wp_texp.
wp_pure _ credit:"H4".
iPoseProof (public_signE with "p_m3 [//] [//]") as "{p_m3} [_ inv]".
wp_pures. wp_list. wp_term_of_list.
wp_pures. pose si := SessInfo skI skR ga gb gab.
wp_apply wp_derive_key. rewrite -[Spec.derive_key _]/(si_key si).
rewrite -/(released_session si).
iAssert (▷ released_session si → public (si_key si))%I as "s_k1".
{ iIntros "#released".
  rewrite public_derive_key public_of_list /=.
  do !iSplit => //; try by iApply sign_key_public.
  iApply public_TExp => //. by iApply "s_b". }
iAssert (|={⊤}=> compromised_session si ∨
                   □ (public (si_key si) → ▷ released_session si))%I
  with "[H4]" as "> #i_m3".
{ iDestruct "inv" as "[comp|#inv]".
  { rewrite /compromised_session. by eauto. }
  iDestruct "inv" as "(%a & %gb' & %skR' & %e_m3 & comp)".
  case/Spec.of_list_inj: e_m3 => -> <- <- {ga gb' skR'} in gb gab si *.
  rewrite !TExp_TExpN TExpC2 in gab si *. by eauto. }
iAssert (minted (si_key si)) as "#m_kS".
{ rewrite minted_derive_key !minted_of_list /= !minted_TExp minted_TInt.
  do !iSplit => //; iApply public_minted => //.
  by iApply sign_key_public. }
iAssert (minted skI) as "#m_skI".
{ iApply minted_TKey. by iApply public_minted. }
wp_pures.
iApply ("Hpost" $! (Some (TKey Open skI, si_key si))).
iModIntro. iExists si. iFrame. by do !iSplit => //.
Qed.

Lemma wp_responder_weak c skR :
  channel c -∗
  cryptis_ctx -∗
  iso_dh_ctx N -∗
  sign_key skR -∗
  {{{ True }}}
    responder c skR
  {{{ okS,
      RET (repr okS);
      if okS is Some (vkI, kS) then ∃ si,
        ⌜vkI = TKey Open (si_init si)⌝ ∗
        ⌜si_resp si = skR⌝ ∗
        ⌜si_key si = kS⌝ ∗
        public vkI ∗
        minted kS ∗
        (compromised_session si ∨ □ (public kS ↔ ▷ False)) ∗
        term_token (si_resp_share si) (↑isoN)
      else True
 }}}.
Proof.
iIntros "#chan_c #ctx #? #skR %Ψ !> _ Hpost".
iApply wp_fupd. wp_apply wp_responder => //.
iIntros "%okS HkS".
case: okS => [[vkI kS]|]; last by iApply ("Hpost" $! None).
iDestruct "HkS" as "(%si & -> & <- & <- & #? & #m_kS & #sec & rel & tok)".
iMod (unrelease with "rel") as "#un". iModIntro.
iApply ("Hpost" $! (Some (TKey Open (si_init si), si_key si))).
iExists si. iFrame. do !iSplit => //.
iDestruct "sec" as "(sec1 & [?|sec2])"; eauto.
iRight. iApply (unreleased_key_secrecy Resp) => //.
iModIntro. by iSplit.
Qed.

End Verif.
