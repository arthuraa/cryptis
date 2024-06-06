From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics nown.
From cryptis Require Import role.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).

Variable N : namespace.

(*

A --> B: g^a; vkA
B --> A: {g^a; g^b; vkA}@skB
A --> B: {g^a; g^b; vkB}@skA

g^{nAnB}

*)

Definition mkkeyshare : val := λ: "k",
  texp (tgroup (tint #0)) "k".

Lemma wp_mkkeyshare (t : term) E :
  {{{ True }}}
    mkkeyshare t @ E
  {{{ RET (repr (TExp (TInt 0) [t])); True : iProp}}}.
Proof.
iIntros "%Φ _ Hpost". wp_lam.
wp_bind (tint _). iApply wp_tint.
wp_bind (tgroup _). iApply wp_tgroup.
wp_bind (texp _ _). iApply wp_texp. rewrite Spec.texpA.
by iApply "Hpost".
Qed.

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
  let: "m3" := tenc (N.@"m3") "skI" (term_of_list ["ga"; "gb"; "vkR"]) in
  send "c" "m3";;
  SOME "gab".

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
  SOME ("vkI", "gab").

Definition in_honest kI kR (T : gset term) : bool :=
  bool_decide (TKey Enc kI ∈ T ∧ TKey Enc kR ∈ T).

Definition dh_auth_pred t : iProp :=
  ⌜∀ g ts, t = TExp g ts → length ts = 1⌝.

Definition msg2_pred kR m2 : iProp :=
  ∃ ga b kI n T,
    ⌜m2 = Spec.of_list [ga; TExp (TInt 0) [b]; TKey Dec kI]⌝ ∗
    (public b ↔ ▷ □ False) ∗
    (∀ t, dh_pred b t ↔ ▷ □ dh_auth_pred t) ∗
    ◯H{n} T ∗
    nonce_meta b (N.@"session") (Resp, ga, b, kI, kR, n, T).

Definition msg3_pred kI m3 : iProp :=
  ∃ a gb kR n T,
    ⌜m3 = Spec.of_list [TExp (TInt 0) [a]; gb; TKey Dec kR]⌝ ∗
    (public a ↔ ▷ □ ⌜TKey Enc kI ∉ T ∨ TKey Enc kR ∉ T⌝) ∗
    (∀ t, dh_pred a t ↔ ▷ □ dh_auth_pred t) ∗
    ◯H{n} T ∗
    nonce_meta a (N.@"session") (Init, gb, a, kI, kR, n, T) ∗
    (public (TKey Enc kR) ∨
     ∃ b n' (T' : gset term),
       ⌜gb = TExp (TInt 0) [b]⌝ ∗
       ⌜n' ≤ n⌝ ∗
       nonce_meta b (N.@"session") (Resp, TExp (TInt 0) [a], b, kI, kR, n', T')).

Definition dh_auth_ctx : iProp :=
  enc_pred (N.@"m2") msg2_pred ∗
  enc_pred (N.@"m3") msg3_pred.

Definition session kI kR k rl : iProp :=
  ∃ share x ts T,
    ⌜k = Spec.texp share x⌝ ∗
    ◯H{ts} T ∗
    nonce_meta x (N.@"session") (rl, share, x, kI, kR, ts, T).

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_initiator c kI kR dq n T E :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  dh_auth_ctx -∗
  public (TKey Dec kI) -∗
  public (TKey Dec kR) -∗
  {{{ ●H{dq|n} T }}}
    initiator c (TKey Dec kI) (TKey Enc kI) (TKey Dec kR) @ E
  {{{ okS, RET (repr okS);
      ●H{dq|n} T ∗
      if okS is Some kS then
        minted kS ∗
        session kI kR kS Init ∗
        if in_honest kI kR T then
          session kI kR kS Resp ∗
          □ (public kS -∗ ▷ False)
        else public kS
      else True
 }}}.
Proof.
rewrite /initiator /in_honest bool_decide_decide.
iIntros (??) "#chan_c #ctx #(? & ?) #p_kI #p_kR %Ψ !> hon Hpost".
wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce (λ _, ⌜TKey Enc kI ∉ T ∨ TKey Enc kR ∉ T⌝)%I
          dh_auth_pred).
iIntros "%a #m_a #p_a #a_pred token".
iPoseProof (honest_auth_frag with "hon") as "#honI".
wp_pures. wp_bind (mkkeyshare _). iApply wp_mkkeyshare => //.
iIntros "!> _". wp_pures. wp_list. wp_term_of_list.
wp_pure _ credit:"H1".
wp_pure _ credit:"H2".
iAssert (public (TExp (TInt 0) [a])) as "p_ga".
{ iApply public_TExp1.
  rewrite minted_TInt. do 2![iSplit => //].
  iRight. iApply "a_pred". iModIntro. iModIntro.
  iIntros "%g %ts %e".
  case/TExp_inj: e => _ perm.
  by rewrite -(Permutation_length perm). }
wp_bind (send _ _). iApply wp_send => //.
{ rewrite public_of_list /=. iModIntro.
  do 2?[iSplit => //]. }
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
wp_pures. wp_list. wp_term_of_list. wp_tenc.
iMod (term_meta_set _ _ (Init, gb, a, kI, kR, n, T)
       (N.@"session") with "token") as "#sessionI" => //.
iAssert (
    ▷ (public (TKey Enc kR) ∨
    ∃ b n' (T' : gset term),
     ⌜gb = TExp (TInt 0) [b]⌝ ∗
     ⌜n' ≤ n⌝ ∗
     nonce_meta b (N.@"session") (Resp, TExp (TInt 0) [a], b, kI, kR, n', T')))%I
  as "#p_m2'".
{ iPoseProof (public_TEncE with "p_m2 [//]") as "{p_m2} p_m2".
  iDestruct "p_m2" as "[[? _]  | (#i_m2 & _ & _)]"; first by eauto.
  iModIntro. iRight.
  iDestruct "i_m2"
    as "(%ga & %b & %kI' & %n' & %T' & %e_m2 & _ & _ & honR & pred_b)".
  case/Spec.of_list_inj: e_m2 => <- -> <- {ga gb kI'}.
  iPoseProof (honest_auth_frag_agree with "hon honR") as "[%n'_n _]".
  iExists _, _, _. iSplit => //. iSplit; last by [].
  by []. }
wp_pures. wp_bind (send _ _). iApply wp_send => //.
{ iModIntro.
  iApply public_TEncIS => //.
  - by rewrite !public_minted !minted_TKey.
  - iModIntro. iExists a, gb, kR, n, T. by do ![iSplitL => //].
  - rewrite minted_of_list /= minted_TExp /= minted_TInt minted_TKey.
    rewrite !public_minted !minted_TKey. by do ![iSplitL => //].
  - iIntros "!> _".
    rewrite public_of_list /=.
    by do ![iSplit => //]. }
iAssert (session kI kR (Spec.texp gb a) Init) as "#sessionI'".
{ iExists gb, a, n, T; eauto. }
case: decide => [[honI honR]|cor]; last first.
{ iAssert (public (Spec.texp gb a)) as "#p_kS".
  iApply public_texp => //.
  iApply "p_a". by rewrite not_and_r in cor.
  wp_pures. iApply ("Hpost" $! (Some (Spec.texp gb a))).
  iFrame. iModIntro. iSplit; first by iApply public_minted.
  iSplit => //. }
iPoseProof (public_TEncE with "p_m2 [//]") as "[[contra _]|(#p & _ & _)]".
{ iMod (honest_public with "[//] hon contra") as "H" => //.
  - solve_ndisj.
  - wp_pures. iDestruct "H" as ">[]". }
iDestruct "p" as "(%ga & %b & %kI' & %n' & %T' & p)".
wp_pures.
iDestruct "p" as "(%e & p_b & b_pred & honR & sessionR)".
case/Spec.of_list_inj: e => <- -> <- {ga gb kI'}.
rewrite !Spec.texpA.
iPoseProof (honest_auth_frag_agree with "hon honR") as "[%n'n %agree]".
iApply ("Hpost" $! (Some (TExp (TInt 0) [a; b]))). iFrame.
rewrite !minted_TExp /= minted_TInt.
iDestruct "m_gb" as "(_ & m_b & _)". iModIntro.
iSplit; first do ![iSplit => //].
iSplit => //.
iSplit.
{ iExists (TExp (TInt 0) [a]), b, n', T'.
  rewrite Spec.texpA [TExp _ [a; b]]TExpC2. iSplit => //.
  iSplit => //. }
rewrite public_TExp2.
iIntros "!> [[_ p_b'] | [[_ p_a'] | (_ & a_pred' & _)]]".
- admit.
- iPoseProof ("p_a" with "p_a'") as ">%hon". tauto.
- iPoseProof ("a_pred" with "a_pred'") as ">%contra".
  by have := contra _ _ eq_refl.
Admitted.

Lemma wp_responder c kR dq n T E :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  dh_auth_ctx -∗
  public (TKey Dec kR) -∗
  {{{ ●H{dq|n} T }}}
    responder c (TKey Dec kR) (TKey Enc kR) @ E
  {{{ okS, RET (repr okS);
      ●H{dq|n} T ∗
      if okS is Some (vkI, kS) then ∃ kI,
        ⌜vkI = TKey Dec kI⌝ ∗
        minted kI ∗
        minted kS ∗
        session kI kR kS Resp ∗
        if in_honest kI kR T then
          session kI kR kS Init ∗
          □ (public kS -∗ ▷ False)
        else public kS
      else True
 }}}.
Proof.
iIntros "% % #chan_c #? (#? & #?) #p_vkR !> %Φ hon_auth Hpost".
wp_lam. wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m1 #p_m1". wp_pures.
wp_list_of_term m1; last by protocol_failure.
wp_pures. wp_list_match => [ga vkI -> {m1}|]; last by protocol_failure.
rewrite public_of_list /=.
iDestruct "p_m1" as "(p_ga & p_vkI & _)".
wp_bind (is_key _). iApply wp_is_key.
case: Spec.is_keyP => [kt kI -> {vkI}|]; last by protocol_failure.
wp_pures. case: kt => //=; first by protocol_failure.
wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce (λ _, False)%I dh_auth_pred).
iIntros "%b #m_b #p_b #dh_gb token".
iAssert (public (TExp (TInt 0) [b])) as "#p_gb".
{ iApply public_TExp1. rewrite minted_TInt.
  do ![iSplit => //].
  iRight. iApply "dh_gb". iIntros "!> !> %g %ts %e".
  case/TExp_inj: e => _ perm.
  by rewrite -(Permutation_length perm). }
wp_pure _ credit:"H1".
wp_pure _ credit:"H2".
wp_pures. wp_bind (mkkeyshare _). iApply wp_mkkeyshare => //.
iIntros "!> _". wp_pures. wp_list. wp_term_of_list. wp_tenc.
iMod (term_meta_set _ _ (Resp, ga, b, kI, kR, n, T)
       (N.@"session") with "token")
  as "#meta"; first solve_ndisj.
iPoseProof (honest_auth_frag with "hon_auth") as "#honR".
wp_pures. wp_bind (send _ _). iApply wp_send => //.
{ iModIntro.
  iApply public_TEncIS => //.
  - by rewrite public_minted !minted_TKey.
  - iModIntro.
    iExists ga, b, kI, n, T.  by do 5![iSplitL => //].
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
wp_pures. wp_bind (texp _ _). iApply wp_texp. wp_pures.
iAssert (session kI kR (Spec.texp ga b) Resp) as "sessionR".
{ iExists _, _, n, T; eauto. }
iAssert (minted (Spec.texp ga b)) as "#m_kS".
{ iApply minted_texp => //. by iApply public_minted. }
iAssert (minted kI) as "#m_kI".
{ iApply minted_TKey. by iApply public_minted. }
iPoseProof (public_TEncE with "p_m3 [//]") as "{p_m3} p_m3".
rewrite public_of_list /=.
iAssert ( □ ▷ □ (
  (public (TKey Enc kI) ∨ public (TKey Enc kR)) ∨
  ∃ a,
    ⌜ga = TExp (TInt 0) [a]⌝ ∗
    (public a ↔ ▷ □ ⌜TKey Enc kI ∉ T ∨ TKey Enc kR ∉ T⌝) ∗
    (∀ t, dh_pred a t ↔ ▷ □ dh_auth_pred t) ∗
    nonce_meta a (N.@"session") (Init, TExp (TInt 0) [b], a, kI, kR, n, T)))%I
  as "{p_m3} #i_m3".
{ iDestruct "p_m3" as "[(p_skI & _) | (#i_m3 & _ & _)]";
    first by iModIntro; eauto.
  iApply bi.later_intuitionistically. iModIntro.
  iDestruct "i_m3" as "(%a & %gb & %kR' & %n' & %T' & %e_m3 &
                        p_a & pred_a & honI & sessionI & i_m3)".
  case/Spec.of_list_inj: e_m3 => -> <- <- {ga gb kR'}.
  iDestruct "i_m3" as "[i_m3 | i_m3]"; first by eauto.
  iDestruct "i_m3" as "(%b' & %n'' & %T'' & %e_b & %n''_n' & i_m3)".
  case/TExp_inj: e_b => _ /(Permutation_singleton_inj _ _) <- {b'}.
  iPoseProof (term_meta_agree with "meta i_m3") as "%e_meta".
  case: e_meta => <- <- {n'' T''} in n''_n' *.
  iPoseProof (honest_auth_frag_agree with "hon_auth honI") as "[%n'_n %T'_T]".
  rewrite -(T'_T n''_n') {T' T'_T}.
  assert (n' = n) as -> by lia.
  rewrite Spec.texpA TExpC2.
  iModIntro. iModIntro.
  iRight. iExists a. by do ![iSplitL => //]. }
iMod (lc_fupd_elim_later with "H1 i_m3") as "{i_m3} #i_m3".
iDestruct "i_m3" as "[compromise|i_m3]".
{ case: (decide (TKey Enc kI ∈ T ∧ TKey Enc kR ∈ T)) =>
        [[honI honR]|compromise].
  { iDestruct "compromise" as "[compI | compR]".
    - iMod (honest_public with "[//] hon_auth compI") as "H" => //;
        first by solve_ndisj.
      iMod (lc_fupd_elim_later with "H2 H") as ">[]".
    - iMod (honest_public with "[//] hon_auth compR") as "H" => //;
        first by solve_ndisj.
      iMod (lc_fupd_elim_later with "H2 H") as ">[]". }
  iApply ("Hpost" $! (Some (TKey Dec kI, Spec.texp ga b))).
  iFrame. iModIntro. iExists kI.
  rewrite /in_honest bool_decide_decide decide_False //.
  do 4![iSplit => //].
  iApply public_texp => //.
  admit. }
iDestruct "i_m3" as "(%a & -> & p_a & pred_a & metaI)".
rewrite Spec.texpA TExpC2.
iApply ("Hpost" $! (Some (TKey Dec kI, TExp (TInt 0) [a; b]))).
iFrame. iModIntro. iExists kI. do 2![iSplit => //].
rewrite minted_TExp minted_TInt /=. iSplit; first by eauto.
iSplit => //.
case: (decide (TKey Enc kI ∈ T ∧ TKey Enc kR ∈ T)) =>
        [[honI honR]|compromise]; last first.
- rewrite /in_honest bool_decide_decide decide_False //.
  rewrite not_and_r in compromise.
  rewrite -(Spec.texpA _ [b] a).
  iApply public_texp => //.
  iApply "p_a". eauto.
- rewrite /in_honest bool_decide_decide decide_True //.
  iSplitL.
  { iExists (TExp (TInt 0) [b]), a, n, T.
    rewrite Spec.texpA. do 2![iSplit => //]. }
  iIntros "!> #p_kS".
  iDestruct (public_TExp2 with "p_kS")
  as "[[_ p_b'] | [ [_ p_a'] | (_ & contra & _)]]".
  + iDestruct ("p_b" with "p_b'") as ">[]".
  + iPoseProof ("p_a" with "p_a'") as ">%compromised".
    by case: compromised => [/(_ honI) | /(_ honR)].
  + iPoseProof ("pred_a" with "contra") as ">%contra".
    by have := contra _ _ eq_refl.
Admitted.

End Verif.
