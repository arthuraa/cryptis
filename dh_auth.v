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

(* MOVE *)
Lemma lc_fupd_elim_later_pers `{invGS Σ} E (P : iProp Σ) :
  £ 1 -∗ □ ▷ P ={E}=∗ □ P.
Proof.
rewrite bi.later_intuitionistically_2.
exact: lc_fupd_elim_later.
Qed.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).
Implicit Types (γ γa γb : gname) (ok : bool).
Implicit Types (ts : nat) (T : gset term).

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

Definition in_honest kI kR T : bool :=
  bool_decide (TKey Enc kI ∈ T ∧ TKey Enc kR ∈ T).

Definition dh_auth_pred t : iProp :=
  ⌜∀ g ks, t = TExp g ks → length ks = 1⌝.

Definition msg2_pred kR m2 : iProp :=
  ∃ ga b kI n T γb,
    ⌜m2 = Spec.of_list [ga; TExp (TInt 0) [b]; TKey Dec kI]⌝ ∗
    (public b ↔ ▷ □ (compromised_at n (TKey Enc kI) ∨
                     compromised_at n (TKey Enc kR))) ∗
    (∀ t, dh_pred b t ↔ ▷ □ dh_auth_pred t) ∗
    ◯H{n} T ∗
    nonce_meta b (N.@"session") (Resp, ga, kI, kR, n, T, γb).

Definition msg3_pred kI m3 : iProp :=
  ∃ a gb kR n T γa,
    ⌜m3 = Spec.of_list [TExp (TInt 0) [a]; gb; TKey Dec kR]⌝ ∗
    (public a ↔ ▷ □ ⌜negb (in_honest kI kR T)⌝) ∗
    (∀ t, dh_pred a t ↔ ▷ □ dh_auth_pred t) ∗
    ◯H{n} T ∗
    nonce_meta a (N.@"session") (Init, gb, kI, kR, n, T, γa) ∗
    (public (TKey Enc kR) ∨
     ∃ b n' T' γb,
       ⌜gb = TExp (TInt 0) [b]⌝ ∗
       ⌜n' ≤ n⌝ ∗
       nonce_meta b (N.@"session")
         (Resp, TExp (TInt 0) [a], kI, kR, n', T', γb)).

Definition dh_auth_ctx : iProp :=
  enc_pred (N.@"m2") msg2_pred ∗
  enc_pred (N.@"m3") msg3_pred.

Definition session γ kI kR k rl ok : iProp :=
  ∃ share x ts T,
    ⌜k = Spec.texp share x⌝ ∗
    ⌜ok = in_honest kI kR T⌝ ∗
    ◯H{ts} T ∗
    nonce_meta x (N.@"session") (rl, share, kI, kR, ts, T, γ) ∗
    if ok then ∃ y ts' T' γ',
        ⌜share = TExp (TInt 0) [y]⌝ ∗
        ⌜ts' ≤ ts⌝ ∗
        nonce_meta y (N.@"session")
          (swap_role rl, TExp (TInt 0) [x], kI, kR, ts', T', γ')
    else
      True.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_initiator c kI kR dq n T γ E :
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
        session γ kI kR kS Init (in_honest kI kR T) ∗
        □ (public kS ↔ ▷ ⌜negb (in_honest kI kR T)⌝)
      else True
 }}}.
Proof.
rewrite /initiator.
iIntros (??) "#chan_c #ctx #(? & ?) #p_kI #p_kR %Ψ !> hon Hpost".
wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce (λ _, ⌜negb (in_honest kI kR T)⌝)%I
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
wp_pures. wp_list. wp_term_of_list. wp_tenc.
iMod (term_meta_set _ _ (Init, gb, kI, kR, n, T, γ)
       (N.@"session") with "token") as "#sessionI" => //.
iAssert ( |={E}=>
    ●H{dq|n} T ∗
    (compromised_at n (TKey Enc kR) ∨
    ∃ b n' T' γ',
     ⌜gb = TExp (TInt 0) [b]⌝ ∗
     ⌜n' ≤ n⌝ ∗
     □ (public b ↔ ▷ □ (compromised_at n' (TKey Enc kI) ∨
                        compromised_at n' (TKey Enc kR))) ∗
     nonce_meta b (N.@"session")
       (Resp, TExp (TInt 0) [a], kI, kR, n', T', γ')))%I
  with "[hon H3]"
  as "{p_m2} > [hon #p_m2]".
{ iPoseProof (public_TEncE with "p_m2 [//]") as "{p_m2} p_m2".
  iDestruct "p_m2" as "[[comp _]  | (#i_m2 & _ & _)]".
  { iMod (compromised_atI with "[ctx] [H3] [hon] [comp]")
      as "[hon comp']" => //; try solve_ndisj. }
  iMod (lc_fupd_elim_later_pers with "H3 i_m2") as "{i_m2} #i_m2".
  iDestruct "i_m2"
    as "(%ga & %b & %kI' & %n' & %T' & %γr & %e_m2 & ? & _ & honR & pred_b)".
  case/Spec.of_list_inj: e_m2 => <- -> <- {ga gb kI'}.
  iPoseProof (honest_auth_frag_agree with "hon honR") as "[% %]".
  iModIntro. iFrame. iRight.
  iExists _, _, _, _. iSplit => //. iSplit => //. iSplit; last by [].
  by []. }
wp_pures. wp_bind (send _ _). iApply wp_send => //.
{ iModIntro.
  iApply public_TEncIS => //.
  - by rewrite !public_minted !minted_TKey.
  - iModIntro. iExists a, gb, kR, n, T, γ. do ![iSplitL => //].
    iDestruct "p_m2" as "[?|p_m2]".
    { iLeft. by iApply compromised_at_public. }
    iDestruct "p_m2" as "(%b & %n' & %T' & %γ' & % & % & ? & ?)".
    iRight. iExists b, n', T', γ'. by eauto.
  - rewrite minted_of_list /= minted_TExp /= minted_TInt minted_TKey.
    rewrite !public_minted !minted_TKey. by do ![iSplitL => //].
  - iIntros "!> _".
    rewrite public_of_list /=.
    by do ![iSplit => //]. }
iAssert (session γ kI kR (Spec.texp gb a) Init (in_honest kI kR T))
  as "#sessionI'".
{ iExists gb, a, n, T.
  do 4![iSplit => //].
  iDestruct "p_m2" as "[comp|p_m2]".
  - iPoseProof (honest_frag_compromised_at with "honI comp")
      as "%comp" => //.
    rewrite /in_honest bool_decide_decide decide_False //.
    tauto.
  - iDestruct "p_m2"
      as "(%b & %n' & %T' & %γ' & % & % & ? & ?)".
    case: in_honest => //.
    iExists b, n', T', γ'.
    eauto. }
case hon: (in_honest kI kR T); last first.
{ iAssert (public a) as "{p_a} p_a".
    by iApply "p_a".
  wp_pures. iApply ("Hpost" $! (Some (Spec.texp gb a))).
  iFrame. iModIntro. iSplit; first by iApply minted_texp.
  iSplit => //=.
  iModIntro.
  iSplit => //=; eauto.
  iIntros "_". by iApply public_texp. }
iDestruct "p_m2" as "[comp|p_m2]".
{ rewrite /in_honest bool_decide_eq_true in hon.
  iPoseProof (honest_frag_compromised_at with "honI comp") as "%" => //.
  tauto. }
rewrite /in_honest bool_decide_eq_true in hon.
case: hon => honI honR.
iDestruct "p_m2"
  as "(%b & %n' & %T' & %γ' & -> & %n'_n & p_b & p_m2)".
rewrite Spec.texpA.
wp_pures.
iApply ("Hpost" $! (Some (TExp (TInt 0) [a; b]))). iFrame.
rewrite !minted_TExp /= minted_TInt.
iDestruct "m_gb" as "(_ & m_b & _)". iModIntro.
iSplit; first do ![iSplit => //].
iSplit => //.
iModIntro.
rewrite public_TExp2.
iSplit; last first.
{ iIntros "#contra".
  iRight. iLeft. iSplit => //. iApply "p_a". by eauto. }
iIntros "[[_ #p_b'] | [[_ p_a'] | (_ & a_pred' & _)]]".
- iPoseProof ("p_b" with "p_b'") as "{p_b} p_b".
  iModIntro. iDestruct "p_b" as "[#compR | #compI]".
  + iPoseProof (honest_frag_compromised_at _ _ n'_n with "honI compR") as "%".
    set_solver.
  + iPoseProof (honest_frag_compromised_at _ _ n'_n with "honI compI") as "%".
    set_solver.
- iPoseProof ("p_a" with "p_a'") as ">%hon". tauto.
- iPoseProof ("a_pred" with "a_pred'") as ">%contra".
  by have := contra _ _ eq_refl.
Qed.

Lemma wp_responder c kR dq n T γ E :
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
        session γ kI kR kS Resp (in_honest kI kR T) ∗
        □ (public kS ↔ ▷ ⌜negb (in_honest kI kR T)⌝)
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
iApply (wp_mknonce (λ _, compromised_at n (TKey Enc kI) ∨
                         compromised_at n (TKey Enc kR))%I dh_auth_pred).
iIntros "%b #m_b #p_b #dh_gb token".
iAssert (public (TExp (TInt 0) [b])) as "#p_gb".
{ iApply public_TExp1. rewrite minted_TInt.
  do ![iSplit => //].
  iRight. iApply "dh_gb". iIntros "!> !> %g %ts %e".
  case/TExp_inj: e => _ perm.
  by rewrite -(Permutation_length perm). }
wp_pure _ credit:"H1".
wp_pure _ credit:"H2".
wp_bind (mkkeyshare _). iApply wp_mkkeyshare => //.
iIntros "!> _". wp_pures. wp_list. wp_term_of_list. wp_tenc.
iMod (term_meta_set _ _ (Resp, ga, kI, kR, n, T, γ)
       (N.@"session") with "token")
  as "#meta"; first solve_ndisj.
iPoseProof (honest_auth_frag with "hon_auth") as "#honR".
wp_pures. wp_bind (send _ _). iApply wp_send => //.
{ iModIntro.
  iApply public_TEncIS => //.
  - by rewrite public_minted !minted_TKey.
  - iModIntro.
    iExists ga, b, kI, n, T, γ.  by do ![iSplitL => //].
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
iAssert ( |={E}=> ●H{dq|n} T ∗
  □ (
  (compromised_at n (TKey Enc kI) ∨ compromised_at n (TKey Enc kR)) ∨
  ∃ a γ',
    ⌜ga = TExp (TInt 0) [a]⌝ ∗
    (public a ↔ ▷ □ ⌜negb (in_honest kI kR T)⌝) ∗
    (∀ t, dh_pred a t ↔ ▷ □ dh_auth_pred t) ∗
    nonce_meta a (N.@"session") (Init, TExp (TInt 0) [b], kI, kR, n, T, γ')))%I
  with "[hon_auth H3 H4]"
  as "{p_m3} > [hon_auth #i_m3]".
{ iDestruct "p_m3" as "[(p_skI & _) | (#i_m3 & _ & _)]".
  { iMod (compromised_atI with "[//] H3 hon_auth p_skI")
      as "[hon_auth #comp]" => //; try by solve_ndisj. }
  iMod (lc_fupd_elim_later_pers with "H4 i_m3") as "{i_m3} #i_m3".
  iDestruct "i_m3" as "(%a & %gb & %kR' & %n' & %T' & %γ' & %e_m3 &
                        p_a & pred_a & honI & sessionI & i_m3)".
  case/Spec.of_list_inj: e_m3 => -> <- <- {ga gb kR'}.
  iDestruct "i_m3" as "[i_m3 | i_m3]".
  { iMod (compromised_atI with "[//] H3 hon_auth i_m3")
      as "[hon_auth #comp]" => //; try by solve_ndisj. }
  iDestruct "i_m3" as "(%b' & %n'' & %T'' & %γ'' & %e_b & %n''_n' & i_m3)".
  case/TExp_inj: e_b => _ /(Permutation_singleton_inj _ _) <- {b'}.
  iPoseProof (term_meta_agree with "meta i_m3") as "%e_meta".
  case: e_meta => <- <- <- {n'' T'' γ''} in n''_n' *.
  iPoseProof (honest_auth_frag_agree with "hon_auth honI") as "[%n'_n %T'_T]".
  rewrite -(T'_T n''_n') {T' T'_T}.
  assert (n' = n) as -> by lia.
  iModIntro. iFrame.
  iRight. iModIntro. iExists a, γ'. by do ![iSplitL => //]. }
iAssert (session γ kI kR (Spec.texp ga b) Resp (in_honest kI kR T))
  as "sessionR".
{ iExists _, _, n, T. iSplit => //.
  do ![iSplit => //].
  iDestruct "i_m3" as "[[comp | comp]|i_m3]".
  - iPoseProof (honest_frag_compromised_at with "honR comp") as "%" => //.
    rewrite /in_honest bool_decide_eq_false_2 //; tauto.
  - iPoseProof (honest_frag_compromised_at with "honR comp") as "%" => //.
    rewrite /in_honest bool_decide_eq_false_2 //; tauto.
  case: in_honest => //.
  iDestruct "i_m3" as "(%a & %γ' & -> & ? & ? & ?)".
  iExists _, _, _, _; eauto. }
iAssert (minted (Spec.texp ga b)) as "#m_kS".
{ iApply minted_texp => //. by iApply public_minted. }
iAssert (minted kI) as "#m_kI".
{ iApply minted_TKey. by iApply public_minted. }
iDestruct "i_m3" as "[compromise|i_m3]".
{ iAssert (⌜in_honest kI kR T = false⌝)%I as "%hon".
  { iDestruct "compromise" as "[compI | compR]".
    - iPoseProof (honest_frag_compromised_at with "honR compI") as "%" => //.
      iPureIntro. apply/bool_decide_eq_false. tauto.
    - iPoseProof (honest_frag_compromised_at with "honR compR") as "%" => //.
      iPureIntro. apply/bool_decide_eq_false. tauto. }
  wp_pures.
  iApply ("Hpost" $! (Some (TKey Dec kI, Spec.texp ga b))).
  iFrame. iModIntro. iExists kI.
  rewrite hon.
  do 4![iSplit => //].
  iModIntro.
  iSplit.
  - by eauto.
  - iIntros "/= #contra". iApply public_texp => //.
    iApply "p_b". by eauto. }
iDestruct "i_m3" as "(%a & %γ' & -> & p_a & pred_a & metaI)".
rewrite Spec.texpA TExpC2. wp_pures.
iApply ("Hpost" $! (Some (TKey Dec kI, TExp (TInt 0) [a; b]))).
iFrame. iModIntro. iExists kI. do 2![iSplit => //].
rewrite minted_TExp minted_TInt /=. iSplit; first by eauto.
iSplit => //.
rewrite public_TExp2. iModIntro. iSplit.
- iIntros "#p_kS".
  iDestruct "p_kS" as "[[_ p_b'] | [ [_ p_a'] | (_ & contra & _)]]".
  + iPoseProof ("p_b" with "p_b'") as "#[#comp|#comp]"; iModIntro.
    * iDestruct (honest_frag_compromised_at with "honR comp") as "%" => //.
      rewrite /in_honest bool_decide_eq_false_2 //=. tauto.
    * iDestruct (honest_frag_compromised_at with "honR comp") as "%" => //.
      rewrite /in_honest bool_decide_eq_false_2 //=. tauto.
  + iPoseProof ("p_a" with "p_a'") as "{p_a} p_a".
    iModIntro. by eauto.
  + iPoseProof ("pred_a" with "contra") as ">%contra".
    by have := contra _ _ eq_refl.
- iIntros "#comp". iRight. iLeft. iSplit => //.
  iApply "p_a". by eauto.
Qed.

End Verif.
