From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics nown.
From cryptis Require Import role.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record sess_info := SessInfo {
  si_init : term;
  si_resp : term;
  si_key  : term;
  si_time : nat;
}.

(* MOVE *)
Lemma lc_fupd_elim_later_pers `{invGS Σ} E (P : iProp Σ) :
  £ 1 -∗ □ ▷ P ={E}=∗ □ P.
Proof.
rewrite bi.later_intuitionistically_2.
exact: lc_fupd_elim_later.
Qed.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).
Implicit Types (γ γa γb : gname) (ok : bool).
Implicit Types (ts : nat) (T : gset term).
Implicit Types (si : sess_info).

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
  let: "session_key" := mkskey (tag (nroot.@"keys".@"sym") "gab") in
  SOME "session_key".

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
  let: "session_key" := mkskey (tag (nroot.@"keys".@"sym") "gab") in
  SOME ("vkI", "session_key").

Definition in_honest kI kR T : bool :=
  bool_decide (TKey Enc kI ∈ T ∧ TKey Enc kR ∈ T).

Definition dh_auth_pred t : iProp :=
  ⌜∀ g ks, t = TExp g ks → length ks = 1⌝.

Definition msg2_pred kR m2 : iProp :=
  ∃ ga b kI n T γb,
    ⌜m2 = Spec.of_list [ga; TExp (TInt 0) [b]; TKey Dec kI]⌝ ∗
    minted_at n ga ∗
    (public b ↔ ▷ □ (compromised_at n (TKey Enc kI) ∨
                     compromised_at n (TKey Enc kR))) ∗
    (∀ t, dh_pred b t ↔ ▷ □ dh_auth_pred t) ∗
    ◯H{n} T ∗
    nonce_meta b (nroot.@"session") (Resp, ga, kI, kR, n, γb).

Definition msg3_pred kI m3 : iProp :=
  ∃ a gb kR n T γa,
    ⌜m3 = Spec.of_list [TExp (TInt 0) [a]; gb; TKey Dec kR]⌝ ∗
    (public a ↔ ▷ □ ⌜negb (in_honest kI kR T)⌝) ∗
    (∀ t, dh_pred a t ↔ ▷ □ dh_auth_pred t) ∗
    ◯H{n} T ∗
    nonce_meta a (nroot.@"session") (Init, gb, kI, kR, n, γa) ∗
    (public (TKey Enc kR) ∨
     ∃ b γb,
       ⌜gb = TExp (TInt 0) [b]⌝ ∗
       nonce_meta b (nroot.@"session")
         (Resp, TExp (TInt 0) [a], kI, kR, n, γb)).

Definition dh_auth_ctx : iProp :=
  enc_pred (N.@"m2") msg2_pred ∗
  enc_pred (N.@"m3") msg3_pred.

Lemma dh_auth_ctx_alloc E :
  ↑N ⊆ E →
  enc_pred_token E ==∗
  dh_auth_ctx.
Proof.
iIntros "%sub token".
iMod (enc_pred_set (N.@"m2") msg2_pred with "token")
  as "[#? token]"; try solve_ndisj.
iMod (enc_pred_set (N.@"m3") msg3_pred with "token")
  as "[#? token]"; try solve_ndisj.
iModIntro. by iSplit.
Qed.

Definition session si rl γ ok : iProp :=
  ∃ share x T,
    ⌜si_key si = Spec.tag (nroot.@"keys".@"sym") (Spec.texp share x)⌝ ∗
    ⌜ok = in_honest (si_init si) (si_resp si) T⌝ ∗
    ◯H{si_time si} T ∗
    nonce_meta x (nroot.@"session")
      (rl, share, si_init si, si_resp si, si_time si, γ) ∗
    if ok then ∃ y γ',
        ⌜share = TExp (TInt 0) [y]⌝ ∗
        nonce_meta y (nroot.@"session")
          (swap_role rl, TExp (TInt 0) [x],
            si_init si, si_resp si, si_time si, γ')
    else
      True.

Global Typeclasses Opaque session.

Global Instance session_persistent si rl γ ok :
  Persistent (session si rl γ ok).
Proof. rewrite /session. apply _. Qed.

Section WithSSRBool.

Import ssrbool.

Lemma eq_texp2 g a1 a2 b1 b2 :
  Spec.texp a1 b1 = Spec.texp (TExp g [a2]) b2 →
  a1 = TExp g [a2] ∧ b1 = b2 ∨
  a1 = TExp g [b2] ∧ b1 = a2.
Proof.
move=> e.
have /Spec.is_expP [g' [] ks e_exp] : is_true (is_exp a1).
  case exp: is_exp => //.
  rewrite Spec.is_expN_texp // ?exp //= in e *; auto.
  suff: is_true (is_exp (TInt 0)) by [].
  by rewrite e Spec.texpA is_exp_TExp.
rewrite {}e_exp !Spec.texpA {a1} in e *. symmetry in e.
case/TExp_inj: e => <- {g'} /(@Permutation_length_2_inv _ _ _ _) [].
- case=> <- -> {b2 ks}. by eauto.
- case=> <- -> {a2 ks}. by eauto.
Qed.

End WithSSRBool.

Lemma session_agree si1 si2 γ1 γ2 rl1 rl2 ok1 :
  si_key si1 = si_key si2 →
  session si1 rl1 γ1 ok1  -∗
  session si2 rl2 γ2 true -∗
  ⌜si1 = si2 ∧ ok1 = true⌝.
Proof.
case: si1 si2 => [kI1 kR1 kS ts1] [kI2 kR2 _ ts2] /= <-.
rewrite /session /=.
iIntros "(%share1 & %x1 & %T1 & -> & %e_hon1 & #hon1 & #meta1 & #rest1)".
iIntros "(%share2 & %x2 & %T2 & %e_kS & %e_hon2 & #hon2 & #meta2 & #rest2)".
iDestruct "rest2" as "(%y2 & %γ' & -> & meta')".
case/Spec.tag_inj: e_kS => _ /eq_texp2 [].
- case=> -> <- {share1 x2}.
  iPoseProof (term_meta_agree with "meta1 meta2") as "%e".
  case: e => <- <- <- <- <- in e_hon2 *.
  iPoseProof (honest_frag_agree with "hon1 hon2") as "<-".
  by rewrite e_hon1 -e_hon2.
- case=> -> <- {share1 y2}.
  iPoseProof (term_meta_agree with "meta1 meta'") as "%e".
  case: e => <- <- <- <- <- in e_hon2 *.
  iPoseProof (honest_frag_agree with "hon1 hon2") as "<-".
  by rewrite e_hon1 -e_hon2.
Qed.

Lemma session_agree_name si1 si2 γ1 γ2 rl ok1 :
  si_key si1 = si_key si2 →
  session si1 rl γ1 ok1 -∗
  session si2 rl γ2 true -∗
  ⌜si1 = si2 ∧ γ1 = γ2 ∧ ok1 = true⌝.
Proof.
case: si1 si2 => [kI1 kR1 kS ts1] [kI2 kR2 _ ts2] /= <-.
rewrite /session /=.
iIntros "(%share1 & %x1 & %T1 & -> & %e_hon1 & #hon1 & #meta1 & #rest1)".
iIntros "(%share2 & %x2 & %T2 & %e_kS & %e_hon2 & #hon2 & #meta2 & #rest2)".
iDestruct "rest2" as "(%y2 & %γ' & -> & meta')".
case/Spec.tag_inj: e_kS => _ /eq_texp2 [].
- case=> -> <- {share1 x2}.
  iPoseProof (term_meta_agree with "meta1 meta2") as "%e".
  case: e => <- <- <- <- in e_hon2 *.
  iPoseProof (honest_frag_agree with "hon1 hon2") as "<-".
  by rewrite e_hon1 -e_hon2.
- case=> -> <- {share1 y2}.
  iPoseProof (term_meta_agree with "meta1 meta'") as "%e".
  case: e; by case: rl.
Qed.

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
  {{{ okS, RET (repr (Spec.mkskey <$> okS));
      ●H{dq|n} T ∗
      if okS is Some kS then
        minted kS ∗
        session (SessInfo kI kR kS n) Init γ (in_honest kI kR T) ∗
        □ (∀ kt, public (TKey kt kS) ↔ ▷ ⌜negb (in_honest kI kR T)⌝)
      else True
 }}}.
Proof.
rewrite /initiator.
iIntros (??) "#chan_c #ctx #(? & ?) #p_kI #p_kR %Ψ !> hon Hpost".
iMod (minted_at_list with "[//] hon") as "[hon list]" => //;
  try solve_ndisj.
wp_pures.
iDestruct "list" as "(%M & #m_M & #minted_at_M)".
wp_bind (mknonce _).
iApply (wp_mknonce_gen M (λ _, ⌜negb (in_honest kI kR T)⌝)%I
          dh_auth_pred).
{ iIntros "% ?". rewrite big_sepS_forall. by iApply "m_M". }
iIntros "%a %fresh #m_a #p_a #a_pred token".
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
iMod (term_meta_set _ _ (Init, gb, kI, kR, n, γ)
       (nroot.@"session") with "token") as "#sessionI" => //.
iAssert ( |={E}=>
    ●H{dq|n} T ∗
    (compromised_at n (TKey Enc kR) ∨
    ∃ b γ',
     ⌜gb = TExp (TInt 0) [b]⌝ ∗
     □ (public b ↔ ▷ □ (compromised_at n (TKey Enc kI) ∨
                        compromised_at n (TKey Enc kR))) ∗
     nonce_meta b (nroot.@"session")
       (Resp, TExp (TInt 0) [a], kI, kR, n, γ')))%I
  with "[hon H3]"
  as "{p_m2} > [hon #p_m2]".
{ iPoseProof (public_TEncE with "p_m2 [//]") as "{p_m2} p_m2".
  iDestruct "p_m2" as "[[comp _]  | (#i_m2 & _ & _)]".
  { iMod (compromised_atI with "[ctx] [H3] [hon] [comp]")
      as "[hon comp']" => //; try solve_ndisj. }
  iMod (lc_fupd_elim_later_pers with "H3 i_m2") as "{i_m2} #i_m2".
  iDestruct "i_m2"
    as "(%ga & %b & %kI' & %n' & %T' & %γr & %e_m2 &
         m_ga & ? & _ & honR & pred_b)".
  case/Spec.of_list_inj: e_m2 => <- -> <- {ga gb kI'}.
  iPoseProof (honest_auth_frag_agree with "hon honR") as "[% %]".
  case: (decide (n' < n)) => [contra|?].
  { iPoseProof ("minted_at_M" with "[//] m_ga") as "%ga_M".
    move/(_ _ ga_M)/subtermsP: fresh.
    rewrite subterms_TExp /= !elem_of_union => fresh.
    case: fresh.
    right. right. left. apply/subtermsP. apply/STRefl. }
  have ? : n' = n by lia. subst n'.
  iPoseProof (honest_frag_agree with "honR honI") as "->".
  iModIntro. iFrame. iRight.
  iExists _, _. do !iSplit => //. }
wp_pures. wp_bind (send _ _). iApply wp_send => //.
{ iModIntro.
  iApply public_TEncIS => //.
  - by rewrite !public_minted !minted_TKey.
  - iModIntro. iExists a, gb, kR, n, T, γ. do ![iSplitL => //].
    iDestruct "p_m2" as "[?|p_m2]".
    { iLeft. by iApply compromised_at_public. }
    iDestruct "p_m2" as "(%b & %γ' & % & ? & ?)".
    iRight. iExists b, γ'. by eauto.
  - rewrite minted_of_list /= minted_TExp /= minted_TInt minted_TKey.
    rewrite !public_minted !minted_TKey. by do ![iSplitL => //].
  - iIntros "!> _".
    rewrite public_of_list /=.
    by do ![iSplit => //]. }
wp_pures. wp_tag. wp_bind (mkskey _). iApply wp_mkskey.
set sk := Spec.tag _ _.
pose si := SessInfo kI kR sk n.
iAssert (session si Init γ (in_honest kI kR T)) as "#sessionI'".
{ iExists gb, a, T.
  do 4![iSplit => //].
  iDestruct "p_m2" as "[comp|p_m2]".
  - iPoseProof (honest_frag_compromised_at with "honI comp")
      as "%comp" => //.
    rewrite /in_honest bool_decide_decide decide_False //.
    tauto.
  - iDestruct "p_m2" as "(%b & %γ' & % & ? & ?)".
    case: in_honest => //.
    iExists b, γ'.
    eauto. }
case hon: (in_honest kI kR T); last first.
{ iAssert (public a) as "{p_a} p_a".
    by iApply "p_a".
  wp_pures. iApply ("Hpost" $! (Some sk)).
  iFrame. iModIntro. iSplit.
    iApply minted_tag. by iApply minted_texp.
  iSplit => //=.
  iIntros "!> %kt".
  iSplit => //=; eauto.
  iIntros "_".
  rewrite (public_TKey kt) public_tag. iLeft.
  by iApply public_texp. }
iDestruct "p_m2" as "[comp|p_m2]".
{ rewrite /in_honest bool_decide_eq_true in hon.
  iPoseProof (honest_frag_compromised_at with "honI comp") as "%" => //.
  tauto. }
rewrite /in_honest bool_decide_eq_true in hon.
case: hon => honI honR.
iDestruct "p_m2" as "(%b & %γ' & -> & p_b & p_m2)".
rewrite Spec.texpA in sk si *.
wp_pures.
iApply ("Hpost" $! (Some sk)). iFrame.
rewrite minted_tag !minted_TExp /= minted_TInt.
iDestruct "m_gb" as "(_ & m_b & _)". iModIntro.
iSplit; first do ![iSplit => //].
iSplit => //.
iIntros "!> %kt".
iSplit; last first.
{ iIntros "#contra".
  rewrite (public_TKey kt). iLeft.
  rewrite public_tag public_TExp2.
  iRight. iLeft. iSplit => //. iApply "p_a". by eauto. }
iIntros "#p_sk".
iPoseProof (public_sym_keyE with "[//] p_sk") as "{p_sk} >p_sk".
rewrite public_TExp2.
iDestruct "p_sk" as "[[_ #p_b'] | [[_ p_a'] | (_ & a_pred' & _)]]".
- iPoseProof ("p_b" with "p_b'") as "{p_b} p_b".
  iModIntro. iDestruct "p_b" as "[#compR | #compI]".
  + iPoseProof (honest_frag_compromised_at _ _ with "honI compR") as "%" => //.
  + iPoseProof (honest_frag_compromised_at _ _ with "honI compI") as "%" => //.
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
  {{{ okS,
      RET (repr ((λ p, pair p.1 (Spec.mkskey p.2)) <$> okS));
      ●H{dq|n} T ∗
      if okS is Some (vkI, kS) then ∃ kI,
        ⌜vkI = TKey Dec kI⌝ ∗
        minted kI ∗
        minted kS ∗
        session (SessInfo kI kR kS n) Resp γ (in_honest kI kR T) ∗
        □ (∀ kt, public (TKey kt kS) ↔ ▷ ⌜negb (in_honest kI kR T)⌝)
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
iPoseProof (public_minted with "p_ga") as "m_ga".
iMod (minted_atI with "[//] hon_auth m_ga")
  as "{m_ga} [hon_auth #m_ga]"; first by solve_ndisj.
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
iMod (term_meta_set _ _ (Resp, ga, kI, kR, n, γ)
       (nroot.@"session") with "token")
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
    nonce_meta a (nroot.@"session") (Init, TExp (TInt 0) [b], kI, kR, n, γ')))%I
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
  iDestruct "i_m3" as "(%b' & %γ'' & %e_b & i_m3)".
  case/TExp_inj: e_b => _ /(Permutation_singleton_inj _ _) <- {b'}.
  iPoseProof (term_meta_agree with "meta i_m3") as "%e_meta".
  case: e_meta => <- <-.
  iPoseProof (honest_frag_agree with "honR honI") as "->".
  iModIntro. iFrame.
  iRight. iModIntro. iExists a, γ'. by do ![iSplitL => //]. }
wp_pures. wp_tag. set sk := Spec.tag _ _. pose si := SessInfo kI kR sk n.
iAssert (session si Resp γ (in_honest kI kR T)) as "sessionR".
{ iExists _, _, T. iSplit => //.
  do ![iSplit => //].
  iDestruct "i_m3" as "[[comp | comp]|i_m3]".
  - iPoseProof (honest_frag_compromised_at with "honR comp") as "%" => //.
    rewrite /in_honest bool_decide_eq_false_2 //; tauto.
  - iPoseProof (honest_frag_compromised_at with "honR comp") as "%" => //.
    rewrite /in_honest bool_decide_eq_false_2 //; tauto.
  case: in_honest => //.
  iDestruct "i_m3" as "(%a & %γ' & -> & ? & ? & ?)".
  iExists _, _; eauto. }
iAssert (minted sk) as "#m_kS".
{ iApply minted_tag. iApply minted_texp => //. by iApply public_minted. }
iAssert (minted kI) as "#m_kI".
{ iApply minted_TKey. by iApply public_minted. }
wp_bind (mkskey _). iApply wp_mkskey. wp_pures.
iDestruct "i_m3" as "[compromise|i_m3]".
{ iAssert (⌜in_honest kI kR T = false⌝)%I as "%hon".
  { iDestruct "compromise" as "[compI | compR]".
    - iPoseProof (honest_frag_compromised_at with "honR compI") as "%" => //.
      iPureIntro. apply/bool_decide_eq_false. tauto.
    - iPoseProof (honest_frag_compromised_at with "honR compR") as "%" => //.
      iPureIntro. apply/bool_decide_eq_false. tauto. }
  iApply ("Hpost" $! (Some (TKey Dec kI, sk))).
  iFrame. iModIntro. iExists kI.
  rewrite hon.
  do 4![iSplit => //].
  iIntros "!> %kt".
  iSplit.
  - by eauto.
  - iIntros "/= #contra".
    rewrite (public_TKey kt) public_tag. iLeft.
    iApply public_texp => //.
    iApply "p_b". by eauto. }
iDestruct "i_m3" as "(%a & %γ' & -> & p_a & pred_a & metaI)".
rewrite Spec.texpA TExpC2 in sk si *.
iApply ("Hpost" $! (Some (TKey Dec kI, sk))).
iFrame. iModIntro. iExists kI. do 2![iSplit => //].
rewrite minted_tag minted_TExp minted_TInt /=. iSplit; first by eauto.
iSplit => //.
iIntros "!> %kt". iSplit.
- iIntros "#p_kS".
  iPoseProof (public_sym_keyE with "[//] p_kS") as "{p_kS} >p_kS".
  rewrite public_TExp2.
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
- iIntros "#comp". rewrite (public_TKey kt). iLeft.
  rewrite public_tag public_TExp2. iRight. iLeft. iSplit => //.
  iApply "p_a". by eauto.
Qed.

End Verif.
