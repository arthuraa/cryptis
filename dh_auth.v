From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis primitives tactics.
From cryptis Require Import role.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record sess_info := SessInfo {
  si_init : term;
  si_resp : term;
  si_key  : term;
  si_time : nat;
  si_hon  : gset term;
}.

Global Instance sess_info_inhabited : Inhabited sess_info :=
  populate (SessInfo inhabitant inhabitant inhabitant inhabitant inhabitant).

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

Definition dh_auth_pred t : iProp :=
  ⌜∀ g ks, t = TExp g ks → length ks = 1⌝.

Definition session_fail si : iProp :=
  public_at (si_time si) (TKey Enc (si_init si)) ∨
  public_at (si_time si) (TKey Enc (si_resp si)).

Definition msg2_pred kR m2 : iProp :=
  ∃ ga b kI n T γb,
    ⌜m2 = Spec.of_list [ga; TExp (TInt 0) [b]; TKey Dec kI]⌝ ∗
    minted_at n ga ∗
    (public b ↔ ▷ □ (public_at n (TKey Enc kI) ∨
                     public_at n (TKey Enc kR))) ∗
    (∀ t, dh_pred b t ↔ ▷ □ dh_auth_pred t) ∗
    ◯H{n} T ∗
    nonce_meta b nroot (Resp, ga, kI, kR, n, γb).

Definition msg3_pred kI m3 : iProp :=
  ∃ a gb kR n T γa,
    ⌜m3 = Spec.of_list [TExp (TInt 0) [a]; gb; TKey Dec kR]⌝ ∗
    (public a ↔ ▷ □ (public_at n (TKey Enc kI) ∨
                     public_at n (TKey Enc kR))) ∗
    (∀ t, dh_pred a t ↔ ▷ □ dh_auth_pred t) ∗
    ◯H{n} T ∗
    nonce_meta a nroot (Init, gb, kI, kR, n, γa) ∗
    (public_at n (TKey Enc kR) ∨
     ∃ b γb,
       ⌜gb = TExp (TInt 0) [b]⌝ ∗
       nonce_meta b nroot (Resp, TExp (TInt 0) [a], kI, kR, n, γb)).

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

Definition session γ si rl : iProp := ∃ x gy,
  ⌜si_key si = Spec.tag (nroot.@"keys".@"sym") (Spec.texp gy x)⌝ ∗
  gmeta γ (nroot.@"dh_auth")
    (rl, gy, si_init si, si_resp si, si_time si, x) ∗
  nonce_meta x nroot (rl, gy, si_init si, si_resp si, si_time si, γ) ∗
  ◯H{si_time si} si_hon si ∗
  (session_fail si ∨ ∃ y γ',
     ⌜gy = TExp (TInt 0) [y]⌝ ∗
     nonce_meta y nroot (swap_role rl, TExp (TInt 0) [x],
       si_init si, si_resp si, si_time si, γ')).

Global Typeclasses Opaque session.

Global Instance session_persistent si rl γ : Persistent (session γ si rl).
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

Lemma session_agree si1 si2 γ1 γ2 rl1 rl2 :
  si_key si1 = si_key si2 →
  session γ1 si1 rl1 -∗
  session γ2 si2 rl2 -∗
  session_fail si2 ∨ ⌜si1 = si2⌝.
Proof.
case: si1 si2 => [kI1 kR1 kS ts1 T1] [kI2 kR2 _ ts2 T2] /= <-.
iIntros "#sess1 #sess2". rewrite /session /=.
iDestruct "sess1" as "(%x1 & %gx2 & -> & #γ1 & #x1 & #hon1 & #sess1)".
iDestruct "sess2" as "(%x2 & %gx1 & %e & #γ2 & #x2 & #hon2 & #sess2)".
case/Spec.tag_inj: e => _ e.
iDestruct "sess2" as "[fail|sess2]"; first by eauto.
iDestruct "sess2" as "(%x1' & %γ1' & -> & #x1')".
case/eq_texp2: e.
- case=> -> <- {gx2 x2} /=.
  iPoseProof (term_meta_agree with "x1 x2") as "%e".
  case: e => <- <- <- <- <-.
  iPoseProof (honest_frag_agree with "hon1 hon2") as "<-".
  by eauto.
- case=> -> <- {gx2 x1'} /=.
  iPoseProof (term_meta_agree with "x1 x1'") as "%e".
  case: e => -> <- <- <- <-.
  iPoseProof (honest_frag_agree with "hon1 hon2") as "<-".
  by eauto.
Qed.

Lemma session_agree_name si1 si2 γ1 γ2 rl :
  si_key si1 = si_key si2 →
  session γ1 si1 rl -∗
  session γ2 si2 rl -∗
  session_fail si2 ∨ ⌜si1 = si2 ∧ γ1 = γ2⌝.
Proof.
case: si1 si2 => [kI1 kR1 kS ts1 T1] [kI2 kR2 _ ts2 T2] /= <-.
iIntros "#sess1 #sess2". rewrite /session /=.
iDestruct "sess1" as "(%x1 & %gx2 & -> & #γ1 & #x1 & #hon1 & #sess1)".
iDestruct "sess2" as "(%x2 & %gx1 & %e & #γ2 & #x2 & #hon2 & #sess2)".
case/Spec.tag_inj: e => _ e.
iDestruct "sess2" as "[fail|sess2]"; first by eauto.
iDestruct "sess2" as "(%x1' & %γ1' & -> & #x1')".
case/eq_texp2: e.
- case=> -> <- {gx2 x2} /=.
  iPoseProof (term_meta_agree with "x1 x2") as "%e".
  case: e => <- <- <- <-.
  iPoseProof (honest_frag_agree with "hon1 hon2") as "<-".
  by eauto.
- case=> -> <- {gx2 x1'} /=.
  iPoseProof (term_meta_agree with "x1 x1'") as "%e".
  by case: rl in e *.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_initiator c kI kR dq n T E :
  ↑cryptisN ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  dh_auth_ctx -∗
  public (TKey Dec kI) -∗
  public (TKey Dec kR) -∗
  {{{ ●H{dq|n} T }}}
    initiator c (TKey Dec kI) (TKey Enc kI) (TKey Dec kR) @ E
  {{{ okS, RET (repr (Spec.mkskey <$> okS));
      ●H{dq|n} T ∗
      if okS is Some kS then ∃ γ,
        let si := SessInfo kI kR kS n T in
        minted kS ∗
        session γ si Init ∗
        gmeta_token γ (⊤ ∖ ↑nroot.@"dh_auth") ∗
        □ (∀ kt, public (TKey kt kS) ↔ ▷ session_fail si)
      else True
 }}}.
Proof.
rewrite /initiator.
iIntros (?) "#chan_c #ctx #(? & ?) #p_kI #p_kR %Ψ !> hon Hpost".
iMod gmeta_token_alloc as (γ) "γ_token".
iMod (minted_at_list with "[//] hon") as "[hon list]" => //;
  try solve_ndisj.
wp_pures.
iDestruct "list" as "(%M & #m_M & #minted_at_M)".
wp_bind (mknonce _).
iApply (wp_mknonce_fresh M (λ _, public_at n (TKey Enc kI) ∨
                                 public_at n (TKey Enc kR))%I
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
iMod (gmeta_set' _ _ (nroot.@"dh_auth") (Init, gb, kI, kR, n, a)
        with "γ_token") as "[#γ_own γ_token]" => //.
iMod (term_meta_set _ _ (Init, gb, kI, kR, n, γ)
       nroot with "token") as "#sessionI" => //.
iAssert ( |={E}=>
    ●H{dq|n} T ∗
    (public_at n (TKey Enc kR) ∧ ⌜TKey Enc kR ∉ T⌝ ∨
    ∃ b γ',
     ⌜gb = TExp (TInt 0) [b]⌝ ∗
     □ (public b ↔ ▷ □ (public_at n (TKey Enc kI) ∨
                        public_at n (TKey Enc kR))) ∗
     nonce_meta b nroot
       (Resp, TExp (TInt 0) [a], kI, kR, n, γ')))%I
  with "[hon H3]"
  as "{p_m2} > [hon #p_m2]".
{ iPoseProof (public_TEncE with "p_m2 [//]") as "{p_m2} p_m2".
  iDestruct "p_m2" as "[[comp _]  | (#i_m2 & _ & _)]".
  { iMod (public_atI with "[ctx] [H3] [hon] [comp]")
      as "[hon #comp']" => //; try solve_ndisj.
    iPoseProof (honest_frag_public_at with "honI comp'") as "%" => //.
    iFrame. eauto. }
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
    iDestruct "p_m2" as "[[? _]|p_m2]"; eauto.
    iDestruct "p_m2" as "(%b & %γ' & % & ? & ?)".
    iRight. iExists b, γ'. by eauto.
  - rewrite minted_of_list /= minted_TExp /= minted_TInt minted_TKey.
    rewrite !public_minted !minted_TKey. by do ![iSplitL => //].
  - iIntros "!> _".
    rewrite public_of_list /=.
    by do ![iSplit => //]. }
wp_pures. wp_tag. wp_bind (mkskey _). iApply wp_mkskey.
set sk := Spec.tag _ _.
pose si := SessInfo kI kR sk n T.
iAssert (session γ si Init) as "#sessionI'".
{ iExists a, gb.
  do 4![iSplit => //].
  iDestruct "p_m2" as "[[? %comp]|p_m2]".
  - iLeft. by iRight.
  - iDestruct "p_m2" as "(%b & %γ' & % & ? & ?)".
    iRight.
    iExists b, γ'.
    eauto. }
iAssert (minted sk) as "#?".
{ rewrite minted_tag. iApply minted_texp => //. }
iAssert (□ (∀ kt, public (TKey kt sk) ↔ ▷ session_fail si))%I as "#sec_sk".
{ iIntros "!> %kt". iSplit; last first.
  { iIntros "#comp".
    rewrite (public_TKey kt) public_tag. iLeft.
    iApply public_texp => //.
    iApply "p_a". eauto. }
  iIntros "#p_sk".
  iPoseProof (public_sym_keyE with "[//] p_sk") as "{p_sk} >p_sk".
  iDestruct "p_m2" as "[[? %comp]|p_m2]".
  - by iRight.
  - iDestruct "p_m2" as "(%b & %γ' & -> & #p_b & p_m2)".
    rewrite Spec.texpA public_TExp2.
    iDestruct "p_sk" as "[[_ #p_b'] | [[_ p_a'] | (_ & a_pred' & _)]]".
    + iPoseProof ("p_b" with "p_b'") as "{p_b} p_b". by eauto.
    + iPoseProof ("p_a" with "p_a'") as "hon'". by eauto.
    + iPoseProof ("a_pred" with "a_pred'") as ">%contra".
      by have := contra _ _ eq_refl. }
wp_pures. iApply ("Hpost" $! (Some sk)). iFrame.
rewrite -[SessInfo _ _ _ _ _]/si. iExists γ.
iFrame. eauto.
Qed.

Lemma wp_responder c kR dq n T E :
  ↑cryptisN ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  dh_auth_ctx -∗
  public (TKey Dec kR) -∗
  {{{ ●H{dq|n} T }}}
    responder c (TKey Dec kR) (TKey Enc kR) @ E
  {{{ okS,
      RET (repr ((λ p, pair p.1 (Spec.mkskey p.2)) <$> okS));
      ●H{dq|n} T ∗
      if okS is Some (vkI, kS) then ∃ kI γ,
        let si := SessInfo kI kR kS n T in
        ⌜vkI = TKey Dec kI⌝ ∗
        public vkI ∗
        minted kS ∗
        session γ si Resp ∗
        gmeta_token γ (⊤ ∖ ↑nroot.@"dh_auth") ∗
        □ (∀ kt, public (TKey kt kS) ↔ ▷ session_fail si)
      else True
 }}}.
Proof.
iIntros "% #chan_c #? (#? & #?) #p_vkR !> %Φ hon_auth Hpost".
iMod gmeta_token_alloc as (γ) "γ_token".
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
iApply (wp_mknonce (λ _, public_at n (TKey Enc kI) ∨ 
                         public_at n (TKey Enc kR))%I
          dh_auth_pred).
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
iMod (term_meta_set _ _ (Resp, ga, kI, kR, n, γ) nroot with "token")
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
wp_pures. wp_tag. set sk := Spec.tag _ _. pose si := SessInfo kI kR sk n T.
iAssert ( |={E}=> ●H{dq|n} T ∗
  □ (session_fail si ∧
  ⌜¬ (TKey Enc kI ∈ T ∧ TKey Enc kR ∈ T)⌝ ∨
  ∃ a γ',
    ⌜ga = TExp (TInt 0) [a]⌝ ∗
    (public a ↔ ▷ □ session_fail si) ∗
    (∀ t, dh_pred a t ↔ ▷ □ dh_auth_pred t) ∗
    nonce_meta a nroot (Init, TExp (TInt 0) [b], kI, kR, n, γ')))%I
  with "[hon_auth H3 H4]"
  as "{p_m3} > [hon_auth #i_m3]".
{ iDestruct "p_m3" as "[(p_skI & _) | (#i_m3 & _ & _)]".
  { iMod (public_atI with "[//] H3 hon_auth p_skI")
      as "[hon_auth #comp]" => //; try by solve_ndisj.
    iPoseProof (honest_frag_public_at with "honR comp") as "%" => //.
    iFrame. iLeft. iIntros "!> !>". iSplit.
    - by iLeft.
    - by iIntros "%"; tauto. }
  iMod (lc_fupd_elim_later_pers with "H4 i_m3") as "{i_m3} #i_m3".
  iDestruct "i_m3" as "(%a & %gb & %kR' & %n' & %T' & %γ' & %e_m3 &
                        p_a & pred_a & honI & sessionI & i_m3)".
  case/Spec.of_list_inj: e_m3 => -> <- <- {ga gb kR'} in sk si *.
  iDestruct "i_m3" as "[i_m3 | i_m3]".
  { iPoseProof (public_at_public with "i_m3") as "i_m3'".
    iMod (public_atI with "[//] H3 hon_auth i_m3'")
      as "[hon_auth #comp]" => //; try by solve_ndisj.
    iPoseProof (honest_frag_public_at with "honR comp") as "%" => //.
    iFrame. iLeft. iIntros "!> !>". iSplit.
    - by iRight.
    - by iIntros "%"; tauto. }
  iDestruct "i_m3" as "(%b' & %γ'' & %e_b & i_m3)".
  case/TExp_inj: e_b => _ /(Permutation_singleton_inj _ _) <- {b'}.
  iPoseProof (term_meta_agree with "meta i_m3") as "%e_meta".
  case: e_meta => <- <-.
  iPoseProof (honest_frag_agree with "honR honI") as "->".
  iModIntro. iFrame.
  iRight. iModIntro. iExists a, γ'. by do ![iSplitL => //]. }
iMod (gmeta_set' _ _ (nroot.@"dh_auth") (Resp, ga, kI, kR, n, b)
        with "γ_token") as "[#γ_own γ_token]" => //.
iAssert (session γ si Resp) as "sessionR".
{ iExists _, _. iSplit => //.
  do ![iSplit => //].
  iDestruct "i_m3" as "[[fail %comp]|i_m3]".
  - by eauto.
  - iRight.
    iDestruct "i_m3" as "(%a & %γ' & -> & ? & ? & ?)".
    iExists _, _; eauto. }
iAssert (minted sk) as "#m_kS".
{ iApply minted_tag. iApply minted_texp => //. by iApply public_minted. }
iAssert (minted kI) as "#m_kI".
{ iApply minted_TKey. by iApply public_minted. }
wp_bind (mkskey _). iApply wp_mkskey. wp_pures.
iAssert (□ (∀ kt, public (TKey kt sk) ↔ ▷ session_fail si))%I
  as "#sec_sk".
{ iIntros "!> %kt". iSplit; last first.
  { iIntros "#comp". iApply public_TKey. iLeft.
    iApply public_tag. iApply public_texp => //.
    iApply "p_b". eauto. }
  iIntros "#p_sk".
  iPoseProof (public_sym_keyE with "[//] p_sk") as ">p_kS".
  iDestruct "i_m3" as "[[? compromise]|i_m3]" => //.
  iDestruct "i_m3" as "(%a & %γ' & -> & p_a & pred_a & metaI)".
  rewrite Spec.texpA TExpC2 in sk si *.
  rewrite public_TExp2.
  iDestruct "p_kS" as "[[_ p_b'] | [ [_ p_a'] | (_ & contra & _)]]".
  - iPoseProof ("p_b" with "p_b'") as "?". by eauto.
  - iPoseProof ("p_a" with "p_a'") as "{p_a} p_a". by eauto.
  + iPoseProof ("pred_a" with "contra") as ">%contra".
    by have := contra _ _ eq_refl. }
iApply ("Hpost" $! (Some (TKey Dec kI, sk))).
iFrame. iModIntro. iExists kI, γ. iFrame. by eauto.
Qed.

End Verif.

Arguments dh_auth_ctx_alloc {Σ _ _} N E.
