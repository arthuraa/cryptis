From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics role nown dh.
From cryptis Require Import pk_auth.
From cryptis Require Import session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PKDH.

Context `{heap : !heapGS Σ, cryptis : !cryptisG Σ, sess : !sessionG Σ}.
Notation iProp := (iProp Σ).
Implicit Types rl : role.
Implicit Types t kI kR nI nR sI sR : term.

Definition pk_dh_mk_key_share n := TExp (TInt 0) [n].

Definition pk_dh_mk_key_share_impl : val := λ: <>,
  let: "n" := mknonce #() in
  ("n", texp (tgroup (tint #0)) "n").

Definition pk_dh_mk_session_key rl n s : term :=
  Spec.texp s n.

Definition pk_dh_mk_session_key_impl rl : val :=
  λ: "n" "s", texp "s" "n".

Variable N : namespace.

Definition pk_dh_init : val := λ: "c",
  pk_auth_init N "c" pk_dh_mk_key_share_impl (pk_dh_mk_session_key_impl Init).

Definition pk_dh_resp : val := λ: "c",
  pk_auth_resp N "c" pk_dh_mk_key_share_impl (pk_dh_mk_session_key_impl Resp).

#[local]
Program Instance PK_DH : PK := {
  is_priv_key n kI kR := dh_seed (λ _, corruption kI kR) n;

  mk_key_share := pk_dh_mk_key_share;
  mk_key_share_impl := pk_dh_mk_key_share_impl;
  mk_session_key := pk_dh_mk_session_key;
  mk_session_key_impl := pk_dh_mk_session_key_impl;

}.

Next Obligation.
by move=> t1 t2 /TExp_inj [_ /(Permutation_singleton_inj _ _) t1t2].
Qed.

Next Obligation.
move=> n; rewrite sterm_TExp /= sterm_TInt. apply: anti_symm.
- by iIntros "(_ & ? & _)".
- by eauto.
Qed.

Next Obligation.
iIntros "%nI %kI %kR #s_nI #dh".
rewrite /pk_dh_mk_key_share /secret_of. iModIntro. iSplit.
- iIntros "#p_sI".
  by iPoseProof (dh_seed_elim1 with "dh p_sI") as "H".
- iIntros "#fail". iApply dh_pterm_TExp; eauto. by rewrite sterm_TInt.
Qed.

Next Obligation.
move=> nI nR; rewrite /pk_dh_mk_key_share /pk_dh_mk_session_key.
by rewrite !Spec.texpA TExpC2.
Qed.

Next Obligation.
iIntros "%rl %t1 %t2 #s_t1 #s_t2".
by rewrite /pk_dh_mk_session_key; iApply sterm_texp.
Qed.

Next Obligation.
iIntros "%E %kI %kR %Φ _ post". rewrite /pk_dh_mk_key_share_impl.
wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce _ (λ _, False)%I (dh_publ (λ _, corruption kI kR))).
iIntros "%n #s_n #p_n #dh token". wp_pures.
wp_bind (tint _). iApply wp_tint.
wp_bind (tgroup _). iApply wp_tgroup.
wp_bind (texp _ _). iApply wp_texp. rewrite Spec.texpA.
wp_pures. iModIntro. iApply "post".
rewrite bi.intuitionistic_intuitionistically.
iFrame. by do !iSplit => //.
Qed.

Next Obligation.
iIntros "%E %rl %n %s %Φ _ post".
rewrite /pk_dh_mk_session_key_impl.
wp_pures. iApply wp_texp. by iApply "post".
Qed.

Lemma pk_dh_session_key_elim kI kR kS :
  session_key N kI kR kS -∗
  pterm kS →
  ◇ False.
Proof.
iIntros "(%nI & %nR & -> & #priv_nI & #priv_nR & _)".
rewrite /= /pk_dh_mk_session_key /pk_dh_mk_key_share Spec.texpA.
iIntros "#p_kS".
iDestruct (dh_seed_elim2 with "priv_nI p_kS") as "[>p_sI >contra]".
by iDestruct (dh_seed_elim0 with "priv_nR contra") as ">[]".
Qed.

Lemma wp_pk_dh_init c kI kR E :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  ctx N -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  {{{ True }}}
    pk_dh_init c (TKey Dec kI) (TKey Enc kI) (TKey Enc kR) @ E
  {{{ (okS : option term), RET repr okS;
      if okS is Some kS then
        sterm kS ∗
        (corruption kI kR ∨
         □ (pterm kS → ◇ False) ∗
         session_key_token N Init kS ∗
         session_key N kI kR kS)
      else True
  }}}.
Proof.
iIntros "% % #chan_c #ctx #p_ekI #p_ekR %Ψ !> _ post".
rewrite /pk_dh_init; wp_pures.
iApply (wp_pk_auth_init with "chan_c ctx"); eauto.
iIntros "!> %okS". case: okS => [kS|]; last first.
  by iApply ("post" $! None).
iIntros "[#s_kS kSP]". iApply ("post" $! (Some kS)).
iSplitR => //.
iDestruct "kSP" as "[fail|[token #key]]"; eauto.
iRight. iFrame. iSplit => //. iModIntro.
by iApply pk_dh_session_key_elim.
Qed.

Lemma wp_pk_dh_resp c kR E :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  ctx N -∗
  pterm (TKey Enc kR) -∗
  {{{ True }}}
    pk_dh_resp c (TKey Dec kR) (TKey Enc kR) @ E
  {{{ (res : option (term * term)), RET repr res;
      if res is Some (pkI, kS) then ∃ kI,
        ⌜pkI = TKey Enc kI⌝ ∧
        pterm pkI ∧
        sterm kS ∧
        (corruption kI kR ∨
         □ (pterm kS → ◇ False) ∗
         session_key_token N Resp kS ∗
         session_key N kI kR kS)
      else True
  }}}.
Proof.
iIntros "% % #chan_c #ctx #p_ekR %Ψ !> _ post".
rewrite /pk_dh_resp; wp_pures.
iApply (wp_pk_auth_resp with "chan_c ctx"); eauto.
iIntros "!> %res". case: res => [[pkI kS]|]; last first.
  by iApply ("post" $! None).
iIntros "(%kI & -> & #p_pkI & #s_kS & kSP)".
iApply ("post" $! (Some (TKey Enc kI, kS))). iExists kI.
do 3!iSplitR => //.
iDestruct "kSP" as "[fail|[token #key]]"; eauto.
iRight. iFrame. iSplit => //. iModIntro.
by iApply pk_dh_session_key_elim.
Qed.

End PKDH.
