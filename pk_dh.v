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

Variable pk_dh_confirmation : role → term → term → term → iProp.

Definition pk_dh_init : val := λ: "c",
  pk_auth_init N "c" pk_dh_mk_key_share_impl (pk_dh_mk_session_key_impl Init).

Definition pk_dh_resp : val := λ: "c",
  pk_auth_resp N "c" pk_dh_mk_key_share_impl (pk_dh_mk_session_key_impl Resp).

#[local]
Program Instance PK_DH : PK := {
  is_priv_key n kI kR := dh_seed (λ _, corruption kI kR) n;
  confirmation := pk_dh_confirmation;
  mk_key_share := pk_dh_mk_key_share;
  mk_key_share_impl := pk_dh_mk_key_share_impl;
  mk_session_key := pk_dh_mk_session_key;
  mk_session_key_impl := pk_dh_mk_session_key_impl;

}.

Next Obligation.
by move=> t1 t2 /TExp_inj1 [_ ?].
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
move=> rl nI nI' nR nR'.
rewrite /pk_dh_mk_key_share /pk_dh_mk_session_key {rl}.
rewrite !Spec.texpA. move=> /TExp_inj [_ en].
by apply Permutation_length_2.
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
iApply (wp_mknonce (λ _, False)%I (dh_publ (λ _, corruption kI kR))).
iIntros "%n #s_n #p_n #dh token". wp_pures.
wp_bind (tint _). iApply wp_tint.
wp_bind (tgroup _). iApply wp_tgroup.
wp_bind (texp _ _). iApply wp_texp. rewrite Spec.texpA.
wp_pures. iModIntro. iApply "post".
rewrite bi.intuitionistic_intuitionistically.
iFrame. do !iSplit => //. iModIntro. by do!iSplit => //.
Qed.

Next Obligation.
iIntros "%E %rl %n %s %Φ _ post".
rewrite /pk_dh_mk_session_key_impl.
wp_pures. iApply wp_texp. by iApply "post".
Qed.

Definition pk_dh_ctx : iProp := ctx N.

Definition pk_dh_session_meta rl kI kR :=
  @session_key_meta _ _ _ _ N _ rl kI kR.

Definition pk_dh_session_meta_token rl kI kR :=
  @session_key_meta_token _ _ _ _ N _ rl kI kR.

Global Instance pk_dh_session_term_meta rl kI kR :
  TermMeta (pk_dh_session_meta rl kI kR)
           (pk_dh_session_meta_token rl kI kR).
Proof. apply _. Qed.

Lemma pk_dh_alloc E1 E2 E' :
  ↑N ⊆ E1 →
  ↑N ⊆ E2 →
  nown_token session_name E1 -∗
  enc_pred_token E2 ={E'}=∗
  pk_dh_ctx ∗
  nown_token session_name (E1 ∖ ↑N) ∗
  enc_pred_token (E2 ∖ ↑N).
Proof. exact: pk_auth_alloc. Qed.

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

Lemma wp_pk_dh_init c kI kR dq n T E :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  pterm (TKey Enc kI) -∗
  pterm (TKey Enc kR) -∗
  {{{ init_confirm kI kR ∗ ●H{dq|n} T }}}
    pk_dh_init c (TKey Dec kI) (TKey Enc kI) (TKey Enc kR) @ E
  {{{ (okS : option term), RET repr okS;
      ●H{dq|n} T ∗
      if okS is Some kS then
        sterm kS ∗
        □ pk_dh_confirmation Init kI kR kS ∗
        session_weak N Init kI kR kS T ∗
        if in_honest kI kR T then
          □ (pterm kS → ◇ False) ∗
          pk_dh_session_meta_token Init kI kR kS ⊤ ∗
          session_key N kI kR kS
        else True
      else True
  }}}.
Proof.
iIntros "% % #chan_c #ctx #ctx' #p_ekI #p_ekR %Ψ !> confirm post".
rewrite /pk_dh_init; wp_pures.
iApply (wp_pk_auth_init with "chan_c ctx ctx' [] [] [confirm]"); eauto.
iIntros "!> %okS". case: okS => [kS|]; last first.
  by iApply ("post" $! None).
iIntros "(hon & #s_kS & #confirmed & #sess_weak & kSP)".
iApply ("post" $! (Some kS)).
iFrame. iSplitR => //. iSplit => //.
rewrite /in_honest.
case: bool_decide_reflect => [[kIP kRP]|]; eauto.
iDestruct "kSP" as "[token #key]"; eauto.
iFrame. do 2!iSplit => //. iModIntro.
by iApply pk_dh_session_key_elim.
Qed.

Lemma wp_pk_dh_resp c kR dq n T E :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  cryptis_ctx -∗
  ctx N -∗
  pterm (TKey Enc kR) -∗
  {{{ resp_confirm kR ∗ ●H{dq|n} T }}}
    pk_dh_resp c (TKey Dec kR) (TKey Enc kR) @ E
  {{{ (res : option (term * term)), RET repr res;
      ●H{dq|n} T ∗
      if res is Some (pkI, kS) then ∃ kI,
        ⌜pkI = TKey Enc kI⌝ ∗
        pterm pkI ∗
        sterm kS ∗
        □ pk_dh_confirmation Resp kI kR kS ∗
        session_weak N Resp kI kR kS T ∗
        if in_honest kI kR T then
          □ (pterm kS → ◇ False) ∗
          pk_dh_session_meta_token Resp kI kR kS ⊤ ∗
          session_key N kI kR kS
        else True
      else True
  }}}.
Proof.
iIntros "% % #chan_c #ctx #ctx' #p_ekR %Ψ !> confirm post".
rewrite /pk_dh_resp; wp_pures.
iApply (wp_pk_auth_resp with "chan_c ctx ctx' [] [confirm]"); eauto.
iIntros "!> %res". case: res => [[pkI kS]|]; last first.
  by iApply ("post" $! None).
iIntros "(hon & %kI & -> & #p_pkI & #s_kS & #confirmed & #sess_weak & kSP)".
iApply ("post" $! (Some (TKey Enc kI, kS))). iFrame. iExists kI.
do 5!iSplitR => //.
rewrite /in_honest.
case: bool_decide_reflect => // - [kIP kRP].
iDestruct "kSP" as "[token #key]"; eauto.
iFrame. iSplit => //. iModIntro.
by iApply pk_dh_session_key_elim.
Qed.

End PKDH.

Arguments PK_DH {Σ _ _} pk_dh_confirmation.
Arguments pk_dh_ctx {Σ _ _ _} N _.
Arguments pk_dh_session_meta {Σ _ _ _} _ _ _ _ _ {L _ _} _ _ _.
Arguments pk_dh_session_meta_token {Σ _ _ _} _ _ _ _ _ _ _.
Arguments pk_dh_alloc {Σ _ _ _} N _ _ _.
Arguments wp_pk_dh_init {Σ _ _ _} N.
Arguments wp_pk_dh_resp {Σ _ _ _} N.
