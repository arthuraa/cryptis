From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics role dh.
From cryptis Require Import pk_auth.
From cryptis Require Import session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PKDH.

Context `{heap : !heapGS Σ, cryptis : !cryptisGS Σ, sess : !sessionGS Σ}.
Notation iProp := (iProp Σ).
Implicit Types rl : role.
Implicit Types t kI kR nI nR sI sR : term.

Definition pk_dh_mk_key_share n := TExp (TInt 0) n.

Definition pk_dh_mk_key_share_impl : val := λ: <>,
  let: "n" := mknonce #() in
  ("n", texp (tint #0) "n").

Definition pk_dh_mk_session_key rl n s : term :=
  TExp s n.

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
by move=> t1 t2 /TExp_injr.
Qed.

Next Obligation.
move=> n; rewrite minted_TExp /= minted_TInt. apply: anti_symm.
- by iIntros "(_ & ?)".
- by eauto.
Qed.

Next Obligation.
iIntros "%nI %kI %kR #s_nI #dh".
rewrite /pk_dh_mk_key_share /secret_of. iModIntro. iSplit.
- iIntros "#p_sI".
  by iPoseProof (dh_seed_elim1 with "dh p_sI") as "H"; eauto.
- iIntros "#fail". iApply dh_public_TExp; eauto.
Qed.

Next Obligation.
move=> rl1 rl2 nI nI' nR nR'.
rewrite /pk_dh_mk_key_share /pk_dh_mk_session_key {rl1 rl2} TExp_TExpN.
move=> eX.
move/(f_equal base): (eX); rewrite !base_TExpN /= => base_nR'.
have en: [nI; nR] ≡ₚ exps nR' ++ [nI'].
  by rewrite -exps_TExpN -eX exps_TExpN.
have := Permutation_length en; rewrite app_length /= => ?.
have lenR' : length (exps nR') = 1 by lia.
case eenR': (exps nR') => [|x [|??]] //= in lenR' en *.
have [[-> ->]|[-> ->]] := Permutation_length_2 en.
- right. split => //. apply: base_exps_inj.
  + by rewrite base_TExpN.
  + by rewrite exps_TExpN eenR'.
- left. split => //. apply: base_exps_inj.
  + by rewrite base_TExpN.
  + by rewrite exps_TExpN eenR'.
Qed.

Next Obligation.
move=> nI nR; rewrite /pk_dh_mk_key_share /pk_dh_mk_session_key.
by rewrite !TExp_TExpN TExpC2.
Qed.

Next Obligation.
iIntros "%rl %t1 %t2 #s_t1 #s_t2".
by rewrite /pk_dh_mk_session_key; iApply minted_TExp; iSplit.
Qed.

Next Obligation.
iIntros "%kI %kR %Φ #? post". rewrite /pk_dh_mk_key_share_impl.
wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce (λ _, False)%I (dh_publ (λ _, corruption kI kR))) => //.
iIntros "%n _ #s_n #p_n #dh token". wp_pures.
wp_bind (tint _). iApply wp_tint.
wp_bind (texp _ _). iApply wp_texp.
wp_pures. iModIntro. iApply "post".
rewrite bi.intuitionistic_intuitionistically.
iFrame. do !iSplit => //. iModIntro. by do!iSplit => //.
Qed.

Next Obligation.
iIntros "%rl %n %s %Φ _ post".
rewrite /pk_dh_mk_session_key_impl.
wp_pures. iApply wp_texp. by iApply "post".
Qed.

Definition pk_dh_ctx : iProp := pk_auth_ctx N.

Definition pk_dh_session_meta kI kR :=
  @session_key_meta _ _ _ _ N _ kI kR.

Definition pk_dh_session_meta_token kI kR :=
  @session_key_meta_token _ _ _ _ N _ kI kR.

Definition pk_dh_session_weak rl kI kR kS ph :=
  session_weak N rl kI kR kS ph.

Definition pk_dh_session_key kI kR kS ph:=
  session_key N kI kR kS ph.

Lemma pk_dh_alloc E1 E2 E' :
  ↑N ⊆ E1 →
  ↑N ⊆ E2 →
  session_token E1 -∗
  enc_pred_token E2 ={E'}=∗
  pk_dh_ctx ∗
  session_token (E1 ∖ ↑N) ∗
  enc_pred_token (E2 ∖ ↑N).
Proof. exact: pk_auth_alloc. Qed.

Lemma pk_dh_session_key_elim kI kR kS n :
  pk_dh_session_key kI kR kS n -∗
  public kS →
  ◇ False.
Proof.
iIntros "(%nI & %nR & -> & _ & _ & #priv_nI & #priv_nR & _)".
rewrite /= /pk_dh_mk_session_key /pk_dh_mk_key_share TExp_TExpN.
iIntros "#p_kS".
iDestruct (dh_seed_elim2 with "priv_nI p_kS") as "[>p_sI >contra]"; eauto.
by iDestruct (dh_seed_elim0 with "priv_nR contra") as ">[]".
Qed.

Lemma wp_pk_dh_init c kI kR dq n T :
  channel c -∗
  cryptis_ctx -∗
  pk_auth_ctx N -∗
  public (TKey Enc kI) -∗
  public (TKey Enc kR) -∗
  honest n T -∗
  {{{ init_confirm kI kR ∗ ●Ph{dq} n }}}
    pk_dh_init c (TKey Dec kI) (TKey Enc kI) (TKey Enc kR)
  {{{ (okS : option term), RET repr okS;
      ●Ph{dq} n ∗
      if okS is Some kS then
        minted kS ∗
        □ pk_dh_confirmation Init kI kR kS ∗
        pk_dh_session_weak Init kI kR kS n ∗
        if in_honest kI kR T then
          □ (public kS → ◇ False) ∗
          pk_dh_session_meta_token kI kR kS (↑N.@"init") ∗
          pk_dh_session_key kI kR kS n
        else True
      else True
  }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_ekI #p_ekR #hon %Ψ !> confirm post".
rewrite /pk_dh_init; wp_pures.
iApply (wp_pk_auth_init with "chan_c ctx ctx' [] [] [] [confirm]"); eauto.
iIntros "!> %okS". case: okS => [kS|]; last first.
  by iApply ("post" $! None).
iIntros "(phase & #s_kS & #confirmed & #sess_weak & kSP)".
iApply ("post" $! (Some kS)).
iFrame. iSplitR => //. iSplit => //.
rewrite /in_honest.
case: bool_decide_reflect => [[kIP kRP]|]; eauto.
iDestruct "kSP" as "[token #key]"; eauto.
iFrame. do 2!iSplit => //. iModIntro.
by iApply pk_dh_session_key_elim.
Qed.

Lemma wp_pk_dh_resp c kR dq n T :
  channel c -∗
  cryptis_ctx -∗
  pk_auth_ctx N -∗
  public (TKey Enc kR) -∗
  honest n T -∗
  {{{ resp_confirm kR ∗ ●Ph{dq} n }}}
    pk_dh_resp c (TKey Dec kR) (TKey Enc kR)
  {{{ (res : option (term * term)), RET repr res;
      ●Ph{dq} n ∗
      if res is Some (pkI, kS) then ∃ kI,
        ⌜pkI = TKey Enc kI⌝ ∗
        public pkI ∗
        minted kS ∗
        □ pk_dh_confirmation Resp kI kR kS ∗
        pk_dh_session_weak Resp kI kR kS n ∗
        if in_honest kI kR T then
          □ (public kS → ◇ False) ∗
          pk_dh_session_meta_token kI kR kS (↑N.@"resp") ∗
          pk_dh_session_key kI kR kS n
        else True
      else True
  }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_ekR #hon %Ψ !> confirm post".
rewrite /pk_dh_resp; wp_pures.
iApply (wp_pk_auth_resp with "chan_c ctx ctx' [] [] [confirm]"); eauto.
iIntros "!> %res". case: res => [[pkI kS]|]; last first.
  by iApply ("post" $! None).
iIntros "(phase & %kI & -> & #p_pkI & #s_kS & #confirmed & #sess_weak & kSP)".
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
Arguments pk_dh_session_meta {Σ _ _ _} _ _ _ _ {L _ _} _ _ _.
Arguments pk_dh_session_meta_token {Σ _ _ _} _ _ _ _ _ _.
Arguments pk_dh_alloc {Σ _ _ _} N _ _ _.
Arguments wp_pk_dh_init {Σ _ _ _} N.
Arguments wp_pk_dh_resp {Σ _ _ _} N.
