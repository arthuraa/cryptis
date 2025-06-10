From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics role.
From cryptis Require Import pk_auth.
From cryptis Require Import session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSL.

Context `{heap : !heapGS Σ, cryptis : !cryptisGS Σ, sess : !sessionGS Σ}.
Notation iProp := (iProp Σ).
Implicit Types t kI kR nI nR : term.

Definition nsl_mk_key_share_impl : val := λ: <>,
    let: "n" := mknonce #() in ("n", "n").

Definition nsl_mk_session_key rl n1 n2 : term :=
  if rl is Init then TPair n1 n2 else TPair n2 n1.

Definition nsl_mk_session_key_impl rl : val :=
  if rl is Init then λ: "nI" "nR", tuple "nI" "nR"
  else λ: "nR" "nI", tuple "nI" "nR".

Variable N : namespace.

Variable nsl_confirmation : role → term → term → term → iProp.

Definition nsl_init : val := λ: "c",
  pk_auth_init N "c" nsl_mk_key_share_impl (nsl_mk_session_key_impl Init).

Definition nsl_resp : val := λ: "c",
  pk_auth_resp N "c" nsl_mk_key_share_impl (nsl_mk_session_key_impl Resp).

#[local]
Program Instance PK_NSL : PK := {
  confirmation := nsl_confirmation;
  is_priv_key := secret_of;

  mk_key_share n := n;
  mk_key_share_impl := nsl_mk_key_share_impl;
  mk_session_key := nsl_mk_session_key;
  mk_session_key_impl := nsl_mk_session_key_impl;

}.

Next Obligation. by eauto. Qed.

Next Obligation. by eauto. Qed.

Next Obligation.
case=> [] [] nI nI' nR nR' [] -> ->; eauto.
Qed.

Next Obligation. by case; eauto. Qed.

Next Obligation.
by case=> t1 t2; iIntros "#s1 #s2"; rewrite minted_TPair; iSplit.
Qed.

Next Obligation.
iIntros "%kI %kR %Φ #? post". rewrite /nsl_mk_key_share_impl.
wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce (λ _, corruption kI kR) (λ _, False)%I) => //.
iIntros "%n % #s_n #p_n _ token". wp_pures. iModIntro.
iApply "post". rewrite bi.intuitionistic_intuitionistically. by eauto.
Qed.

Next Obligation.
iIntros "%rl %n1 %n2 %Φ _ post".
case: rl; rewrite /nsl_mk_session_key_impl /=; wp_pures;
iApply wp_tuple; by iApply "post".
Qed.

Lemma wp_nsl_init c kI kR :
  channel c -∗
  cryptis_ctx -∗
  pk_auth_ctx N -∗
  public (TKey Seal kI) -∗
  public (TKey Seal kR) -∗
  {{{ init_confirm kI kR }}}
    nsl_init c kI (TKey Seal kR)
  {{{ (okS : option term), RET repr okS;
      if okS is Some kS then
        minted kS ∗
        □ nsl_confirmation Init kI kR kS ∗
        session_weak N Init kI kR kS ∗
        (corruption kI kR ∨
          session_key_meta_token N kI kR kS (↑N.@"init") ∗
          session_key N kI kR kS)
      else True
  }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_ekI #p_ekR %Ψ !> confirm post".
rewrite /nsl_init; wp_pures.
iApply (wp_pk_auth_init with "chan_c ctx ctx' [] [] [confirm]"); eauto.
Qed.

Lemma wp_nsl_resp c kR :
  channel c -∗
  cryptis_ctx -∗
  pk_auth_ctx N -∗
  public (TKey Seal kR) -∗
  {{{ resp_confirm kR }}}
    nsl_resp c kR
  {{{ (res : option (term * term)), RET repr res;
      if res is Some (pkI, kS) then ∃ kI,
        ⌜pkI = TKey Seal kI⌝ ∗
        public pkI ∗
        minted kS ∗
        □ confirmation Resp kI kR kS ∗
        session_weak N Resp kI kR kS ∗
        (corruption kI kR ∨
          session_key_meta_token N kI kR kS (↑N.@"resp") ∗
          session_key N kI kR kS)
      else True
  }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_ekR %Ψ !> confirm post".
rewrite /nsl_resp; wp_pures.
iApply (wp_pk_auth_resp with "chan_c ctx ctx' [] [confirm]"); eauto.
Qed.

End NSL.
