From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics role.
From cryptis.examples.pk_auth Require Import pk_auth.
From cryptis Require Import session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSL.

Context `{heap : !heapGS Σ, cryptis : !cryptisGS Σ, sess : !sessionGS Σ}.
Notation iProp := (iProp Σ).
Implicit Types t nI nR : term.
Implicit Types skI skR : aenc_key.

Definition nsl_mk_key_share_impl : val := λ: <>,
    let: "n" := mk_nonce #() in ("n", "n").

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
iIntros "%skI %skR %Φ #? post". rewrite /nsl_mk_key_share_impl.
wp_pures. wp_bind (mk_nonce _).
iApply (wp_mk_nonce (λ _, corruption skI skR) (λ _, False)%I) => //.
iIntros "%n % #s_n #p_n _ token". wp_pures. iModIntro.
iApply "post". rewrite bi.intuitionistic_intuitionistically. by eauto.
Qed.

Next Obligation.
iIntros "%rl %n1 %n2 %Φ _ post".
case: rl; rewrite /nsl_mk_session_key_impl /=; wp_pures;
iApply wp_tuple; by iApply "post".
Qed.

Lemma wp_nsl_init c skI skR :
  channel c -∗
  cryptis_ctx -∗
  pk_auth_ctx N -∗
  minted skI -∗
  minted skR -∗
  {{{ init_confirm skI skR }}}
    nsl_init c skI (Spec.pkey skR)
  {{{ (okS : option term), RET repr okS;
      if okS is Some kS then
        minted kS ∗
        □ nsl_confirmation Init skI skR kS ∗
        session_weak N Init skI skR kS ∗
        (corruption skI skR ∨
          session_key_meta_token N skI skR kS (↑N.@"init") ∗
          session_key N skI skR kS)
      else True
  }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_ekI #p_ekR %Ψ !> confirm post".
rewrite /nsl_init; wp_pures.
iApply (wp_pk_auth_init with "chan_c ctx ctx' [] [] [confirm]"); eauto.
Qed.

Lemma wp_nsl_resp c skR :
  channel c -∗
  cryptis_ctx -∗
  pk_auth_ctx N -∗
  minted skR -∗
  {{{ resp_confirm skR }}}
    nsl_resp c skR
  {{{ (res : option (term * term)), RET repr res;
      if res is Some (pkI, kS) then ∃ skI,
        ⌜pkI = Spec.pkey skI⌝ ∗
        minted skI ∗
        minted kS ∗
        □ confirmation Resp skI skR kS ∗
        session_weak N Resp skI skR kS ∗
        (corruption skI skR ∨
          session_key_meta_token N skI skR kS (↑N.@"resp") ∗
          session_key N skI skR kS)
      else True
  }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_ekR %Ψ !> confirm post".
rewrite /nsl_resp; wp_pures.
iApply (wp_pk_auth_resp with "chan_c ctx ctx' [] [confirm]"); eauto.
Qed.

End NSL.
