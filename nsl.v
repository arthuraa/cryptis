From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics role nown.
From cryptis Require Import pk_auth.
From cryptis Require Import session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSL.

Context `{heap : !heapGS Σ, cryptis : !cryptisG Σ, sess : !session.sessionG Σ}.
Notation iProp := (iProp Σ).
Implicit Types t kI kR nI nR : term.

Definition nsl_mk_session_key rl n1 n2 : term :=
  if rl is Init then n1 else n2.

Definition nsl_mk_session_key_impl rl : val :=
  if rl is Init then λ: "nI" <>, "nI"
  else λ: <> "nI", "nI".

Variable N : namespace.

Program Instance PK_NSL : PK := {
  is_priv_key := secret_of;

  mk_key_share n := n;
  mk_key_share_impl := λ: <>,
    let: "n" := mknonce #() in ("n", "n");
  mk_session_key := nsl_mk_session_key;
  mk_session_key_impl := nsl_mk_session_key_impl;

}.

Next Obligation. by eauto. Qed.

Next Obligation. by eauto. Qed.

Next Obligation. by eauto. Qed.

Next Obligation. by case; eauto. Qed.

Next Obligation.
iIntros "%E %kI %kR %Φ _ post". wp_pures.
wp_bind (mknonce _).
iApply (wp_mknonce _ (λ _, corruption kI kR) (λ _, False)%I).
iIntros "%n #s_n #p_n _ token". wp_pures. iModIntro.
iApply "post". rewrite bi.intuitionistic_intuitionistically. by eauto.
Qed.

Next Obligation.
iIntros "%E %rl %n1 %n2 %Φ _ post".
case: rl; rewrite /nsl_mk_session_key_impl /=; wp_pures;
iModIntro; by iApply "post".
Qed.

End NSL.
