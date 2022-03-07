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

Program Instance PK_DH : PK := {
  is_priv_key n kI kR := (
    □ (pterm n ↔ ▷ False) ∧
    □ (∀ s, dh_pred n s ↔ ▷ corruption kI kR)
  )%I;

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
iIntros "%nI %kI %kR #s_nI [#p_nI #dh]".
rewrite /pk_dh_mk_key_share /secret_of pterm_TExp1 sterm_TInt.
iModIntro. iSplit.
- iIntros "(_ & _ & #[contra|p_sI])".
  + iDestruct ("p_nI" with "contra") as ">[]".
  + iApply "dh". by eauto.
- iIntros "#fail". do !iSplit => //. iRight. by iApply "dh".
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
iApply (wp_mknonce _ (λ _, False)%I (λ _, corruption kI kR)).
iIntros "%n #s_n #p_n #dh token". wp_pures.
wp_bind (tint _). iApply wp_tint.
wp_bind (tgroup _). iApply wp_tgroup.
wp_bind (texp _ _). iApply wp_texp. rewrite Spec.texpA.
wp_pures. iModIntro. iApply "post".
rewrite bi.intuitionistic_intuitionistically.
iFrame. iSplit => //. iSplit => //. iModIntro.
iIntros "%t". iSpecialize ("dh" $! t).
by rewrite bi.intuitionistic_intuitionistically.
Qed.

Next Obligation.
iIntros "%E %rl %n %s %Φ _ post".
rewrite /pk_dh_mk_session_key_impl.
wp_pures. iApply wp_texp. by iApply "post".
Qed.

End PKDH.
