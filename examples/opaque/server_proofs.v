From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.

From cryptis.examples Require Import alist.
From cryptis.examples.opaque Require Import impl shared.

From iris.base_logic.lib Require Import invariants.

From cryptis.lib Require Import term_set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Opaque.

Context `{!cryptisGS Σ, !heapGS Σ}.

Notation iProp := (iProp Σ).

Definition opaque_file (file : val) : iProp :=
  ∃ (k_s : nonce) (p_s : nonce) P_s P_u envelope,
    ⌜file = Spec.of_list [TNonce k_s; TNonce p_s; P_s; P_u; envelope]⌝
    ∗ minted k_s ∗ □(public k_s ↔ ▷ □ False) ∗
    □(∀ t' : term, exp_pred_base k_s t' ↔ ▷ □ True) ∗
    □(∀ t' : term, exp_pred_base (TInv k_s) t' ↔ ▷ False) ∗
    public P_s ∗ public envelope ∗
    opaque_public_private_pair p_s P_u.

Definition opaque_db (db : gmap term val) : iProp :=
[∗ map] (k : term) ↦ (file : val) ∈ db,
public k ∗ opaque_file file.

Lemma wp_make_file (pw : term) :
  {{{
    cryptis_ctx
    ∗ minted pw
    ∗ □ (public pw ↔ ▷ □ False)
    ∗ hash_pred (opN.@"rw") (λ _,  False)
    ∗ senc_pred (opN.@"AuthEnc") envelope_pred
  }}} Server.make_file pw {{{ file, RET (repr file); opaque_file file }}}.
Proof.
iIntros "%ϕ (#cryptis & #Hmintedpw & #Hprivpw & #Hhashpred & #Hsencpred) post".
wp_lam.
wp_apply (wp_mk_nonce_freshN ∅ (fun _ => False)%I (fun _ => True)%I
                               (fun t =>  {[(TInv t)]})) => //.
- by iIntros "%_ %contra".
- iIntros "%t".
  rewrite big_sepS_singleton minted_TInv.
  by iModIntro; auto.
iIntros "%k_s _ #Hmintedk_s #Hprivatek_s #Hexpk_s #Hexpk_sV Htokenk_sV".
rewrite big_sepS_singleton.
wp_pures; wp_lam; wp_pures.
wp_apply wp_H'; wp_apply wp_texp; wp_list; wp_apply wp_H.
wp_apply wp_derive_senc_key.
wp_pures.
wp_apply (wp_mk_nonce_freshN ∅ (fun _ => False)%I opaque_secret
                               (fun t =>  {[(TInv t)]})) => //.
- by iIntros "%_ %contra".
- iIntros "%t".
  rewrite big_sepS_singleton minted_TInv.
  by iModIntro; auto.
iIntros "%p_s _ #Hmintedp_s #Hprivatep_s #Hexpp_s #Hexpp_sV Htokenp_sV".
rewrite big_sepS_singleton.
wp_pures.
wp_apply (wp_mk_nonce_freshN {[(TExp g p_s)]} (fun _ => False)%I opaque_secret
                                              (fun t =>  {[(TInv t)]})) => //.
- iIntros "%"; rewrite elem_of_singleton; iIntros "->".
  iApply minted_TExp.
    by intro contra.
  iSplit => //.
  by iApply minted_TInt.
- iIntros "%t".
  rewrite big_sepS_singleton minted_TInv.
  by iModIntro; auto.
iIntros "%p_u %Hfreshp_u #Hmintedp_u #Hprivatep_u #Hexpp_u #Hexpp_uV Htokenp_uV".
rewrite big_sepS_singleton.
assert (p_u ≠ p_s) as Hneq.
  intro contra.
  apply (Hfreshp_u (TExp g p_s)).
    by rewrite elem_of_singleton.
  rewrite contra.
  apply: subterm_TExp_exp; [done | exact: (negb_is_mul_nonce p_s) | exact: STRefl].
wp_pures.
wp_apply wp_texp; wp_pures.
wp_apply wp_texp.
wp_list; wp_term_of_list.
wp_lam; wp_pures.
wp_apply wp_senc'.
wp_list; wp_term_of_list.
iApply "post".
iExists k_s, p_s, (TExp g p_s), (TExp g p_u), _.
do !iSplit => //.
- iApply public_TExp_iff.
    by case.
    by exact: (proj1 (is_trueP _) (negb_is_mul_nonce p_s)).
  do !iSplit => //.
  + by iApply minted_TInt.
  + iApply exp_pred_intro1.
    iApply "Hexpp_s".
    iNext; iModIntro; iPureIntro.
    have Nm : is_true (negb (is_mul p_s)) := negb_is_mul_nonce p_s.
    rewrite (_ : TExp g p_s = TExpN g [TNonce p_s]); last by rewrite /TExpN TMulN1.
    by rewrite exps_TExpN'; [by [] | by case | by [] | exact: (invs_canceled1 Nm)].
  + by iModIntro; iIntros "?"; iApply public_TInt.
- iApply (public_sencIS _ (opN.@"AuthEnc") envelope_pred _) => //.
  1: rewrite minted_senc minted_THash minted_tag.
  1, 2: iApply minted_of_list; do !iSplit => //; iApply minted_TExp.
  1, 3, 5: by intro contra.
  1-3: iSplit => //.
  1: by rewrite minted_THash minted_tag.
  1, 2: by iApply minted_TInt.
  iModIntro.
  iExists p_u, (TExp g p_u), (TExp g p_s).
  iSplit => //.
  iExists p_s.
  do !iSplit => //.
    iPureIntro.
    apply Hfreshp_u.
    by rewrite elem_of_singleton.
  iApply public_TExp_exp_pred;
    first by exact: (proj1 (is_trueP _) (negb_is_mul_nonce p_s)).
    + by iApply public_TInt.
    + done.
    + iApply exp_pred_intro1.
      iApply "Hexpp_s".
      iNext; iModIntro; iPureIntro.
      have Nm : is_true (negb (is_mul p_s)) := negb_is_mul_nonce p_s.
      rewrite (_ : TExp g p_s = TExpN g [TNonce p_s]); last by rewrite /TExpN TMulN1.
      by rewrite exps_TExpN'; [by [] | by case | by [] | exact: (invs_canceled1 Nm)].
    + done.
  iModIntro.
  rewrite public_senc_key.
  iIntros "#Hcompromise".
  iDestruct (public_THashE with "Hhashpred Hcompromise") as "[Hpub | [Hmin contra]]";
      rewrite !public_of_list /=.
    iDestruct "Hprivpw" as "[Hprivpw _]".
    iDestruct "Hpub" as "[Hpubpw _]".
    iDestruct ("Hprivpw" with "Hpubpw") as "contra".
    1, 2: iDestruct "Hprivatep_u" as "[_ Hprivatep_u]";
        iDestruct ("Hprivatep_u" with "contra") as "Hpubp_u";
        iDestruct "Hprivatep_s" as "[_ Hprivatep_s]";
        iDestruct ("Hprivatep_s" with "contra") as "Hpubp_s";
        by do !iSplit => //; do ?iApply public_TExp => //; rewrite public_TInt.
- iExists p_u.
  do !iSplit => //.
  + iPureIntro.
    apply /subtermsP.
    have Nm : is_true (negb (is_mul p_u)) := negb_is_mul_nonce p_u.
    rewrite (_ : TExp g p_u = TExpN g [TNonce p_u]); last by rewrite /TExpN TMulN1.
    rewrite subtermsE //.
    rewrite cancel_invs1 /= [subterms p_u]subterms_nonce //.
    rewrite /g subtermsE /=.
    have p_s_ne2 : TNonce p_s ≠ TInt 0 by move=> E; discriminate E.
    have Hne1 : is_true (negb (is_nonce (TExpN (TInt 0) [TNonce p_u]))).
      rewrite (_ : TExpN (TInt 0) [TNonce p_u] = TExp (TInt 0) p_u); last by rewrite /TExpN TMulN1.
      by apply: is_nonce_TExp => //; exact: (negb_is_mul_nonce p_u).
    have p_s_ne1 : TNonce p_s ≠ TExpN (TInt 0) [TNonce p_u].
      by move=> E; rewrite -E in Hne1; discriminate Hne1.
    set_solver.
  + iApply public_TExp_exp_pred;
      first by exact: (proj1 (is_trueP _) (negb_is_mul_nonce p_u)).
    * by iApply public_TInt.
    * done.
    * iApply exp_pred_intro1.
      iApply "Hexpp_u".
      iNext; iModIntro; iPureIntro.
      have Nm : is_true (negb (is_mul p_u)) := negb_is_mul_nonce p_u.
      rewrite (_ : TExp g p_u = TExpN g [TNonce p_u]); last by rewrite /TExpN TMulN1.
      by rewrite exps_TExpN'; [by [] | by case | by [] | exact: (invs_canceled1 Nm)].
    * done.
Qed.

Lemma wp_server_session (db c : val) (alist : gmap term val) (fresh : gset term) :
{{{ cryptis_ctx
    ∗ hash_pred (opN.@"A_s") A_pred
    ∗ hash_pred (opN.@"SK") (λ _,  False)
    ∗ hash_pred (opN.@"K") (λ _,  False)
    ∗ channel c
    ∗ AList.is_alist db alist
    ∗ opaque_db alist
    ∗ ∀ t : term, ⌜t ∈ fresh⌝ -∗ minted t
  }}}
    Server.session db c
  {{{ x, RET (repr x); SK_result x fresh ∗ AList.is_alist db alist }}}.
Proof.
iIntros "%ϕ".
rewrite /opaque_db big_sepM_forall.
iIntros "(#Cryptis & #HpredA_s & #HpredSK & #HpredK & #Hc & Hdb & #Hmapcontents & #Hfresh) Hhl".
wp_lam; wp_pures.
wp_apply (wp_recv with "Hc"); iIntros "%m1 #Hpubm1".
wp_list_of_term m1; wp_pures; last first.
  by iApply ("Hhl" $! None); iModIntro; do !iSplit.
rewrite !subst_list_match /=.
wp_list_match => [uid α X_u -> | _]; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; do !iSplit.
wp_bind (AList.find _ _); iApply (AList.wp_find with "Hdb"); iIntros "!> Hdb".
case db_uid: (alist !! uid) => [file|]; wp_pures; last first.
  by iApply ("Hhl" $! None); iModIntro; do !iSplit.
iDestruct ("Hmapcontents" $! uid file with "[//]") as
    "[_ (%k_s & %p_s & %P_s & %P_u & %envelope &
         %e & Hmk_s & Hprivk_s & Hexpk_s & Hexpk_sV &
         HpubP_s & Hpenvelope & %p_u & %HP_u & %Hfreshp_u &
         HpubP_u & Hminp_s & ? & Hexpp_s & ? & Hprivp_s & ?)]".
rewrite !subst_list_match /= e.
wp_apply wp_list_of_term.
rewrite Spec.of_listK.
wp_pures.
rewrite subst_list_match /=.
wp_list_match => [k_s' p_s' P_s' P_u' envelope' e' | ]; last first.
  by intro contra.
symmetry in e'; inversion e'; subst; clear e'.
rewrite public_of_list /=.
iDestruct "Hpubm1" as "(? & ? & ? & _)".
wp_apply (wp_mk_nonce_fresh ({[X_u]} ∪ fresh) (fun _ => False)%I
                                              (fun t => opaque_secret t)%I) => //.
  iIntros "%".
  rewrite elem_of_union.
  rewrite elem_of_singleton public_minted.
  iIntros "[-> | %H]".
  - by iApply public_minted.
  - by iApply "Hfresh".
iIntros "%x_s %Hfreshx_s #Hmintedx_s #Hprivatex_s #Hexpx_s #Hexpx_sV _".
wp_pures.
wp_apply wp_texp; wp_pures.
wp_apply wp_texp; wp_pures.
wp_apply wp_ke; wp_list.
wp_apply wp_H; wp_list.
wp_apply wp_prf; wp_list.
wp_apply wp_prf; wp_list.
wp_term_of_list; wp_pures.
set m2 := (Spec.of_list [_; _; _; _]).
wp_apply wp_send => //.
  rewrite public_of_list => //.
  do !iSplit => //.
  - iApply public_TExp_exp_pred => //.
    iApply exp_pred_intro1 => //.
    by iApply "Hexpk_s".
  - iApply public_TExp_iff.
      by case.
      by exact: (proj1 (is_trueP _) (negb_is_mul_nonce x_s)).
    do !iSplit => //.
    + by iApply minted_TInt.
    + iApply exp_pred_intro1.
      iApply "Hexpx_s"; iPureIntro.
      have Nm : is_true (negb (is_mul x_s)) := negb_is_mul_nonce x_s.
      rewrite (_ : TExp g x_s = TExpN g [TNonce x_s]); last by rewrite /TExpN TMulN1.
      by rewrite exps_TExpN'; [by [] | by case | by [] | exact: (invs_canceled1 Nm)].
    + by rewrite public_TInt; auto.
  - iApply public_THashIS => //.
      rewrite minted_of_list /= !minted_THash !minted_tag !minted_of_list /=.
      by do !iSplit => //;
          try (iApply all_minted_TExp; iSplit => //);
          iApply public_minted.
    iNext; iModIntro.
    iExists (TExp g p_u), p_s, X_u, x_s, (hash_result "ssid'" (Spec.of_list [uid; α])).
    do !iSplit => //.
    iExists p_u.
    do !iSplit => //.
wp_pures.
wp_apply (wp_recv with "Hc"); iIntros "%m3 #Hm3pub".
wp_list; wp_apply wp_prf.
wp_eq_term Heq; wp_pures; last first.
  by iApply ("Hhl" $! None); iModIntro; do !iSplit.
wp_list; wp_term_of_list; wp_pures.
iModIntro.
set SK := Spec.of_list _.
iApply ("Hhl" $! (Some SK)).
iSplitR => //.
rewrite /SK_result.
iSplit.
- rewrite /SK_priv public_of_list /=.
  iSplit; iIntros "contra".
  + iDestruct "contra" as "(_ & contra & _)".
    iDestruct (public_THashE with "HpredSK contra") as "[Hpub | [_ contra]]" => //.
    rewrite public_of_list /=.
    iDestruct "Hpub" as "[Hpub _]".
    iDestruct (public_THashE with "HpredK Hpub") as "[Hpub' | [_ contra]]" => //.
    rewrite public_of_list /=.
    iDestruct "Hpub'" as "(contra & _)".
    rewrite TExp2_TExpN.
    have p_s_u: TNonce p_s ≠ TNonce p_u.
      move=> p_u_s; apply: Hfreshp_u; rewrite -p_u_s.
      apply/subtermsP.
      rewrite (_ : TExp g p_s = TExpN g [TNonce p_s]); last by rewrite /TExpN TMulN1.
      have Nm : is_true (negb (is_mul p_s)) := negb_is_mul_nonce p_s.
      rewrite subtermsE //.
      rewrite cancel_invs1 /=.
      by rewrite [subterms p_s]subterms_nonce //; set_solver.
    have p_s_uV : TNonce p_s ≠ TInv p_u.
      move=> contra; have: is_inv (TInv p_u).
        by rewrite (is_inv_TInv (TNonce p_u) (negb_is_mul_nonce p_u)).
      by rewrite -contra; case: (p_s) => //.
    by iApply (public_opaque_secret _ (negb_is_mul_nonce p_s) (negb_is_mul_nonce p_u) p_s_u p_s_uV).
  + do !iSplit => //.
    iApply (public_THashIS with "HpredSK") => //.
    rewrite minted_of_list.
    do !iSplit => //; rewrite minted_THash minted_tag minted_of_list; do !iSplit => //.
      1, 2: rewrite -all_minted_TExp; iSplit => //.
      1-4: by iApply public_minted.
- iSplit.
  + iPureIntro.
    intro contra.
    apply (Hfreshx_s SK).
      by apply elem_of_union_r.
    rewrite /SK.
    apply subterm_of_list.
    set SK' := hash_result "SK" _; exists SK'.
    rewrite !elem_of_cons /SK'.
    split.
      by right; left.
    apply STHash.
    apply subterm_tag.
    apply subterm_of_list.
    set K := hash_result "K"_; exists K.
    rewrite elem_of_cons /K.
    split.
      by left.
    apply STHash.
    apply subterm_tag.
    apply subterm_of_list.
    exists (TExp X_u x_s).
    split.
      rewrite !elem_of_cons.
      by right; left.
    assert (¬ subterm x_s X_u) as Hfreshx_s'. {
      apply Hfreshx_s.
      rewrite elem_of_union elem_of_singleton.
      by left.
    }
    apply subterm_TExp_exp' => //.
    move=> contra'.
    destruct Hfreshx_s'.
    rewrite subterm_exp.
    right. right.
    exists (TInv x_s).
    split => //.
    apply STInv => //; by destruct x_s.
  + rewrite minted_of_list /=
      minted_THash minted_tag minted_of_list /=
      !minted_THash !minted_tag !minted_of_list /=
      -!all_minted_TExp /=.
    do !iSplit => //; iApply public_minted => //.
    by iApply public_TInt.
Qed.

End Opaque.
