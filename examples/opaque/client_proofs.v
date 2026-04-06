From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.

From cryptis.examples Require Import alist.
From cryptis.examples.opaque Require Import impl shared.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Opaque.

Context `{!cryptisGS Σ, !heapGS Σ}.
Notation iProp := (iProp Σ).

Lemma wp_client_session (uid pw : term) (c : val):
{{{ cryptis_ctx
      ∗ hash_pred (opN.@"A_u") A_pred
      ∗ hash_pred (opN.@"A_s") A_pred
      ∗ hash_pred (opN.@"SK") (λ _,  False)
      ∗ hash_pred (opN.@"K") (λ _,  False)
      ∗ hash_pred (opN.@"α") (λ _,  True)
      ∗ senc_pred (opN.@"AuthEnc") envelope_pred
      ∗ channel c
      ∗ public uid
      ∗ minted uid
      ∗ minted pw }}}
Client.session uid c pw
{{{ x , RET (repr x) ; SK_priv x }}}.
Proof.
  iIntros "%ϕ (#Cryptis & #HpredA_u & #HpredA_s & #HpredSK & #HpredK & #Hpredα & #SpredAuth & #Hc & #pubuid & #minteduid & #mintedpw) Hhl".
  wp_lam. wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun t => opaque_secret t)%I) => //.
  iIntros "%x_u %Hnoncex_u #Hmintedx_u #Hprivatex_u #Hexpx_u #? #Hexpx_uV Htokenx_u".
  wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => True)%I) => //.
  iIntros "%r %Hnoncer #Hmintedr #Hprivater #Heqr #HsrV #HeqrV Htokenr".
  wp_pures.
  wp_apply wp_H'.
  wp_apply wp_texp.
  wp_pures.
  wp_apply wp_texp.
  wp_list.
  wp_term_of_list.
  wp_pures.
  set m1 := Spec.of_list _.
  wp_apply wp_send => //.
  do !rewrite public_of_list /=.
  do !iSplit => //.
  iApply public_TExp_iff.
  by intro contra.
  do !iSplit => //.
  by rewrite minted_THash minted_tag.
  iApply exp_pred_intro1.
  by iApply "Heqr".
  iModIntro; iIntros "#p".
  iApply (public_THashIS with "Hpredα") => //.
  iApply public_TExp_iff; auto.
  do !iSplit => //.
  by iApply minted_TInt.
  iApply exp_pred_intro1.
  by iApply "Hexpx_u"; iPureIntro; rewrite exps_TExpN.
  by rewrite public_TInt; auto.
  wp_pures.
  wp_apply wp_recv => //.
  iIntros "%m2 #pubm2".
  iAssert (minted m2) as "minm2".
  by iApply public_minted.
  iClear "pubm2".
  wp_list_of_term m2; wp_pures => //.
  wp_list_match => [β X_s envelope A_s -> | _].
  1, 2: wp_pures.
  2, 3: by iApply ("Hhl" $! None).
  wp_apply wp_hl_inv_term.
  wp_apply wp_texp.
  wp_list.
  wp_apply wp_H.
  wp_apply wp_derive_senc_key.
  set k := SEncKey _.
  wp_pures.
  wp_lam.
  wp_pures.
  wp_apply wp_sdec'.
  rewrite minted_of_list => /=.
  iSplit.
  2: iIntros "_"; wp_pures; by iApply ("Hhl" $! None).
  iDestruct "minm2" as "[_ [minX_s [minenv _]]]".
  iIntros "%clear -> _".
  rewrite minted_TSeal.
  iDestruct "minenv" as "[mink minclear]".
  rewrite minted_tag.
  wp_list_of_term clear.
  2: wp_pures; by iApply ("Hhl" $! None).
  wp_list_match => [p_u P_u P_s -> | _].
  2: wp_pures; by iApply ("Hhl" $! None).
  wp_apply wp_ke => /=.
  wp_list.
  wp_apply wp_H => /=.
  wp_list.
  wp_apply wp_prf => /=.
  wp_list.
  wp_apply wp_prf.
  rewrite minted_of_list => /=.
  iDestruct "minclear" as "[minp_u [minP_u [minP_s _]]]".
  wp_eq_term eq_A_s => /= //.
  wp_list.
  wp_apply wp_prf.
  wp_pures.
  wp_apply wp_send => //.
  iApply public_THashIS; eauto.
  rewrite !minted_of_list /=.
  do !iSplit => //.
  rewrite minted_THash minted_tag minted_of_list.
  do !iSplit => //; iApply all_minted_TExp; iSplit => //.
  rewrite minted_THash minted_tag minted_of_list /=.
  do !iSplit => //.
  rewrite [minted (TExp _ r)]minted_TExp.
  iSplit => //.
  by rewrite minted_THash minted_tag.
  by intro contra.
  3: by wp_pures; iApply ("Hhl" $! None).
  iNext. iModIntro.
  iExists P_s, p_u, X_s, x_u, (hash_result "ssid'" (Spec.of_list [uid; TExp (hash_result "α" pw) r])).
  do !iSplit => //.
  unfold opaque_public_private_pair.
  admit.
  wp_list.
  wp_pures.
  set SK := hash_result _ _.
  iApply ("Hhl" $! (Some SK)).
  iModIntro.
  rewrite /SK_priv /SK.
  iSplit; iIntros "contra".
  iDestruct (public_THashE with "HpredSK contra") as "[contra | [_ contra]]" => //.
  rewrite public_of_list.
  iDestruct "contra" as "[contra _]".
  iDestruct (public_THashE with "HpredK contra") as "[contra | [_ contra]]" => //.
  rewrite public_of_list.
  iDestruct "contra" as "(contra & _ & _)".
  admit.
  iApply (public_THashIS with "HpredSK") => //.
  rewrite minted_of_list.
  do !iSplit => //; rewrite minted_THash minted_tag minted_of_list; do !iSplit => //.
  1: rewrite -[minted (TExp P_s p_u)]all_minted_TExp.
  2: rewrite -all_minted_TExp.
  1, 2: iSplit => //.
  rewrite -[minted (TExp _ r)] all_minted_TExp minted_THash minted_tag.
  by iSplit => //.
Admitted.

End Opaque.
