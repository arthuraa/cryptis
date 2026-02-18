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
      ∗ hash_pred (opN.@"A_u") (λ _,  True)
      ∗ channel c
      ∗ public uid
      ∗ minted uid
      ∗ minted pw }}}
Client.session uid c pw
{{{ x , RET x ; True }}}.
Proof.
  iIntros "%ϕ [#Cryptis [#Hpred [#Hc [#pubuid [#minteduid #mintedpw]]]]] Hhl".
  wp_lam. wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => True)%I) => //.
  iIntros "%x_u %Hnoncex_u #Hmintedx_u #Hprivatex_u #Heqx_u Htokenx_u".
  wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => True)%I) => //.
  iIntros "%r %Hnoncer #Hmintedr #Hprivater #Heqr Htokenr".
  wp_pures.
  wp_apply wp_H'.
  wp_apply wp_texp.
  wp_pures.
  wp_apply wp_texp.
  wp_pures.
  wp_list.
  wp_term_of_list.
  wp_pures.
  do !rewrite subst_list_match /=.
  wp_apply wp_send => //.
  do !rewrite public_of_list /=.
  do !iSplit => //.
  iApply public_TExp_iff.
  intro contra => //.
  iRight.
  do !iSplit => //.
  iApply minted_THash.
  by iApply minted_tag.
  iApply "Heqr".
  iNext. by iModIntro.
  iApply public_TExp_iff.
  by intro contra.
  iRight.
  do !iSplit => //.
  by iApply minted_TInt.
  iApply "Heqx_u".
  iNext. by iModIntro.
  wp_pures.
  wp_apply wp_recv => //.
  iIntros "%m2 #pubm2".
  iAssert (minted m2 ) as "minm2".
  by iApply public_minted.
  iClear "pubm2".
  wp_list_of_term m2; wp_pures => //.
  wp_list_match => [β X_s envelope A_s -> | _].
  2: wp_pures.
  2, 3: by iApply "Hhl".
  wp_pures.
  wp_apply wp_hl_inv_term.
  wp_apply wp_texp.
  wp_list.
  wp_apply wp_H.
  wp_apply wp_derive_senc_key.
  set k := SEncKey _.
  wp_pures.
  do !rewrite subst_list_match /=.
  wp_lam.
  wp_pures.
  wp_apply wp_sdec'.
  rewrite minted_of_list => /=.
  iSplit.
  2: iIntros "_"; wp_pures; by iApply "Hhl".
  iDestruct "minm2" as "[_ [minX_s [minenv _]]]".
  iIntros "%clear -> _".
  rewrite minted_TSeal.
  iDestruct "minenv" as "[mink minclear]".
  rewrite minted_tag.
  wp_pures.
  wp_list_of_term clear.
  2: wp_pures; by iApply "Hhl".
  wp_list_match => [p_u P_u P_s -> | _].
  2: wp_pures; by iApply "Hhl".
  wp_apply wp_ke => /=.
  wp_list.
  wp_apply wp_H => /=.
  wp_list.
  wp_apply wp_prf => /=.
  wp_list.
  wp_apply wp_prf.
  wp_eq_term eq_A_s => /= //.
  wp_list.
  wp_apply wp_prf.
  wp_pures.
  wp_apply wp_send => //.
  iApply public_THashIS; eauto.
  rewrite !minted_of_list /=.
  iDestruct "minclear" as "[minp_u [minP_u [minP_s _]]]".
  do !iSplit => //.
  rewrite minted_THash minted_tag minted_of_list.
  do !iSplit => //; iApply all_minted_TExp; iSplit => //.
  rewrite minted_THash minted_tag minted_of_list /=.
  do !iSplit => //.
  rewrite minted_TExp.
  iSplit => //.
  by rewrite minted_THash minted_tag.
  by intro contra.
  2: wp_pures; by iApply "Hhl".
  wp_pures.
  wp_list.
  wp_pures.
  by iApply "Hhl".
Qed.

End Opaque.
