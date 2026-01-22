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

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ}.
Notation iProp := (iProp Σ).


Lemma wp_hl_inv E r (Ψ: val -> iProp) :
Ψ (TInv r) ⊢
WP hl_inv r @ E {{ Ψ }}.
Proof.  Admitted.

Lemma wp_client_session (uid c pw : term):
cryptis_ctx -∗
channel c -∗
public uid -∗
minted uid -∗
minted pw -∗
WP Client.session uid c pw
{{ x , True }}.
Proof.
  iIntros "#Cryptis #Hc #pubuid #minteduid #mintedpw".
  wp_lam. wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I) => //.
  iIntros "%x_u %Hnoncex_u #Hmintedx_u #Hprivatex_u #H!eqx_u Htokenx_u".
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
  iApply public_TExp.
  by iApply public_g.
  admit.
  wp_pures.
  wp_apply wp_recv => //.
  iIntros "%m2 #pubm2".
  wp_list_of_term m2; wp_pures => //.
  wp_list_match => [β X_s envelope A_s | _].
  2: by wp_pures.
  intro Hm2eq.
  (* the start of the curse *)
  wp_pures.
  wp_apply wp_hl_inv.
  (* the end of the curse *)
  wp_apply wp_texp.
  wp_list.
  wp_apply wp_H.
  wp_apply wp_derive_senc_key.
  set k := SEncKey _.
  wp_pures.
  unfold AuthDec. wp_pures.
  do !rewrite subst_list_match /=.
  wp_apply wp_sdec'.
  iSplit.
  2: iIntros "_"; by wp_pures.
  iIntros "%clear %henvelope %henvelopedec".
  wp_pures.
  wp_list_of_term clear_list.
  2: by wp_pures.
  wp_list_match => [p_u P_u P_s | _].
  2: by wp_pures.
  iIntros "%Hclearlist".
  wp_apply wp_ke.
  wp_pures.
  wp_list.
  wp_apply wp_H.
  wp_pures.
  unfold hash_result.
  wp_list.
  wp_apply wp_prf.
  wp_pures.
  wp_list.
  wp_apply wp_prf.
  wp_eq_term eq_A_s; wp_pures => //.
  wp_list.
  wp_apply wp_prf.
  wp_pures.
  unfold hash_result.
  wp_pures.
  wp_apply wp_send => //.
  iApply public_THash.
  (* start *)
  iLeft.
  iApply public_tag.

  iApply public_of_list.
  do !iSplit => //.
  iApply public_THash.
  iRight.
  iSplit.
  iApply minted_tag.
  iApply minted_of_list.
  do !iSplit => //; iApply minted_TExp.
  admit.
  admit.
  admit.
  iSplit => //.
  admit.
  admit.
  iApply public_THash.
  iRight.
  iSplit.
  iApply minted_tag.
  iApply minted_of_list.
  do !iSplit => //.
  iApply minted_TExp.
  by intro contra.
  iSplit => //.
  iApply minted_THash.
  by iApply minted_tag.
  admit.
(* end *)

  wp_pures.
  wp_list.
  by wp_pures.
Admitted.

End Opaque.
