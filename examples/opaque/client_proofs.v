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
minted pw -∗
WP Client.session uid c pw
{{ x , True }}.
Proof.
  iIntros "#Cryptis #Hc #pubuid #mintedpw".
  wp_lam. wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I) => //.
  iIntros "%x_u %Hnoncex_u #Hmintedx_u #Hprivatex_u #H!eqx_u Htokenx_u".
  wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I) => //.
  iIntros "%r %Hnoncer #Hmintedr #Hprivater #H!eqr Htokenr".
  wp_pures.
  wp_apply wp_H' => //.
  iIntros "_".
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
  iApply "H!eqr".
  iNext. iModIntro.
  admit.
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
  wp_apply wp_H => //.
  iIntros "_".
  wp_apply wp_derive_senc_key.
  set k := SEncKey _.
  wp_pures.
  unfold AuthDec. wp_pures.
  (* wp_apply (wp_sdec $! k (opN.@"AuthEnc") (term_of_list envelope)). *)
Admitted.

End Opaque.
