From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
(* From iris.algebra Require Import agree auth csum gset gmap excl frac. *)
(* From iris.algebra Require Import max_prefix_list. *)
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

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ}.

Notation iProp := (iProp Σ).

Definition opaque_file (file : term) : iProp :=
  ∃ k_s p_s P_s P_u envelope,
    ⌜file = Spec.of_list [k_s; p_s; P_s; P_u; envelope]⌝
    ∗ minted k_s ∗ minted p_s ∗ public P_s ∗ public P_u ∗ public envelope.

Definition opaque_db (db : gmap term term) : iProp :=
[∗ map] (k : term) ↦ (file : term) ∈ db,
public k ∗ opaque_file file.

Lemma wp_make_file (pw : term) :
{{{ cryptis_ctx ∗ minted pw }}}
Server.make_file pw
{{{ file , RET file ; True }}}.
Proof.
  iIntros "%ϕ [#cryptis #Hmintedpw] post".
  wp_lam.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I) => //.
  iIntros "%k_s %Hnoncek_s #Hmintedk_s #Hprivatek_s #H!eqk_s Htokenk_s".
  wp_pures.
  wp_lam.
  wp_pures.
  wp_apply wp_H'.
  unfold hash_result.
  wp_pures.
  wp_apply wp_texp.
  wp_list.
  wp_apply wp_H.
  wp_apply wp_derive_senc_key.
  wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I) => //.
  iIntros "%p_s %Hnoncep_s #Hmintedp_s #Hprivatep_s #H!eqp_s Htokenp_s".
  wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I) => //.
  iIntros "%p_u %Hnoncep_u #Hmintedp_u #Hprivatep_u #H!eqp_u Htokenp_u".
  wp_pures.
  wp_apply wp_texp. wp_pures.
  wp_apply wp_texp. wp_pures.
  unfold AuthEnc.
  wp_list. wp_pures.
  wp_term_of_list. wp_pures.
  wp_apply wp_senc'. wp_pures.
  wp_list.
  wp_term_of_list.
  by iApply "post".
Qed.

Lemma wp_server_session (db c : term) (alist : gmap term term) :
cryptis_ctx -∗
channel c -∗
AList.is_alist db (repr <$> alist) -∗
opaque_db alist -∗
WP Server.session db c
{{ x , True }}.
Proof.
  rewrite /opaque_db big_sepM_forall.
  iIntros "#Cryptis #Hc Hdb #Hmapcontents".
  wp_lam. wp_pures.
  wp_apply (wp_recv with "Hc").
  iIntros "%m1 #Hpubm1".
  wp_list_of_term m1; wp_pures.
  2: by iModIntro.
  do !rewrite subst_list_match /=.
  wp_list_match => [uid α X_u | _].
  2: wp_pures; by iModIntro.
  intro Hm1eq.
  wp_bind (AList.find _ _).
  iApply (AList.wp_find with "Hdb").
  iIntros "!> Hdb". rewrite lookup_fmap.
  case db_uid: (alist !! uid) => [file|]; wp_pures.
  2: by iModIntro.
  iDestruct ("Hmapcontents" $! uid file with "[//]") as
    "[_ (%k_s & %p_s & %P_s & %P_u & %envelope &
        %e & Hmk_s & Hmp_s & HpP_s & HpP_u & Hpenvelope)]".
  repeat rewrite subst_list_match /=.
  wp_apply wp_list_of_term.
  rewrite e.
  rewrite Spec.of_listK.
  wp_pures.
  rewrite subst_list_match /=.
  wp_list_match => [k_s' p_s' P_s' P_u' envelope' e' | ].
  inversion e'. subst. clear e'.
  2: intro H; wp_pures; by iModIntro.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => False)%I).
  1: iAssumption.
  iIntros "%x_s %Hnoncex_s #Hmintedx_s #Hprivatex_s #H!eqx_s Htokenx_s".
  wp_pures.
  wp_apply wp_texp. wp_pures.
  wp_apply wp_texp. wp_pures.
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
  unfold hash_result.
  wp_list.
  wp_term_of_list.
  wp_pures.
  rewrite public_of_list.
  simpl.
  iDestruct "Hpubm1" as "[Hpubuid [Hpubα [HpubX_u _]]]".
  wp_apply wp_send.
  1: done.
  1: rewrite public_of_list => //.
  do !iSplit => //.
  iApply public_TExp_iff => //.
  admit.
  admit.
  iApply public_TExp_iff.
  intro contra. destruct contra.
  iRight.
  do !iSplit => //.
  by iApply minted_TInt.
  iApply "H!eqx_s". iNext. iModIntro. admit.
  admit.
  wp_pures.
  wp_apply (wp_recv with "Hc").
  iIntros "%m3 #Hm3pub".
  wp_pures.
  wp_list.
  wp_apply wp_prf.
  wp_eq_term Heq; wp_pures.
  2: by iModIntro.
  wp_list.
  wp_pures.
  by iModIntro.
Admitted.

End Opaque.
