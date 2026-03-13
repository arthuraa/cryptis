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
  ∃ k_s p_s P_s P_u envelope,
    ⌜file = Spec.of_list [k_s; p_s; P_s; P_u; envelope]⌝
    ∗ minted k_s ∗
    □(∀ t' : term, exp_pred_base k_s t' ↔ ▷ □ True) ∗
    □(∀ t' : term, exp_pred_base (TInv k_s) t' ↔ ▷ False) ∗
    minted p_s ∗ public P_s ∗ public P_u ∗ public envelope.

Definition opaque_db (db : gmap term val) : iProp :=
[∗ map] (k : term) ↦ (file : val) ∈ db,
public k ∗ opaque_file file.

Lemma public_THashE N φ t :
  hash_pred N φ -∗
  public (THash (Spec.tag (Tag N) t)) -∗
  public t ∨ minted t ∗ ▷ □ φ t.
Proof.
  iIntros "#Hpred #Hpub".
  rewrite public_THash.
  iDestruct "Hpub" as "[Hpub | [Hmint Hwfhash]]".
  rewrite public_tag.
  by iLeft.
  rewrite minted_tag.
  iRight.
  iSplit => //.
  iDestruct (wf_hash_elim N t φ with "Hwfhash Hpred") as "H".
  by iNext.
Qed.

Lemma wp_make_file (pw : term) (Φ : senc_key → term → iProp) :
{{{ cryptis_ctx
      ∗ minted pw
      ∗ □ (public pw ↔ ▷ □ False)
      ∗ hash_pred (opN.@"rw") (λ _,  False)
      ∗ senc_pred (opN.@"AuthEnc") Φ
      ∗ □ ∀ s t, Φ s t }}}
Server.make_file pw
{{{ file , RET (repr file) ; opaque_file file }}}.
Proof.
  iIntros "%ϕ [#cryptis [#Hmintedpw [#Hprivpw [#Hhashpred [#Hsencpred #Henc]]]]] post".
  wp_lam.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => True)%I) => //.
  iIntros "%k_s %Hnoncek_s #Hmintedk_s #Hprivatek_s #Heqk_s #Heqk_sV Htokenk_s".
  wp_pures.
  wp_lam.
  wp_pures.
  wp_apply wp_H'.
  wp_apply wp_texp.
  wp_list.
  wp_apply wp_H.
  wp_apply wp_derive_senc_key.
  wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => True)%I) => //.
  iIntros "%p_s %Hnoncep_s #Hmintedp_s #Hprivatep_s #Heqp_s #Heqp_sV Htokenp_s".
  wp_pures.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => True)%I) => //.
  iIntros "%p_u %Hnoncep_u #Hmintedp_u #Hprivatep_u #Heqp_u #Heqp_uV Htokenp_u".
  wp_pures.
  wp_apply wp_texp. wp_pures.
  wp_apply wp_texp.
  wp_list.
  wp_term_of_list.
  wp_lam. wp_pures.
  wp_apply wp_senc'.
  wp_list.
  wp_term_of_list.
  iApply "post".
  iExists k_s, p_s, (TExp g p_s), (TExp g p_u), _.
  do !iSplit => //.
  1, 2: iApply public_TExp_iff; auto.
  1, 2: do !iSplit => //.
  1, 4: by iApply minted_TInt.
  iApply exp_pred_intro1.
  by iApply "Heqp_s"; auto.
  1, 3: by rewrite public_TInt; auto.
  iApply exp_pred_intro1.
  by iApply "Heqp_u"; auto.
  iApply (public_sencIS _ (opN.@"AuthEnc") Φ _) => //.
  rewrite minted_senc minted_THash minted_tag.
  1, 2: iApply minted_of_list; do !iSplit => //; iApply minted_TExp.
  1, 3, 5: by intro contra.
  1- 3: iSplit => //.
  by rewrite minted_THash minted_tag.
  1, 2: by iApply minted_TInt.
  iModIntro.
  rewrite public_senc_key.
  iIntros "#Hcompromise".
  iDestruct (public_THashE with "Hhashpred Hcompromise") as "[Hpub | [Hmin contra]]";
    rewrite !public_of_list /=.
  iDestruct "Hprivpw" as "[Hprivpw _]".
  iDestruct "Hpub" as "[Hpubpw _]".
  iDestruct ("Hprivpw" with "Hpubpw") as "contra".
  all: iDestruct "Hprivatep_u" as "[_ Hprivatep_u]";
    iDestruct ("Hprivatep_u" with "contra") as "Hpubp_u";
    iDestruct "Hprivatep_s" as "[_ Hprivatep_s]";
    iDestruct ("Hprivatep_s" with "contra") as "Hpubp_s";
    do !iSplit => //; do ?iApply public_TExp => //; by rewrite public_TInt.
Qed.

Lemma wp_server_session (db c : val) (alist : gmap term val) :
{{{ cryptis_ctx
      ∗ hash_pred (opN.@"A_s") (λ _,  True)
      ∗ channel c
      ∗ AList.is_alist db alist
      ∗ opaque_db alist }}}
  Server.session db c
{{{ x , RET x ; True }}}.
Proof.
  iIntros "%ϕ".
  rewrite /opaque_db. rewrite big_sepM_forall.
  iIntros "[#Cryptis [#Hpred [#Hc [Hdb #Hmapcontents]]]] Hhl".
  wp_lam. wp_pures.
  wp_apply (wp_recv with "Hc").
  iIntros "%m1 #Hpubm1".
  wp_list_of_term m1; wp_pures.
  2: by iApply "Hhl".
  do !rewrite subst_list_match /=.
  wp_list_match => [uid α X_u -> | _].
  2: wp_pures; by iApply "Hhl".
  wp_bind (AList.find _ _).
  iApply (AList.wp_find with "Hdb").
  iIntros "!> Hdb".
  case db_uid: (alist !! uid) => [file|]; wp_pures.
  2: by iApply "Hhl".
  iDestruct ("Hmapcontents" $! uid file with "[//]") as
  "[_ (%k_s & %p_s & %P_s & %P_u & %envelope &
        %e & Hmk_s & Hdhpredk_s & Hmp_s & Hmp_sV & HpP_s & HpP_u & Hpenvelope)]".
  rewrite !subst_list_match /= e.
  wp_apply wp_list_of_term.
  rewrite Spec.of_listK.
  wp_pures.
  rewrite subst_list_match /=.
  wp_list_match => [k_s' p_s' P_s' P_u' envelope' e' | ].
  inversion e'. subst. clear e'.
  2: by intro contra.
  wp_apply (wp_mk_nonce (fun _ => False)%I (fun _ => True)%I) => //.
  iIntros "%x_s %Hnoncex_s #Hmintedx_s #Hprivatex_s #Hdhx_s #Hdhx_sV Htokenx_s".
  wp_pures.
  wp_apply wp_texp. wp_pures.
  wp_apply wp_texp. wp_pures.
  wp_apply wp_ke.
  wp_list.
  wp_apply wp_H.
  wp_list.
  wp_apply wp_prf.
  wp_list.
  wp_apply wp_prf.
  wp_list.
  wp_term_of_list.
  rewrite public_of_list => /=.
  iDestruct "Hpubm1" as "[Hpubuid [Hpubα [HpubX_u _]]]".
  iAssert (▷ public (TExp α k_s'))%I as "#?".
  { admit. }
  wp_pures.
  wp_apply wp_send => //.
  rewrite public_of_list => //.
  do !iSplit => //.
  iApply public_TExp_iff; auto.
  do !iSplit => //.
  by iApply minted_TInt.
  iApply exp_pred_intro1.
  by iApply "Hdhx_s"; auto.
  by rewrite public_TInt; auto.
  iApply public_THashIS => //.
  rewrite minted_of_list /= !minted_THash !minted_tag !minted_of_list /=.
  do !iSplit => //.
  1, 2: iApply all_minted_TExp; iSplit => //.
  1- 4: by iApply public_minted.
  wp_pures.
  wp_apply (wp_recv with "Hc").
  iIntros "%m3 #Hm3pub".
  wp_list.
  wp_apply wp_prf.
  wp_eq_term Heq; wp_pures.
  2: by iApply "Hhl".
  wp_list.
  wp_pures.
  by iApply "Hhl".
Admitted.

End Opaque.
