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
    ∗ minted k_s ∗ □(public k_s ↔ ▷ □ False) ∗
    □(public (TInv k_s) ↔ ▷ False) ∗
    □(∀ t' : term, exp_pred_base k_s t' ↔ ▷ □ True) ∗
    □(∀ t' : term, exp_pred_base (TInv k_s) t' ↔ ▷ False) ∗
    public P_s ∗ public envelope ∗
    opaque_public_private_pair p_s P_u.

Definition opaque_db (db : gmap term val) : iProp :=
[∗ map] (k : term) ↦ (file : val) ∈ db,
public k ∗ opaque_file file.

Lemma wp_make_file (pw : term) :
{{{ cryptis_ctx
    ∗ minted pw
    ∗ □ (public pw ↔ ▷ □ False)
    ∗ hash_pred (opN.@"rw") (λ _,  False)
    ∗ senc_pred (opN.@"AuthEnc") envelope_pred
    }}}
Server.make_file pw
{{{ file , RET (repr file) ; opaque_file file }}}.
Proof.
  iIntros "%ϕ (#cryptis & #Hmintedpw & #Hprivpw & #Hhashpred & #Hsencpred) post".
  wp_lam.
  wp_apply (wp_mk_nonce_freshN ∅ (fun _ => False)%I (fun _ => True)%I
                               (fun t =>  {[(TInv t)]})) => //.
  - by iIntros "%_ %contra".
  - iIntros "%t". rewrite big_sepS_singleton minted_TInv. iModIntro.
    by auto.
  iIntros "%k_s _ %Hnoncek_s #Hmintedk_s #Hprivatek_s #Hexpk_s #H #Hexpk_sV Htokenk_sV".
  rewrite big_sepS_singleton.
  iDestruct ("H" $! False%I with "Htokenk_sV") as ">#Hprivk_sV".
  iClear "H".
  wp_pures.
  wp_lam.
  wp_pures.
  wp_apply wp_H'.
  wp_apply wp_texp.
  wp_list.
  wp_apply wp_H.
  wp_apply wp_derive_senc_key.
  wp_pures.
  wp_apply (wp_mk_nonce_freshN ∅ (fun _ => False)%I opaque_secret
                               (fun t =>  {[(TInv t)]})) => //.
  - by iIntros "%_ %contra".
  - iIntros "%t". rewrite big_sepS_singleton minted_TInv. iModIntro.
    by auto.
  iIntros "%p_s _ %Hnoncep_s #Hmintedp_s #Hprivatep_s #Hexpp_s #H #Hexpp_sV Htokenp_sV".
  rewrite big_sepS_singleton.
  iDestruct ("H" $! False%I with "Htokenp_sV") as ">#Hprivp_sV".
  iClear "H".
  wp_pures.
  wp_apply (wp_mk_nonce_freshN {[(TExp g p_s)]} (fun _ => False)%I opaque_secret
                               (fun t =>  {[(TInv t)]})) => //.
  - iIntros "%". rewrite elem_of_singleton. iIntros "->".
    iApply minted_TExp.
    by intro contra.
    iSplit => //.
    by iApply minted_TInt.
  - iIntros "%t". rewrite big_sepS_singleton minted_TInv. iModIntro.
    by auto.
  iIntros "%p_u %Hfreshp_u %Hnoncep_u #Hmintedp_u #Hprivatep_u #Hexpp_u #H #Hexpp_uV Htokenp_uV".
  rewrite big_sepS_singleton.
  iDestruct ("H" $! False%I with "Htokenp_uV") as ">#Hprivp_uV".
  iClear "H".
  assert (p_u ≠ p_s) as Hneq.
  intro contra.
  apply (Hfreshp_u (TExp g p_s)).
  by rewrite elem_of_singleton.
  rewrite contra.
  assert (negb (is_exp g)) as H0.
  done.
  assert (invs_canceled [p_s]) as H1.
  by apply invs_canceled1.
  assert (subterm p_s p_s) as H2.
  by apply STRefl.
  apply (STExp2 H0 H1 H2).
  by rewrite elem_of_list_singleton.
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
  by rewrite bi.intuitionistically_False.
  iApply public_TExp_iff; auto.
  do !iSplit => //.
  by iApply minted_TInt.
  iApply exp_pred_intro1.
  iApply "Hexpp_s".
  by iNext; iModIntro; iPureIntro; rewrite exps_TExpN.
  by iModIntro; iIntros "?"; iApply public_TInt.
  iApply (public_sencIS _ (opN.@"AuthEnc") envelope_pred _) => //.
  rewrite minted_senc minted_THash minted_tag.
  1, 2: iApply minted_of_list; do !iSplit => //; iApply minted_TExp.
  1, 3, 5: by intro contra.
  1- 3: iSplit => //.
  by rewrite minted_THash minted_tag.
  1, 2: by iApply minted_TInt.
  iModIntro.
  iExists p_u, (TExp g p_u), (TExp g p_s).
  iSplit => //.
  iExists p_s.
  do !iSplit => //.
  iPureIntro.
  apply Hfreshp_u.
  by rewrite elem_of_singleton.
  iApply public_TExp_exp_pred => //.
  by iApply public_TInt.
  iApply exp_pred_intro1.
  iApply "Hexpp_s".
  by iNext; iModIntro; iPureIntro; rewrite exps_TExpN.  
  by rewrite bi.intuitionistically_False.
  iModIntro.
  rewrite public_senc_key.
  iIntros "#Hcompromise".
  iDestruct (public_THashE with "Hhashpred Hcompromise") as "[Hpub | [Hmin contra]]";
    rewrite !public_of_list /=.
  iDestruct "Hprivpw" as "[Hprivpw _]".
  iDestruct "Hpub" as "[Hpubpw _]".
  iDestruct ("Hprivpw" with "Hpubpw") as "contra".
  1, 2: by iDestruct "Hprivatep_u" as "[_ Hprivatep_u]";
  iDestruct ("Hprivatep_u" with "contra") as "Hpubp_u";
  iDestruct "Hprivatep_s" as "[_ Hprivatep_s]";
  iDestruct ("Hprivatep_s" with "contra") as "Hpubp_s";
  do !iSplit => //; do ?iApply public_TExp => //; rewrite public_TInt.
  iExists p_u.
  do !iSplit => //.
  iPureIntro.
  apply /subtermsP. rewrite subtermsE // cancel_exps1 /g subtermsE /= !right_id_L.
  rewrite [subterms p_u]subterms_nonce //.
  rewrite !not_elem_of_union.
  do !split; rewrite elem_of_singleton //; destruct p_s => //.
  destruct p_u => //.
  rewrite /TExpN unlock /fold_term unlock /PreTerm.exp /= /PreTerm.insert_exp /path.sort /=
  /fold_term_def /PreTerm.normalize /= /PreTerm.insert_exp /path.sort /= /PreTerm.invs_canceled /=.
  by destruct (ssrbool.boolP true); intro contra.
  iApply public_TExp_exp_pred => //.
  by iApply public_TInt.
  iApply exp_pred_intro1.
  iApply "Hexpp_u".
  by iNext; iModIntro; iPureIntro; rewrite exps_TExpN.
  by rewrite bi.intuitionistically_False.
Qed.

Lemma wp_server_session (db c : val) (alist : gmap term val) (fresh : gset term) :
{{{ cryptis_ctx
    ∗ hash_pred (opN.@"A_s") A_pred
    ∗ hash_pred (opN.@"SK") (λ _,  False)
    ∗ hash_pred (opN.@"K") (λ _,  False)
    ∗ channel c
    ∗ AList.is_alist db alist
    ∗ opaque_db alist
    ∗ ∀ t : term, ⌜t ∈ fresh⌝ -∗ minted t}}}
Server.session db c
{{{ x , RET (repr x) ; SK_result x fresh ∗ AList.is_alist db alist }}}.
Proof.
  iIntros "%ϕ".
  rewrite /opaque_db big_sepM_forall.
  iIntros "(#Cryptis & #HpredA_s & #HpredSK & #HpredK & #Hc & Hdb & #Hmapcontents & #Hfresh) Hhl".
  wp_lam. wp_pures.
  wp_apply (wp_recv with "Hc").
  iIntros "%m1 #Hpubm1".
  wp_list_of_term m1; wp_pures.
  2: by iApply ("Hhl" $! None); iModIntro; do !iSplit.
  rewrite !subst_list_match /=.
  wp_list_match => [uid α X_u -> | _].
  2: by wp_pures; iApply ("Hhl" $! None); iModIntro; do !iSplit.
  wp_bind (AList.find _ _).
  iApply (AList.wp_find with "Hdb").
  iIntros "!> Hdb".
  case db_uid: (alist !! uid) => [file|]; wp_pures.
  2: by iApply ("Hhl" $! None); iModIntro; do !iSplit.
  iDestruct ("Hmapcontents" $! uid file with "[//]") as
    "[_ (%k_s & %p_s & %P_s & %P_u & %envelope &
        %e & Hmk_s & Hprivk_s & Hprivk_sV & Hexpk_s & Hexpk_sV &
        HpubP_s & Hpenvelope & %p_u & %HP_u & %Hfreshp_u &
        %Hnoncep_s & %Hnoncep_u & HpubP_u & Hminp_s & ? & Hexpp_s & ? & Hprivp_s & ?)]".
  rewrite !subst_list_match /= e.
  wp_apply wp_list_of_term.
  rewrite Spec.of_listK.
  wp_pures.
  rewrite subst_list_match /=.
  wp_list_match => [k_s' p_s' P_s' P_u' envelope' e' | ].
  symmetry in e'.
  inversion e'. subst. clear e'.
  2: by intro contra.
  rewrite public_of_list /=.
  iDestruct "Hpubm1" as "(? & ? & ? & _)".
  wp_apply (wp_mk_nonce_fresh ({[X_u]} ∪ fresh) (fun _ => False)%I (fun t => opaque_secret t)%I) => //.
  - iIntros "%".
    rewrite elem_of_union.
    rewrite elem_of_singleton public_minted. iIntros "[-> | %H]".
    by iApply public_minted.
    by iApply "Hfresh".
  iIntros "%x_s %Hfreshx_s %Hnoncex_s #Hmintedx_s #Hprivatex_s #Hexpx_s #? #Hexpx_sV _".
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
  wp_pures.
  set m2 := (Spec.of_list [_; _; _; _]).
  wp_apply wp_send => //.
  rewrite public_of_list => //.
  do !iSplit => //.
  iApply public_TExp_exp_pred => //.
  iApply exp_pred_intro1 => //.
  by iApply "Hexpk_s".
  iApply public_TExp_iff; auto.
  do !iSplit => //.
  by iApply minted_TInt.
  iApply exp_pred_intro1.
  by iApply "Hexpx_s"; iPureIntro; rewrite exps_TExpN.
  by rewrite public_TInt; auto.
  iApply public_THashIS => //.
  rewrite minted_of_list /= !minted_THash !minted_tag !minted_of_list /=.
  do !iSplit => //.
  1, 2: iApply all_minted_TExp; iSplit => //.
  1- 4: by iApply public_minted.
  iNext. iModIntro.
  iExists (TExp g p_u), p_s, X_u, x_s, (hash_result "ssid'" (Spec.of_list [uid; α])).
  do !iSplit => //.  
  iExists p_u.
  do !iSplit => //.
  wp_pures.
  wp_apply (wp_recv with "Hc").
  iIntros "%m3 #Hm3pub".
  wp_list.
  wp_apply wp_prf.
  wp_eq_term Heq; wp_pures.
  2: by iApply ("Hhl" $! None); iModIntro; do !iSplit.
  wp_list.
  wp_term_of_list.
  wp_pures.
  iModIntro.
  set SK := Spec.of_list _.
  iApply ("Hhl" $! (Some SK)).
  iSplitR => //.
  rewrite /SK_result /SK.
  iSplit.
  rewrite /SK_priv public_of_list /=.
  iSplit; iIntros "contra".
  iDestruct "contra" as "(_ & contra & _)".
  iDestruct (public_THashE with "HpredSK contra") as "[Hpub | [_ contra]]" => //.
  rewrite public_of_list /=.
  iDestruct "Hpub" as "[Hpub _]".
  iDestruct (public_THashE with "HpredK Hpub") as "[Hpub' | [_ contra]]" => //.
  rewrite public_of_list /=.
  iDestruct "Hpub'" as "(contra & _)".
  rewrite TExp_TExpN.
  have p_s_u: p_s ≠ p_u.
    move=> p_u_s; apply: Hfreshp_u; rewrite -p_u_s.
    apply/subtermsP; rewrite subtermsE // cancel_exps1 /=.
    rewrite [subterms p_s]subterms_nonce //; set_solver.
  have p_s_uV : p_s ≠ TInv p_u.
    move=> contra; have: is_inv (TInv p_u).
      by rewrite is_inv_TInv; case: (p_u) => // in Hnoncep_u *.
    by rewrite -contra; case: (p_s) => // in Hnoncep_s *.
  by iApply (public_opaque_secret _ p_s_u p_s_uV).
  do !iSplit => //.
  iApply (public_THashIS with "HpredSK") => //.
  rewrite minted_of_list.
  do !iSplit => //; rewrite minted_THash minted_tag minted_of_list; do !iSplit => //.
  1, 2: rewrite -all_minted_TExp; iSplit => //.
  1- 4: by iApply public_minted.
  iSplit.
  admit.
  rewrite minted_of_list /=.
  do !iSplit => //.
  by iApply public_minted.
  rewrite minted_THash minted_tag minted_of_list /=.
  do !iSplit => //;
      rewrite minted_THash minted_tag minted_of_list /=; do !iSplit => //.
  rewrite TExp_TExpN -all_minted_TExpN /=.
  do !iSplit => //.
  by iApply minted_TInt.
  rewrite -all_minted_TExp.
  iSplit => //.
  all: by iApply public_minted.
Admitted.

End Opaque.
