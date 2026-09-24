From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis.lib Require Import dh.

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
    by [].
    by [].
    by [].
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
  apply: subterm_TExp_exp;
    [done | done | done | exact: (negb_is_mul_nonce p_s) | exact: STRefl].
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
    by [].
    by [].
    by [].
    by exact: (negb_is_mul_nonce p_s).
  do !iSplit => //.
  + by iApply minted_TInt.
  + iApply exp_pred_intro1.
    iApply "Hexpp_s".
    iNext; iModIntro; iPureIntro.
    have Nm : negb (is_mul p_s) := negb_is_mul_nonce p_s.
    rewrite (_ : TExp g p_s = TExpN g [TNonce p_s]); last by rewrite /TExpN TMulN1.
    by rewrite exps_TExpN; [by [] | by [] | by [] | by [] | exact: invs_canceled1 Nm].
  + by iModIntro; iIntros "?"; iApply public_TInt.
- iApply (public_sencIS _ (opN.@"AuthEnc") envelope_pred _) => //.
  1: rewrite minted_senc minted_THash minted_tag.
  1, 2: iApply minted_of_list; do !iSplit => //; iApply minted_TExp.
  all: try by [].
  all: try (iSplit => //).
  all: try by rewrite minted_THash minted_tag.
  all: try by iApply minted_TInt.
  iModIntro.
  iExists p_u, (TExp g p_u), (TExp g p_s).
  iSplit => //.
  iExists p_s.
  do !iSplit => //.
    iPureIntro.
    apply Hfreshp_u.
    by rewrite elem_of_singleton.
  iApply public_TExp_exp_pred.
    + by [].
    + by [].
    + by exact: (negb_is_mul_nonce p_s).
    + by iApply public_TInt.
    + done.
    + iApply exp_pred_intro1.
      iApply "Hexpp_s".
      iNext; iModIntro; iPureIntro.
      have Nm : negb (is_mul p_s) := negb_is_mul_nonce p_s.
      rewrite (_ : TExp g p_s = TExpN g [TNonce p_s]); last by rewrite /TExpN TMulN1.
      by rewrite exps_TExpN; [by [] | by [] | by [] | by [] | exact: invs_canceled1 Nm].
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
    have Nm : negb (is_mul p_u) := negb_is_mul_nonce p_u.
    rewrite (_ : TExp g p_u = TExpN g [TNonce p_u]); last by rewrite /TExpN TMulN1.
    rewrite subtermsE //; last exact: invs_canceled1 Nm.
    rewrite /= [subterms p_u]subterms_nonce //.
    rewrite /g subtermsE /=.
    have p_s_ne2 : TNonce p_s ≠ TInt 0 by move=> E; discriminate E.
    have p_s_ne1 : TNonce p_s ≠ TExpN (TInt 0) [TNonce p_u].
      move=> E.
      have H1 : exps (TExpN (TInt 0) [TNonce p_u]) ≡ₚ [TNonce p_u].
        rewrite exps_TExpN //; exact: invs_canceled1 (negb_is_mul_nonce p_u).
      have H2 : exps (TNonce p_s) = [].
        by rewrite /exps (expo_expN (TNonce p_s) I) factors_TMulN0.
      by move: H1; rewrite -E H2 => /Permutation_length.
    set_solver.
  iApply public_TExp_exp_pred.
    * by [].
    * by [].
    * by exact: (negb_is_mul_nonce p_u).
    * by iApply public_TInt.
    * done.
    * iApply exp_pred_intro1.
      iApply "Hexpp_u".
      iNext; iModIntro; iPureIntro.
      have Nm : negb (is_mul p_u) := negb_is_mul_nonce p_u.
      rewrite (_ : TExp g p_u = TExpN g [TNonce p_u]); last by rewrite /TExpN TMulN1.
      by rewrite exps_TExpN; [by [] | by [] | by [] | by [] | exact: invs_canceled1 Nm].
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
wp_eq_term X_u_one; wp_pures.
  by iApply ("Hhl" $! None); iModIntro; do !iSplit.
wp_bind (AList.find _ _); iApply (AList.wp_find with "Hdb"); iIntros "!> Hdb".
case db_uid: (alist !! uid) => [file|]; wp_pures; last first.
  by iApply ("Hhl" $! None); iModIntro; do !iSplit.
iDestruct ("Hmapcontents" $! uid file with "[//]") as
    "[_ (%k_s & %p_s & %P_s & %P_u & %envelope &
         %e & Hmk_s & Hprivk_s & Hexpk_s & Hexpk_sV &
         HpubP_s & Hpenvelope & %p_u & %HP_u & %Hfreshp_u &
         HpubP_u & Hminp_s & Hminp_u & Hexpp_s & Hexpp_u & Hprivp_s
         & Hprivp_u)]".
rewrite !subst_list_match /= e.
wp_apply wp_list_of_term.
rewrite Spec.of_listK.
wp_pures.
rewrite subst_list_match /=.
wp_list_match => [k_s' p_s' P_s' P_u' envelope' e' | ]; last first.
  by [].
symmetry in e'; inversion e'; subst; clear e'.
rewrite public_of_list /=.
iDestruct "Hpubm1" as "(#p_uid & #p_α & #p_X_u & _)".
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
(* [d := H "d" [X_u; P_s]] and [e := H "e" [X_s; P_u]] *)
wp_list; wp_apply wp_H; wp_pures.
wp_list; wp_apply wp_H; wp_pures.
wp_apply wp_ke; wp_list.
wp_apply wp_H; wp_list.
wp_apply wp_prf; wp_list.
wp_apply wp_prf; wp_list.
wp_term_of_list; wp_pures.
iAssert (minted X_u) as "#minX_u". by iApply public_minted.
iAssert (minted P_s) as "#minP_s". by iApply public_minted.
iAssert (minted (TExp g p_u)) as "#minP_u". by iApply public_minted.
iAssert (minted (hash_result "d" (Spec.of_list [X_u; P_s]))) as "#mintedd".
  by iApply minted_hash_listI; rewrite /=; do !iSplit => //.
iAssert (minted (hash_result "e" (Spec.of_list [TExp g x_s; TExp g p_u])))
  as "#mintede".
  iApply minted_hash_listI; rewrite /=; do !iSplit => //.
  by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
set m2 := (Spec.of_list [_; _; _; _]).
wp_apply wp_send => //.
  rewrite public_of_list => //.
  do !iSplit => //.
  - (* [α] comes off the network, so it may well be a group product.
       Exponentiation distributes over those, so it is enough that each group
       factor of [α], raised to [k_s], be public on its own -- and [k_s]'s seed
       predicate is permissive enough to grant exactly that, factor by
       factor. *)
    iApply public_TExp_gfactors.
    iEval (rewrite public_gfactors) in "p_α".
    iDestruct "p_α" as "[_ #fs]".
    iApply big_sepL_forall; iIntros "%k %u %Hu".
    have u_α : u ∈ gfactors α := list_elem_of_lookup_2 _ _ _ Hu.
    have Nmu : negb (is_gmul u) := Ngmul_gfactors _ _ u_α.
    iAssert (public u) as "#p_u".
      by iApply (big_sepL_elem_of with "fs").
    case Ei: (is_ginv u); last first.
    + have Niu : negb (is_ginv u) by rewrite Ei.
      iApply public_TExp_exp_pred => //.
      iApply exp_pred_intro1.
      by iApply "Hexpk_s".
    + (* A group-inverse factor: [(v⁻¹) ^ k_s = (v ^ k_s)⁻¹], so peel it off. *)
      have Nmv : negb (is_gmul (TGInv u)) by rewrite is_gmul_TGInv.
      have Niv : negb (is_ginv (TGInv u)) by rewrite (is_ginv_TGInv _ Nmu) Ei.
      have -> : TExp u k_s = TGInv (TExp (TGInv u) k_s).
        by rewrite -TExp_TGInv TGInvK.
      rewrite [public (TGInv (TExp _ _))]public_TGInv.
      iAssert (public (TGInv u)) as "#p_Iu".
        by rewrite [public (TGInv u)]public_TGInv.
      iApply public_TExp_exp_pred => //.
      iApply exp_pred_intro1.
      by iApply "Hexpk_s".
  - iApply public_TExp_iff.
      by [].
      by [].
      by [].
      by exact: (negb_is_mul_nonce x_s).
    do !iSplit => //.
    + by iApply minted_TInt.
    + iApply exp_pred_intro1.
      iApply "Hexpx_s"; iPureIntro.
      have Nm : negb (is_mul x_s) := negb_is_mul_nonce x_s.
      rewrite (_ : TExp g x_s = TExpN g [TNonce x_s]); last by rewrite /TExpN TMulN1.
      by rewrite exps_TExpN; [by [] | by [] | by [] | by [] | exact: invs_canceled1 Nm].
    + by rewrite public_TInt; auto.
  - iApply public_THashIS => //.
      iApply minted_of_listI; rewrite /=; do !iSplit => //.
      + iApply minted_hash_listI; rewrite /=; iSplit => //.
        by iApply (minted_hmqv_K with
                     "Hminp_s Hmintedx_s mintede minP_u minX_u mintedd").
      + iApply minted_hash_listI; rewrite /=; do !iSplit => //;
          by iApply public_minted.
    iNext; iModIntro.
    iExists (TExp g p_u), p_s, X_u, x_s,
        (hash_result "e" (Spec.of_list [TExp g x_s; TExp g p_u])),
        (hash_result "d" (Spec.of_list [X_u; P_s])),
        (hash_result "ssid'" (Spec.of_list [uid; α])).
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
set SK := (Spec.of_list [uid; _] : term).
iApply ("Hhl" $! (Some SK)).
iSplitR => //.
rewrite /SK_result.
(* The server's static private key and the client's are distinct: [p_s] is not
   a subterm of [P_u = g^p_u]. *)
have p_s_u : p_s ≠ p_u.
  move=> e; apply: Hfreshp_u; rewrite e.
  apply/subtermsP.
  rewrite (_ : TExp g p_u = TExpN g [TNonce p_u]); last by rewrite /TExpN TMulN1.
  have Nm : negb (is_mul p_u) := negb_is_mul_nonce p_u.
  rewrite subtermsE //; last exact: invs_canceled1 Nm.
  rewrite /=.
  by rewrite [subterms p_u]subterms_nonce //; set_solver.
(* Two group factors of the key survive whatever [X_u] the peer sent: the
   static-static one, which carries secrecy, and the peer-static x
   own-ephemeral one, which carries freshness. *)
have Xu_in : X_u ∈ [X_u; P_s] by set_solver.
have tags : "e"%string ≠ "d"%string by [].
have [gf_ss [gf_eph [in_ps in_pu]]] :=
  @hmqv_key_gfactors p_s p_u x_s "e" "d"
    (Spec.of_list [TExp g x_s; TExp g p_u]) [X_u; P_s] X_u
    tags p_s_u Xu_in.
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
    iEval (rewrite public_gfactors) in "contra".
    iDestruct "contra" as "[_ #fs]".
    have p_s_uT : TNonce p_s ≠ TNonce p_u by case=> /p_s_u.
    iApply (public_opaque_secret_gen _ p_s_uT in_ps in_pu with
              "Hprivp_s Hexpp_s Hprivp_u Hexpp_u").
    by iApply (big_sepL_elem_of with "fs").
  + do !iSplit => //.
    iApply (public_THashIS with "HpredSK") => //.
    iApply minted_of_listI; rewrite /=; do !iSplit => //.
    * iApply minted_hash_listI; rewrite /=; iSplit => //.
      by iApply (minted_hmqv_K with
                   "Hminp_s Hmintedx_s mintede minP_u minX_u mintedd").
    * iApply minted_hash_listI; rewrite /=; do !iSplit => //;
        by iApply public_minted.
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
    eexists; split; first by rewrite elem_of_cons; left.
    apply: (subterm_gfactors gf_eph).
    apply: subterm_exps_TExp_g.
    exact: exps_hmqv_eph_x.
  + iApply minted_of_listI; rewrite /=; do !iSplit => //;
      first by iApply public_minted.
    iApply minted_hash_listI; rewrite /=; do !iSplit => //.
    * iApply minted_hash_listI; rewrite /=; iSplit => //.
      by iApply (minted_hmqv_K with
                   "Hminp_s Hmintedx_s mintede minP_u minX_u mintedd").
    * iApply minted_hash_listI; rewrite /=; do !iSplit => //;
        by iApply public_minted.
Qed.

End Opaque.
