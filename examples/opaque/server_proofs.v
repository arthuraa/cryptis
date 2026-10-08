From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics role.
From cryptis.lib Require Import dh.

From cryptis.examples Require Import alist.
From cryptis.examples.opaque Require Import impl shared.

From iris.base_logic.lib Require Import invariants.

From cryptis.lib Require Import term_set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Opaque.

Context `{!cryptisGS Σ, !heapGS Σ, !opaqueGS Σ}.

Abbreviation iProp := (iProp Σ).

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
wp_apply (wp_mk_nonce_freshN ∅ (fun _ => False)%I dh_key_share
                               (fun t =>  {[(TInv t)]})) => //.
- by iIntros "%_ %contra".
- iIntros "%t".
  rewrite big_sepS_singleton minted_TInv.
  by iModIntro; auto.
iIntros "%p_s _ #Hmintedp_s #Hprivatep_s #Hexpp_s #Hexpp_sV Htokenp_sV".
rewrite big_sepS_singleton.
wp_pures.
wp_apply (wp_mk_nonce_freshN {[(TExp g p_s)]} (fun _ => False)%I dh_key_share
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

Lemma wp_server_session (db c : val) (alist : gmap term val) φ :
{{{ cryptis_ctx
    ∗ opaque_ctx
    ∗ opaque_pred φ
    ∗ channel c
    ∗ AList.is_alist db alist
    ∗ opaque_db alist
    ∗ (∀ si, term_token (si_sshare si) (↑opN.@"res") ={⊤}=∗
             φ si Init ∗ φ si Resp)
  }}}
    Server.session db c
  {{{ r, RET (repr r);
      AList.is_alist db alist ∗
      (⌜r = None⌝ ∨ ∃ si,
         ⌜r = Some (si_result si)⌝ ∗
         opaque_session_for (si_uid si) si ∗
         (∃ (k_s p_s : nonce) envelope,
            ⌜alist !! si_uid si =
             Some (Spec.of_list [TNonce k_s; TNonce p_s;
                                 si_skey si; si_ckey si; envelope] : val)⌝) ∗
         □ (public (si_key si) ↔ ▷ □ False) ∗
         term_token (si_key si) (↑opN.@"server") ∗
         φ si Resp) }}}.
Proof.
iIntros "%ϕ".
rewrite /opaque_db big_sepM_forall.
iIntros "(#Cryptis & (_ & #HpredA_s & _ & #HpredSK & #HpredK & _ & _)
          & #N_φ & #Hc & Hdb & #Hmapcontents & res) Hhl".
wp_lam; wp_pures.
wp_apply (wp_recv with "Hc"); iIntros "%m1 #Hpubm1".
wp_list_of_term m1; wp_pures; last first.
  by iApply ("Hhl" $! None); iModIntro; iFrame "Hdb"; iLeft.
rewrite !subst_list_match /=.
wp_list_match => [uid α X_u -> | _]; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iFrame "Hdb"; iLeft.
wp_eq_term X_u_one; wp_pures.
  by iApply ("Hhl" $! None); iModIntro; iFrame "Hdb"; iLeft.
wp_bind (AList.find _ _); iApply (AList.wp_find with "Hdb"); iIntros "!> Hdb".
case db_uid: (alist !! uid) => [file|]; wp_pures; last first.
  by iApply ("Hhl" $! None); iModIntro; iFrame "Hdb"; iLeft.
iDestruct ("Hmapcontents" $! uid file with "[//]") as
    "[_ (%k_s & %p_s & %P_s & %P_u & %envelope &
         %e & #Hmk_s & #Hprivk_s & #Hexpk_s & #Hexpk_sV &
         #HpubP_s & #Hpenvelope & %p_u & %HP_u & %Hfreshp_u &
         #HpubP_u & #Hminp_s & #Hminp_u & #Hexpp_s & #Hexpp_u & #Hprivp_s
         & #Hprivp_u)]".
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
iAssert (minted uid) as "#minuid". by iApply public_minted.
iAssert (minted α) as "#minα". by iApply public_minted.
iAssert (minted X_u) as "#minX_u". by iApply public_minted.
iAssert (minted P_s) as "#minP_s". by iApply public_minted.
iAssert (minted (TExp g p_u)) as "#minP_u". by iApply public_minted.
(* The fresh ephemeral comes with tokens on the server's share and on the
   session key, which is a function of the ephemeral: see [server_fresh_set]. *)
wp_apply (wp_mk_nonce_freshN ∅ (fun _ => False)%I (fun t => dh_key_share t)%I
            (server_fresh_set uid α X_u P_s (TExp g p_u) p_s)) => //.
  by iIntros "% %contra".
  by iApply (server_fresh_set_minted uid α X_u P_s p_s_u
               with "minuid minα minX_u minP_s Hminp_s Hminp_u").
iIntros "%x_s _ #Hmintedx_s #Hprivatex_s #Hexpx_s #Hexpx_sV tokens".
rewrite server_fresh_setE.
set si := server_si uid α X_u P_s (TExp g p_u) p_s x_s.
have ne : TExp g x_s ≠ si_key si by exact: TExp_g_nonce_hash_ne.
rewrite big_sepS_union ?big_sepS_singleton; last set_solver.
iDestruct "tokens" as "[tok_Xs tok_SK]".
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
iAssert (minted (hash_result "d" (Spec.of_list [X_u; P_s]))) as "#mintedd".
  by iApply minted_hash_listI; rewrite /=; do !iSplit => //.
iAssert (minted (hash_result "e" (Spec.of_list [TExp g x_s; TExp g p_u])))
  as "#mintede".
  iApply minted_hash_listI; rewrite /=; do !iSplit => //.
  by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
iAssert (minted (si_key si)) as "#mintedSK".
  iApply minted_hash_listI; rewrite /=; do !iSplit => //.
  - iApply minted_hash_listI; rewrite /=; iSplit => //.
    by iApply (minted_hmqv_K with
                 "Hminp_s Hmintedx_s mintede minP_u minX_u mintedd").
  - by iApply minted_hash_listI; rewrite /=; do !iSplit => //.
(* The caller's resources for this session come from the [↑opN.@"res"] slice
   of the token on the server's share; the client's copy is escrowed at once,
   as is the client's slice of the token on the session key. *)
iDestruct (term_token_difference (TExp g x_s) (↑opN.@"res") with "tok_Xs")
  as "[tok_res _]"; first solve_ndisj.
iMod ("res" $! si with "tok_res") as "[res_I res_R]".
iMod (opaque_ready_alloc with "N_φ res_I") as "#ready".
iDestruct (term_token_difference (si_key si) (↑opN.@"client") with "tok_SK")
  as "[tok_client tok_SK]"; first solve_ndisj.
iMod (opaque_client_token_alloc with "tok_client") as "#cl_tok".
iDestruct (term_token_drop (↑opN.@"server") with "tok_SK") as "tok_server";
  first solve_ndisj.
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
    iExists si; rewrite /si /server_si /si_K /si_ssid /=.
    by do !iSplit => //.
wp_pures.
wp_apply (wp_recv with "Hc"); iIntros "%m3 #Hm3pub".
wp_list; wp_apply wp_prf.
wp_eq_term Heq; wp_pures; last first.
  by iApply ("Hhl" $! None); iModIntro; iFrame "Hdb"; iLeft.
wp_list; wp_term_of_list; wp_pures.
iModIntro.
iApply ("Hhl" $! (Some (si_result si))).
iFrame "Hdb".
iRight; iExists si.
iFrame "tok_server res_R".
(* Two group factors of the key survive whatever [X_u] the peer sent: the
   static-static one, which carries secrecy, and the peer-static x
   own-ephemeral one, which carries freshness. *)
have Xu_in : X_u ∈ [X_u; P_s] by set_solver.
have tags : "e"%string ≠ "d"%string by [].
have [gf_ss [gf_eph [in_ps in_pu]]] :=
  @hmqv_key_gfactors p_s p_u x_s "e" "d"
    (Spec.of_list [TExp g x_s; TExp g p_u]) [X_u; P_s] X_u
    tags p_s_u Xu_in.
iSplit; first by [].
iSplit.
  by do !iSplit => //.
iSplit.
  iExists k_s, p_s, envelope; iPureIntro.
  by rewrite /si /server_si /= db_uid.
iModIntro; iSplit; iIntros "#contra".
- iDestruct (public_THashE with "HpredSK contra") as "[Hpub | [_ contra']]" => //.
  rewrite public_of_list /=.
  iDestruct "Hpub" as "[Hpub _]".
  iDestruct (public_THashE with "HpredK Hpub") as "[Hpub' | [_ contra']]" => //.
  rewrite public_of_list /=.
  iDestruct "Hpub'" as "(contra' & _)".
  iEval (rewrite public_gfactors) in "contra'".
  iDestruct "contra'" as "[_ #fs]".
  have p_s_uT : TNonce p_s ≠ TNonce p_u by case=> /p_s_u.
  iApply (public_dh_secret_gen _ p_s_uT in_ps in_pu with
            "Hprivp_s Hexpp_s Hprivp_u Hexpp_u").
  by iApply (big_sepL_elem_of with "fs").
- iApply (public_THashIS with "HpredSK [] contra").
  by iEval (rewrite /si_key minted_hash_resultE) in "mintedSK".
Qed.

End Opaque.
