From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics role.
From cryptis.lib Require Import dh.

From cryptis.examples Require Import alist.
From cryptis.examples.opaque Require Import impl shared.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Opaque.

Context `{!cryptisGS Σ, !heapGS Σ, !opaqueGS Σ}.
Abbreviation iProp := (iProp Σ).

Lemma wp_client_session (uid pw : term) (c : val) φ :
  {{{
    cryptis_ctx
    ∗ opaque_ctx
    ∗ opaque_pred φ
    ∗ channel c
    ∗ public uid
    ∗ minted pw
    ∗ □(public pw ↔ ▷ □ False)
  }}} Client.session uid c pw
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_result si)⌝ ∗
        opaque_session_for uid si ∗
        □ (public (si_key si) ↔ ▷ □ False) ∗
        (public (si_key si) ∨
           term_token (si_key si) (↑opN.@"client") ∗ φ si Init) }}}.
Proof.
iIntros "%ϕ (#Cryptis & (#Hpredrw & #HpredA_s & #HpredA_u & #HpredSK & #HpredK
  & #Hpredα & #SpredAuth) & #N_φ & #Hc & #pubuid & #mintedpw & #privpw) Hhl".
iAssert (minted uid) as "#minteduid"; first by iApply public_minted.
wp_lam; wp_pures.
wp_apply (wp_mk_nonce (fun _ => False)%I (fun t => dh_key_share t)%I) => //.
iIntros "%x_u #Hmintedx_u #Hprivatex_u #Hexpx_u #Hexpx_uV _".
wp_pures.
(* The blind [α] is the client's share: the server keys both escrows on its
   token, so it is minted together with [r]. *)
wp_apply (wp_mk_nonce_freshN ∅ (fun _ => False)%I (fun _ => True)%I
            (client_fresh_set pw)) => //.
- by iIntros "% %contra".
- by iApply client_fresh_set_minted.
iIntros "%r _ #Hmintedr #Hprivater #Hexpr #HexprV tok_α".
rewrite /client_fresh_set big_sepS_singleton.
iAssert (minted (TExp (hash_result "α" pw) r)) as "#mintedα".
  by iApply all_minted_TExp; iSplit => //; iApply minted_hash_resultI.
set α := TExp (hash_result "α" pw) r.
wp_pures.
iDestruct (term_token_difference α (↑opN.@"ready") with "tok_α")
  as "[tok_ready tok_α]"; first solve_ndisj.
iDestruct (term_token_difference α (↑opN.@"tok") with "tok_α")
  as "[tok_tok _]"; first solve_ndisj.
wp_apply wp_H'; wp_apply wp_texp; wp_pures.
wp_apply wp_texp; wp_list; wp_term_of_list; wp_pures.
set m1 := Spec.of_list _.
wp_apply wp_send => //.
  do !rewrite public_of_list /=.
  do !iSplit => //.
  - iApply public_TExp_iff => //.
    do !iSplit => //.
    + by rewrite minted_THash minted_tag.
    + iApply exp_pred_intro1.
      by iApply "Hexpr".
    + iModIntro; iIntros "#p".
      by iApply (public_THashIS with "Hpredα") => //.
  - iApply public_TExp_iff => //.
    do !iSplit => //.
    + by iApply minted_TInt.
    + iApply exp_pred_intro1.
      iApply "Hexpx_u"; iPureIntro.
      rewrite (_ : TExp g x_u = TExpN g [TNonce x_u]); last by rewrite /TExpN TMulN1.
      by rewrite exps_TExpN //; exact: invs_canceled1.
    + by rewrite public_TInt; auto.
wp_pures.
wp_apply wp_recv => //.
iIntros "%m2 #pubm2".
iAssert (minted m2) as "minm2". by iApply public_minted.
wp_list_of_term m2; wp_pures => //.
  1: wp_list_match => [β X_s envelope A_s -> | _].
  1, 2: wp_pures.
  2, 3: by iApply ("Hhl" $! None); iModIntro; iLeft.
wp_apply wp_hl_inv_aux_term => //.
wp_apply wp_texp; wp_list; wp_apply wp_H.
wp_apply wp_derive_senc_key; set k := SEncKey _.
wp_pures; wp_lam; wp_pures.
rewrite minted_of_list public_of_list => /=.
iDestruct "minm2" as "(_ & minX_s & minenv & _)".
iDestruct "pubm2" as "(_ & _ & pubenv & pubA_s & _)".
wp_apply wp_sdec => //; iSplit; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iLeft.
iIntros "%clear #minclear [#pubkey | #envpred] _".
  rewrite /k public_senc_key.
  iPoseProof (public_THashE with "Hpredrw pubkey") as "[contra | [_ contra]]".
  - rewrite public_of_list /=.
    iDestruct "contra" as "(contra & _ & _)".
    iPoseProof ("privpw" with "contra") as "contra'".
    wp_pures. by iDestruct "contra'" as "[]".
  - wp_pures. by iDestruct "contra" as "[]".
iDestruct "envpred" as "(%p_u & %P_u & %P_s & -> & Hopaquepair)".
wp_pures.
wp_list_of_term_eq clear Hclear; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iLeft.
apply Spec.of_list_inj in Hclear.
rewrite -Hclear.
wp_pures.
wp_list_match => [p_u' P_u' P_s' H | _]; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iLeft.
symmetry in H; inversion H; subst; clear H.
(* [d := H "d" [X_u; P_s]] and [e := H "e" [X_s; P_u]] *)
wp_list; wp_apply wp_H; wp_pures.
wp_list; wp_apply wp_H; wp_pures.
wp_apply wp_ke => /=.
wp_list.
wp_apply wp_H => /=.
wp_list.
wp_apply wp_prf => /=.
wp_list.
wp_apply wp_prf.
rewrite minted_of_list => /=.
iDestruct "minclear" as "(minp_u & minP_u & minP_s & _)".
iAssert (minted (hash_result "d" (Spec.of_list [TExp g x_u; P_s])))
  as "#mintedd".
  iApply minted_hash_listI; rewrite /=; do !iSplit => //.
  by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
iAssert (minted (hash_result "e" (Spec.of_list [X_s; P_u]))) as "#mintede".
  by iApply minted_hash_listI; rewrite /=; do !iSplit => //.
set d := hash_result "d" (Spec.of_list [TExp g x_u; P_s]).
set e := hash_result "e" (Spec.of_list [X_s; P_u]).
set K := hash_result "K" (Spec.of_list [hmqv_K p_u x_u d P_s X_s e]).
set ssid' := hash_result "ssid'" (Spec.of_list [uid; α]).
set SK := hash_result "SK" (Spec.of_list [K; ssid']).
iAssert (minted K) as "#mintedK".
  iApply minted_hash_listI; rewrite /=; iSplit => //.
  by iApply (minted_hmqv_K with
               "minp_u Hmintedx_u mintedd minP_s minX_s mintede").
iAssert (minted ssid') as "#mintedssid".
  by iApply minted_hash_listI; rewrite /=; do !iSplit => //.
iAssert (minted SK) as "#mintedSK".
  by iApply minted_hash_listI; rewrite /=; do !iSplit => //.
iPoseProof "Hopaquepair" as
    "(%p_s & -> & %Hfreshp_u & #pubP_s & _ & #minp_s & #pred_p_u & #pred_p_s
      & #priv_p_u & #priv_p_s)".
(* The client's static private key and the server's are distinct: [p_u] is
   not a subterm of [P_s = g^p_s]. *)
have p_u_s : p_u ≠ p_s.
  move=> e'; apply: Hfreshp_u; rewrite e'.
  apply/subtermsP.
  rewrite (_ : TExp g p_s = TExpN g [TNonce p_s]); last by rewrite /TExpN TMulN1.
  rewrite subtermsE //; last exact: invs_canceled1.
  rewrite /=.
  by rewrite [subterms p_s]subterms_nonce //; set_solver.
(* The static-static factor [g^(p_s·e·d·p_u)] is a group factor of the key
   whatever [X_s] the peer sent, so the key is public only if it is; and it
   is not, since [p_u] and [p_s] are both honest DH seeds. *)
have Xs_in : X_s ∈ [X_s; P_u] by set_solver.
have tags : "d"%string ≠ "e"%string by [].
have [gf [_ [in_pu in_ps]]] :=
  @hmqv_key_gfactors p_u p_s x_u "d" "e"
    (Spec.of_list [TExp g x_u; TExp g p_s]) [X_s; P_u] X_s
    tags p_u_s Xs_in.
have p_u_sT : TNonce p_u ≠ TNonce p_s by case=> /p_u_s.
iAssert (□ (public K → ▷ □ False))%I as "#secK".
  iIntros "!> #pubK".
  iDestruct (public_THashE with "HpredK pubK") as "[contra | [_ contra]]" => //.
  rewrite public_of_list /=.
  iDestruct "contra" as "(contra & _)".
  iEval (rewrite public_gfactors) in "contra".
  iDestruct "contra" as "[_ #fs]".
  iApply (public_dh_secret_gen _ p_u_sT in_pu in_ps with
            "priv_p_u pred_p_u priv_p_s pred_p_s").
  by iApply (big_sepL_elem_of with "fs").
wp_eq_term eq_A_s => //=; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iLeft.
subst A_s.
(* The authentication step.  A valid [A_s] was either forged -- in which case
   [K] is public, which the two honest static keys rule out -- or produced by
   the honest server, which then vouches for its session [si]: its [K] and
   [ssid'] are ours, so [si_key si] is our [SK]. *)
iAssert (▷ □ A_s_pred (Spec.of_list [K; ssid']))%I as "#auth".
  iDestruct (public_THashE with "HpredA_s pubA_s") as "[contra | [_ #auth]]" => //.
  rewrite public_of_list /=.
  iDestruct "contra" as "(contra & _)".
  iDestruct ("secK" with "contra") as "contra'".
  by iNext; iDestruct "contra'" as "[]".
wp_pures; wp_list.
wp_apply wp_prf.
wp_pures.
iDestruct "auth" as "(%si & %e_si & #pubck & #pubsk & #cl_tok & #ready)".
have eSK : si_key si = SK by rewrite /si_key /SK e_si.
case/Spec.of_list_inj: e_si => _ essid.
case/Spec.tag_inj: essid => _ /Spec.of_list_inj [] euid eα.
iMod (escrowE with "cl_tok [tok_tok]") as "tok_SK" => //.
  by rewrite -eα.
iMod ("ready" with "N_φ [tok_ready]") as "res" => //.
  by rewrite -eα.
wp_apply wp_send => //.
  iApply public_THashIS; eauto.
  - rewrite !minted_of_list /=.
    by do !iSplit => //.
  - iNext; iModIntro.
    iExists (TExp g p_s), p_u, X_s, x_u, d, e, ssid'.
    by do !iSplit => //.
wp_pures; wp_list; wp_term_of_list; wp_pures.
have -> : Spec.of_list [uid; SK] = si_result si.
  by rewrite /si_result eSK -euid.
iApply ("Hhl" $! (Some (si_result si))).
iModIntro; iRight; iExists si.
rewrite eSK.
iSplit; first by [].
iSplit; first by rewrite /opaque_session_for -euid eSK; do !iSplit => //.
iSplit; last by iRight; iFrame "tok_SK res".
iModIntro; iSplit; iIntros "#contra".
- iDestruct (public_THashE with "HpredSK contra") as "[Hpub | [_ contra']]" => //.
  rewrite public_of_list /=.
  iDestruct "Hpub" as "[Hpub _]".
  by iApply "secK".
- iApply (public_THashIS with "HpredSK [] contra").
  by iEval (rewrite /SK minted_hash_resultE) in "mintedSK".
Qed.

End Opaque.
