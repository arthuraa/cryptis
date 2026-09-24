From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis.lib Require Import dh.

From cryptis.examples Require Import alist.
From cryptis.examples.opaque Require Import impl shared.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Opaque.

Context `{!cryptisGS Σ, !heapGS Σ}.
Notation iProp := (iProp Σ).

Lemma wp_client_session (uid pw : term) (c : val) (fresh : gset term):
  {{{
    cryptis_ctx
    ∗ hash_pred (opN.@"rw") (λ _, False)
    ∗ hash_pred (opN.@"A_u") A_pred
    ∗ hash_pred (opN.@"A_s") A_pred
    ∗ hash_pred (opN.@"SK") (λ _,  False)
    ∗ hash_pred (opN.@"K") (λ _,  False)
    ∗ hash_pred (opN.@"α") (λ _,  True)
    ∗ senc_pred (opN.@"AuthEnc") envelope_pred
    ∗ channel c
    ∗ public uid
    ∗ minted uid
    ∗ minted pw
    ∗ □(public pw ↔ ▷ □ False)
    ∗ ∀ t : term, ⌜t ∈ fresh⌝ -∗ minted t
  }}} Client.session uid c pw {{{ x , RET (repr x) ; SK_result x fresh }}}.
Proof.
iIntros "%ϕ (#Cryptis & #Hpredrw & #HpredA_u & #HpredA_s & #HpredSK & #HpredK
  & #Hpredα & #SpredAuth & #Hc & #pubuid & #minteduid & #mintedpw & #privpw &
  #Hfresh) Hhl".
wp_lam; wp_pures.
wp_apply (wp_mk_nonce_fresh fresh (fun _ => False)%I (fun t => opaque_secret t)%I) => //.
iIntros "%x_u %Hfreshx_u #Hmintedx_u #Hprivatex_u #Hexpx_u #Hexpx_uV Htokenx_u".
wp_pures.
wp_apply (wp_mk_nonce_fresh fresh (fun _ => False)%I (fun _ => True)%I) => //.
iIntros "%r %Hfreshr #Hmintedr #Hprivater #Hexpr #HexprV Htokenr".
wp_pures.
wp_apply wp_H'; wp_apply wp_texp; wp_pures.
wp_apply wp_texp; wp_list; wp_term_of_list; wp_pures.
set m1 := Spec.of_list _.
wp_apply wp_send => //.
  do !rewrite public_of_list /=.
  do !iSplit => //.
  - iApply public_TExp_iff.
      by [].
      by [].
      by [].
      by exact: (negb_is_mul_nonce r).
    do !iSplit => //.
    + by rewrite minted_THash minted_tag.
    + iApply exp_pred_intro1.
      by iApply "Hexpr".
    + iModIntro; iIntros "#p".
      by iApply (public_THashIS with "Hpredα") => //.
  - iApply public_TExp_iff.
      by [].
      by [].
      by [].
      by exact: (negb_is_mul_nonce x_u).
    do !iSplit => //.
    + by iApply minted_TInt.
    + iApply exp_pred_intro1.
      iApply "Hexpx_u"; iPureIntro.
      have Nm : negb (is_mul x_u) := negb_is_mul_nonce x_u.
      rewrite (_ : TExp g x_u = TExpN g [TNonce x_u]); last by rewrite /TExpN TMulN1.
      by rewrite exps_TExpN; [by [] | by [] | by [] | by [] | exact: invs_canceled1 Nm].
    + by rewrite public_TInt; auto.
wp_pures.
wp_apply wp_recv => //.
iIntros "%m2 #pubm2".
iAssert (minted m2) as "minm2". by iApply public_minted.
wp_list_of_term m2; wp_pures => //.
  1: wp_list_match => [β X_s envelope A_s -> | _].
  1, 2: wp_pures.
  2, 3: by iApply ("Hhl" $! None); iModIntro; iSplit.
wp_apply wp_hl_inv_aux_term; first by exact: (negb_is_mul_nonce r).
wp_apply wp_texp; wp_list; wp_apply wp_H.
wp_apply wp_derive_senc_key; set k := SEncKey _.
wp_pures; wp_lam; wp_pures.
rewrite minted_of_list public_of_list => /=.
iDestruct "minm2" as "(_ & minX_s & minenv & _)".
iDestruct "pubm2" as "(_ & _ & pubenv & pubA_s & _)".
wp_apply wp_sdec => //; iSplit; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iSplit.
iIntros "%clear #minclear [#pubkey | #envpred] _".
  rewrite /k public_senc_key.
  iPoseProof (public_THashE with "Hpredrw pubkey") as "[contra | [_ contra]]";
      rewrite bi.intuitionistically_False; last first.
    by wp_pures.
  rewrite public_of_list /=.
  iDestruct "contra" as "(contra & _ & _)".
  iPoseProof ("privpw" with "contra") as "?".
  by wp_pures.
iDestruct "envpred" as "(%p_u & %P_u & %P_s & -> & Hopaquepair)".
wp_pures.
wp_list_of_term_eq clear Hclear; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iSplit.
apply Spec.of_list_inj in Hclear.
rewrite -Hclear.
wp_pures.
wp_list_match => [p_u' P_u' P_s' H | _]; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iSplit.
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
wp_eq_term eq_A_s => //=; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iSplit.
wp_pures; wp_list.
wp_apply wp_prf.
wp_pures.
wp_apply wp_send => //.
  iApply public_THashIS; eauto.
  - rewrite !minted_of_list /=.
    do !iSplit => //.
    + iApply minted_hash_listI; rewrite /=; iSplit => //.
      by iApply (minted_hmqv_K with
                   "minp_u Hmintedx_u mintedd minP_s minX_s mintede").
    + iApply minted_hash_listI; rewrite /=; do !iSplit => //.
      iApply all_minted_TExp; iSplit => //.
      by iApply minted_hash_resultI.
  - iNext; iModIntro.
    iExists P_s, p_u, X_s, x_u,
        (hash_result "d" (Spec.of_list [TExp g x_u; P_s])),
        (hash_result "e" (Spec.of_list [X_s; P_u])),
        (hash_result "ssid'" (Spec.of_list [uid; TExp (hash_result "α" pw) r])).
    by do !iSplit => //.
wp_pures; wp_list; wp_term_of_list; wp_pures.
set SK := (Spec.of_list [uid; _] : term).
iApply ("Hhl" $! (Some SK)).
iModIntro; iSplit.
  rewrite /SK_priv /SK public_of_list /=.
  iSplit; iIntros "contra".
  - iDestruct "contra" as "(_ & contra & _)".
    iDestruct (public_THashE with "HpredSK contra") as "[contra | [_ contra]]" => //.
    rewrite public_of_list.
    iDestruct "contra" as "[contra _]".
    iDestruct (public_THashE with "HpredK contra") as "[contra | [_ contra]]" => //.
    rewrite public_of_list.
    iDestruct "contra" as "(contra & _)".
    iDestruct "Hopaquepair" as
        "(%p_s & -> & %Hfreshp_u & _ & _ & _ & #pred_p_u & #pred_p_s
          & #priv_p_u & #priv_p_s)".
    (* The client's static private key and the server's are distinct: [p_u] is
       not a subterm of [P_s = g^p_s]. *)
    have p_u_s : p_u ≠ p_s.
      move=> e; apply: Hfreshp_u; rewrite e.
      apply/subtermsP.
      rewrite (_ : TExp g p_s = TExpN g [TNonce p_s]); last by rewrite /TExpN TMulN1.
      have Nm : negb (is_mul p_s) := negb_is_mul_nonce p_s.
      rewrite subtermsE //; last exact: invs_canceled1 Nm.
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
    iEval (rewrite public_gfactors) in "contra".
    iDestruct "contra" as "[_ #fs]".
    have p_u_sT : TNonce p_u ≠ TNonce p_s by case=> /p_u_s.
    iApply (public_opaque_secret_gen _ p_u_sT in_pu in_ps with
              "priv_p_u pred_p_u priv_p_s pred_p_s").
    by iApply (big_sepL_elem_of with "fs").
  - do !iSplit => //.
    iApply (public_THashIS with "HpredSK") => //.
    iApply minted_of_listI; rewrite /=; do !iSplit => //.
    + iApply minted_hash_listI; rewrite /=; iSplit => //.
      by iApply (minted_hmqv_K with
                   "minp_u Hmintedx_u mintedd minP_s minX_s mintede").
    + iApply minted_hash_listI; rewrite /=; do !iSplit => //.
      iApply all_minted_TExp; iSplit => //.
      by iApply minted_hash_resultI.
iSplit.
- iPureIntro => /Hfreshr; apply.
  rewrite /SK.
  apply subterm_of_list.
  clear SK eq_A_s k m1 m2.
  set SK := hash_result "SK" _; exists SK.
  rewrite !elem_of_cons /SK.
  split.
    by right; left.
  apply STHash.
  apply subterm_of_tag.
  apply subterm_of_list.
  set ssid' := hash_result "ssid'" _; exists ssid'.
  rewrite !elem_of_cons /ssid'.
  split.
    by right; left.
  apply STHash.
  apply subterm_of_tag.
  apply subterm_of_list.
  set β' := TExp _ _; exists β'.
  rewrite !elem_of_cons /β'.
  split.
    by right; left.
  apply: subterm_TExp_exp; [done | done | done | exact: (negb_is_mul_nonce r) | exact: STRefl].
- iApply minted_of_listI; rewrite /=; do !iSplit => //.
  iApply minted_hash_listI; rewrite /=; do !iSplit => //.
  + iApply minted_hash_listI; rewrite /=; iSplit => //.
    by iApply (minted_hmqv_K with
                 "minp_u Hmintedx_u mintedd minP_s minX_s mintede").
  + iApply minted_hash_listI; rewrite /=; do !iSplit => //.
    iApply all_minted_TExp; iSplit => //.
    by iApply minted_hash_resultI.
Qed.

End Opaque.
