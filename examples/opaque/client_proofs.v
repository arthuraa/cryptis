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
  }}} Client.session uid c pw
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨ ∃ si,
        ⌜r = Some (si_result si)⌝ ∗
        opaque_session_for uid si ∗
        session pw si ∗
        release_token (si_blind si) ∗
        term_token (si_blind si) (⊤ ∖ ↑opN) ∗
        (public (si_key si) ∨ φ si Init) }}}.
Proof.
iIntros "%ϕ (#Cryptis & (#Hpredrw & #HpredA_s & #HpredA_u & #HpredSK & #HpredK
  & #Hpredα & #SpredAuth) & #N_φ & #Hc & #pubuid & #mintedpw) Hhl".
iAssert (minted uid) as "#minteduid"; first by iApply public_minted.
wp_lam; wp_pures.
wp_apply (wp_mk_nonce_freshN ∅
            (fun x => term_meta (TExp g x) (opN.@"failed") true)%I
            (fun t => dh_key_share t)%I
            (fun t => {[TExp g t]})) => //.
  by iIntros "% %contra".
  iIntros "%t"; rewrite big_sepS_singleton; iModIntro; iSplit.
  - iIntros "#?"; by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
  - rewrite (minted_TExp t) //; by iIntros "[_ ?]".
iIntros "%x_u _ #Hmintedx_u #Hprivatex_u #Hexpx_u #Hexpx_uV tok_Xu".
rewrite big_sepS_singleton.
iDestruct (term_token_difference (TExp g x_u) (↑opN.@"failed") with "tok_Xu")
  as "[tok_failed _]"; first solve_ndisj.
wp_pures.
(* The blind [α] is the client's share: the server keys the resource escrow
   on its token, so it is minted together with [r]; the part outside [↑opN]
   goes back to the caller. *)
wp_apply (wp_mk_nonce_freshN ∅ (fun _ => False)%I (fun _ => True)%I
            (client_fresh_set pw)) => //.
- by iIntros "% %contra".
- by iApply client_fresh_set_minted.
iIntros "%r _ #Hmintedr #Hprivater #Hexpr #HexprV tok_α".
rewrite /client_fresh_set big_sepS_singleton.
iAssert (minted (TExp (hash_result "α" pw) r)) as "#mintedα".
  by iApply all_minted_TExp; iSplit => //; iApply minted_hash_result.
set α := TExp (hash_result "α" pw) r.
wp_pures.
iDestruct (term_token_difference α (↑opN.@"ready") with "tok_α")
  as "[tok_ready tok_α]"; first solve_ndisj.
iDestruct (term_token_difference α (↑opN.@"released") with "tok_α")
  as "[tok_rel tok_α]"; first solve_ndisj.
iDestruct (term_token_drop (⊤ ∖ ↑opN) with "tok_α") as "tok_α";
  first solve_ndisj.
iAssert (public α) as "#pubα".
{ iApply public_TExp_iff => //.
  do !iSplit => //.
  - by rewrite minted_THash minted_tag.
  - iApply exp_pred_intro1.
    by iApply "Hexpr".
  - iModIntro; iIntros "#p".
    by iApply (public_THashIS with "Hpredα") => //. }
iAssert (public (TExp g x_u)) as "#pubX_u".
{ iApply public_TExp_iff => //.
  do !iSplit => //.
  - by iApply minted_TInt.
  - iApply exp_pred_intro1.
    iApply "Hexpx_u"; iPureIntro.
    rewrite (_ : TExp g x_u = TExpN g [TNonce x_u]); last by rewrite /TExpN TMulN1.
    by rewrite exps_TExpN //; exact: invs_canceled1.
  - by rewrite public_TInt; auto. }
wp_apply wp_H'; wp_apply wp_texp; wp_pures.
wp_apply wp_texp; wp_list; wp_term_of_list; wp_pures.
set m1 := Spec.of_list _.
wp_apply wp_send => //.
  iApply public_of_list => /=.
  by do !iSplit => //.
wp_pures.
wp_apply wp_recv => //.
iIntros "%m2 #pubm2".
iAssert (minted m2) as "minm2". by iApply public_minted.
wp_list_of_term m2; wp_pures => //.
  1: wp_list_match => [β X_s envelope A_s -> | _].
  1, 2: wp_pures.
  2, 3: by iApply ("Hhl" $! None); iModIntro; iLeft.
wp_apply wp_tinv => //.
wp_apply wp_texp; wp_list; wp_apply wp_H.
wp_apply wp_derive_senc_key; set k := SEncKey _.
wp_pures; wp_lam; wp_pures.
rewrite minted_of_list public_of_list => /=.
iDestruct "minm2" as "(_ & minX_s & minenv & _)".
iDestruct "pubm2" as "(_ & #pubX_s & #pubenv & #pubA_s & _)".
wp_apply wp_sdec => //; iSplit; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iLeft.
iIntros "%clear #minclear #decr #keyclear".
(* Either the envelope key, hence the password, is public, or the envelope is
   the honest registration. *)
iAssert (▷ public pw ∗ public clear
         ∨ ∃ (p_u : nonce) P_s,
             ⌜clear = Spec.of_list [TNonce p_u; TExp g p_u; P_s]⌝ ∗
             public (TExp g p_u) ∗
             opaque_public_private_pair pw p_u P_s)%I as "#env".
{ iDestruct "decr" as "[#pubkey | #envpred]".
  - iLeft; iSplit; last by iApply "keyclear".
    iEval (rewrite /k public_senc_key) in "pubkey".
    iDestruct (public_THashE with "Hpredrw pubkey") as "[p_l | [_ contra]]".
    + iEval (rewrite public_of_list /=) in "p_l".
      iDestruct "p_l" as "[#? _]". by iNext.
    + by iNext; iDestruct "contra" as "[]".
  - iDestruct "envpred"
      as "(%pw' & %β' & %p_u & %P_s & %ek & %eclear & #pubP_u & #pair)".
    move: ek; rewrite /k; case=> /Spec.tag_inj [] _ /Spec.of_list_inj [] epw _.
    subst pw'.
    iRight. iExists p_u, P_s. by do !iSplit => //. }
iClear "decr keyclear".
wp_pures.
wp_list_of_term_eq clear_l Hclear; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iLeft.
wp_pures.
wp_list_match => [p_u' P_u' P_s' e_l | _]; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iLeft.
have eclear : clear = Spec.of_list [p_u'; P_u'; P_s'].
  by rewrite Hclear; congruence.
iEval (rewrite eclear minted_of_list /=) in "minclear".
iDestruct "minclear" as "(minp_u & minP_u & minP_s & _)".
iAssert (▷ public pw ∗ public p_u' ∗ public P_u' ∗ public P_s'
         ∨ ∃ (p_u : nonce),
             ⌜p_u' = TNonce p_u⌝ ∗ ⌜P_u' = TExp g p_u⌝ ∗
             public P_u' ∗ opaque_public_private_pair pw p_u P_s')%I as "#env'".
{ iDestruct "env" as "[[#p_pw #p_clear] | (%p_u & %P_s & %e & #pubP_u & #pair)]".
  - iLeft. iEval (rewrite eclear public_of_list /=) in "p_clear".
    iDestruct "p_clear" as "(#? & #? & #? & _)". by do !iSplit => //.
  - move: e; rewrite eclear => /Spec.of_list_inj [] -> -> ->.
    iRight. iExists p_u. by do !iSplit => //. }
iClear "env".
wp_pures.
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
iAssert (minted (hash_result "d" (Spec.of_list [TExp g x_u; P_s'])))
  as "#mintedd".
  rewrite minted_hash_result minted_of_list /=; do !iSplit => //.
  by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
iAssert (minted (hash_result "e" (Spec.of_list [X_s; P_u']))) as "#mintede".
  iApply minted_hash_result; iApply minted_of_list => /=.
  by do !iSplit.
set d := hash_result "d" (Spec.of_list [TExp g x_u; P_s']).
set e := hash_result "e" (Spec.of_list [X_s; P_u']).
set K := hash_result "K" (Spec.of_list [hmqv_K p_u' x_u d P_s' X_s e]).
set ssid' := hash_result "ssid'" (Spec.of_list [uid; α]).
set SK := hash_result "SK" (Spec.of_list [K; ssid']).
iAssert (minted K) as "#mintedK".
  iApply minted_hash_result; iApply minted_of_list => /=.
  iSplit => //=.
  by iApply minted_hmqv_K.
iAssert (minted ssid') as "#mintedssid".
  iApply minted_hash_result; iApply minted_of_list => /=.
  by do !iSplit => //.
iAssert (public ssid') as "#pubssid".
  iApply public_THash; iLeft; iApply public_tag.
  iApply public_of_list => /=.
  by do !iSplit => //.
iAssert (minted SK) as "#mintedSK".
  iApply minted_hash_result; iApply minted_of_list => /=.
  by do !iSplit => //.
wp_eq_term eq_A_s => //=; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iLeft.
subst A_s.
(* A valid [A_s] was either forged -- then the key is public, and with it, one
   way or another, the password -- or produced by the honest server, which
   vouches for its ephemeral. *)
iAssert (public (Spec.of_list [K; ssid'])
         ∨ ▷ □ A_s_pred (Spec.of_list [K; ssid']))%I as "#auth".
  by iDestruct (public_THashE with "HpredA_s pubA_s") as "[? | [_ ?]]"; eauto.
wp_pures; wp_list.
wp_apply wp_prf.
wp_pures.
have tags : "d"%string ≠ "e"%string by [].
iAssert (|={⊤}=> ∃ si, ⌜si_key si = SK⌝ ∗ ⌜uid = si_uid si⌝ ∗ ⌜α = si_blind si⌝ ∗
           public (si_ckey si) ∗ public (si_skey si) ∗
           session pw si ∗
           (public (si_key si) ∨ ▷ φ si Init) ∗
           (public (Spec.of_list [K; ssid'])
            ∨ ▷ □ A_u_pred (Spec.of_list [K; ssid'])))%I
  with "[tok_ready tok_failed]"
  as ">(%si & %eSK & %euid & %eα & #pubck & #pubsk & #sess & res & #authu)".
{ iDestruct "auth" as "[#p_t | #auth]".
  - (* Forged: the key is public. *)
    iAssert (public SK) as "#p_SK".
    { iApply public_THash; iLeft. by iApply public_tag. }
    iAssert (public K) as "#p_K".
    { iEval (rewrite public_of_list /=) in "p_t". by iDestruct "p_t" as "[#? _]". }
    iAssert (▷ public pw ∗ public P_u' ∗ public P_s')%I
      as "#(p_pw & pubP_u' & pubP_s')".
    { iDestruct "env'" as "[(#? & _ & #? & #?) | (%p_u & %ep & %eP & #pubP_u & #pair)]";
        first by do !iSplit => //.
      iPoseProof "pair" as
        "(%p_s & %eP_s & %p_u_s & #pubP_s & _ & _ & #pred_p_u & #pred_p_s
          & #priv_p_u & #priv_p_s)".
      subst p_u' P_u' P_s'.
      iSplit; last by iSplit.
      (* The static-static factor is a group factor of the key, and its two
         exponents are the long-term keys, which are as secret as the
         password. *)
      have [gf [_ [in_pu in_ps]]] :=
        @hmqv_key_gfactors p_u p_s x_u "d" "e" (TExp g p_u) X_s tags.
      have p_u_sT : TNonce p_u ≠ TNonce p_s by case=> /p_u_s.
      iDestruct (public_THashE with "HpredK p_K") as "[p_t' | [_ contra]]";
        last by iNext; iDestruct "contra" as "[]".
      iEval (rewrite public_of_list /=) in "p_t'".
      iDestruct "p_t'" as "(p_K' & _)".
      iEval (rewrite public_gfactors) in "p_K'".
      iDestruct "p_K'" as "[_ #fs]".
      iAssert (▷ □ public pw)%I as "#p_pw".
      { iApply (public_dh_secret_gen _ p_u_sT in_pu in_ps with
                  "priv_p_u pred_p_u priv_p_s pred_p_s").
        by iApply (big_sepL_elem_of with "fs"). }
      by iNext. }
    iModIntro.
    iExists (client_si uid P_u' P_s' α x_u X_s p_u').
    have e1 : si_key (client_si uid P_u' P_s' α x_u X_s p_u') = SK by [].
    have e2 : si_ckey (client_si uid P_u' P_s' α x_u X_s p_u') = P_u' by [].
    have e3 : si_skey (client_si uid P_u' P_s' α x_u X_s p_u') = P_s' by [].
    have e4 : si_uid (client_si uid P_u' P_s' α x_u X_s p_u') = uid by [].
    have e5 : si_blind (client_si uid P_u' P_s' α x_u X_s p_u') = α by [].
    rewrite /session /compromised e1 e2 e3 e4 e5.
    do 3?(iSplit; first by []).
    iSplit => //. iSplit => //.
    iSplit.
    { iSplit => //. iSplit; first by iIntros "!> _".
      by iLeft; iSplit. }
    iSplit; first by iLeft.
    by iLeft.
  - (* Honest server. *)
    iDestruct "auth" as "(%uid_s & %α_s & %X_u_s & %p_u_s & %p_s_s & %x_s
                          & %e_si & %X_u_x_s & #eph_s & #pubck & #pubsk & #ready)".
    set si_s := server_si uid_s α_s X_u_s (TExp g p_u_s) p_s_s x_s.
    have eSK : si_key si_s = SK by rewrite /si_key /SK e_si.
    move: (e_si) => /Spec.of_list_inj /(f_equal (λ l, nth 0 l (TInt 0))) /= eK.
    move: eK; rewrite /K /si_K => /hash_result_inj [] _ /Spec.of_list_inj.
    move=> /(f_equal (λ l, nth 0 l (TInt 0))) /= eKK.
    move: (e_si) => /Spec.of_list_inj /(f_equal (λ l, nth 1 l (TInt 0))) /= essid.
    move: essid; rewrite /ssid' /si_ssid => /hash_result_inj [] _ /Spec.of_list_inj.
    move=> [] euid eα.
    iDestruct "env'" as "[(#p_pw & #pubp_u' & #pubP_u' & #pubP_s')
                          | (%p_u & %ep & %eP & #pubP_u' & #pair)]".
    + (* Forged envelope: the password is public, so make the ephemeral public
         too, and with it the key. *)
      iMod (term_meta_set (opN.@"failed") true with "tok_failed") as "#failed";
        first solve_ndisj.
      iAssert (public (TNonce x_u)) as "#p_x_u".
      { iDestruct "Hprivatex_u" as "[_ s]". iApply "s". by iIntros "!> !>". }
      iAssert (public d) as "#p_d".
      { iApply public_THash; iLeft; iApply public_tag.
        iApply public_of_list => /=. by do !iSplit => //. }
      iAssert (public e) as "#p_e".
      { iApply public_THash; iLeft; iApply public_tag.
        iApply public_of_list => /=. by do !iSplit => //. }
      iAssert (public (hmqv_K p_u' x_u d P_s' X_s e)) as "#p_hK".
      { rewrite /hmqv_K /hmqv_Y.
        iAssert (public (TGMulN [X_s; TExp P_s' e])) as "#p_Y".
        { iApply public_TGMulN2 => //. by iApply public_TExp. }
        iApply public_TGMulN2; iApply public_TExp => //.
        by iApply public_TMulN2. }
      iAssert (public K) as "#p_K".
      { iApply public_THash; iLeft; iApply public_tag.
        iApply public_of_list => /=. by do !iSplit => //. }
      iAssert (public SK) as "#p_SK".
      { iApply public_THash; iLeft; iApply public_tag.
        iApply public_of_list => /=. by do !iSplit => //. }
      iModIntro.
      iExists si_s.
      rewrite /session /compromised eSK.
      do 3?(iSplit; first by []).
      iSplit => //. iSplit => //.
      iSplit.
      { iSplit => //. iSplit; first by iIntros "!> _".
        by iLeft; iSplit. }
      iSplit; first by iLeft.
      iLeft. iApply public_of_list => /=. by do !iSplit => //.
    + (* Honest envelope: both ephemerals are honest, so the key stays secret
         whatever happens to the password. *)
      subst p_u' P_u'.
      iPoseProof "pair" as
        "(%p_s & %eP_s & %p_u_s' & #pubP_s' & _ & _ & #pred_p_u & #pred_p_s
          & #priv_p_u & #priv_p_s)".
      subst P_s'.
      have [epa [epb [eXs eXu]]] :=
        @hmqv_K_inj' "d" "e" p_u x_u p_s p_u_s x_s p_s_s X_s X_u_s tags eKK.
      iMod (term_meta_set (opN.@"failed") false with "tok_failed") as "#failed";
        first solve_ndisj.
      iAssert (eph_seed x_u) as "#eph_u".
      { iSplit => //. iIntros "!> #p_x".
        iDestruct "Hprivatex_u" as "[s _]".
        iDestruct ("s" with "p_x") as "#contra". iNext.
        by iPoseProof (term_meta_agree with "failed contra") as "%". }
      have x_u_s : x_u ≠ x_s.
        by move=> e'; apply: X_u_x_s; rewrite eXu e'.
      subst X_u_s.
      iEval (rewrite -eSK) in "mintedSK".
      iPoseProof (honest_session_ok uid_s α_s p_u_s p_s_s x_u_s
                    with "HpredSK HpredK eph_u eph_s mintedSK") as "#[ok1 ok2]".
      iMod ("ready" with "N_φ [tok_ready]") as "res" => //.
        by rewrite /si_s /= -eα.
      iModIntro.
      iExists si_s.
      do 3?(iSplit; first by []).
      iSplit => //. iSplit => //.
      iSplit.
      { iSplit => //. iSplit; first by iApply "ok2". by iRight. }
      iSplit; first by iRight.
      iRight. iNext; iModIntro. iExists si_s, x_u.
      iSplit; first by [].
      iSplit; first by iPureIntro; exists uid_s, α_s, (TExp g x_u), p_u_s, p_s_s, x_s.
      by iSplit. }
wp_apply wp_send => //.
  iDestruct "authu" as "[#p_t | #authu]".
  - iApply public_THash; iLeft. by iApply public_tag.
  - iApply (public_THashIS with "HpredA_u [] authu").
    rewrite !minted_of_list /=. by do !iSplit => //.
wp_pures; wp_list; wp_term_of_list; wp_pures.
have -> : Spec.of_list [uid; SK] = si_result si.
  by rewrite /si_result eSK -euid.
iApply ("Hhl" $! (Some (si_result si))).
iModIntro; iRight; iExists si.
rewrite -eα /release_token.
iFrame "tok_α tok_rel res".
iSplit; first by [].
iSplit; first by rewrite /opaque_session_for -euid eSK; do !iSplit => //.
(* The steps above stripped the later off [compromised]. *)
iDestruct "sess" as "(#mSK & #rel & [[#p_pw #p_k] | #sec])".
- iSplit => //. iSplit => //. iLeft. by iSplit => //.
- iSplit => //. iSplit => //. by iRight.
Qed.

End Opaque.
