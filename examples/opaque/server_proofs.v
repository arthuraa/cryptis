From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics role.
From cryptis.lib Require Import dh hmqv.

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

Definition opaque_file (pw : term) (file : val) : iProp :=
  ∃ (k_s : nonce) (p_s : nonce) P_u envelope,
    ⌜file = Spec.of_list [TNonce k_s; TNonce p_s; TExp g p_s; P_u; envelope]⌝
    ∗ minted k_s ∗ □(public k_s ↔ ▷ □ False) ∗
    □(∀ t' : term, exp_pred_base k_s t' ↔ ▷ □ True) ∗
    □(∀ t' : term, exp_pred_base (TInv k_s) t' ↔ ▷ False) ∗
    public (TExp g p_s) ∗ public envelope ∗
    opaque_public_private_pair pw p_s P_u.

(** The database, with the password each file was registered with. *)
Definition opaque_db (pw_of : term → term) (db : gmap term val) : iProp :=
[∗ map] (k : term) ↦ (file : val) ∈ db,
public k ∗ opaque_file (pw_of k) file.

Lemma wp_make_file (pw : term) :
  {{{
    cryptis_ctx
    ∗ opaque_ctx
    ∗ minted pw
  }}} Server.make_file pw {{{ file, RET (repr file); opaque_file pw file }}}.
Proof.
iIntros "%ϕ (#cryptis & #ctx & #Hmintedpw) post".
iPoseProof "ctx" as "(#Hhashpred & _ & _ & _ & _ & _ & #Hsencpred)".
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
(* The long-term keys are exactly as secret as the password. *)
wp_apply (wp_mk_nonce_freshN ∅ (fun _ => public pw)%I dh_key_share
                               (fun t =>  {[(TInv t)]})) => //.
- by iIntros "%_ %contra".
- iIntros "%t".
  rewrite big_sepS_singleton minted_TInv.
  by iModIntro; auto.
iIntros "%p_s _ #Hmintedp_s #Hprivatep_s #Hexpp_s #Hexpp_sV Htokenp_sV".
rewrite big_sepS_singleton.
wp_pures.
(* Fresh against [p_s] itself: distinctness is all the pair predicate records. *)
wp_apply (wp_mk_nonce_freshN {[TNonce p_s]} (fun _ => public pw)%I dh_key_share
                                              (fun t =>  {[(TInv t)]})) => //.
- by iIntros "%"; rewrite elem_of_singleton; iIntros "->".
- iIntros "%t".
  rewrite big_sepS_singleton minted_TInv.
  by iModIntro; auto.
iIntros "%p_u %Hfreshp_u #Hmintedp_u #Hprivatep_u #Hexpp_u #Hexpp_uV Htokenp_uV".
rewrite big_sepS_singleton.
have Hneq : p_u ≠ p_s.
  move=> e; apply: (Hfreshp_u (TNonce p_s)); first by rewrite elem_of_singleton.
  by rewrite e.
wp_pures.
wp_apply wp_texp; wp_pures.
wp_apply wp_texp.
wp_list; wp_term_of_list.
wp_lam; wp_pures.
wp_apply wp_senc'.
wp_list; wp_term_of_list.
have Nm_s : negb (is_mul (TNonce p_s)) by [].
have Nm_u : negb (is_mul (TNonce p_u)) by [].
iAssert (public g) as "#pubg"; first by iApply public_TInt.
iAssert (public (TExp g p_s)) as "#pubP_s".
  by iApply (public_dh_share gNX gNm gNi Nm_s with "pubg Hmintedp_s Hexpp_s").
iAssert (public (TExp g p_u)) as "#pubP_u".
  by iApply (public_dh_share gNX gNm gNi Nm_u with "pubg Hmintedp_u Hexpp_u").
iApply "post".
iExists k_s, p_s, (TExp g p_u), _.
do !iSplit => //.
- iApply (public_sencIS _ (opN.@"AuthEnc") envelope_pred _) => //.
  1: rewrite minted_senc minted_THash minted_tag.
  1, 2: iApply minted_of_list; do !iSplit => //; iApply minted_TExp.
  all: try by [].
  all: try (iSplit => //).
  all: try by rewrite minted_THash minted_tag.
  all: try by iApply minted_TInt.
  iModIntro.
  iExists pw, (TExp (hash_result "α" pw) k_s), p_u, (TExp g p_s).
  do !iSplit => //.
  iExists p_s.
  by do !iSplit => //.
  iModIntro.
  rewrite public_senc_key.
  iIntros "#Hcompromise".
  (* A public envelope key is a public password, which makes both long-term
     keys public. *)
  iAssert (▷ □ public pw)%I as "#Hpubpw".
  { iDestruct (public_THashE with "Hhashpred Hcompromise") as "[Hpub | [_ contra]]".
    - rewrite public_of_list /=.
      iDestruct "Hpub" as "[#? _]".
      by iIntros "!> !>".
    - by iNext; iDestruct "contra" as "[]". }
  iDestruct "Hprivatep_u" as "[_ Hprivatep_u]".
  iDestruct ("Hprivatep_u" with "Hpubpw") as "#Hpubp_u".
  iDestruct "Hprivatep_s" as "[_ Hprivatep_s]".
  iDestruct ("Hprivatep_s" with "Hpubpw") as "#Hpubp_s".
  rewrite public_of_list /=.
  by do !iSplit => //.
- iExists p_u.
  by do !iSplit => //.
Qed.

Lemma wp_server_session (db c : val) pw_of (alist : gmap term val) φ :
{{{ cryptis_ctx
    ∗ opaque_ctx
    ∗ opaque_pred φ
    ∗ channel c
    ∗ AList.is_alist db alist
    ∗ opaque_db pw_of alist
    ∗ (∀ si, term_token (si_sshare si) (↑opN.@"res") ={⊤}=∗
             φ si Init ∗ φ si Resp)
  }}}
    Server.session db c
  {{{ r, RET (repr r);
      AList.is_alist db alist ∗
      (⌜r = None⌝ ∨ ∃ si,
         ⌜r = Some (si_result si)⌝ ∗
         ⌜server_session si⌝ ∗
         opaque_session_for (si_uid si) si ∗
         (∃ (k_s p_s : nonce) envelope,
            ⌜alist !! si_uid si =
             Some (Spec.of_list [TNonce k_s; TNonce p_s;
                                 si_skey si; si_ckey si; envelope] : val)⌝) ∗
         session (pw_of (si_uid si)) si ∗
         release_token (si_sshare si) ∗
         term_token (si_sshare si) (⊤ ∖ ↑opN) ∗
         φ si Resp) }}}.
Proof.
iIntros "%ϕ".
rewrite /opaque_db big_sepM_forall.
iIntros "(#Cryptis & (_ & #HpredA_s & #HpredA_u & #HpredSK & #HpredK & _ & _)
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
    "[_ (%k_s & %p_s & %P_u & %envelope &
         %e & #Hmk_s & #Hprivk_s & #Hexpk_s & #Hexpk_sV &
         #HpubP_s & #Hpenvelope & %p_u & %HP_u & %p_s_u &
         #HpubP_u & #Hminp_s & #Hminp_u & #Hexpp_s & #Hexpp_u & #Hprivp_s
         & #Hprivp_u)]".
set P_s := TExp g p_s.
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
iAssert (minted uid) as "#minuid". by iApply public_minted.
iAssert (minted α) as "#minα". by iApply public_minted.
iAssert (minted X_u) as "#minX_u". by iApply public_minted.
iAssert (minted P_s) as "#minP_s". by iApply public_minted.
iAssert (minted (TExp g p_u)) as "#minP_u". by iApply public_minted.
(* The fresh ephemeral comes with a token on the server's share, as in
   [iso_dh]; freshness against the peer's share keeps the two ephemerals
   apart. *)
wp_apply (wp_mk_nonce_freshN {[X_u]} (fun _ => False)%I (fun t => dh_key_share t)%I
            (fun t => {[TExp g t]})) => //.
  by iIntros "%"; rewrite elem_of_singleton; iIntros "->".
  iIntros "%t"; rewrite big_sepS_singleton; iModIntro; iSplit.
  - iIntros "#?"; by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
  - rewrite (minted_TExp t) //; by iIntros "[_ ?]".
iIntros "%x_s %fresh_x_s #Hmintedx_s #Hprivatex_s #Hexpx_s #Hexpx_sV tok_Xs".
rewrite big_sepS_singleton.
have X_u_x_s : X_u ≠ TExp g x_s.
  move=> e; apply: (fresh_x_s X_u); first by rewrite elem_of_singleton.
  rewrite e; apply: subterm_exps.
  by rewrite (exps_TExp_g gNX gNm gNi) factors_Nmul // list_elem_of_singleton.
iPoseProof (eph_seed_intro with "Hprivatex_s Hexpx_s") as "#eph_s".
set si := server_si uid α X_u (TExp g p_u) p_s x_s.
wp_pures.
wp_apply wp_texp; wp_pures.
wp_apply wp_texp; wp_pures.
(* [d := H "d" [X_u; P_s]] and [e := H "e" [X_s; P_u]] *)
wp_list; wp_apply wp_H; wp_pures.
wp_list; wp_apply wp_H; wp_pures.
wp_apply wp_hmqv_ke; wp_list; wp_apply wp_H; wp_list.
wp_apply wp_H; wp_list.
wp_apply wp_prf; wp_list.
wp_apply wp_prf; wp_list.
wp_term_of_list; wp_pures.
iAssert (minted (hash_result "d" (Spec.of_list [X_u; P_s]))) as "#mintedd".
{ iApply minted_hash_result; iApply minted_of_list => /=.
  by do !iSplit => //. }
iAssert (minted (hash_result "e" (Spec.of_list [TExp g x_s; TExp g p_u])))
  as "#mintede".
{ iApply minted_hash_result; iApply minted_of_list => /=; do !iSplit => //=.
  by iApply all_minted_TExp; iSplit => //; iApply minted_TInt. }
iAssert (minted (si_key si)) as "#mintedSK".
{ iApply minted_hash_result; iApply minted_of_list; rewrite /=; do !iSplit => //.
  - iApply minted_hash_result; rewrite minted_of_list /=; iSplit => //.
    by iApply minted_hmqv_K => //.
  - iEval (rewrite minted_hash_result minted_of_list /=).
    by eauto. }
(* The caller's resources for this session come from the [↑opN.@"res"] slice
   of the token on the server's share; the client's copy is escrowed at once.
   The part of the token outside [↑opN] goes back to the caller. *)
iDestruct (term_token_difference (TExp g x_s) (↑opN.@"res") with "tok_Xs")
  as "[tok_res tok_Xs]"; first solve_ndisj.
iMod ("res" $! si with "tok_res") as "[res_I res_R]".
iMod (opaque_ready_alloc with "N_φ res_I") as "#ready".
iDestruct (term_token_difference (TExp g x_s) (↑opN.@"released") with "tok_Xs")
  as "[tok_rel tok_Xs]"; first solve_ndisj.
iDestruct (term_token_drop (⊤ ∖ ↑opN) with "tok_Xs") as "tok_Xs";
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
  - iApply public_TExp_iff => //.
    do !iSplit => //.
    + by iApply minted_TInt.
    + iApply exp_pred_intro1.
      iApply "Hexpx_s"; iPureIntro.
      rewrite (_ : TExp g x_s = TExpN g [TNonce x_s]); last by rewrite /TExpN TMulN1.
      by rewrite exps_TExpN //; exact: invs_canceled1.
    + by rewrite public_TInt; auto.
  - iApply public_THashIS => //.
      iEval (rewrite minted_of_list /=); do !iSplit => //.
      + iEval (rewrite minted_hash_result minted_of_list /=); iSplit => //.
        by iApply (minted_hmqv_K with
                     "Hminp_s Hmintedx_s mintede minP_u minX_u mintedd").
      + iEval (rewrite minted_hash_result minted_of_list /=); do !iSplit => //;
        by iApply public_minted.
    iNext; iModIntro.
    iExists uid, α, X_u, p_u, p_s, x_s; rewrite /si_K /si_ssid /=.
    by do !iSplit => //.
wp_pures.
wp_apply (wp_recv with "Hc"); iIntros "%m3 #Hm3pub".
wp_list; wp_apply wp_prf.
wp_eq_term Heq; wp_pures; last first.
  by iApply ("Hhl" $! None); iModIntro; iFrame "Hdb"; iLeft.
iAssert (public (hash_result "A_u" (Spec.of_list [si_K si; si_ssid si])))
  as "#pubA_u"; first by rewrite -Heq.
(* A valid [A_u] was either forged -- then the key is public, and with it the
   password -- or produced by the honest client, which vouches for its
   ephemeral. *)
iAssert (public (Spec.of_list [si_K si; si_ssid si])
         ∨ ▷ □ A_u_pred (Spec.of_list [si_K si; si_ssid si]))%I as "#auth".
  by iDestruct (public_THashE with "HpredA_u pubA_u") as "[? | [_ ?]]"; eauto.
wp_list; wp_term_of_list; wp_pures.
have tags : "e"%string ≠ "d"%string by [].
iAssert (session (pw_of uid) si) as "#sess".
{ iDestruct "auth" as "[#p_t | #auth]".
  - iAssert (public (si_key si)) as "#p_SK".
    { iApply public_THash; iLeft. by iApply public_tag. }
    iSplit => //.
    iSplit; first by iIntros "!> _".
    iLeft; iSplit => //.
    rewrite public_of_list /=.
    iDestruct "p_t" as "[p_K _]".
    iDestruct (public_THashE with "HpredK p_K") as "[p_t | [_ contra]]";
      last by iNext; iDestruct "contra" as "[]".
    rewrite public_of_list /=.
    iDestruct "p_t" as "(p_K' & _)".
    iAssert (▷ □ public (pw_of uid))%I as "#p_pw".
    { iDestruct (@public_hmqv_K_static _ _ _ opN g "e" "d" p_s x_s p_u P_s X_u
                   gNX gNm gNi tags p_s_u with "Hexpp_s Hexpp_u p_K'")
        as "[p|p]".
      - by iApply "Hprivp_s".
      - by iApply "Hprivp_u". }
    by iNext.
  - iDestruct "auth" as "(%si' & %x_u & %e & %ss' & %eX & #eph_u)".
    have ss : server_session si by exists uid, α, X_u, p_u, p_s, x_s.
    have ek : si_key si = si_key si' by rewrite {2}/si_key -e.
    have [_ eXu] := server_session_key_inj ss ss' ek.
    rewrite /si /= eX in eXu.
    have x_u_s : x_u ≠ x_s.
      by move=> e'; apply: X_u_x_s; rewrite eXu e'.
    subst X_u.
    iPoseProof (honest_session_ok uid α p_u p_s x_u_s
                  with "HpredSK HpredK eph_u eph_s mintedSK") as "#[ok1 ok2]".
    iSplit => //.
    iSplit; first by iApply "ok2".
    by iRight. }
iModIntro.
iApply ("Hhl" $! (Some (si_result si))).
iFrame "Hdb".
iRight; iExists si.
have -> : si_sshare si = TExp g x_s by [].
have -> : si_uid si = uid by [].
rewrite /release_token.
iFrame "tok_Xs tok_rel res_R".
iSplit; first by [].
iSplit; first by iPureIntro; exists uid, α, X_u, p_u, p_s, x_s.
iSplit.
  by do !iSplit => //.
iSplit.
  iExists k_s, p_s, envelope; iPureIntro.
  by rewrite /si /server_si /= db_uid.
by iApply "sess".
Qed.

End Opaque.
