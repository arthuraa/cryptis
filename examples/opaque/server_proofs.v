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
iPoseProof "ctx" as "(#Hhashpred & _ & _ & _ & #Hsencpred)".
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
wp_apply (wp_mk_nonce_freshN ∅ (fun _ => public pw)%I dh_key_share
                               (fun t =>  {[(TInv t)]})) => //.
- by iIntros "%_ %contra".
- iIntros "%t".
  rewrite big_sepS_singleton minted_TInv.
  by iModIntro; auto.
iIntros "%p_u _ #Hmintedp_u #Hprivatep_u #Hexpp_u #Hexpp_uV Htokenp_uV".
rewrite big_sepS_singleton.
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
  by iApply (public_dh_share (g := g) I I I Nm_s
               with "pubg Hmintedp_s Hexpp_s").
iAssert (public (TExp g p_u)) as "#pubP_u".
  by iApply (public_dh_share (g := g) I I I Nm_u
               with "pubg Hmintedp_u Hexpp_u").
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
  iExists pw, (TExp (hash_result "H" pw) k_s), p_u, (TExp g p_s).
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

Lemma wp_server_session (db c : val) pw_of (alist : gmap term val) φ ψ :
{{{ cryptis_ctx
    ∗ opaque_ctx
    ∗ opaque_pred φ
    ∗ channel c
    ∗ AList.is_alist db alist
    ∗ opaque_db pw_of alist
    ∗ (∀ si (x_s : nonce),
         ⌜si_sshare si = TExp g x_s⌝ -∗
         secret x_s -∗
         term_token (si_sshare si) (↑opN.@"res") ={⊤}=∗
         φ si Init ∗ ψ x_s)
  }}}
    Server.session db c
  {{{ r, RET (repr r);
      AList.is_alist db alist ∗
      (⌜r = None⌝ ∨ ∃ si (x_s : nonce),
         ⌜r = Some (si_result si)⌝ ∗
         ⌜server_session si⌝ ∗
         ⌜si_sshare si = TExp g x_s⌝ ∗
         opaque_session_for (si_uid si) si ∗
         (∃ (k_s p_s : nonce) envelope,
            ⌜alist !! si_uid si =
             Some (Spec.of_list [TNonce k_s; TNonce p_s;
                                 si_skey si; si_ckey si; envelope] : val)⌝) ∗
         session (pw_of (si_uid si)) si ∗
         release_token (si_sshare si) ∗
         term_token (si_sshare si) (⊤ ∖ ↑opN) ∗
         ψ x_s ∗
         (public (si_key si) ∨ φ si Resp)) }}}.
Proof.
iIntros "%ϕ".
rewrite /opaque_db big_sepM_forall.
iIntros "(#Cryptis & (#HpredH & #HpredA_s & #HpredA_u & #HpredSK & _)
          & #N_φ & #Hc & Hdb & #Hmapcontents & hook) Hhl".
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
         #HpubP_s & #Hpenvelope & %p_u & %HP_u &
         #HpubP_u & #Hkeyp_s & #Hkeyp_u & #Hprivp_s & #Hprivp_u)]".
iPoseProof "Hkeyp_s" as "[#Hminp_s #Hexpp_s]".
iPoseProof "Hkeyp_u" as "[#Hminp_u #Hexpp_u]".
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
(* The ephemeral is a [secret] of its owner, with a token on the server's
   share as in [iso_dh]. *)
iMod pending_alloc as (γ) "pend".
wp_apply (wp_mk_nonce_freshN ∅ (λ _, shot γ 1)%I dh_key_share
            (fun t => {[TExp g t]})) => //.
  by iIntros "% %contra".
  iIntros "%t"; rewrite big_sepS_singleton; iModIntro; iSplit.
  - iIntros "#?"; by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
  - rewrite (minted_TExp t) //; by iIntros "[_ ?]".
iIntros "%x_s _ #Hmintedx_s #Hprivatex_s #Hexpx_s #Hexpx_sV tok_Xs".
rewrite big_sepS_singleton.
iAssert (□ (public x_s ↔ ▷ shot γ 1))%I as "#s_xs'".
{ iModIntro; iSplit.
  - iIntros "#p". iDestruct ("Hprivatex_s" with "p") as "#s". iNext.
    by iDestruct "s" as "#s".
  - iIntros "#s". iApply "Hprivatex_s". iNext. by iModIntro. }
iPoseProof (secret_alloc with "s_xs' pend") as "s_xs".
iAssert (hmqv_key x_s) as "#key_xs"; first by iSplit.
set si := server_si uid α X_u (TExp g p_u) p_s x_s.
wp_pures.
wp_apply wp_texp; wp_pures.
wp_apply wp_texp; wp_pures.
wp_apply wp_hmqv_ke; wp_list; wp_apply wp_H; wp_list.
wp_apply wp_H; wp_list.
wp_apply wp_prf; wp_list.
wp_apply wp_prf; wp_list.
wp_term_of_list; wp_pures.
iAssert (minted (TExp g x_s)) as "#minX_s".
{ by iApply all_minted_TExp; iSplit => //; iApply minted_TInt. }
iAssert (minted (si_key si)) as "#mintedSK".
{ iApply minted_hash_result; iApply minted_of_list; rewrite /=; do !iSplit => //.
  - iApply minted_hash_result; rewrite minted_of_list /=; iSplit => //.
    by iApply minted_hmqv_K => //.
  - iEval (rewrite minted_hash_result minted_of_list /=).
    by eauto. }
(* The caller's resources for this session come from the [↑opN.@"res"] slice
   of the token on the server's share; the client's copy is escrowed at once,
   and the [ready] slice will redeem the client's.  The part of the token
   outside [↑opN] goes back to the caller. *)
iDestruct (term_token_difference (TExp g x_s) (↑opN.@"res") with "tok_Xs")
  as "[tok_res tok_Xs]"; first solve_ndisj.
iMod ("hook" $! si x_s with "[//] s_xs tok_res") as "[gift keep]".
iMod (opaque_ready_alloc si Init with "N_φ gift") as "#ready".
iDestruct (term_token_difference (TExp g x_s) (↑opN.@"ready") with "tok_Xs")
  as "[tok_ready tok_Xs]"; first solve_ndisj.
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
                     "Hminp_s Hmintedx_s minP_s minX_s minP_u minX_u").
      + iEval (rewrite minted_hash_result minted_of_list /=); do !iSplit => //;
        by iApply public_minted.
    iNext; iModIntro.
    iExists uid, α, X_u, p_u, p_s, x_s; rewrite /si_K /si_ssid /=.
    by do !iSplit => //.
wp_pures.
wp_apply (wp_recv with "Hc"); iIntros "%m3 #Hm3pub".
wp_list; wp_apply wp_prf.
wp_eq_term Heq; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iFrame "Hdb"; iLeft.
iAssert (public (hash_result "A_u" (Spec.of_list [si_K si; si_ssid si])))
  as "#pubA_u"; first by rewrite -Heq.
(* A valid [A_u] was either forged -- then the key is public, and with it the
   password -- or produced by the honest client, which vouches for its
   ephemeral and hands over the escrowed resources. *)
iAssert (public (Spec.of_list [si_K si; si_ssid si])
         ∨ ▷ □ A_u_pred (Spec.of_list [si_K si; si_ssid si]))%I as "#auth".
  by iDestruct (public_THashE with "HpredA_u pubA_u") as "[? | [_ ?]]"; eauto.
wp_pures.
iAssert (states_pw (pw_of uid) si) as "#st_pw".

{ by iApply (states_pw_intro (si := si) (p_u := p_u) (p_s := p_s) (pw_of uid)
               eq_refl eq_refl with "Hprivp_u Hprivp_s"). }

iAssert (|={⊤}=> session (pw_of uid) si ∗
                 (public (si_key si) ∨ ▷ φ si Resp))%I
  with "[tok_ready]" as ">(#sess & res)".
{ iDestruct "auth" as "[#p_t | #auth]".
  - iAssert (public (si_key si)) as "#p_SK".
    { iApply public_THash; iLeft. by iApply public_tag. }
    iAssert (▷ □ public (pw_of uid))%I as "#p_pw".
    { rewrite public_of_list /=.
      iDestruct "p_t" as "[p_K _]".
      iDestruct (public_THashE with "HpredH p_K") as "[p_t | [_ contra]]";
        last by iNext; iDestruct "contra" as "[]".
      rewrite public_of_list /=.
      iDestruct "p_t" as "(p_K' & _)".
      have tags : "e"%string ≠ "d"%string by [].
      iDestruct (@public_hmqv_K_static _ _ _ opN g "e" "d" p_s x_s p_u
                   P_s (TExp g x_s) X_u I I I tags
                   with "Hkeyp_s Hkeyp_u p_K'")
        as "[p|p]".
      - by iApply "Hprivp_s".
      - by iApply "Hprivp_u". }
    iModIntro. iSplit; last by iLeft.
    iSplit => //. iSplit => //.
    iSplit; first by iIntros "!> _".
    iLeft; iSplit => //. by iNext.
  - iDestruct "auth" as "(%si' & %x_u & %e & %ss' & %eX & #key_xu & #ready_u)".
    have ss : server_session si by exists uid, α, X_u, p_u, p_s, x_s.
    have ek : si_key si = si_key si' by rewrite {2}/si_key -e.
    have e_si := server_session_key_inj ss ss' ek.
    have eXu : X_u = TExp g x_u by rewrite -eX -e_si.
    subst X_u.
    iPoseProof (honest_session_ok uid α p_u p_s x_u x_s
                  with "HpredSK HpredH p_uid p_α Hkeyp_u Hkeyp_s key_xu key_xs
                        mintedSK") as "#[ok1 ok2]".
    subst si'.
    iMod ("ready_u" with "N_φ tok_ready") as "res".

    iModIntro. iSplit; last by iRight.
    iSplit => //. iSplit => //.
    iSplit; first by iApply "ok2".
    by iRight. }
wp_list; wp_term_of_list; wp_pures.
iModIntro.
iApply ("Hhl" $! (Some (si_result si))).

iFrame "Hdb".
iRight; iExists si, x_s.
have -> : si_sshare si = TExp g x_s by [].
have -> : si_uid si = uid by [].
rewrite /release_token.
iFrame "tok_Xs tok_rel keep res".
iSplit; first by [].
iSplit; first by iPureIntro; exists uid, α, X_u, p_u, p_s, x_s.
iSplit; first by [].
iSplit.

  by do !iSplit => //.
iSplit.
  iExists k_s, p_s, envelope; iPureIntro.
  by rewrite /si /server_si /= db_uid.
(* The steps above stripped the later off [compromised]. *)
iDestruct "sess" as "(#mSK & #st_pw' & #rel & [[#p_pw #p_k] | #sec])".
- iSplit => //. iSplit => //. iSplit => //. iLeft. by iSplit => //.

- iSplit => //. iSplit => //. iSplit => //. by iRight.
Qed.


End Opaque.
