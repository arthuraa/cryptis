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
  ∃ (k_s p_s p_u : nonce) envelope,
    ⌜file = Spec.of_list [TNonce k_s; TNonce p_s; TExp g p_s; TExp g p_u;
                          envelope]⌝ ∗
    minted k_s ∗ oprf_key pw k_s ∗ □ (public k_s ↔ ▷ □ stolen pw) ∗
    □ (∀ t', exp_pred k_s t' ↔ ▷ □ oprf_pred pw t') ∗
    public envelope ∗ opaque_keys pw p_u p_s.

(** The database, with the password each file was registered with. *)
Definition opaque_db (pw_of : term → term) (db : gmap term val) : iProp :=
[∗ map] (k : term) ↦ (file : val) ∈ db,
public k ∗ opaque_file (pw_of k) file.

Definition opaque_logs (pw_of : term → term) (db : gmap term val) : iProp :=
  [∗ map] k ↦ _ ∈ db, ∃ B, oprf_log (pw_of k) B.

Lemma public_opaque_file pw file :
  opaque_file pw file -∗ stolen pw -∗ ∃ t : term, ⌜file = t⌝ ∗ public t.
Proof.
iIntros "(%k_s & %p_s & %p_u & %envelope & -> & _ & _ & #s_k & _ & #p_env &
          #keys) #st".
iPoseProof "keys" as "(#key_u & #key_s & _ & #s_s)".
iExists _; iSplit; first done.
rewrite public_of_list /=.
do !iSplit => //.
- iApply "s_k". by iIntros "!> !>".
- iApply "s_s". by iIntros "!> !>".
- by iApply hmqv_key_public.
- by iApply hmqv_key_public.
Qed.

Lemma wp_make_file (pw : term) :
  {{{
    cryptis_ctx
    ∗ opaque_ctx
    ∗ minted pw
    ∗ term_token pw (↑opN.@"log" ∪ ↑opN.@"key")
  }}} Server.make_file pw
  {{{ file, RET (repr file); opaque_file pw file ∗ oprf_log pw ∅ }}}.
Proof.
iIntros "%ϕ (#cryptis & #ctx & #Hmintedpw & tok) post".
iDestruct (term_token_difference pw (↑opN.@"log") with "tok")
  as "[tok_log tok_key]"; first set_solver.
iMod (oprf_log_alloc with "tok_log") as "log".
iPoseProof "ctx" as "(#Hhashpred & _ & _ & #Hsencpred)".
wp_lam.
wp_apply (wp_mk_nonce_freshN ∅ (fun _ => stolen pw)%I (oprf_pred pw)
                               (fun t =>  {[(TInv t)]})) => //.
- by iIntros "%_ %contra".
- iIntros "%t".
  rewrite big_sepS_singleton minted_TInv.
  by iModIntro; auto.
iIntros "%k_s _ #Hmintedk_s #Hprivatek_s #Hexpk_s #Hexpk_sV Htokenk_sV".
iMod (term_meta_set (opN.@"key") (TNonce k_s) with "tok_key") as "#key";
  first solve_ndisj.
rewrite big_sepS_singleton.
wp_pures; wp_lam; wp_pures.
wp_apply wp_H'; wp_apply wp_texp; wp_list; wp_apply wp_H.
wp_apply wp_derive_senc_key.
wp_pures.
wp_apply (wp_mk_nonce_freshN ∅ (fun _ => stolen pw)%I dh_key_share
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
iAssert (opaque_keys pw p_u p_s) as "#keys"; first by do !iSplit.
iPoseProof (hmqv_key_public p_s with "[]") as "#pubP_s"; first by iSplit.
iPoseProof (hmqv_key_public p_u with "[]") as "#pubP_u"; first by iSplit.
iApply "post". iFrame "log".
iExists k_s, p_s, p_u, _.
do 5!(iSplit; first done). iSplit; last done.
iApply (public_sencIS _ (opN.@"AuthEnc") envelope_pred _) => //.
- rewrite minted_senc minted_THash minted_tag minted_of_list /=.
  do !iSplit => //. iApply all_minted_TExp.
  iSplit => //. by rewrite minted_hash_result.
- iApply minted_of_list. rewrite /=. do !iSplit => //; by iApply public_minted.
- iModIntro. iExists pw, (TExp (hash_result "H" pw) k_s), p_u, p_s.
  by do !iSplit.
iModIntro. rewrite public_senc_key. iIntros "#Hcompromise".
(* A public envelope key is a public password, which makes the client's
   long-term key public. *)
iAssert (▷ □ public pw)%I as "#Hpubpw".
{ iDestruct (public_THashE with "Hhashpred Hcompromise")
    as "[Hpub | [_ contra]]".
  - rewrite public_of_list /=.
    iDestruct "Hpub" as "[#? _]".
    by iIntros "!> !>".
  - by iNext; iDestruct (H_pred_oprf_key with "key contra") as "[]". }
iDestruct "Hprivatep_u" as "[_ Hprivatep_u]".
iDestruct ("Hprivatep_u" with "Hpubpw") as "#Hpubp_u".
rewrite public_of_list /=.
by do !iSplit => //.
Qed.

(** What the server keeps between its two messages. *)
Definition server_state_val si : val :=
  (si_result si, (si_K si, si_ssid si))%V.

Definition server_state pw_of si : iProp :=
  ∃ uid α X_u (p_u p_s x_s : nonce),
    ⌜si = server_si uid α X_u (TExp g p_u) p_s x_s⌝ ∗
    public uid ∗ public α ∗
    opaque_keys (pw_of uid) p_u p_s ∗ ephemeral x_s ∗
    minted (si_key si) ∗
    term_token (TExp g x_s) (↑opN.@"ready") ∗
    term_token (TExp g x_s) (↑opN.@"compromised").

Lemma wp_server_result si :
  {{{ True }}}
    Server.result (server_state_val si)
  {{{ RET (repr (si_result si)); True }}}.
Proof. iIntros "%Φ _ post". wp_lam. wp_pures. by iApply "post". Qed.

(** The server answers whichever user the first message claims.  The hook runs
    only if the server answers, so a caller that lends it [R] gets [R] back
    otherwise. *)
Lemma wp_server_accept (db c : val) pw_of (alist : gmap term val) φ ρ ψ R :
{{{ cryptis_ctx
    ∗ opaque_ctx
    ∗ opaque_pred φ ρ
    ∗ channel c
    ∗ AList.is_alist db alist
    ∗ opaque_logs pw_of alist
    ∗ opaque_db pw_of alist
    ∗ (R ∧ ∀ si, term_token (si_sshare si) (⊤ ∖ ↑opN) ={⊤}=∗ φ si Init ∗ ψ si)
  }}}
    Server.accept db c
  {{{ v, RET v;
      AList.is_alist db alist ∗ opaque_logs pw_of alist ∗
      (⌜v = NONEV⌝ ∗ R ∨ ∃ si,
         ⌜v = SOMEV (server_state_val si)⌝ ∗
         ⌜server_session si⌝ ∗
         opaque_session_for (si_uid si) si ∗
         (∃ (k_s p_s : nonce) envelope,
            ⌜alist !! si_uid si =
             Some (Spec.of_list [TNonce k_s; TNonce p_s;
                                 si_skey si; si_ckey si; envelope] : val)⌝) ∗
         server_state pw_of si ∗ ψ si) }}}.
Proof.
iIntros "%ϕ".
rewrite /opaque_db big_sepM_forall.
iIntros "(#Cryptis & (#HpredH & #HpredA_s & #HpredA_u & _)
          & #N_φ & #Hc & Hdb & Hlogs & #Hmapcontents & hook) Hhl".
wp_lam; wp_pures.
wp_apply (wp_recv with "Hc"); iIntros "%m1 #Hpubm1".
wp_list_of_term m1; wp_pures; last first.
  by iApply "Hhl"; iModIntro; iFrame "Hdb Hlogs"; iLeft;
     iDestruct "hook" as "[$ _]".
rewrite !subst_list_match /=.
wp_list_match => [uid α X_u -> | _]; last first.
  by wp_pures; iApply "Hhl"; iModIntro; iFrame "Hdb Hlogs"; iLeft;
     iDestruct "hook" as "[$ _]".
wp_eq_term X_u_one; wp_pures.
  by iApply "Hhl"; iModIntro; iFrame "Hdb Hlogs"; iLeft;
     iDestruct "hook" as "[$ _]".
wp_bind (AList.find _ _); iApply (AList.wp_find with "Hdb"); iIntros "!> Hdb".
case db_uid: (alist !! uid) => [file|]; wp_pures; last first.
  by iApply "Hhl"; iModIntro; iFrame "Hdb Hlogs"; iLeft;
     iDestruct "hook" as "[$ _]".
iDestruct ("Hmapcontents" $! uid file with "[//]") as
    "[_ (%k_s & %p_s & %p_u & %envelope & %e & #Hmk_s & _ & #Hprivk_s & #Hexpk_s
         & #Hpenvelope & #Hkeyp_u & #Hkeyp_s & #Hprivp_u & #Hprivp_s)]".
iPoseProof (hmqv_key_public with "Hkeyp_s") as "#HpubP_s".
iPoseProof (hmqv_key_public with "Hkeyp_u") as "#HpubP_u".
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
(* The ephemeral never leaks, and the server keeps a token on its share. *)
wp_apply (wp_mk_nonce_freshN ∅ (λ _, False)%I dh_key_share
            (fun t => {[TExp g t]})) => //.
  by iIntros "% %contra".
  iIntros "%t"; rewrite big_sepS_singleton; iModIntro; iSplit.
  - iIntros "#?"; by iApply all_minted_TExp; iSplit => //; iApply minted_TInt.
  - rewrite (minted_TExp (t2 := t)) //; last by apply: atom_frac_neq0.
    by iIntros "[_ ?]".
iIntros "%x_s _ #Hmintedx_s #Hprivatex_s #Hexpx_s #Hexpx_sV tok_Xs".
rewrite big_sepS_singleton.
iAssert (ephemeral x_s) as "#eph_xs".
{ iSplit; first by iSplit. iIntros "!>". iSplit.
  - iIntros "#p". iDestruct ("Hprivatex_s" with "p") as "#f". iNext.
    by iDestruct "f" as "#[]".
  - iIntros "#f". iApply "Hprivatex_s". iNext. by iDestruct "f" as "[]". }
iPoseProof "eph_xs" as "[#key_xs _]".
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
(* The caller's hook gets the part of the token on the server's share outside
   [↑opN]; its gift for the client is escrowed at once, and the [ready] slice
   will redeem the client's. *)
iDestruct (term_token_difference (TExp g x_s) (↑opN.@"ready") with "tok_Xs")
  as "[tok_ready tok_Xs]"; first solve_ndisj.
iDestruct (term_token_difference (TExp g x_s) (↑opN.@"compromised")
             with "tok_Xs") as "[tok_comp tok_Xs]"; first solve_ndisj.
iDestruct (term_token_drop (⊤ ∖ ↑opN) with "tok_Xs") as "tok_Xs";
  first solve_ndisj.
iDestruct "hook" as "[_ hook]".
iMod ("hook" $! si with "tok_Xs") as "[gift ψ]".
iMod (opaque_ready_alloc si Init with "N_φ gift") as "#ready".
(* The OPRF key consents only to the bases the server logs. *)
iAssert ([∗ set] b ∈ list_to_set (base <$> elements (gfactors α)), minted b)%I
  as "#m_bases".
{ iApply big_sepS_intro. iIntros "!> %b %b_α".
  move: b_α; rewrite elem_of_list_to_set list_elem_of_fmap => - [u [-> u_α]].
  iEval (rewrite public_gfactors) in "p_α".
  iDestruct "p_α" as "[_ #fs]".
  iPoseProof (big_sepL_elem_of with "fs") as "p_u"; first exact: u_α.
  iPoseProof (public_minted with "p_u") as "m_u".
  iEval (rewrite minted_base_exps) in "m_u".
  by iDestruct "m_u" as "[$ _]". }
iDestruct (big_sepM_lookup_acc with "Hlogs") as "[(%B & log) close_logs]";
  first exact: db_uid.
iMod (oprf_log_query with "m_bases log") as "[log #queried]".
iDestruct ("close_logs" with "[log]") as "Hlogs"; first by iExists _.
set m2 := (Spec.of_list [_; _; _; _]).
wp_apply wp_send => //.
  rewrite public_of_list => //.
  do !iSplit => //.
  - iApply public_TExp_consent => //.
    iIntros "!> %t %e_t #p_t". iApply "Hexpk_s". iIntros "!> !>".
    iExists (base t). iSplit.
    + iApply (big_sepS_elem_of with "queried").
      by rewrite elem_of_list_to_set.
    + move: e_t; rewrite list_elem_of_fmap => - [u [e_t u_in]].
      have Nm_u := Ngmul_gfactors _ _ (proj1 (SMS.elem_of_elements _ _) u_in).
      have Nm_t : negb (is_gmul t) by rewrite -is_gmul_base e_t is_gmul_base.
      by rewrite (base_TExp Nm_t (mono_num_atom (TNonce k_s) I)).
  - iApply public_TExp_iff => //.
    do !iSplit => //.
    + by iApply minted_TInt.
    + iRight.
      iApply "Hexpx_s"; iPureIntro.
      rewrite (exps_TExp_expN _ _ (mono_num_atom (TNonce x_s) I)) //.
      by rewrite factors_Nmod // SMS.elements_singleton.
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
wp_list; wp_term_of_list. wp_pures.
iApply ("Hhl" $! (SOMEV (server_state_val si))). iModIntro.
iFrame "Hdb Hlogs". iRight. iExists si. iFrame "ψ".
have -> : si_uid si = uid by [].
iSplit; first done.
iSplit; first by iPureIntro; exists uid, α, X_u, p_u, p_s, x_s.
iSplit; first by do !iSplit => //.
iSplit.
{ iExists k_s, p_s, envelope; iPureIntro. by rewrite /si /server_si /= db_uid. }
iExists uid, α, X_u, p_u, p_s, x_s. iFrame "tok_ready tok_comp".
by do !iSplit => //.
Qed.

Lemma wp_server_finish c pw_of si φ ρ :
  {{{ cryptis_ctx ∗ opaque_ctx ∗ opaque_pred φ ρ ∗ channel c ∗
      server_state pw_of si }}}
    Server.finish c (server_state_val si)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∨
      ⌜r = Some (si_result si)⌝ ∗
      session (pw_of (si_uid si)) ρ Resp si ∗
      (compromised Resp si ∨ φ si Resp) }}}.
Proof.
iIntros "%ϕ (#Cryptis & (#HpredH & #HpredA_s & #HpredA_u & _) & #N_φ & #Hc &
             (%uid & %α & %X_u & %p_u & %p_s & %x_s & -> & #p_uid & #p_α &
              #keys & #eph_xs & #mintedSK & tok_ready & tok_comp)) Hhl".
iPoseProof "keys" as "(#Hkeyp_u & #Hkeyp_s & #Hprivp_u & _)".
iPoseProof "eph_xs" as "[#key_xs _]".
set P_s := TExp g p_s.
set si := server_si uid α X_u (TExp g p_u) p_s x_s.
wp_lam. wp_pures.
wp_apply (wp_recv with "Hc"); iIntros "%m3 #Hm3pub".
wp_list; wp_apply wp_prf.
wp_eq_term Heq; last first.
  by wp_pures; iApply ("Hhl" $! None); iModIntro; iLeft.
iAssert (public (hash_result "A_u" (Spec.of_list [si_K si; si_ssid si])))
  as "#pubA_u"; first by rewrite -Heq.
(* A valid [A_u] was either forged -- then the key is public, and with it the
   password, even if the file was stolen -- or produced by the honest client,
   which vouches for its ephemeral and hands over the escrowed resources. *)
iAssert (public (Spec.of_list [si_K si; si_ssid si])
         ∨ ▷ □ A_u_pred (Spec.of_list [si_K si; si_ssid si]))%I as "#auth".
  by iDestruct (public_THashE with "HpredA_u pubA_u") as "[? | [_ ?]]"; eauto.
wp_pure _ credit:"cr". wp_pures.
iAssert (|={⊤}=> session (pw_of uid) ρ Resp si ∗
                 (compromised Resp si ∨ ▷ φ si Resp))%I
  with "[tok_ready tok_comp cr]" as ">(#sess & res)".
{ iDestruct "auth" as "[#p_t | #auth]".
  - iAssert (public (si_key si)) as "#p_SK".
    { iApply public_THash; iLeft. by iApply public_tag. }
    iAssert (▷ □ public (pw_of uid))%I as "#p_pw".
    { rewrite public_of_list /=.
      iDestruct "p_t" as "[p_K _]".
      iDestruct (public_THashE with "HpredH p_K") as "[p_t | [_ contra]]";
        last by iNext; iDestruct (H_pred_single with "contra") as "[]".
      rewrite public_of_list /=.
      iDestruct "p_t" as "(p_K' & _)".
      have tags : "e"%string ≠ "d"%string by [].
      iDestruct (@public_hmqv_K_forged _ _ _ opN g "e" "d" p_s x_s p_u
                   P_s (TExp g x_s) X_u I I tags
                   with "Hkeyp_s key_xs Hkeyp_u p_K'")
        as "[p|[_ p]]".
      - by iApply "Hprivp_u".
      - iDestruct "eph_xs" as "[_ s_xs]".
        iDestruct ("s_xs" with "p") as "f". iNext.
        by iDestruct "f" as "[]". }
    iMod (lc_fupd_elim_later with "cr p_pw") as "#p_pw'".
    iMod (term_meta_set (opN.@"compromised") true with "tok_comp")
      as "#comp"; first done.
    iModIntro. iSplit; last by iLeft.
    iSplit; first done. iSplit; first by iIntros "!> _".
    iLeft. iSplit; first done. iSplit; first done. by iLeft.
  - iDestruct "auth" as "(%si' & %x_u & %e & %ss' & %eX & #eph_xu & #ready_u)".
    have ss : server_session si by exists uid, α, X_u, p_u, p_s, x_s.
    have ek : si_key si = si_key si' by rewrite {2}/si_key -e.
    have e_si := server_session_key_inj ss ss' ek.
    have eXu : X_u = TExp g x_u by rewrite -eX -e_si.
    subst X_u.
    iPoseProof (honest_session uid α p_u p_s x_u x_s φ ρ
                  with "N_φ HpredH p_uid p_α Hkeyp_u Hkeyp_s eph_xu eph_xs
                        mintedSK") as "#ok".
    subst si'.
    iMod (term_meta_set (opN.@"compromised") false with "tok_comp")
      as "#ncomp"; first done.
    iMod ("ready_u" with "N_φ tok_ready") as "res".
    iModIntro. iSplit; last by iRight.
    iSplit; first done.
    iSplit; first by iIntros "!> #r"; iApply "ok".
    iRight. iSplit.
    + iIntros "!> #c".
      by iDestruct (term_meta_agree with "c ncomp") as %?.
    + iIntros "!> #p". by iApply "ok". }
wp_lam. wp_pures.
iModIntro.
iApply ("Hhl" $! (Some (si_result si))).
iRight. by iFrame "res sess".
Qed.

Lemma wp_server_session (db c : val) pw_of (alist : gmap term val) φ ρ ψ :
{{{ cryptis_ctx
    ∗ opaque_ctx
    ∗ opaque_pred φ ρ
    ∗ channel c
    ∗ AList.is_alist db alist
    ∗ opaque_logs pw_of alist
    ∗ opaque_db pw_of alist
    ∗ (∀ si, term_token (si_sshare si) (⊤ ∖ ↑opN) ={⊤}=∗ φ si Init ∗ ψ si)
  }}}
    Server.session db c
  {{{ r, RET (repr r);
      AList.is_alist db alist ∗ opaque_logs pw_of alist ∗
      (⌜r = None⌝ ∨ ∃ si,
         ⌜r = Some (si_result si)⌝ ∗
         ⌜server_session si⌝ ∗
         opaque_session_for (si_uid si) si ∗
         (∃ (k_s p_s : nonce) envelope,
            ⌜alist !! si_uid si =
             Some (Spec.of_list [TNonce k_s; TNonce p_s;
                                 si_skey si; si_ckey si; envelope] : val)⌝) ∗
         session (pw_of (si_uid si)) ρ Resp si ∗ ψ si ∗
         (compromised Resp si ∨ φ si Resp)) }}}.
Proof.
iIntros "%Φ (#ctx & #octx & #N_φ & #chan & db & logs & #odb & hook) post".
wp_lam. wp_pures.
wp_apply (wp_server_accept db c pw_of alist φ ρ ψ True%I
            with "[$db $logs hook]").
{ iFrame "#". by iSplit. }
iIntros "%v (db & logs & [[-> _]|(%si & -> & %ss & #sf & #lk & st & ψ)])";
  wp_pures.
  by iApply ("post" $! None); iFrame; iLeft.
wp_apply (wp_server_finish with "[$st]"); first by iFrame "#".
iIntros "%r [->|(-> & #sess & res)]".
- iApply ("post" $! None). iFrame. by iLeft.
- iApply "post". iFrame. iRight. iExists si. by iFrame "∗ #".
Qed.


End Opaque.
