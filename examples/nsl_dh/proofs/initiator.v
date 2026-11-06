From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.lib Require Import dh.
From cryptis.examples.nsl_dh Require Import impl.
From cryptis.examples.nsl_dh.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !nsl_dhGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : aenc_key).
Implicit Types (si : sess_info).
Implicit Types (N : namespace).
Implicit Types (φ : sess_info → role → iProp) (ρ : sess_info → iProp).

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); eauto.

#[local] Lemma wp_initiator_send_msg1 c skI skR :
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    minted skI ∗
    minted skR
  }}}
    initiator_send_msg1 c skI (Spec.pkey skR)
  {{{ (a : nonce), RET (TNonce a, TExp (TInt 0) a);
      let ga := TExp (TInt 0) a in
      dh_key skI skR (term_meta ga (nsl_dhN.@"compromised") true) a ∗
      term_token ga ⊤
  }}}.
Proof.
iIntros "%Ψ (#chan_c & #ctx & #(m1_pred & _) & #m_skI & #m_skR) Hpost".
rewrite /initiator_send_msg1.
wp_pures. wp_apply wp_pkey. wp_pures.
set pkI := Spec.pkey skI.
wp_apply (wp_mk_dh_keys ∅ skI skR
            (λ ga, term_meta ga (nsl_dhN.@"compromised") true));
  first by iFrame "#".
{ iIntros "%t". rewrite elem_of_empty. by iIntros "[]". }
iIntros "%a _ #dh_a token".
set ga := TExp (TInt 0) a.
wp_pures. wp_list. wp_term_of_list. wp_pures.
wp_apply wp_aenc => //.
{ iDestruct "dh_a" as "(#m_a & _)".
  rewrite minted_of_list /= minted_TExp //.
  rewrite minted_TInt /= minted_pkey.
  by do !iSplit. }
{ iRight. iSplit.
  - iModIntro. iExists ga, skI. iSplit => //.
    iIntros "#corr".
    iApply (public_dh_share with "dh_a").
    by iModIntro.
  - iIntros "!> #p_skR". rewrite public_of_list /=. do !iSplit => //.
    + iApply (public_dh_share with "dh_a"). iModIntro. by eauto.
    + by iApply public_aenc_key. }
iIntros "%m1 #p_m1". wp_pures.
wp_apply wp_send => //.
wp_pures.
iApply ("Hpost" $! a). by iFrame "∗ #".
Qed.

#[local] Lemma wp_initiator_recv_msg2 c skI skR a N :
  let ga := TExp (TInt 0) a in
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx
  }}}
    initiator_recv_msg2 c skI (Spec.pkey skR) (Tag N) a ga
  {{{ r, RET (repr r);
    ⌜r = None⌝ ∨ ∃ gb : term,
    ⌜r = Some gb⌝ ∗
    (public ga ∧ public gb ∨ msg2_pred' skI skR ga gb N)
  }}}.
Proof.
move=> ga.
iIntros "%Ψ (#chan_c & #ctx & #(m1_pred & m2_pred & _)) Hpost".
rewrite /initiator_recv_msg2.
wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m) "#p_m".
wp_apply wp_adec => //. iSplit; last by protocol_failure.
iClear "p_m" => {m}. iIntros "%m2 #m_m2 #inv_m2".
wp_list_of_term m2; last by protocol_failure.
wp_list_match => [ga' gb pkR' N' {m2} ->|_]; last by protocol_failure.
wp_eq_term e; last by protocol_failure. subst ga'.
wp_eq_term e; last by protocol_failure. subst pkR'.
wp_eq_term e; last by protocol_failure. subst N'.
wp_pures.
iApply ("Hpost" $! (Some gb)). iRight. iExists gb.
iModIntro. iSplit => //.
iDestruct "inv_m2" as "[#p_m2|[#inv_m2 _]]".
- (* public plaintext *)
  iLeft. rewrite public_of_list /=.
  iDestruct "p_m2" as "(#p_ga & #p_gb & _)".
  by iSplit.
- (* msg2_pred *)
  iDestruct "inv_m2" as
    "(%ga0 & %gb0 & %skR0 & %N0 & %e_m2 & inv_m2)".
  case/Spec.of_list_inj: e_m2
      => <- <- /Spec.aenc_pkey_inj <- /Tag_inj <-.
  by iRight.
Qed.

(* A forged [m2] reveals the initiator's share, which only a leaked long-term
   key explains, and the initiator then publishes its exponent.  Otherwise the
   responder vouches for its share and hands over the escrowed gift. *)
#[local] Lemma initiator_process_msg2 skI skR (a : nonce) gb N φ ρ ψ :
  let ga := TExp (TInt 0) a in
  let si := SessInfo skI skR ga gb (TExp gb a) in
  £ 1 -∗ £ 1 -∗
  nsl_dh_ctx -∗
  nsl_dh_pred N φ ρ -∗
  minted skI -∗
  minted skR -∗
  dh_key skI skR (compromised Init si) a -∗
  term_token ga ⊤ -∗
  (term_token ga (⊤ ∖ ↑nsl_dhN) ={⊤}=∗ φ si Resp ∗ ψ si) -∗
  (public ga ∧ public gb ∨ msg2_pred' skI skR ga gb N) ={⊤}=∗
  session ρ Init si ∗ ψ si ∗ (compromised Init si ∨ φ si Init) ∗
  minted gb ∗
  (public gb ∨ □ msg3_pred skR gb ∧ □ (public skR → public gb)).
Proof.
move=> ga si.
iIntros "c1 c2 #ctx #N_φ #m_skI #m_skR #dh_a token hook inv".
iPoseProof "dh_a" as "(#m_a & #s_a & #pred_a)".
have Nm_a : negb (is_mul a) by [].
rewrite (term_token_difference ga (↑nsl_dhN)) //.
iDestruct "token" as "[token_N token]".
iDestruct (term_token_difference ga (↑nsl_dhN.@"compromised") with "token_N")
  as "[comp_token token_N]"; first solve_ndisj.
iDestruct (term_token_difference ga (↑nsl_dhN.@"ready") with "token_N")
  as "[ready_token _]"; first solve_ndisj.
iMod ("hook" with "token") as "[gift $]".
iDestruct "inv" as "[[#p_ga #p_gb]|inv]".
- iAssert (|={⊤}=> (public skI ∨ public skR) ∗
             term_token ga (↑nsl_dhN.@"compromised"))%I
    with "[c1 comp_token]" as "> [#comp comp_token]".
  { iPoseProof (public_exp_inv_same (t1 := a) with "p_ga") as "[#p_a|H]";
      first by rewrite (exps_TExp1 Nm_a) /SMS.pos SMS.car_singleton;
               set_solver.
    - iDestruct ("s_a" with "p_a") as "#c".
      iMod (lc_fupd_elim_later_pers with "c1 c") as "#c'".
      by iDestruct (term_meta_token with "comp_token c'") as "[]".
    - iDestruct "H" as "(%t3 & _ & _ & #p)".
      iPoseProof ("pred_a" $! t3 with "p") as "#ks".
      iMod (lc_fupd_elim_later_pers with "c1 ks") as "#[comp _]".
      by iFrame. }
  iMod (term_meta_set (nsl_dhN.@"compromised") true with "comp_token")
    as "#c"; first solve_ndisj.
  iAssert (public a) as "#p_a"; first by iApply "s_a"; iIntros "!> !>".
  iAssert (public (si_key si)) as "#p_k".
  { rewrite /si_key public_senc_key public_THash public_tag. iLeft.
    rewrite /si_seed public_of_list /=.
    do !iSplit => //; try by iApply public_aenc_key.
    by iApply public_TExp. }
  iModIntro. iSplit.
  { iSplit; first by iApply public_minted.
    iSplit; first by iIntros "!> _".
    by iLeft; do !iSplit. }
  iSplit; first by iLeft.
  iSplit; first by iApply public_minted.
  by iLeft.
- iDestruct "inv" as "(%b & %e_gb & %b_ga & #dh_b & #peer & #use & ready)".
  subst gb.
  set gb := TExp (TInt 0) b.
  have e_si : si = SessInfo skI skR ga gb (TExp ga b).
  { by rewrite /si /ga /gb TExpC. }
  iMod (term_meta_set (nsl_dhN.@"compromised") false with "comp_token")
    as "#nc"; first solve_ndisj.
  iAssert (□ (¬ compromised Init si))%I as "#nc'".
  { iIntros "!> #c". by iDestruct (term_meta_agree with "c nc") as %?. }
  iMod (nsl_dh_ready_alloc N si Resp with "N_φ gift") as "#ready_R".
  iAssert (minted gb) as "#m_gb".
  { iDestruct "dh_b" as "[m_b _]".
    by rewrite minted_TExp // minted_TInt /=; iSplit. }
  iAssert (minted (si_key si)) as "#m_k".
  { rewrite minted_si_key /si_seed minted_of_list /= !minted_pkey.
    do !iSplit => //.
    - by iApply all_minted_TExp; rewrite minted_TInt; iSplit.
    - by iApply all_minted_TExp; iSplit. }
  rewrite e_si.
  iDestruct (honest_session with "ctx N_φ dh_a dh_b nc' use m_k")
    as "[#rel #ok]".
  iMod ("ready" with "N_φ ready_token") as "res".
  iMod (lc_fupd_elim_later with "c2 res") as "res".
  iModIntro. iSplit.
  { iSplit; first done. iSplit; first done. iRight. by iSplit. }
  iSplitL "res"; first by iRight.
  iSplit; first done.
  iRight. iSplit.
  + iIntros "!> %skI' %ga' %b' %e_gb' #peer'".
    iPoseProof (term_meta_agree with "peer peer'") as "%e".
    case: e => <- <-.
    have <- : b = b'.
    { have NmInt : negb (is_gmul (TInt 0)) by [].
      have := TExp_injr (Ngmul_neq_unit NmInt) e_gb'. congruence. }
    iExists a. iSplit; first done. iSplit; first done.
    iSplit; first done. iExists N. by iSplit.
  + iIntros "!> #p_skR".
    iApply (public_dh_share with "dh_b"). iModIntro. by iRight.
Qed.

#[local] Lemma wp_initiator_send_msg3 c skI skR a gb :
  let ga := TExp (TInt 0) a in
  let si := SessInfo skI skR ga gb (TExp gb a) in
  {{{
    channel c ∗
    cryptis_ctx ∗
    nsl_dh_ctx ∗
    minted skR ∗
    minted gb ∗
    (public gb ∨ □ msg3_pred skR gb ∧ □ (public skR → public gb))
  }}}
    initiator_send_msg3 c skI (Spec.pkey skR) a ga gb
  {{{ RET (repr (si_key si)); True }}}.
Proof.
move=> ga si.
iIntros "%Ψ (#chan & #ctx & #(m1_pred & m2_pred & m3_pred & _) &
         #m_skR & #m_gb & #inv_m3) Hpost".
rewrite /initiator_send_msg3. wp_pures.
wp_apply wp_pkey. wp_pures.
wp_bind (texp _ _). iApply wp_texp. wp_pures.
wp_list. wp_term_of_list. wp_pures.
wp_apply wp_aenc => //.
iIntros "%m3 #p_m3". wp_pures.
wp_apply wp_send => //. wp_pures.
iApply (wp_session_key si).
by iApply "Hpost".
Qed.

(* The hook runs only if the session succeeds, so a caller that lends it [R]
   gets [R] back otherwise. *)
Lemma wp_initiator c skI skR N φ ρ ψ R :
  channel c ∗
  cryptis_ctx ∗
  nsl_dh_ctx ∗
  nsl_dh_pred N φ ρ ∗
  minted skI ∗
  minted skR -∗
  {{{ R ∧
      ∀ (a : nonce) gb,
        let si := SessInfo skI skR (TExp (TInt 0) a) gb (TExp gb a) in
        term_token (si_init_share si) (⊤ ∖ ↑nsl_dhN) ={⊤}=∗
        φ si Resp ∗ ψ si }}}
    initiator c skI (Spec.pkey skR) (Tag N)
  {{{ r, RET (repr r);
      ⌜r = None⌝ ∗ R ∨ ∃ (a : nonce) gb,
        let si := SessInfo skI skR (TExp (TInt 0) a) gb (TExp gb a) in
        ⌜r = Some (si_key si)⌝ ∗
        session ρ Init si ∗ ψ si ∗
        (compromised Init si ∨ φ si Init)
  }}}.
Proof.
iIntros "#(chan & ctx & nsl_ctx & N_φ & m_skI & m_skR) !> %Ψ hook Hpost".
rewrite /initiator. wp_pures.
wp_apply wp_initiator_send_msg1; first by iFrame "#".
iIntros "%a (#dh_a & token)".
set ga := TExp (TInt 0) a.
wp_pures.
wp_bind (initiator_recv_msg2 _ _ _ _ _ _).
wp_apply wp_initiator_recv_msg2; first by iFrame "#".
iIntros "%r [->|(%gb & -> & inv)]".
{ wp_pures. iApply ("Hpost" $! None). iLeft. iModIntro. iSplit => //.
  by iDestruct "hook" as "[$ _]". }

wp_pure _ credit:"c1". wp_pure _ credit:"c2". wp_pures.
set si := SessInfo skI skR ga gb (TExp gb a).
iDestruct "hook" as "[_ hook]".
iMod (initiator_process_msg2 skI skR a gb N φ ρ ψ
        with "c1 c2 nsl_ctx N_φ m_skI m_skR dh_a token [hook] inv")
  as "(#sess & ψ & res & #m_gb & #inv_m3)".
{ iApply "hook". }
wp_apply wp_initiator_send_msg3; first by iFrame "#".
iIntros "_". wp_pures.
iApply ("Hpost" $! (Some (si_key si))). iRight. iExists a, gb.
iFrame. iModIntro. by iSplit.
Qed.

End Verif.
