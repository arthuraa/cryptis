From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta nown saved_prop.
From cryptis Require Import cryptis primitives tactics role.
From cryptis.examples.nsl_dh Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record sess_info := SessInfo {
  si_init : aenc_key;
  si_resp : aenc_key;
  si_init_share : term;
  si_resp_share : term;
  si_secret : term;
}.

Definition si_share_of rl :=
  if rl is Init then si_init_share
  else si_resp_share.

Global Instance sess_info_inhabited : Inhabited sess_info :=
  populate (SessInfo inhabitant inhabitant
              inhabitant inhabitant inhabitant).

Class nsl_dhGpreS Σ := NslDhGPreS {
  nsl_dhGpreS_meta : metaGS Σ;
  nsl_dhGpreS_pred : savedPredG Σ (aenc_key * aenc_key * sess_info * role);
}.

Local Existing Instance nsl_dhGpreS_meta.
Local Existing Instance nsl_dhGpreS_pred.

Class nsl_dhGS Σ := NslDhGS {
  nsl_dh_inG : nsl_dhGpreS Σ;
  nsl_dh_name : gname;
}.

Local Existing Instance nsl_dh_inG.

Definition nsl_dhΣ := #[
  metaΣ;
  savedPredΣ (aenc_key * aenc_key * sess_info * role)
].

Global Instance subG_nsl_dhGpreS Σ : subG nsl_dhΣ Σ → nsl_dhGpreS Σ.
Proof. solve_inG. Qed.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !nsl_dhGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t sI sR kS : term).
Implicit Types (skI skR : aenc_key) (failed : bool).
Implicit Types (si : sess_info).
Implicit Types (N : namespace) (E : coPset).
Implicit Types (φ : aenc_key → aenc_key → sess_info → role → iProp).

Definition nsl_dh_token E : iProp :=
  gmeta_token nsl_dh_name E.

Definition nsl_dh_pred N φ : iProp :=
  nown nsl_dh_name N
    (saved_pred DfracDiscarded (λ '(skI, skR, si, rl), φ skI skR si rl)).

Lemma nsl_dh_pred_set N φ E :
  ↑N ⊆ E →
  nsl_dh_token E ==∗ nsl_dh_pred N φ ∗ nsl_dh_token (E ∖ ↑N).
Proof. by iIntros "%"; iApply nown_alloc. Qed.

Lemma nsl_dh_token_difference E1 E2 :
  E1 ⊆ E2 →
  nsl_dh_token E2 ⊣⊢ nsl_dh_token E1 ∗ nsl_dh_token (E2 ∖ E1).
Proof. exact: gmeta_token_difference. Qed.

Lemma nsl_dh_token_drop E1 E2 :
  E1 ⊆ E2 →
  nsl_dh_token E2 -∗ nsl_dh_token E1.
Proof. exact: gmeta_token_drop. Qed.

(* Token predicates for nsl_dhN sub-namespaces *)

Definition release_token share : iProp :=
  term_token share (↑nsl_dhN.@"released").

Definition fail_token share : iProp :=
  term_token share (↑nsl_dhN.@"failed").

Definition peer_share_token share : iProp :=
  term_token share (↑nsl_dhN.@"peer_share").

Definition ready_token share : iProp :=
  term_token share (↑nsl_dhN.@"ready").

Definition res_token share : iProp :=
  term_token share (↑nsl_dhN.@"res").

Lemma dh_share_tokenI share E :
  ↑nsl_dhN ⊆ E →
  term_token share E -∗
  release_token share ∗
  fail_token share ∗
  peer_share_token share ∗
  ready_token share ∗
  res_token share ∗
  term_token share (E ∖ ↑nsl_dhN).
Proof.
iIntros "% tok".
rewrite /release_token /fail_token /peer_share_token /ready_token /res_token.
rewrite (term_token_difference share (↑nsl_dhN) E) //.
iDestruct "tok" as "[nsl rest]". iFrame "rest".
iDestruct (term_token_difference share (↑nsl_dhN.@"released") (↑nsl_dhN) with "nsl") as "[$ nsl]"; first solve_ndisj.
iDestruct (term_token_difference share (↑nsl_dhN.@"failed") _ with "nsl") as "[$ nsl]"; first solve_ndisj.
iDestruct (term_token_difference share (↑nsl_dhN.@"peer_share") _ with "nsl") as "[$ nsl]"; first solve_ndisj.
iDestruct (term_token_difference share (↑nsl_dhN.@"ready") _ with "nsl") as "[$ nsl]"; first solve_ndisj.
iDestruct (term_token_difference share (↑nsl_dhN.@"res") _ with "nsl") as "[$ _]"; first solve_ndisj.
Qed.

(* Meta predicates for nsl_dhN sub-namespaces *)

Definition released share : iProp :=
  term_meta share (nsl_dhN.@"released") true.

Lemma release share : release_token share ==∗ released share.
Proof. by apply term_meta_set. Qed.

Definition early_failure share (b : bool) : iProp :=
  term_meta share (nsl_dhN.@"failed") b.

Lemma set_early_failure share (b : bool) :
  fail_token share ==∗ early_failure share b.
Proof. by apply term_meta_set. Qed.

Lemma early_failure_agree share (b1 b2 : bool) :
  early_failure share b1 -∗
  early_failure share b2 -∗
  ⌜b1 = b2⌝.
Proof. exact: term_meta_agree. Qed.

Definition has_peer_share share (gb : term) : iProp :=
  term_meta share (nsl_dhN.@"peer_share") gb.

Lemma set_peer_share share gb :
  peer_share_token share ==∗ has_peer_share share gb.
Proof. by apply term_meta_set. Qed.

Lemma has_peer_share_agree share gb1 gb2 :
  has_peer_share share gb1 -∗
  has_peer_share share gb2 -∗
  ⌜gb1 = gb2⌝.
Proof. exact: term_meta_agree. Qed.

Definition nsl_dh_ready N skI skR si : iProp := ∀ φ,
  nsl_dh_pred N φ →
  ready_token (si_init_share si) ={⊤}=∗
    ▷ φ skI skR si Init.

Lemma nsl_dh_ready_alloc N skI skR si φ :
  nsl_dh_pred N φ -∗
  φ skI skR si Init ={⊤}=∗
  □ nsl_dh_ready N skI skR si.
Proof.
iIntros "#N_φ φ_ts".
iMod (escrowI nroot with "φ_ts []") as "#?".
{ by iApply (term_token_switch (si_init_share si) (nsl_dhN.@"ready")). }
iIntros "!> !>  %φ' #N_φ' ready".
iPoseProof (nown_valid_2 with "N_φ N_φ'") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #φ_eq]".
iSpecialize ("φ_eq" $! (skI, skR, si, Init)).
iMod (escrowE with "[//] ready") as "res" => //.
iIntros "!> !>". by iRewrite -"φ_eq".
Qed.

Definition nsl_dh_key_share skI skR t : iProp :=
  (public skI ∨ public skR) ∧ ⌜length (exps t) = 1⌝.

Definition si_key si : senc_key :=
  SEncKey
    (Spec.of_list [Spec.pkey (si_init si);
                   Spec.pkey (si_resp si);
                   si_init_share si;
                   si_resp_share si;
                   si_secret si]).
Arguments si_key : simpl never.

Lemma session_agree si1 si2 :
  si_key si1 = si_key si2 →
  si1 = si2.
Proof.
case: si1 si2
  => [[skI1] [skR1] ga1 gb1 gab1] [[skI2] [skR2] ga2 gb2 gab2] /=.
rewrite /si_key /=. case => /Spec.of_list_inj.
by case=> /Spec.aenc_pkey_inj <- /Spec.aenc_pkey_inj <- <- <- <-.
Qed.

Definition compromised si : iProp :=
  (public (si_init si) ∨ public (si_resp si)) ∗
  public (si_key si).

Lemma compromised_public si : compromised si ⊢ public (si_key si).
Proof. by iIntros "(_&?)". Qed.

Definition released_session si : iProp :=
  released (si_init_share si) ∧ released (si_resp_share si).

Lemma unrelease rl si : release_token (si_share_of rl si) ==∗ □ ¬ released_session si.
Proof.
iIntros "tok".
iMod (term_meta_set (nsl_dhN.@"released") false with "tok") as "#un" => //.
iIntros "!> !> [#init #resp]".
iAssert (released (si_share_of rl si)) as "r"; first by case: rl.
by iPoseProof (term_meta_agree with "r un") as "%".
Qed.

Lemma release_token_released_session si rl :
  release_token (si_share_of rl si) -∗
  released_session si -∗
  False.
Proof.
iIntros "token [#init #resp]".
iApply (term_meta_token with "token"); last by case: rl.
by [].
Qed.

Definition nonce_secrecy a : iProp :=
  let ga := TExp (TInt 0) a in
  early_failure ga true ∨
  ∃ gb, has_peer_share ga gb ∗ released ga ∗ released gb.

Lemma nonce_secrecy_set a gb :
  has_peer_share (TExp (TInt 0) a) gb ⊢
  nonce_secrecy a ↔
  early_failure (TExp (TInt 0) a) true ∨
  released (TExp (TInt 0) a) ∧ released gb.
Proof.
iIntros "#meta"; iSplit.
- iIntros "[#?|Ha]"; eauto.
  iDestruct "Ha" as "(%gb' & #meta' & #rel_a & #rel_b)". iRight.
  iPoseProof (has_peer_share_agree with "meta meta'") as "->".
  by iSplit.
- rewrite /nonce_secrecy. iIntros "[#?|[#? #?]]"; eauto.
Qed.

Definition dh_key skI skR a : iProp :=
  minted a ∧
  □ (public a ↔ ▷ □ nonce_secrecy a) ∧
  □ (∀ t, dh_pred a t ↔ ▷ □ nsl_dh_key_share skI skR t).

Global Instance dh_key_persistent skI skR a : Persistent (dh_key skI skR a).
Proof. apply _. Qed.

Definition failed_early skI skR (failed : bool) : iProp :=
  (if failed then public skI ∨ public skR else True)%I.

Definition failed_early_set skI skR share : iProp :=
  (public skI ∨ public skR) ∨ early_failure share false.

Lemma fail_token_failed_early skI skR a failed :
  let ga := TExp (TInt 0) a in
  failed_early skI skR failed -∗
  fail_token ga -∗
  dh_key skI skR a ==∗
  □ (⌜failed⌝ → public a) ∗
  failed_early_set skI skR ga.
Proof.
iIntros (ga) "fe ftok #dk".
iMod (set_early_failure ga failed with "ftok") as "#ef".
rewrite /failed_early /failed_early_set.
destruct failed.
- iDestruct "fe" as "#corr".
  iDestruct "dk" as "(#m_a & #s_a & _)".
  iModIntro. iSplit.
  + iModIntro.
    iAssert (▷ □ nonce_secrecy a)%I as "#ns".
    { iNext. iModIntro. iLeft. done. }
    by iDestruct ("s_a" with "ns") as "$".
  + by iLeft.
- iModIntro. iSplit.
  + by iIntros "!> %".
  + by iRight.
Qed.

Lemma dh_key_public_released skI skR a gb :
  let ga := TExp (TInt 0) a in
  dh_key skI skR a -∗
  early_failure ga false -∗
  has_peer_share ga gb -∗
  □ (public a ↔ ▷ (released ga ∧ released gb)).
Proof.
iIntros (ga) "#(m_a & s_a & dh_a) #ef #ps !>". iSplit.
- iIntros "#p_a".
  iDestruct ("s_a" with "p_a") as "H".
  iNext. iDestruct "H" as "#ns".
  iPoseProof (nonce_secrecy_set a gb with "ps") as "[Hfwd _]".
  iDestruct ("Hfwd" with "ns") as "[#fail|#[r1 r2]]".
  + by iPoseProof (early_failure_agree with "ef fail") as "%".
  + by iSplit.
- iIntros "H".
  iAssert (▷ □ nonce_secrecy a)%I with "[H]" as "ns".
  { iNext. iDestruct "H" as "#[r1 r2]". iModIntro.
    iPoseProof (nonce_secrecy_set a gb with "ps") as "[_ Hbck]".
    iApply "Hbck". iRight. by iSplit. }
  iDestruct ("s_a" with "ns") as "$".
Qed.

Lemma wp_mk_dh_keys skI skR (Ψ : val → iProp) :
  cryptis_ctx -∗
  (∀ a,
    let ga := TExp (TInt 0) a in
    dh_key skI skR a -∗
    release_token ga -∗
    fail_token ga -∗
    peer_share_token ga -∗
    ready_token ga -∗
    res_token ga -∗
    term_token ga (⊤ ∖ ↑nsl_dhN) -∗
    Ψ (repr (a, ga))) -∗
  WP mk_dh_keys #() {{ Ψ }}.
Proof.
iIntros "#ctx post".
rewrite /mk_dh_keys. wp_lam.
wp_apply (wp_mk_nonce_freshN ∅
            nonce_secrecy
            (nsl_dh_key_share skI skR)
            (λ a, {[TExp (TInt 0) a]})) => //.
- iIntros "%". rewrite elem_of_empty. iIntros "[]".
- iIntros "%a".
  rewrite big_sepS_singleton minted_TExp minted_TInt /= bi.True_and.
  iModIntro. by iApply bi.equiv_iff.
iIntros "%a _ _ #m_a #s_a #dh_a token_ga".
rewrite big_sepS_singleton.
iDestruct (dh_share_tokenI with "token_ga")
  as "(rel & fail & peer & ready & res & token_ga)" => //.
wp_pures.
wp_bind (tint _). iApply wp_tint.
wp_bind (texp _ _). iApply wp_texp.
wp_pures.
iAssert (dh_key skI skR a) as "#dh_key_a".
{ rewrite /dh_key. by do !iSplit. }
by iApply ("post" with "dh_key_a rel fail peer ready res token_ga").
Qed.

Definition session skI skR si : iProp :=
  ⌜skI = si_init si⌝ ∗ ⌜skR = si_resp si⌝ ∗ minted (si_key si) ∗
  □ (▷ released_session si → public (si_key si)) ∗
  ((public (si_init si) ∨ public (si_resp si)) ∨
    □ (public (si_key si) → ▷ released_session si)).

Lemma session_minted skI skR si :
  session skI skR si -∗
  minted (si_key si).
Proof.
by iIntros "(?&?&?&?)".
Qed.

Global Instance session_persistent skI skR si : Persistent (session skI skR si).
Proof. apply _. Qed.

Definition session_ok si : iProp :=
  □ (public (si_key si) ↔ ▷ released_session si).

Global Instance session_ok_persistent si : Persistent (session_ok si).
Proof. apply _. Qed.

Lemma secret_session skI skR si :
  secret skI -∗
  secret skR -∗
  session skI skR si -∗
  ◇ session_ok si.
Proof.
iIntros "sI sR (-> & -> & _ & #comp1 & #comp2)".
iDestruct "comp2" as "[[comp2|comp2]|comp2]".
- by iDestruct (secret_not_public with "sI comp2") as ">[]".
- by iDestruct (secret_not_public with "sR comp2") as ">[]".
- iIntros "!> !>". by iSplit.
Qed.

Lemma session_released_session skI skR si :
  session skI skR si -∗
  ▷ released_session si -∗
  public (si_key si).
Proof. iIntros "(_ & _ & _ & #H & _) #rel". by iApply "H". Qed.

Lemma session_session_ok skI skR si :
  session skI skR si -∗
  (public (si_init si) ∨ public (si_resp si)) ∨ session_ok si.
Proof.
iIntros "#(-> & -> & _ & #? & [?|#?])"; eauto. iRight. iModIntro. by iSplit.
Qed.

Lemma unreleased_key_secrecy si :
  □ (¬ released_session si) -∗
  session_ok si -∗
  □ (public (si_key si) ↔ ▷ False).
Proof.
iIntros "#un #s_k !>".
iApply (bi.iff_trans _ (▷ released_session si)). iSplit => //.
iSplit; last by iIntros ">[]".
iIntros "#re !>". by iApply "un".
Qed.

Definition session_weak skI skR si : iProp :=
  ⌜skI = si_init si⌝ ∗ ⌜skR = si_resp si⌝ ∗ minted (si_key si) ∗
  ((public skI ∨ public skR) ∨ □ (public (si_key si) ↔ ▷ False)).

Lemma unreleased_session_weak skI skR si :
  session skI skR si -∗
  □ (¬ released_session si) -∗
  session_weak skI skR si.
Proof.
iIntros "(-> & -> & #m_k & #s_k1 & #s_k2) #un".
do !iSplit => //. iDestruct "s_k2" as "[s_k2|#s_k2]"; eauto.
iRight. iApply unreleased_key_secrecy => //. iModIntro.
by iSplit; eauto.
Qed.

Lemma release_token_key_secrecy rl si :
  release_token (si_share_of rl si) -∗
  session_ok si -∗
  public (si_key si) -∗
  ▷ False.
Proof.
iIntros "token #s_k #p_k".
iPoseProof ("s_k" with "p_k") as "contra".
iModIntro. by iApply (release_token_released_session with "token").
Qed.

Lemma session_ok_compromised rl si :
  session_ok si -∗
  compromised si -∗
  release_token (si_share_of rl si) -∗
  ▷ False.
Proof.
iIntros "#ok [_ #comp] rel".
iApply (release_token_key_secrecy with "rel ok comp").
Qed.

Lemma session_compromised skI skR rl si :
  session skI skR si -∗
  public (si_key si) -∗
  release_token (si_share_of rl si) -∗
  ◇ compromised si.
Proof.
iIntros "(-> & -> & _ & #comp1 & #[[comp2|comp2]|#comp2]) #p_k rel".
- iSplit => //. by eauto.
- iSplit => //. by eauto.
- iSpecialize ("comp2" with "p_k").
  iDestruct (release_token_released_session with "rel comp2") as ">[]".
Qed.

Lemma session_compromised' skI skR si :
  session skI skR si -∗
  compromised si -∗
  public skI ∨ public skR.
Proof. by iIntros "(-> & -> & _) (? & _)". Qed.

(* Message predicates for aenc *)

Definition msg1_pred skR m1 : iProp := ∃ ga skI,
  ⌜m1 = Spec.of_list [ga; Spec.pkey skI]⌝ ∧
  (public skI ∨ public skR → public ga).

Definition msg2_pred skI m2 : iProp := ∃ ga b skR N,
  let gb := TExp (TInt 0) b in
  let gab := TExp ga b in
  let si := SessInfo skI skR ga gb gab in
  ⌜m2 = Spec.of_list [ga; gb; Spec.pkey skR; Tag N]⌝ ∧
  dh_key skI skR b ∧
  has_peer_share gb ga ∧
  early_failure gb false ∧
  nsl_dh_ready N skI skR si.

Definition msg3_pred skR gb : iProp := ∀ ga b,
  let gab := TExp ga b in
  ⌜gb = TExp (TInt 0) b⌝ -∗
  has_peer_share gb ga -∗
  (▷ (released ga ∧ released gb) → public ga) ∗
  (public gab ↔ ▷ (released ga ∧ released gb)).

Definition nsl_dh_ctx : iProp :=
  aenc_pred (nsl_dhN.@"m1") msg1_pred ∧
  aenc_pred (nsl_dhN.@"m2") msg2_pred ∧
  aenc_pred (nsl_dhN.@"m3") msg3_pred.

Lemma nsl_dh_ctx_alloc E :
  ↑nsl_dhN ⊆ E →
  seal_pred_token AENC E ==∗
  nsl_dh_ctx ∗ seal_pred_token AENC (E ∖ ↑nsl_dhN).
Proof.
iIntros (sub) "token".
rewrite (seal_pred_token_difference _ (↑nsl_dhN) E) //.
iDestruct "token" as "[token token']". iFrame.
iMod (aenc_pred_set (N := nsl_dhN.@"m1") msg1_pred with "token")
  as "[#H1 token]"; try solve_ndisj.
iMod (aenc_pred_set (N := nsl_dhN.@"m2") msg2_pred with "token")
  as "[#H2 token]"; try solve_ndisj.
iMod (aenc_pred_set (N := nsl_dhN.@"m3") msg3_pred with "token")
  as "[#H3 token]"; try solve_ndisj.
iModIntro; iFrame; do !iSplit => //.
Qed.

Global Instance nsl_dh_ctx_persistent : Persistent nsl_dh_ctx.
Proof. apply _. Qed.

Lemma public_dh_share skI skR a :
  let ga := TExp (TInt 0) a in
  dh_key skI skR a -∗
  ▷ (public skI ∨ public skR) -∗
  public ga.
Proof.
iIntros (ga) "#(m_a & _ & #pred_a) corr".
iAssert (dh_pred a (TExp (TInt 0) a)) with "[corr]" as "#dp".
{ iAssert (▷ □ nsl_dh_key_share skI skR (TExp (TInt 0) a))%I
    with "[corr]" as "#ns".
  { iNext. iDestruct "corr" as "#corr".
    iModIntro. rewrite /nsl_dh_key_share. iSplit => //.
    iPureIntro. by rewrite exps_TExpN /=. }
  by iDestruct ("pred_a" $! (TExp (TInt 0) a) with "ns") as "$". }
rewrite /ga. iApply public_TExp_iff; eauto.
rewrite minted_TInt. iRight. do ![iSplit => //].
Qed.

Lemma public_dh_share_inv skI skR a :
  let ga := TExp (TInt 0) a in
  dh_key skI skR a -∗
  release_token ga -∗
  public ga -∗
  ▷ (public skI ∨ public skR).
Proof. Admitted.

Lemma public_dh_secret a b skI skR :
  let ga := TExp (TInt 0) a in
  let gb := TExp (TInt 0) b in
  dh_key skI skR a -∗
  dh_key skI skR b -∗
  early_failure ga false -∗
  early_failure gb false -∗
  has_peer_share ga gb -∗
  has_peer_share gb ga -∗
  (public (TExpN (TInt 0) [a; b]) → ◇ (released ga ∨ released gb)).
Proof.
iIntros (ga gb) "#dh_a #dh_b #efa #efb #ps_a #ps_b".
iPoseProof (dh_key_public_released with "dh_a efa ps_a") as "#rel_a".
iPoseProof (dh_key_public_released with "dh_b efb ps_b") as "#rel_b".
iDestruct "dh_a" as "(m_a & _ & pred_a)".
rewrite public_TExp2_iff //; last by eauto.
iIntros "[[_ #p_b] | [[_ #p_a] | (_ & contra & _)]]".
- iDestruct ("rel_b" with "p_b") as ">[#r #_]". by iRight.
- iDestruct ("rel_a" with "p_a") as ">[#r #_]". by iLeft.
- iPoseProof ("pred_a" with "contra") as "#contra2".
  iAssert (▷ False)%I as ">[]".
  { iModIntro. iDestruct "contra2" as "[_ %contra]".
    by rewrite /nsl_dh_key_share exps_TExpN /= in contra. }
Qed.

End Verif.

Arguments nsl_dh_ctx_alloc {Σ _ _ _} E.

Lemma nsl_dhGS_alloc `{!heapGS Σ, !cryptisGS Σ} E :
  ↑nsl_dhN ⊆ E →
  nsl_dhGpreS Σ →
  seal_pred_token AENC E ={⊤}=∗ ∃ (H : nsl_dhGS Σ),
    nsl_dh_ctx ∗ nsl_dh_token ⊤ ∗
    seal_pred_token AENC (E ∖ ↑nsl_dhN).
Proof.
iIntros "% % token".
iMod gmeta_token_alloc as (γ_meta) "own".
iExists (NslDhGS _ γ_meta).
iMod (nsl_dh_ctx_alloc with "token") as "[#H ?]" => //.
by iFrame.
Qed.

Arguments nsl_dhGS_alloc {Σ _ _ E}.
Arguments nsl_dh_pred_set {Σ _} N φ E.
Global Typeclasses Opaque session_ok.
