From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta nown saved_prop.
From cryptis Require Import cryptis primitives tactics role.
From cryptis.examples.iso_dh Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record sess_info := SessInfo {
  si_init : sign_key;
  si_resp : sign_key;
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

Class iso_dhGpreS Σ := IsoDhGPreS {
  iso_dhGpreS_meta : metaGS Σ;
  iso_dhGpreS_pred : savedPredG Σ (sign_key * sign_key * sess_info * role);
}.

Local Existing Instance iso_dhGpreS_meta.
Local Existing Instance iso_dhGpreS_pred.

Class iso_dhGS Σ := IsoDhGS {
  iso_dh_inG : iso_dhGpreS Σ;
  iso_dh_name : gname;
}.

Local Existing Instance iso_dh_inG.

Definition iso_dhΣ := #[
  metaΣ;
  savedPredΣ (sign_key * sign_key * sess_info * role)
].

Global Instance subG_iso_dhGpreS Σ : subG iso_dhΣ Σ → iso_dhGpreS Σ.
Proof. solve_inG. Qed.

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ, !iso_dhGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : sign_key) (failed : bool).
Implicit Types (si : sess_info).
Implicit Types (N : namespace) (E : coPset).
Implicit Types (φ : sign_key → sign_key → sess_info → role → iProp).

Definition iso_dh_token E : iProp :=
  gmeta_token iso_dh_name E.

Definition iso_dh_pred N φ : iProp :=
  nown iso_dh_name N
    (saved_pred DfracDiscarded (λ '(skI, skR, si, rl), φ skI skR si rl)).

Lemma iso_dh_pred_set N φ E :
  ↑N ⊆ E →
  iso_dh_token E ==∗ iso_dh_pred N φ ∗ iso_dh_token (E ∖ ↑N).
Proof. by iIntros "%"; iApply nown_alloc. Qed.

Lemma iso_dh_token_difference E1 E2 :
  E1 ⊆ E2 →
  iso_dh_token E2 ⊣⊢ iso_dh_token E1 ∗ iso_dh_token (E2 ∖ E1).
Proof. exact: gmeta_token_difference. Qed.

Lemma iso_dh_token_drop E1 E2 :
  E1 ⊆ E2 →
  iso_dh_token E2 -∗ iso_dh_token E1.
Proof. exact: gmeta_token_drop. Qed.

Definition iso_dh_ready N skI skR si : iProp := ∀ φ,
  iso_dh_pred N φ →
  term_token (si_init_share si) (↑iso_dhN.@"ready") ={⊤}=∗
    ▷ φ skI skR si Init.

Lemma iso_dh_ready_alloc N skI skR si φ :
  iso_dh_pred N φ -∗
  φ skI skR si Init ={⊤}=∗
  □ iso_dh_ready N skI skR si.
Proof.
iIntros "#N_φ φ_ts".
iMod (escrowI nroot with "φ_ts []") as "#?".
{ by iApply (term_token_switch (si_init_share si) (iso_dhN.@"ready")). }
iIntros "!> !>  %φ' #N_φ' ready".
iPoseProof (nown_valid_2 with "N_φ N_φ'") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #φ_eq]".
iSpecialize ("φ_eq" $! (skI, skR, si, Init)).
iMod (escrowE with "[//] ready") as "res" => //.
iIntros "!> !>". by iRewrite -"φ_eq".
Qed.

Lemma wp_mk_keyshare (t : term) :
  {{{ True }}}
    mk_keyshare t
  {{{ RET (repr (TExp (TInt 0) t)); True : iProp}}}.
Proof.
iIntros "%Φ _ Hpost". wp_lam.
wp_bind (tint _). iApply wp_tint.
wp_bind (texp _ _). iApply wp_texp.
by iApply "Hpost".
Qed.

Definition iso_dh_key_share t : iProp :=
  ⌜length (exps t) = 1⌝.

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
by case=> /Spec.sign_pkey_inj <- /Spec.sign_pkey_inj <- <- <- <-.
Qed.

Definition compromised si : iProp :=
  (public (si_init si) ∨ public (si_resp si)) ∗
  public (si_key si).

Lemma compromised_public si : compromised si ⊢ public (si_key si).
Proof. by iIntros "(_&?)". Qed.

Definition release_token share : iProp :=
  term_token share (↑iso_dhN.@"released").

Lemma release_tokenI share E :
  ↑iso_dhN.@"released" ⊆ E →
  term_token share E -∗
  release_token share ∗ term_token share (E ∖ ↑iso_dhN.@"released").
Proof.
iIntros "% ?"; by rewrite -term_token_difference.
Qed.

Definition released share : iProp :=
  term_meta share (iso_dhN.@"released") true.

Lemma release share : release_token share ==∗ released share.
Proof. by apply term_meta_set. Qed.

Definition released_session si : iProp :=
  released (si_init_share si) ∧ released (si_resp_share si).

Lemma unrelease rl si : release_token (si_share_of rl si) ==∗ □ ¬ released_session si.
Proof.
iIntros "tok".
iMod (term_meta_set (iso_dhN.@"released") false with "tok") as "#un" => //.
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

Definition msg2_pred skR m2 : iProp :=
  ∃ ga b skI N,
    let pkI := Spec.pkey skI in
    let pkR := Spec.pkey skR in
    let gb := TExp (TInt 0) b in
    let gab := TExp ga b in
    let si := SessInfo skI skR ga gb gab in
    ⌜m2 = Spec.of_list [ga; gb; pkI; Tag N]⌝ ∧
    ((public skI ∨ public skR) ∨ (public b ↔ ▷ (released ga ∧ released gb))) ∧
    (∀ t, dh_pred_base b t ↔ ▷ □ iso_dh_key_share t) ∧
    ⌜is_nonce b⌝ ∧
    ⌜¬ subterm b ga⌝ ∧
    iso_dh_ready N skI skR si.

Definition msg3_pred skI m3 : iProp :=
  ∃ a gb skR,
    let pkI := Spec.pkey skI in
    let pkR := Spec.pkey skR in
    let ga := TExp (TInt 0) a in
    let gab := TExp gb a in
    let si := SessInfo skI skR ga gb gab in
    ⌜m3 = Spec.of_list [ga; gb; pkR]⌝ ∧
    ((public skI ∨ public skR) ∨
      □ (public (si_key si) → ▷ released_session si)).

Definition iso_dh_ctx : iProp :=
  sign_pred (iso_dhN.@"m2") msg2_pred ∗
  sign_pred (iso_dhN.@"m3") msg3_pred.

Lemma iso_dh_ctx_alloc E :
  ↑iso_dhN ⊆ E →
  seal_pred_token SIGN E ==∗
  iso_dh_ctx ∗ seal_pred_token SIGN (E ∖ ↑iso_dhN).
Proof.
iIntros "%sub token".
iMod (sign_pred_set (N := iso_dhN.@"m2") msg2_pred with "token")
  as "[? token]"; try solve_ndisj. iFrame.
iMod (sign_pred_set (N := iso_dhN.@"m3") msg3_pred with "token")
  as "[? token]"; try solve_ndisj. iFrame.
iApply (seal_pred_token_drop with "token"). solve_ndisj.
Qed.

Lemma public_dh_share a :
  minted a -∗
  □ (∀ t, dh_pred_base a t ↔ ▷ □ iso_dh_key_share t) -∗
  public (TExp (TInt 0) a).
Proof.
iIntros "#m_a #pred_a".
rewrite public_TExpN //=; auto; last exact: invs_canceled1.
iRight. rewrite minted_TExp; auto.
rewrite TExpNK public_TInt minted_TInt.
do !iSplit => //; auto.
iApply dh_pred_intro1. iApply "pred_a". iPureIntro. by rewrite exps_TExpN.
Qed.

Lemma public_dh_secret1 a b :
  minted a -∗
  minted b -∗
  □ (∀ t, dh_pred_base a t ↔ ▷ □ iso_dh_key_share t) -∗
  □ (∀ t, dh_pred_base b t ↔ ▷ □ iso_dh_key_share t) -∗
  ◇ (public a ∨ public b) -∗
  public (TExpN (TInt 0) [a; b]).
Proof.
iIntros "#m_a #m_b #pred_a #pred_b".
case: (decide (a = TInv b)) => [-> {a} | a_b].
  by rewrite -TExp_TExpN TExpNK public_TInt; eauto.
rewrite public_TExp2_iff // /bi_except_0; eauto.
iIntros "#[H|[H|H]]".
- iRight; iRight; iSplit; eauto.
    by iApply all_minted_TExpN; rewrite minted_TInt; do !iSplit.
  do !iSplit.
  + by iApply dh_pred_intro1; iApply "pred_a"; auto.
  + by iApply dh_pred_intro1; iApply "pred_b"; auto.
  + by iIntros "!> _"; iApply public_TExp; [rewrite public_TInt | iApply False_public].
  + by iIntros "!> _"; iApply public_TExp; [rewrite public_TInt | iApply False_public].
- by iRight; iLeft; iSplit; first iApply public_dh_share.
- by iLeft; iSplit; first iApply public_dh_share.
Qed.

Lemma public_dh_secret2 a b :
  a ≠ b →
  a ≠ TInv b →
  □ (∀ t, dh_pred_base a t ↔ ▷ □ iso_dh_key_share t) -∗
  □ (∀ t, dh_pred_base b t ↔ ▷ □ iso_dh_key_share t) -∗
  public (TExpN (TInt 0) [a; b]) -∗
  ▷ (public a ∨ public b).
Proof.
iIntros "%a_b %a_bV #pred_a #pred_b".
rewrite public_TExp2_iff //; eauto.
iIntros "[[_ #p_b] | [[_ #p_a] | (_ & #contraA & #contraB & _)]]"; eauto.
iPoseProof (dh_pred_inv with "contraA") as "(%t & %t_share & H)".
  by apply: elem_of_TExpN2l; rewrite //= elem_of_nil; eauto.
have exps_share: exps (TExpN (TInt 0) [a; b]) ≡ₚ [a; b].
  by rewrite exps_TExpN' //= ?invs_canceled2; eauto.
rewrite exps_share elem_of_cons elem_of_list_singleton in t_share.
iDestruct "H" as "[H|(%t3 & %e_base & %exps_sub & base)]".
  by case: t_share=> ->; eauto.
rewrite exps_share in exps_sub.
iAssert (▷ □ iso_dh_key_share t3)%I as ">%contra".
  by case: t_share=> ->; [iApply "pred_a"|iApply "pred_b"].
case: (exps t3) => // c [|//] in exps_sub contra.
have [a_c b_c]: a ∈ [c] ∧ b ∈ [c] by set_solver.
rewrite !elem_of_list_singleton in a_c b_c; congruence.
Qed.

Lemma public_dh_secret' a b (P : iProp) :
  a ≠ b →
  a ≠ TInv b →
  □ (public a ↔ P) -∗
  □ (∀ t, dh_pred_base a t ↔ ▷ □ iso_dh_key_share t) -∗
  □ (public b ↔ P) -∗
  □ (∀ t, dh_pred_base b t ↔ ▷ □ iso_dh_key_share t) -∗
  (public (TExpN (TInt 0) [a; b]) → ▷ P).
Proof.
iIntros "%a_b %a_bV #s_a #pred_a #s_b #pred_b #p_share".
iPoseProof (public_dh_secret2 with "pred_a pred_b p_share") as "H" => //.
by iDestruct "H" as "[H|H]"; [iApply "s_a"|iApply "s_b"].
Qed.

End Verif.

Arguments iso_dh_ctx_alloc {Σ _ _ _} E.

Lemma iso_dhGS_alloc `{!heapGS Σ, !cryptisGS Σ} E :
  ↑iso_dhN ⊆ E →
  iso_dhGpreS Σ →
  seal_pred_token SIGN E ={⊤}=∗ ∃ (H : iso_dhGS Σ),
    iso_dh_ctx ∗ iso_dh_token ⊤ ∗
    seal_pred_token SIGN (E ∖ ↑iso_dhN).
Proof.
iIntros "% % token".
iMod gmeta_token_alloc as (γ_meta) "own".
iExists (IsoDhGS _ γ_meta).
iMod (iso_dh_ctx_alloc with "token") as "[#H ?]" => //.
by iFrame.
Qed.

Arguments iso_dhGS_alloc {Σ _ _ E}.
Arguments iso_dh_pred_set {Σ _} N φ E.
Global Typeclasses Opaque session_ok.
