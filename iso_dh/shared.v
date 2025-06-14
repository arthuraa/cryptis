From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis primitives tactics.
From cryptis Require Import role.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition iso_dhN := nroot.@"iso_dh".

Record sess_info := SessInfo {
  si_init : term;
  si_resp : term;
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

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t skI skR nI nR sI sR kS : term).
Implicit Types (γ γa γb : gname) (ok failed : bool).
Implicit Types (ts : nat) (T : gset term).
Implicit Types (si : sess_info).

(*

A --> B: g^a; vkA
B --> A: {g^a; g^b; vkA}@skB
A --> B: {g^a; g^b; vkB}@skA

Result: derive_key [vkA; vkB; g^nA; g^nB; g^{nAnB}]

*)

Definition mk_keyshare : val := λ: "k",
  texp (tint #0) "k".

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

Definition iso_dh_pred t : iProp :=
  ⌜length (exps t) = 1⌝.

Definition si_key si :=
  Spec.derive_key
    (Spec.of_list [TKey Open (si_init si);
                   TKey Open (si_resp si);
                   si_init_share si;
                   si_resp_share si;
                   si_secret si]).

Lemma senc_key_si_key si :
  cryptis_ctx -∗
  minted (si_key si) -∗
  senc_key (si_key si).
Proof.
iIntros "#ctx #m_k". iSplit => //. iIntros "!> %kt".
rewrite public_derive_key minted_derive_key.
by iApply public_key_derive_key => //.
Qed.

Lemma session_agree si1 si2 :
  si_key si1 = si_key si2 →
  si1 = si2.
Proof.
case: si1 si2
  => [skI1 skR1 ga1 gb1 gab1] [skI2 skR2 ga2 gb2 gab2] /=.
case/Spec.tag_inj => _.
by case/Spec.of_list_inj => <- <- <- <- <-.
Qed.

Definition compromised_session rl si : iProp :=
  (compromised_key (si_init si) ∨ compromised_key (si_resp si)) ∗
  public (si_key si) ∗
  term_meta (si_share_of rl si) (iso_dhN.@"failed") true.

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

Definition unreleased share : iProp :=
  term_meta share (iso_dhN.@"released") false.

Lemma unrelease share : release_token share ==∗ unreleased share.
Proof. by apply term_meta_set. Qed.

Definition released_session si : iProp :=
  released (si_init_share si) ∧ released (si_resp_share si).

Lemma release_token_released_session si rl :
  release_token (si_share_of rl si) -∗
  released_session si -∗
  False.
Proof.
iIntros "token [#init #resp]".
iApply (term_meta_token with "token"); last by case: rl.
by [].
Qed.

Lemma unreleased_released_session si rl :
  unreleased (si_share_of rl si) -∗
  released_session si -∗
  False.
Proof.
iIntros "#un [#rI #rR]".
iAssert (released (si_share_of rl si)) as "r"; first by case: rl.
by iPoseProof (term_meta_agree with "r un") as "%".
Qed.

Definition session rl si : iProp :=
  □ (▷ released_session si → public (si_key si)) ∗
  ∃ failed,
    term_meta (si_share_of rl si) (iso_dhN.@"failed") failed ∗
    if failed then
      compromised_key (si_init si) ∨ compromised_key (si_resp si)
    else □ (public (si_key si) → ▷ released_session si).

Global Instance session_persistent rl si :
  Persistent (session rl si).
Proof. apply _. Qed.

Lemma secret_session rl si :
  secret (si_init si) -∗
  secret (si_resp si) -∗
  sign_key (si_init si) -∗
  sign_key (si_resp si) -∗
  session rl si -∗
  ◇ □ (public (si_key si) ↔ ▷ released_session si).
Proof.
iIntros "sI sR #signI #signR (#comp1 & %failed & #failed & #comp2)".
case: failed; eauto. iDestruct "comp2" as "[comp2|comp2]".
- by iDestruct (sign_secret_not_compromised_key with "sI [//] [//]")
    as ">[]".
- by iDestruct (sign_secret_not_compromised_key with "sR [//] [//]")
    as ">[]".
Qed.

Lemma unreleased_key_secrecy rl si :
  unreleased (si_share_of rl si) -∗
  □ (public (si_key si) ↔ ▷ released_session si) -∗
  □ (public (si_key si) ↔ ▷ False).
Proof.
iIntros "#un #s_k !>".
iApply (bi.iff_trans _ (▷ released_session si)). iSplit => //.
iSplit; last by iIntros ">[]".
iIntros "#re !>".
by iApply unreleased_released_session.
Qed.

Lemma release_token_key_secrecy rl si :
  release_token (si_share_of rl si) -∗
  □ (public (si_key si) ↔ ▷ released_session si) -∗
  public (si_key si) -∗
  ▷ False.
Proof.
iIntros "token #s_k #p_k".
iPoseProof ("s_k" with "p_k") as "contra".
iModIntro. by iApply (release_token_released_session with "token").
Qed.

Lemma session_compromised rl si :
  session rl si -∗
  public (si_key si) -∗
  release_token (si_share_of rl si) -∗
  ◇ compromised_session rl si.
Proof.
iIntros "(#comp1 & %failed & #failed & #comp2) #p_k rel".
case: failed; first by do !iSplit => //.
iDestruct (release_token_key_secrecy with "rel [] p_k") as ">[]".
iModIntro. by iSplit.
Qed.

Lemma session_not_compromised rl si :
  session rl si -∗
  secret (si_init si) -∗
  secret (si_resp si) -∗
  sign_key (si_init si) -∗
  sign_key (si_resp si) -∗
  ◇ □ ¬ compromised_session rl si.
Proof.
iIntros "(#comp1 & %failed & #failed & #comp2) s_kI s_kR #signI #signR".
case: failed; last first.
{ iIntros "!> !> (_ & _ & #contra)".
  by iPoseProof (term_meta_agree with "failed contra") as "%". }
iDestruct "comp2" as "[comp2|comp2]".
- iDestruct (sign_secret_not_compromised_key with "s_kI [//] [//]") as ">[]".
- iDestruct (sign_secret_not_compromised_key with "s_kR [//] [//]") as ">[]".
Qed.

Definition msg2_pred skR m2 : iProp :=
  ∃ ga b vkI,
    let vkR := TKey Open skR in
    let gb := TExp (TInt 0) b in
    let gab := TExp ga b in
    let secret := Spec.of_list [vkI; vkR; ga; gb; gab] in
    let key := Spec.derive_key secret in
    ⌜m2 = Spec.of_list [ga; gb; vkI]⌝ ∗
    ((∃ skI, ⌜vkI = TKey Open skI⌝ ∗
             (compromised_key skI ∨ compromised_key skR)) ∨
     (public b ↔ ▷ (released ga ∧ released gb))) ∗
    (∀ t, dh_pred b t ↔ ▷ □ iso_dh_pred t).

Definition msg3_pred kI m3 : iProp :=
  ∃ a gb kR,
    let vkI := TKey Open kI in
    let vkR := TKey Open kR in
    let ga := TExp (TInt 0) a in
    let gab := TExp gb a in
    let si := SessInfo kI kR ga gb gab in
    ⌜m3 = Spec.of_list [ga; gb; vkR]⌝ ∗
    ((compromised_key kI ∨ compromised_key kR) ∨
     □ (public (si_key si) → ▷ released_session si)).

Definition iso_dh_ctx : iProp :=
  seal_pred (iso_dhN.@"m2") msg2_pred ∗
  seal_pred (iso_dhN.@"m3") msg3_pred.

Lemma iso_dh_ctx_alloc E :
  ↑iso_dhN ⊆ E →
  seal_pred_token E ==∗
  iso_dh_ctx ∗ seal_pred_token (E ∖ ↑iso_dhN).
Proof.
iIntros "%sub token".
iMod (seal_pred_set (iso_dhN.@"m2") msg2_pred with "token")
  as "[? token]"; try solve_ndisj. iFrame.
iMod (seal_pred_set (iso_dhN.@"m3") msg3_pred with "token")
  as "[? token]"; try solve_ndisj. iFrame.
iApply (seal_pred_token_drop with "token"). solve_ndisj.
Qed.

Lemma public_dh_share a :
  minted a -∗
  □ (∀ t, dh_pred a t ↔ ▷ □ iso_dh_pred t) -∗
  public (TExp (TInt 0) a).
Proof.
iIntros "#m_a #pred_a". rewrite public_TExpN //=; eauto.
iRight. rewrite minted_TExp minted_TInt.
do !iSplit => //.
iApply "pred_a". do !iModIntro. iPureIntro. by rewrite exps_TExpN.
Qed.

Lemma public_dh_secret a b :
  minted a -∗
  minted b -∗
  □ (∀ t, dh_pred a t ↔ ▷ □ iso_dh_pred t) -∗
  □ (∀ t, dh_pred b t ↔ ▷ □ iso_dh_pred t) -∗
  (public (TExpN (TInt 0) [a; b]) ↔ ◇ (public a ∨ public b)).
Proof.
iIntros "#m_a #m_b #pred_a #pred_b".
rewrite public_TExp2_iff //; last by eauto.
rewrite minted_TExpN /= minted_TInt.
iSplit; last first.
{ rewrite /bi_except_0.
  iIntros "#[H|[H|H]]".
  - iRight. iRight. iSplit; eauto.
    by iSplit; [iApply "pred_a"|iApply "pred_b"];
    iDestruct "H" as ">[]".
  - iRight. iLeft. iSplit => //. by iApply public_dh_share.
  - iLeft. iSplit => //. by iApply public_dh_share. }
iIntros "[[_ #p_b] | [[_ #p_a] | (_ & contra & _)]]"; eauto.
iPoseProof ("pred_a" with "contra") as ">%contra".
by rewrite /iso_dh_pred exps_TExpN /= in contra.
Qed.

Lemma public_dh_secret' a b (P : iProp) :
  □ (public a ↔ P) -∗
  □ (∀ t, dh_pred a t ↔ ▷ □ iso_dh_pred t) -∗
  □ (public b ↔ P) -∗
  □ (∀ t, dh_pred b t ↔ ▷ □ iso_dh_pred t) -∗
  (public (TExpN (TInt 0) [a; b]) → ◇ P).
Proof.
iIntros "#s_a #pred_a #s_b #pred_b".
rewrite public_TExp2_iff //; last by eauto.
iIntros "[[_ #p_b] | [[_ #p_a] | (_ & contra & _)]]".
- by iModIntro; iApply "s_b".
- by iModIntro; iApply "s_a".
iPoseProof ("pred_a" with "contra") as ">%contra".
by rewrite /iso_dh_pred exps_TExpN /= in contra.
Qed.

End Verif.

Arguments iso_dh_ctx_alloc {Σ _ _} E.
