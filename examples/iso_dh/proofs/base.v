From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From mathcomp Require ssrbool.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition iso_dhN := nroot.@"iso_dh".

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

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : sign_key).
Implicit Types (γ γa γb : gname) (ok failed : bool).
Implicit Types (ts : nat) (T : gset term).
Implicit Types (si : sess_info).

(*

A --> B: g^a; pkA
B --> A: {g^a; g^b; pkA}@skB
A --> B: {g^a; g^b; pkB}@skA

Result: derive_key [pkA; pkB; g^a; g^b; g^ab]

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

Definition compromised rl si : iProp :=
  (public (si_init si) ∨ public (si_resp si)) ∗
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

Definition session skI skR rl si : iProp :=
  ⌜skI = si_init si⌝ ∗ ⌜skR = si_resp si⌝ ∗ minted (si_key si) ∗
  □ (▷ released_session si → public (si_key si)) ∗
  ∃ failed,
    term_meta (si_share_of rl si) (iso_dhN.@"failed") failed ∗
    if failed then public (si_init si) ∨ public (si_resp si)
    else □ (public (si_key si) → ▷ released_session si).

Global Instance session_persistent skI skR rl si :
  Persistent (session skI skR rl si).
Proof. apply _. Qed.

Lemma session_released_session skI skR rl si :
  session skI skR rl si -∗
  ▷ released_session si -∗
  public (si_key si).
Proof. iIntros "(_ & _ & _ & #H & _) #rel". by iApply "H". Qed.

Lemma secret_session skI skR rl si :
  secret skI -∗
  secret skR -∗
  session skI skR rl si -∗
  ◇ □ (public (si_key si) ↔ ▷ released_session si).
Proof.
iIntros "sI sR (-> & -> & _ & #comp1 & %failed & #failed & #comp2)".
case: failed; eauto. iDestruct "comp2" as "[comp2|comp2]".
- by iDestruct (secret_not_public with "sI comp2") as ">[]".
- by iDestruct (secret_not_public with "sR comp2") as ">[]".
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

Definition session_weak skI skR si : iProp :=
  ⌜skI = si_init si⌝ ∗ ⌜skR = si_resp si⌝ ∗ minted (si_key si) ∗
  ((public skI ∨ public skR) ∨ □ (public (si_key si) ↔ ▷ False)).

Lemma unreleased_session_weak skI skR rl si :
  session skI skR rl si -∗
  unreleased (si_share_of rl si) -∗
  session_weak skI skR si.
Proof.
iIntros "(-> & -> & #m_k & #s_k1 & %failed & _ & #s_k2) #un".
do !iSplit => //. case: failed; eauto.
iRight. iApply unreleased_key_secrecy => //. iModIntro.
by iSplit; eauto.
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

Lemma session_compromised skI skR rl si :
  session skI skR rl si -∗
  public (si_key si) -∗
  release_token (si_share_of rl si) -∗
  ◇ compromised rl si.
Proof.
iIntros "(-> & -> & _ & #comp1 & %failed & #failed & #comp2) #p_k rel".
case: failed; first by do !iSplit => //.
iDestruct (release_token_key_secrecy with "rel [] p_k") as ">[]".
iModIntro. by iSplit.
Qed.

Lemma session_not_compromised skI skR rl si :
  session skI skR rl si -∗
  secret skI -∗
  secret skR -∗
  ◇ □ ¬ compromised rl si.
Proof.
iIntros "(-> & -> & _ & #comp1 & %failed & #failed & #comp2) s_kI s_kR".
case: failed; last first.
{ iIntros "!> !> (_ & _ & #contra)".
  by iPoseProof (term_meta_agree with "failed contra") as "%". }
iDestruct "comp2" as "[comp2|comp2]".
- iDestruct (secret_not_public with "s_kI comp2") as ">[]".
- iDestruct (secret_not_public with "s_kR comp2") as ">[]".
Qed.

Lemma session_compromised' skI skR rl si :
  session skI skR rl si -∗
  compromised rl si -∗
  public skI ∨ public skR.
Proof. by iIntros "(-> & -> & _) (? & _)". Qed.

Definition msg2_pred skR m2 : iProp :=
  ∃ ga b skI,
    let pkI := Spec.pkey skI in
    let pkR := Spec.pkey skR in
    let gb := TExp (TInt 0) b in
    let gab := TExp ga b in
    ⌜m2 = Spec.of_list [ga; gb; pkI]⌝ ∧
    ((public skI ∨ public skR) ∨ (public b ↔ ▷ (released ga ∧ released gb))) ∧
    (∀ t, dh_pred b t ↔ ▷ □ iso_dh_pred t).

Definition msg3_pred skI m3 : iProp :=
  ∃ a gb skR,
    let pkI := Spec.pkey skI in
    let pkR := Spec.pkey skR in
    let ga := TExp (TInt 0) a in
    let gab := TExp gb a in
    let si := SessInfo skI skR ga gb gab in
    ⌜m3 = Spec.of_list [ga; gb; pkR]⌝ ∧
    ((public skI ∨ public skR) ∨ □ (public (si_key si) → ▷ released_session si)).

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
