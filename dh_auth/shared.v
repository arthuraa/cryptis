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

Record sess_info := SessInfo {
  si_init : term;
  si_resp : term;
  si_key  : term;
  si_time : nat;
  si_hon  : gset term;
}.

Global Instance sess_info_inhabited : Inhabited sess_info :=
  populate (SessInfo inhabitant inhabitant inhabitant inhabitant inhabitant).

Section Verif.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).
Implicit Types (γ γa γb : gname) (ok : bool).
Implicit Types (ts : nat) (T : gset term).
Implicit Types (si : sess_info).

Variable N : namespace.

(*

A --> B: g^a; vkA
B --> A: {g^a; g^b; vkA}@skB
A --> B: {g^a; g^b; vkB}@skA

g^{nAnB}

*)

Definition mkkeyshare : val := λ: "k",
  texp (tgroup (tint #0)) "k".

Lemma wp_mkkeyshare (t : term) E :
  {{{ True }}}
    mkkeyshare t @ E
  {{{ RET (repr (TExp (TInt 0) [t])); True : iProp}}}.
Proof.
iIntros "%Φ _ Hpost". wp_lam.
wp_bind (tint _). iApply wp_tint.
wp_bind (tgroup _). iApply wp_tgroup.
wp_bind (texp _ _). iApply wp_texp. rewrite Spec.texpA.
by iApply "Hpost".
Qed.

Definition dh_auth_pred t : iProp :=
  ⌜∀ g ks, t = TExp g ks → length ks = 1⌝.

Definition session_fail si : iProp :=
  public_at (si_time si) (TKey Enc (si_init si)) ∨
  public_at (si_time si) (TKey Enc (si_resp si)).

Definition session si : iProp :=
  ◯H{si_time si} si_hon si ∗
  term_meta (si_key si) (nroot.@"info")
    (si_init si, si_resp si, si_time si).

Lemma session_agree si1 si2 :
  si_key si1 = si_key si2 →
  session si1 -∗ session si2 -∗ ⌜si1 = si2⌝.
Proof.
case: si1 si2 => [kI1 kR1 kS n1 T1] [kI2 kR2 _ n2 T2] /= <-.
iIntros "[#hon1 #meta1] [#hon2 #meta2] /=".
iPoseProof (term_meta_agree with "meta1 meta2") as "%e".
case: e => <- <- <-.
by iPoseProof (honest_frag_agree with "hon1 hon2") as "->".
Qed.

Definition msg2_pred kR m2 : iProp :=
  ∃ ga b kI n T,
    let gb := TExp (TInt 0) [b] in
    let gab := Spec.texp ga b in
    let secret := Spec.of_list [ga; gb; gab] in
    let kS := Spec.tag (nroot.@"keys".@"sym") secret in
    ⌜m2 = Spec.of_list [ga; gb; TKey Dec kI]⌝ ∗
    minted_at n ga ∗
    (public b ↔ ▷ □ (public_at n (TKey Enc kI) ∨
                     public_at n (TKey Enc kR))) ∗
    (∀ t, dh_pred b t ↔ ▷ □ dh_auth_pred t) ∗
    ◯H{n} T ∗
    escrow cryptisN
      (term_token ga ⊤)
      (term_token kS (↑nroot.@"client")) ∗
    term_meta kS (nroot.@"info") (kI, kR, n).

Definition msg3_pred kI m3 : iProp :=
  ∃ a gb kR n T,
    let ga := TExp (TInt 0) [a] in
    let gab := Spec.texp gb a in
    let secret := Spec.of_list [ga; gb; gab] in
    let kS := Spec.tag (nroot.@"keys".@"sym") secret in
    ⌜m3 = Spec.of_list [ga; gb; TKey Dec kR]⌝ ∗
    (public a ↔ ▷ □ (public_at n (TKey Enc kI) ∨
                     public_at n (TKey Enc kR))) ∗
    (∀ t, dh_pred a t ↔ ▷ □ dh_auth_pred t) ∗
    ◯H{n} T ∗
    (public_at n (TKey Enc kR) ∨ term_meta kS (nroot.@"info") (kI, kR, n)).

Definition dh_auth_ctx : iProp :=
  enc_pred (N.@"m2") msg2_pred ∗
  enc_pred (N.@"m3") msg3_pred.

Lemma dh_auth_ctx_alloc E :
  ↑N ⊆ E →
  enc_pred_token E ==∗
  dh_auth_ctx.
Proof.
iIntros "%sub token".
iMod (enc_pred_set (N.@"m2") msg2_pred with "token")
  as "[#? token]"; try solve_ndisj.
iMod (enc_pred_set (N.@"m3") msg3_pred with "token")
  as "[#? token]"; try solve_ndisj.
iModIntro. by iSplit.
Qed.

Section WithSSRBool.

Import ssrbool.

Lemma eq_texp2 g a1 a2 b1 b2 :
  Spec.texp a1 b1 = Spec.texp (TExp g [a2]) b2 →
  a1 = TExp g [a2] ∧ b1 = b2 ∨
  a1 = TExp g [b2] ∧ b1 = a2.
Proof.
move=> e.
have /Spec.is_expP [g' [] ks e_exp] : is_true (is_exp a1).
  case exp: is_exp => //.
  rewrite Spec.is_expN_texp // ?exp //= in e *; auto.
  suff: is_true (is_exp (TInt 0)) by [].
  by rewrite e Spec.texpA is_exp_TExp.
rewrite {}e_exp !Spec.texpA {a1} in e *. symmetry in e.
case/TExp_inj: e => <- {g'} /(@Permutation_length_2_inv _ _ _ _) [].
- case=> <- -> {b2 ks}. by eauto.
- case=> <- -> {a2 ks}. by eauto.
Qed.

End WithSSRBool.

End Verif.

Arguments dh_auth_ctx_alloc {Σ _ _} N E.
