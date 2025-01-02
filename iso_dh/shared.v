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
  si_init_share : term;
  si_resp_share : term;
  si_secret : term;
  si_time : nat;
}.

Global Instance sess_info_inhabited : Inhabited sess_info :=
  populate (SessInfo inhabitant inhabitant inhabitant
              inhabitant inhabitant inhabitant).

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

Result: derive_key [vkA; vkB; g^nA; g^nB; g^{nAnB}]

*)

Definition mkkeyshare : val := λ: "k",
  texp (tint #0) "k".

Lemma wp_mkkeyshare (t : term) :
  {{{ True }}}
    mkkeyshare t
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

Definition session_fail si : iProp :=
  public_at (si_time si) (TKey Seal (si_init si)) ∨
  public_at (si_time si) (TKey Seal (si_resp si)).

Definition session si : iProp :=
  ◯Ph (si_time si) ∗
  term_meta (si_key si) (nroot.@"info") (si_time si).

Lemma session_agree si1 si2 :
  si_key si1 = si_key si2 →
  session si1 -∗ session si2 -∗ ⌜si1 = si2⌝.
Proof.
case: si1 si2 => [kI1 kR1 ga1 gb1 gab1 n1] [kI2 kR2 ga2 gb2 gab2 n2] /=.
case/Spec.tag_inj => _.
case/Spec.of_list_inj => <- <- <- <- <-.
iIntros "[#hon1 #meta1] [#hon2 #meta2] /=".
by iPoseProof (term_meta_agree with "meta1 meta2") as "->".
Qed.

Definition msg2_pred kR m2 : iProp :=
  ∃ ga b vkI n,
    let vkR := TKey Open kR in
    let gb := TExp (TInt 0) b in
    let gab := TExp ga b in
    let secret := Spec.of_list [vkI; vkR; ga; gb; gab] in
    let key := Spec.derive_key secret in
    ⌜m2 = Spec.of_list [ga; gb; vkI]⌝ ∗
    minted_at n ga ∗
    (public b ↔ ▷ □ ((∃ kI, ⌜vkI = TKey Open kI⌝ ∗ public_at n (TKey Seal kI)) ∨
                     public_at n (TKey Seal kR))) ∗
    (∀ t, dh_pred b t ↔ ▷ □ iso_dh_pred t) ∗
    term_meta key (nroot.@"info") n.

Definition msg3_pred kI m3 : iProp :=
  ∃ a gb kR n,
    let vkI := TKey Open kI in
    let vkR := TKey Open kR in
    let ga := TExp (TInt 0) a in
    let gab := TExp gb a in
    let si := SessInfo kI kR ga gb gab n in
    ⌜m3 = Spec.of_list [ga; gb; vkR]⌝ ∗
    (public a ↔ ▷ □ (public_at n (TKey Seal kI) ∨
                     public_at n (TKey Seal kR))) ∗
    (∀ t, dh_pred a t ↔ ▷ □ iso_dh_pred t) ∗
    (public_at n (TKey Seal kR) ∨ term_meta (si_key si) (nroot.@"info") n).

Definition iso_dh_ctx : iProp :=
  seal_pred (N.@"m2") msg2_pred ∗
  seal_pred (N.@"m3") msg3_pred.

Lemma iso_dh_ctx_alloc E :
  ↑N ⊆ E →
  seal_pred_token E ==∗
  iso_dh_ctx.
Proof.
iIntros "%sub token".
iMod (seal_pred_set (N.@"m2") msg2_pred with "token")
  as "[#? token]"; try solve_ndisj.
iMod (seal_pred_set (N.@"m3") msg3_pred with "token")
  as "[#? token]"; try solve_ndisj.
iModIntro. by iSplit.
Qed.

End Verif.

Arguments iso_dh_ctx_alloc {Σ _ _} N E.
