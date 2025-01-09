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

Lemma session_agree si1 si2 :
  si_key si1 = si_key si2 →
  si1 = si2.
Proof.
case: si1 si2 => [kI1 kR1 ga1 gb1 gab1] [kI2 kR2 ga2 gb2 gab2] /=.
case/Spec.tag_inj => _.
by case/Spec.of_list_inj => <- <- <- <- <-.
Qed.

Definition compromised si : iProp :=
  public (TKey Seal (si_init si)) ∨
  public (TKey Seal (si_resp si)).

Definition session_status si (failed : bool) : iProp := ∃ a,
  ⌜si_init_share si = TExp (TInt 0) a⌝ ∗
  term_meta a (nroot.@"failed") failed.

Lemma session_status_agree si failed1 failed2 :
  session_status si failed1 -∗
  session_status si failed2 -∗
  ⌜failed1 = failed2⌝.
Proof.
rewrite /session_status.
iIntros "(%a1 & -> & #meta1) (%a2 & %e & #meta2)".
move/TExp_injr: e => <-.
by iApply (term_meta_agree with "meta1 meta2").
Qed.

Definition msg2_pred kR m2 : iProp :=
  ∃ ga b vkI,
    let vkR := TKey Open kR in
    let gb := TExp (TInt 0) b in
    let gab := TExp ga b in
    let secret := Spec.of_list [vkI; vkR; ga; gb; gab] in
    let key := Spec.derive_key secret in
    ⌜m2 = Spec.of_list [ga; gb; vkI]⌝ ∗
    (public b ↔ ▷ □ False) ∗
    (∀ t, dh_pred b t ↔ ▷ □ iso_dh_pred t).

Definition msg3_pred kI m3 : iProp :=
  ∃ a gb kR failed,
    let vkI := TKey Open kI in
    let vkR := TKey Open kR in
    let ga := TExp (TInt 0) a in
    let gab := TExp gb a in
    let si := SessInfo kI kR ga gb gab in
    ⌜m3 = Spec.of_list [ga; gb; vkR]⌝ ∗
    session_status si failed ∗
    (◇ public (si_key si) ↔ ▷ ⌜failed⌝) ∗
    (compromised si ∨ ⌜failed = false⌝).

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

Lemma public_dh_secret a b :
  □ (public a ↔ ▷ □ False) -∗
  □ (∀ t, dh_pred a t ↔ ▷ □ iso_dh_pred t) -∗
  □ (public b ↔ ▷ □ False) -∗
  □ (∀ t, dh_pred b t ↔ ▷ □ iso_dh_pred t) -∗
  ◇ public (TExpN (TInt 0) [a; b]) ↔ ▷ False.
Proof.
iIntros "#s_a #pred_a #s_b #pred_b".
rewrite public_TExp2_iff //; last by eauto.
iSplit; last by iIntros ">[]".
iIntros "> [[_ #p_b] | [[_ #p_a] | (_ & contra & _)]]".
- by iDestruct ("s_b" with "p_b") as ">[]".
- by iDestruct ("s_a" with "p_a") as ">[]".
iPoseProof ("pred_a" with "contra") as ">%contra".
by rewrite /iso_dh_pred exps_TExpN /= in contra.
Qed.

End Verif.

Arguments iso_dh_ctx_alloc {Σ _ _} N E.
