From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib guarded term crypto primitives tactics session.
From crypto Require Import coGset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TLS.

Context `{!cryptoG Σ, !heapG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types l : level.
Implicit Types rl : role.
Implicit Types Ψ : val → iProp.

Class tlsG := {
  in_tls_sessG :> sessionG Σ;
  tls_name : gname;
}.

Context `{!tlsG}.

Variable send recv : val.

(* MOVE *)
Lemma atomic_atoms t : atomic t → atoms t = {[t]}.
Proof. by case: t. Qed.

Lemma crypto_own_valid_2 td1 td2 :
  crypto_own td1 -∗
  crypto_own td2 -∗
  ✓ (td1 ⋅ td2).
Proof.
iIntros "#own1 #own2".
iAssert (crypto_own (td1 ⋅ td2)) as "own".
  by rewrite /crypto_own auth_own_op; iSplit.
iApply (auth_own_valid with "own").
Qed.

Lemma unpublished_op t Ts1 Ts2 :
  Ts1 ## Ts2 →
  unpublished t (Ts1 ⋅ Ts2) ⊣⊢ unpublished t Ts1 ∗ unpublished t Ts2.
Proof.
move=> disj; apply (anti_symm _).
- iDestruct 1 as (γ) "[#H1 H2]".
  rewrite coGset_pair_unset_union //.
  by iDestruct "H2" as "[H21 H22]"; iSplitL "H21"; iExists γ; iSplit.
- iIntros "[H1 H2]".
  iDestruct "H1" as (γ1) "[#H11 H12]".
  iDestruct "H2" as (γ2) "[#H21 H22]".
  iPoseProof (crypto_own_valid_2 with "H11 H21") as "%valid".
  case: valid => [] /= [] _ /= valid _.
  rewrite singleton_op singleton_valid in valid *.
  move=> /agree_op_invL' ->.
  iExists γ2; iSplit => //.
  by rewrite coGset_pair_unset_union // own_op; iFrame.
Qed.

Lemma unpublished_difference t Ts1 Ts2 :
  Ts1 ⊆ Ts2 →
  unpublished t Ts2 ⊣⊢ unpublished t Ts1 ∗ unpublished t (Ts2 ∖ Ts1).
Proof.
move=> sub.
rewrite {1}(_ : Ts2 = Ts1 ∪ (Ts2 ∖ Ts1)) ?unpublished_op //; first set_solver.
rewrite [_ ∪ _]comm_L difference_union_L. set_solver.
Qed.
(* /MOVE *)


Definition mkhashkey : val := λ: <>,
  let: "k" := mknonce #() in
  let: "k" := mkkey "k" in
  Fst "k".

Lemma wp_mkhashkey E lvl (Ψ : val → iProp) :
  ↑cryptoN ⊆ E →
  crypto_ctx -∗
  (∀ k, stermT lvl (TKey Enc k) -∗ Ψ (TKey Enc k)) -∗
  WP mkhashkey #() @ E {{ Ψ }}.
Proof.
iIntros (?) "#ctx post".
rewrite /mkhashkey; wp_pures.
wp_bind (mknonce _); iApply (wp_mknonce lvl) => //.
iIntros (k) "#Hk %atomic_k unpubl token".
have lvlP : lvl ⊔ lvl ⊑ lvl by rewrite level_join_idemp.
iMod (declare_key with "ctx Hk Hk [unpubl] []") as "(Hkey & _)" => //.
- by rewrite atomic_atoms // elem_of_singleton.
- iIntros "-> /=".
  rewrite (@unpublished_difference _ {[TKey Enc k; TKey Dec k]}); last set_solver.
  by iDestruct "unpubl" as "[??]".
- rewrite atomic_atoms // difference_diag_L; iIntros "_".
  by rewrite big_sepS_empty.
wp_pures; wp_bind (mkkey _); iApply wp_mkkey; wp_pures.
by iApply "post".
Qed.

Definition khash : val := λ: "k" "t",
  bind: "h" := tenc (nroot.@"tls".@"hash") "k" "t" in
  hash "h".

Lemma wp_khash E k t Ψ :
  Ψ (THash (TEnc k (Spec.tag (nroot.@"tls".@"hash") t))) -∗
  WP khash (TKey Enc k) t @ E {{ Ψ }}.
Proof.
iIntros "post"; rewrite /khash; wp_tenc.
by wp_pures; iApply wp_hash.
Qed.

Definition verify_khash : val := λ: "k" "t" "h",
  let: "h'" := khash "k" "t" in eq_term "h" "h'".

Lemma wp_verify_khash E k t h Ψ :
  Ψ (#(bool_decide (h = THash (TEnc k (Spec.tag (nroot.@"tls".@"hash") t))))) -∗
  WP verify_khash (TKey Enc k) t h @ E {{ Ψ }}.
Proof.
iIntros "post"; rewrite /verify_khash.
wp_pures; wp_bind (khash _ _); iApply wp_khash.
by wp_pures; iApply wp_eq_term.
Qed.

Definition verify N : val := λ: "k" "t" "s",
  match: tdec N "k" "s" with
    SOME "t'" => eq_term "t'" "t"
  | NONE      => #false
  end.

Lemma twp_verify E N k t sig Ψ :
  Ψ (#(bool_decide (sig = TEnc k (Spec.tag N t)))) -∗
  WP verify N (TKey Dec k) t sig @ E {{ Ψ }}.
Proof.
rewrite /verify; iIntros "post".
wp_pures; wp_tdec_eq m e; wp_pures.
- wp_eq_term e'; first by rewrite e e' bool_decide_true.
  rewrite bool_decide_false // e => - [ /Spec.tag_inj {} [??]]; congruence.
- move: e; rewrite /Spec.tdec /Spec.dec.
  case: sig => // k' t' untag_t'; rewrite bool_decide_false // => e.
  by case: e untag_t' => -> ->; rewrite decide_True // Spec.tagK.
Qed.

Definition client : val := λ: "sgnkC" "verkC" "pkS" "versionC",
  let: "nC" := mknonce #() in
  let: "m1" := term_of_list ["verkC"; "pkS"; "nC"; "versionC"] in
  send "m1";;
  (* Read server response *)
  let: "m2"        := recv #()   in
  bind: "m2'"      := list_of_term "m2" in
  bind: "pkS'"     := "m2'" !! #0 in
  bind: "verkC'"   := "m2'" !! #1 in
  bind: "nS"       := "m2'" !! #2 in
  bind: "versionS" := "m2'" !! #3 in
  assert: eq_term "pkS'" "pkS" && eq_term "verkC'" "verkC" in
  (* Send signature *)
  let: "secret"   := mkhashkey #() in
  bind: "encky"   := tenc (nroot.@"tls".@"secret") "pkS" "secret" in
  let:  "sigterm" := term_of_list ["m1"; "m2"; "encky"] in
  bind: "sig"     := tenc (nroot.@"tls".@"sig") "sgnkC" "sigterm" in
  (** NB In the PCL version, this hash includes a string "client" *)
  let: "hc2" := khash "secret" (term_of_list ["m1"; "m2"; "encky"; "sig"]) in
  let: "m3" := term_of_list ["verkC"; "pkS"; "encky"; "sig"; "hc2"] in
  send "m3";;
  (* Receive server confirmation *)
  let: "m4"     := recv #() in
  bind: "m4'"   := list_of_term "m4" in
  let: "pkS'"   := "m4'" !! #0 in
  let: "verkC'" := "m4'" !! #1 in
  let: "hs''"   := "m4'" !! #2 in
  assert: eq_term "pkS'" "pkS" && eq_term "verkC'" "verkC" in
  let: "hs0"    := term_of_list ["verkC"; "pkS"; "encky"; "sig"] in
  let: "hs'"    := term_of_list ["m1"; "m2"; "hs0"] in
  assert: verify_khash "secret" "hs'" "hs''" in
  SOME "secret".

Definition server : val := λ: "pkS" "skS" "versionS",
  (* Receive client request *)
  let: "m1"        := recv #() in
  bind: "m1'"      := list_of_term "m1" in
  bind: "verkC"    := "m1'" !! #0 in
  bind: "pkS'"     := "m1'" !! #1 in
  bind: "nC"       := "m1'" !! #2 in
  bind: "versionC" := "m1'" !! #3 in
  assert: eq_term "pkS'" "pkS" in
  (* Send back server info *)
  let: "nS" := mknonce #() in
  let: "m2" := term_of_list ["pkS"; "verkC"; "nS"; "versionS"] in
  send "m2";;
  (* Receive client signature *)
  let: "m3" := recv #() in
  bind: "m3'" := list_of_term "m3" in
  bind: "verkC'" := "m3'" !! #0 in
  bind: "pkS'"   := "m3'" !! #1 in
  bind: "encky"  := "m3'" !! #2 in
  bind: "sig"    := "m3'" !! #3 in
  bind: "hc2''"  := "m3'" !! #4 in
  assert: eq_term "verkC'" "verkC" && eq_term "pkS'" "pkS" in
  let: "sigterm" := term_of_list ["m1"; "m2"; "encky"] in
  assert: verify (nroot.@"tls".@"sig") "verkC" "sigterm" in
  bind: "secret" := tdec (nroot.@"tls".@"secret") "skS" "encky" in
  let: "hc2'" := term_of_list ["m1"; "m2"; "encky"; "sig"] in
  assert: verify_khash "secret" "hc2'" "hc2''" in
  let: "hs" := khash "secret" (term_of_list ["m1"; "m2"; "encky"; "sig"]) in
  send (term_of_list ["pkS"; "verkC"; "hs"]).

Hypothesis wp_send : forall E t Ψ,
  ▷ termT Pub t -∗
  Ψ #() -∗
  WP send t @ E {{ Ψ }}.

Hypothesis wp_recv : forall E Ψ,
  (∀ t, termT Pub t -∗ Ψ t) -∗
  WP recv #() @ E {{ Ψ }}.

End TLS.
