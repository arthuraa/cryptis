(* TLS 1.3 handshake — Meth (key-exchange method) proofs.

   WP specs for the [Meth.I] constructors + the [Meth_wf] well-formedness
   invariant and its public-encoding lemma.  Depends on impl + base; the first
   component proof file, imported by all the others. *)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.lib Require Import dh.
From cryptis.examples.tls13 Require Import impl.
From cryptis.examples.tls13.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Meth.

Section Proofs.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.

Lemma wp_Meth_Psk t E :
  {{{ True }}} I.Psk t @ E {{{ (v : val), RET v; ⌜v = term_of (Psk t)⌝ }}}.
Proof.
iIntros "%Φ _ post"; rewrite /I.Psk.
by wp_pures; wp_tag; iApply "post".
Qed.

Lemma wp_Meth_Dh t E :
  {{{ True }}} I.Dh t @ E {{{ (v : val), RET v; ⌜v = term_of (Dh t)⌝ }}}.
Proof.
iIntros "%Φ _ post"; rewrite /I.Dh.
by wp_pures; wp_tag; iApply "post".
Qed.

Lemma wp_Meth_PskDh t1 t2 E :
  {{{ True }}} I.PskDh t1 t2 @ E
  {{{ (v : val), RET v; ⌜v = term_of (PskDh t1 t2)⌝ }}}.
Proof.
iIntros "%Φ _ post"; rewrite /I.PskDh.
by wp_pures; wp_list; wp_term_of_list; wp_tag; iApply "post".
Qed.

Lemma wp_Meth_case ke (f_psk f_dh f_pskdh : val) E Φ :
  match ke with
  | Psk psk => WP f_psk psk @ E {{ Φ }}
  | Dh g => WP f_dh g @ E {{ Φ }}
  | PskDh psk g => WP f_pskdh psk g @ E {{ Φ }}
  end -∗
  WP I.case (term_of ke) f_psk f_dh f_pskdh @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.case.
wp_untag_eq psk e_psk.
  case: ke e_psk => [?|?|??] /= /Spec.tag_inj []; try set_solver.
  by move=> _ <-; wp_pures.
wp_untag_eq args e_dh.
  case: ke e_psk e_dh => [?|?|??] /= e_psk /Spec.tag_inj []; try set_solver.
  by move=> _ <- {e_psk args}; wp_pures.
wp_untag_eq args e_pskdh; last first.
  by case: ke e_psk e_dh e_pskdh =>> /=; rewrite Spec.tagK.
case: ke e_psk e_dh e_pskdh
  => [?|?|psk g] /= e_psk e_dh /Spec.tag_inj []; try set_solver.
move=> _ <- {e_psk e_dh args}; wp_pures; do !rewrite subst_list_match /=.
wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
move/Spec.of_list_inj: e_l => {l} <-.
by wp_list_match => // _ _ [<- <-].
Qed.

Definition Meth_wf ke : iProp :=
  match ke with
  | Psk psk => minted psk
  | Dh g => ⌜¬ is_exp g⌝ ∧ public g
  | PskDh psk g => minted psk ∧ ⌜¬ is_exp g⌝ ∧ public g
  end.

#[global]
Instance Meth_Persistent_wf ke : Persistent (Meth_wf ke).
Proof. by case: ke => *; apply _. Qed.

Lemma Meth_public_encode N ke :
  Keys.ctx N -∗
  Meth_wf ke -∗
  public (term_of (encode N ke)).
Proof.
iIntros "#hash #p_ke"; case: ke => [psk|g|psk g] /=.
- rewrite public_tag public_THash minted_tag.
  iRight; iSplit => //.
  by iExists _; eauto.
- iDestruct "p_ke" as "[_ ?]". by rewrite public_tag.
- iDestruct "p_ke" as "(s_psk & _ & p_g)".
  rewrite !public_tag public_of_list /= public_THash minted_tag.
  do !iSplit => //=.
  iRight; iSplit => //.
  by iExists _; eauto.
Qed.

End Proofs.

#[global]
Existing Instance Meth_Persistent_wf.
