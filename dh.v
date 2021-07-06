From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DH.

Context `{!cryptisG Σ, !heapG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.

Implicit Types Ψ : val → iProp.
Implicit Types kA kB : term.

Variable P : term → iProp.

Definition dh_publ t : iProp :=
  ∃ g a, ⌜t = TExp g [a]⌝ ∧ □ P t.

Definition dh_seed t : iProp :=
  sterm t ∧
  □ (pterm t ↔ ▷ False) ∧
  □ (∀ t', dh_pred t t' ↔ ▷ □ dh_publ t').

Lemma dh_seed_elim0 a :
  dh_seed a -∗
  pterm a -∗
  ▷ False.
Proof.
iIntros "#(_ & aP & _) #p_t".
by iApply "aP".
Qed.

Lemma dh_seed_elim1 g a :
  dh_seed a -∗
  pterm (TExp g [a]) -∗
  ▷ P (TExp g [a]).
Proof.
iIntros "#aP #p_t".
rewrite pterm_TExp1.
iDestruct "p_t" as "(_ & _ & [contra | p_t])".
  by iPoseProof (@dh_seed_elim0 with "aP contra") as ">[]".
iDestruct "aP" as "(_ & _ & #aP)".
iSpecialize ("aP" with "p_t"); iModIntro.
iDestruct "aP" as (g' a') "# [%e aP]".
by case/TExp_inj: e => _ /Permutation_singleton [] ->; eauto.
Qed.

Lemma dh_seed_elim2 g a t :
  dh_seed a -∗
  pterm (TExp g [a; t]) -∗
  ◇ (pterm (TExp g [a]) ∧ pterm t).
Proof.
iIntros "#aP #p_t".
rewrite pterm_TExp2.
iDestruct "p_t" as "[p_t|[[_ contra]|p_t]]"; eauto.
  by iPoseProof (@dh_seed_elim0 with "aP contra") as ">[]".
iDestruct "p_t" as "(_ & p_t & _)".
iDestruct "aP" as "(_ & _ & #aP)".
iPoseProof ("aP" with "p_t") as "{p_t} p_t".
iAssert (▷ False)%I as ">[]".
iModIntro.
iDestruct "p_t" as (g' a') "(%e & _)".
by case/TExp_inj: e => _ /Permutation_length.
Qed.

Lemma dh_pterm_TExp g a :
  sterm g -∗
  dh_seed a -∗
  ▷ □ P (TExp g [a]) -∗
  pterm (TExp g [a]).
Proof.
iIntros "#gP #(? & ? & aP) #P_a".
rewrite pterm_TExp1; do !iSplit => //.
by iRight; iApply "aP"; iModIntro; iExists _, _; eauto.
Qed.

Definition dh_meta `{Countable L} t N (x : L) : iProp :=
  (∃ g a, ⌜t = TExp g [a]⌝ ∧ nonce_meta a N x)%I.

Definition dh_meta_token t E : iProp :=
  (∃ g a, ⌜t = TExp g [a]⌝ ∧ nonce_meta_token a E)%I.

Program Global Instance dh_term_meta :
  TermMeta (@dh_meta) dh_meta_token.

Next Obligation.
iIntros (L ?? E t x N sub).
iDestruct 1 as (g a) "[-> token]".
iMod (term_meta_set _ _ x with "token") as "meta"; eauto.
by rewrite /dh_meta; eauto.
Qed.

Next Obligation.
iIntros (L ?? t x N E sub).
iDestruct 1 as (g a) "[-> token]".
iDestruct 1 as (??)  "[%e  meta]".
move/TExp_inj: e => [_ /Permutation_singleton [<-]].
by iApply (term_meta_meta_token with "token meta").
Qed.

Next Obligation.
iIntros (L ?? t N x1 x2).
iDestruct 1 as (g a) "[-> meta1]".
iDestruct 1 as (??)  "[%e meta2]".
move/TExp_inj: e => [_ /Permutation_singleton [<-]].
by iApply (term_meta_agree with "meta1 meta2").
Qed.

Next Obligation.
rewrite /dh_meta /dh_meta_token.
move=> t E1 E2 sub; iSplit.
- iDestruct 1 as (g a) "[-> token]".
  rewrite [nonce_meta_token _ _](term_meta_token_difference a E1 E2) //.
  by iDestruct "token" as "[token1 token2]"; iSplitL "token1"; eauto.
- iDestruct 1 as "[token1 token2]".
  iDestruct "token1" as (g a) "[-> token1]".
  iDestruct "token2" as (??) "[%e token2]".
  move/TExp_inj: e => [_ /Permutation_singleton [<-]].
  iExists _, _; iSplit => //.
  rewrite (term_meta_token_difference _ E1 E2) //.
  by iSplitL "token1".
Qed.

Definition mkdh : val := mknonce.

Lemma wp_mkdh g E (Ψ : val → iProp) :
  (∀ a, sterm a -∗
        dh_seed a -∗
        dh_meta_token (TExp g [a]) ⊤ -∗
        Ψ a) -∗
  WP mkdh #() @ E {{ Ψ }}.
Proof.
iIntros "post"; iApply (wp_mknonce _ False%I dh_publ).
iIntros (a) "#s_a #(aP1 & aP2) #? token"; iApply "post" => //.
do !iSplit => //.
iModIntro; iSplit.
- by iIntros "H"; iSpecialize ("aP1" with "H"); iModIntro.
- by iIntros "#?"; iApply "aP2"; iModIntro.
- by iExists g, a; eauto.
Qed.

End DH.
