From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DH.

Context `{!cryptisGS Σ, !heapGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.

Implicit Types Ψ : val → iProp.
Implicit Types kA kB : term.

Variable P : term → iProp.

Definition dh_publ t : iProp :=
  ∃ g a, ⌜t = TExp g [a]⌝ ∧ □ P t.

Definition dh_seed t : iProp :=
  minted t ∧
  □ (public t ↔ ▷ False) ∧
  □ (∀ t', dh_pred t t' ↔ ▷ □ dh_publ t').

Lemma dh_seed_elim0 a :
  dh_seed a -∗
  public a -∗
  ▷ False.
Proof.
iIntros "#(_ & aP & _) #p_t".
by iApply "aP".
Qed.

Lemma dh_seed_elim1 g a :
  dh_seed a -∗
  public (TExp g [a]) -∗
  ▷ P (TExp g [a]).
Proof.
iIntros "#aP #p_t".
rewrite public_TExp1.
iDestruct "p_t" as "(_ & _ & [contra | p_t])".
  by iPoseProof (@dh_seed_elim0 with "aP contra") as ">[]".
iDestruct "aP" as "(_ & _ & #aP)".
iSpecialize ("aP" with "p_t"); iModIntro.
by iDestruct "aP" as (g' a') "# [%e aP]"; case/TExp_inj1: e => _ ->.
Qed.

Lemma dh_seed_elim2 g a t :
  dh_seed a -∗
  public (TExp g [a; t]) -∗
  ◇ (public (TExp g [a]) ∧ public t).
Proof.
iIntros "#aP #p_t".
rewrite public_TExp2.
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

Lemma dh_public_TExp g a :
  minted g -∗
  dh_seed a -∗
  ▷ □ P (TExp g [a]) -∗
  public (TExp g [a]).
Proof.
iIntros "#gP #(? & ? & aP) #P_a".
rewrite public_TExp1; do !iSplit => //.
by iRight; iApply "aP"; iModIntro; iExists _, _; eauto.
Qed.

Definition mkdh : val := mknonce.

Lemma wp_mkdh g (Ψ : val → iProp) :
  cryptis_ctx -∗
  minted g -∗
  (∀ a, minted a -∗
        dh_seed a -∗
        term_token (TExp g [a]) ⊤ -∗
        Ψ a) -∗
  WP mkdh #() {{ Ψ }}.
Proof.
iIntros "#ctx #minted_g post".
iApply (wp_mknonce_freshN ∅ (λ _, False%I) dh_publ (λ t, {[TExp g [t]]})
  with "[//]" ) => //.
- iIntros "%". rewrite elem_of_empty. by iIntros "[]".
- iIntros "%". rewrite big_sepS_singleton. iIntros "!>".
  rewrite minted_TExp /=.
  iSplit.
  + by iIntros "?"; do !iSplit.
  + by iIntros "(? & ? & ?)".
iIntros (a) "_ #m_a #(aP1 & aP2) #? token". rewrite big_sepS_singleton.
iApply "post" => //.
rewrite /dh_seed. do !iSplit => //.
iModIntro; iSplit.
- by iIntros "H"; iSpecialize ("aP1" with "H"); iModIntro.
- by iIntros "#?"; iApply "aP2"; iModIntro.
Qed.

End DH.
