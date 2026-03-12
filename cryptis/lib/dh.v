From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis Require Import cryptis primitives tactics.

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
  ⌜length (exps t) = 1⌝ ∧ P t.

Definition dh_seed t : iProp :=
  minted t ∧
  □ (public t ↔ ▷ False) ∧
  □ (∀ t', dh_pred_base t t' ↔ ▷ □ dh_publ t') ∧
  □ (∀ t', dh_pred_base (TInv t) t' ↔ ▷ False).

Lemma dh_seed_elim0 a :
  dh_seed a -∗
  public a -∗
  ▷ False.
Proof.
iIntros "#(_ & aP & _) #p_t".
by iApply "aP".
Qed.

Lemma dh_seed_dh_pred_base_elim a t :
  a ∈ exps t →
  dh_seed a -∗
  dh_pred_base a t -∗
  □ ▷ (⌜t = TExp (base t) a⌝ ∗ P t).
Proof.
iIntros "%a_t (_ & _ & #dh & _) #base".
iSpecialize ("dh" with "base"); iModIntro; iNext.
iDestruct "dh" as "#(%l_t & p_t)"; iFrame "#".
rewrite -[t in LHS]base_expsK.
case: (exps t) => // b [|//] in a_t l_t *.
by rewrite elem_of_list_singleton in a_t; subst b.
Qed.

Lemma dh_seed_elim1 g a :
  ¬ is_exp g →
  dh_seed a -∗
  public (TExp g a) -∗
  ▷ ◇ P (TExp g a).
Proof.
iIntros "%gNX #aP #p_t".
rewrite public_TExp_iff //.
iDestruct "p_t" as "(_ & _ & p_t & _)".
set t' := TExp g a.
(* MOVE *)
have exps_t': exps t' = [a].
  apply Permutation_singleton_r.
  by rewrite exps_TExpN exps_expN // cancel_exps1.
(* /MOVE *)
have a_t' : a ∈ exps t' by rewrite exps_t'; set_solver.
iPoseProof (dh_pred_inv_same with "p_t") as "[#contra|H]" => //.
  by iModIntro; iDestruct (dh_seed_elim0 with "aP contra") as ">[]".
iDestruct "H" as "(%t & %e_base & %a_t & H)".
iDestruct (dh_seed_dh_pred_base_elim with "aP H")
  as "{H} #[>-> H]" => //; iNext.
by rewrite -[t' in (◇ P t')%I]base_expsK exps_t' e_base.
Qed.

Lemma dh_seed_elim2 g a t :
  ¬ is_exp g →
  a ≠ TInv t →
  dh_seed a -∗
  public (TExpN g [a; t]) -∗
  ▷ ◇ (P (TExp g a) ∧ public t).
Proof. Admitted.
(* iIntros "%gXN %a_t #aP #p_t".
 * rewrite public_TExp2_iff //.
 * iDestruct "p_t" as "[[p_t ?]|[[_ contra]|p_t]]"; eauto.
 * - by iSplit; eauto; iApply dh_seed_elim1.
 * - by iPoseProof (@dh_seed_elim0 with "aP contra") as ">[]".
 * iDestruct "p_t" as "(_ & p_t & _)".
 * have t_t' : t ∈ exps (TExpN g [a; t]).
 *   by apply: elem_of_TExpN2r; rewrite // exps_expN // elem_of_nil; case.
 * iDestruct (dh_pred_inv_same with "p_t") as "[contra|p_t']".
 * - rewrite -TExp_TExpN -count_exp_gt0 count_exp_TExp_eq.
 *   rewrite count_exp_TExp (@decide_False _ (a = TInv t)) //.
 *   rewrite count_exp_eq0 ?exps_expN //; try set_solver.
 *   by case: decide; lia.
 * - iNext; iDestruct (dh_seed_elim0 with "aP contra") as ">[]".
 * rewrite base_TExpN; iDestruct "p_t'" as "(%t2' & %e_base & %a_t2' & p_t2')".
 * iDestruct (dh_seed_dh_pred_base_elim with "aP p_t2'") as "{p_t2'} #[>-> H]"
 *   => //.
 * rewrite {}e_base base_expN {t2' a_t2'} //; iSplit; first by eauto.
 * iDestruct (dh_pred_inv_gen _ t_t' with "p_t") as "{p_t H} [contra|p_t]".
 *   by iNext; iDestruct (dh_seed_elim0 with "aP contra") as ">[]".
 * iDestruct "p_t" as "[p_t|p_t]".
 *   iDestruct "p_t" as "(%t2' & %e_base & %a_t2' & p_t2')".
 *   iDestruct (dh_seed_dh_pred_base_elim with "aP p_t2'") as "{p_t2'} #[>-> H]"
 *     => //.
 *   i
 *
 *
 * iDestruct "aP" as "(_ & _ & #aP & _)".
 * iPoseProof ("aP" with "p_t2'") as "{p_t2'} p_t2'"; iNext.
 * iDestruct "p_t2'" as "#(%l_t2' & p_t2')".
 * have exps_t2' : exps t2' = [a].
 *   case: (exps
 *
 *
 * iPoseProof ("aP" with "p_t") as "{p_t} p_t".
 * iAssert (▷ False)%I as ">[]".
 * iModIntro.
 * iDestruct "p_t" as "(%e & _)".
 * by rewrite exps_TExpN' in e; last exact /invs_canceled2.
 * Qed. *)

Lemma dh_public_TExp g a :
  ¬ is_exp g →
  minted g -∗
  dh_seed a -∗
  ▷ □ P (TExp g a) -∗
  public (TExp g a).
Proof. Admitted.
(* iIntros "%gXN #gP #(? & ap1 & aP2) #P_a".
 * rewrite public_TExp_iff //; iRight; do !iSplit => //.
 * - iApply "aP2"; do 2!iModIntro; iSplit => //.
 *   by rewrite exps_TExpN exps_expN.
 * - iModIntro; iIntros "#p".
 *   by iApply False_public; last iApply "ap1".
 * Qed. *)

Definition mk_dh : val := mk_nonce.

Lemma wp_mk_dh g (Ψ : val → iProp) :
  ¬ is_exp g ->
  cryptis_ctx -∗
  minted g -∗
  (∀ a, minted a -∗
        dh_seed a -∗
        term_token (TExp g a) ⊤ -∗
        Ψ a) -∗
  WP mk_dh #() {{ Ψ }}.
Proof.
iIntros "% #ctx #minted_g post".
iApply (wp_mk_nonce_freshN ∅ (λ _, False%I) dh_publ (λ t, {[TExp g t]})
  with "[//]" ) => //.
- iIntros "%". rewrite elem_of_empty. by iIntros "[]".
- iIntros "%". rewrite big_sepS_singleton. iIntros "!>".
  rewrite minted_TExp //.
  iSplit.
  + by iIntros; iSplit.
  + by iIntros "(? & ?)".
iIntros (a) "_ _ #m_a #(aP1 & aP2) #? token". rewrite big_sepS_singleton.
iApply "post" => //.
rewrite /dh_seed. do !iSplit => //.
iModIntro; iSplit.
- by iIntros "H"; iSpecialize ("aP1" with "H"); iModIntro.
- by iIntros "#?"; iApply "aP2"; iModIntro.
Qed.

End DH.
