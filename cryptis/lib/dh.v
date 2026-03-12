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
  ▷ P (TExp g a).
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
  by iDestruct (dh_seed_elim0 with "aP contra") as ">[]".
iDestruct "H" as "(%t & %e_base & %a_t & H)".
iDestruct (dh_seed_dh_pred_base_elim with "aP H")
  as "{H} #[>-> H]" => //; iNext.
by rewrite -{2}[t']base_expsK exps_t' e_base.
Qed.

Lemma dh_seed_elim2 g a b :
  ¬ is_exp g →
  a ≠ TInv b →
  dh_seed a -∗
  dh_seed b -∗
  public (TExpN g [a; b]) -∗
  ▷ (⌜a = b⌝ ∧ P (TExp g a) ∧ P (TExp g b)).
Proof.
iIntros "%gXN %a_bV #aP #bP #p".
have exps_t : exps (TExpN g [a; b]) ≡ₚ [a; b].
  by rewrite exps_TExpN exps_expN //= cancel_exps_canceled ?invs_canceled2.
have a_t : a ∈ exps (TExpN g [a; b]) by rewrite exps_t; set_solver.
have b_t : b ∈ exps (TExpN g [a; b]) by rewrite exps_t; set_solver.
iPoseProof (dh_pred_exps a_t with "p") as "[dh_a _]".
iPoseProof (dh_pred_inv with "dh_a") as "(%c & %c_t & p_c)" => //.
rewrite exps_t elem_of_cons elem_of_list_singleton in c_t.
rewrite base_TExpN base_expN //.
iDestruct "p_c" as "[p_c|(%t' & %ebase & %exps_t'S & contra)]".
  case: c_t=> ->.
  - iDestruct (dh_seed_elim0 with "aP p_c") as ">[]".
  - iDestruct (dh_seed_elim0 with "bP p_c") as ">[]".
rewrite exps_t in exps_t'S.
iAssert (▷ □ dh_publ t')%I as "[>%len_t' #H]".
  iDestruct "aP" as "(_ & _ & #aP & _)".
  iDestruct "bP" as "(_ & _ & #bP & _)".
  by case: c_t => ->; [iApply "aP"|iApply "bP"].
case exps_t': (exps t') => [//|d [|//]] in exps_t'S len_t'.
have ->: t' = TExp g d by rewrite -exps_t' -ebase base_expsK.
have /elem_of_list_singleton ->: a ∈ [d] by set_solver.
have /elem_of_list_singleton ->: b ∈ [d] by set_solver.
by iModIntro; do !iSplit.
Qed.

Lemma dh_public_TExp g a :
  ¬ is_exp g →
  minted g -∗
  dh_seed a -∗
  ▷ □ P (TExp g a) -∗
  public (TExp g a).
Proof.
iIntros "%gXN #gP (#m & #aP1 & #aP2 & _) #P_a".
rewrite public_TExp_iff //; do !iSplit => //.
- iApply dh_pred_intro1. iApply "aP2"; do 2!iModIntro; iSplit => //.
  by rewrite exps_TExpN exps_expN.
- iModIntro; iIntros "#p".
  by iApply False_public; last iApply "aP1".
Qed.

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
