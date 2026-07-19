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
  ⌜negb (is_mul t)⌝ ∧
  □ (public t ↔ ▷ False) ∧
  □ (∀ t', exp_pred_base t t' ↔ ▷ □ dh_publ t') ∧
  □ (public (TInv t) ↔ ▷ False) ∧
  □ (∀ t', exp_pred_base (TInv t) t' ↔ ▷ False).

Lemma dh_seed_elim0 a :
  dh_seed a -∗
  public a -∗
  ▷ False.
Proof.
iIntros "#(_ & _ & aP & _) #p_t".
by iApply "aP".
Qed.

Lemma dh_seed_exp_pred_base_elim a t :
  a ∈ exps t →
  dh_seed a -∗
  exp_pred_base a t -∗
  □ ▷ (⌜t = TExp (base t) a⌝ ∗ P t).
Proof.
iIntros "%a_t (_ & _ & _ & #dh & _) #base".
iSpecialize ("dh" with "base"); iModIntro; iNext.
iDestruct "dh" as "#(%l_t & p_t)"; iFrame "#".
rewrite -[t in LHS]base_expsK.
case: (exps t) => // b [|//] in a_t l_t *.
rewrite list_elem_of_singleton in a_t; subst b.
by rewrite /TExpN TMulN1.
Qed.

Lemma dh_seed_elim1 g a :
  ¬ is_exp g →
  dh_seed a -∗
  public (TExp g a) -∗
  ▷ P (TExp g a).
Proof.
iIntros "%gNX #aP #p_t".
iAssert ⌜negb (is_mul a)⌝%I as %Nm_a; first by iDestruct "aP" as "(_ & $ & _)".
rewrite public_TExp_iff //.
iDestruct "p_t" as "(_ & _ & p_t & _)".
set t' := TExp g a.
(* MOVE *)
have exps_t': exps t' = [a].
  apply Permutation_singleton_r.
  rewrite /t' (_ : TExp g a = TExpN g [a]); last by rewrite /TExpN TMulN1.
  rewrite exps_TExpN ?exps_expN //=;
    [by rewrite cancel_invs1
    |by rewrite ssrbool.andbT; exact: (proj2 (is_trueP _) Nm_a)].
(* /MOVE *)
have a_t' : a ∈ exps t' by rewrite exps_t'; set_solver.
iPoseProof (exp_pred_inv_same with "p_t") as "[#contra|H]" => //.
  by iDestruct (dh_seed_elim0 with "aP contra") as ">[]".
iDestruct "H" as "(%t & %e_base & %a_t & H)".
iDestruct (dh_seed_exp_pred_base_elim with "aP H")
  as "{H} #[>-> H]" => //; iNext.
have -> : t' = TExp (base t) a; last by iApply "H".
by rewrite /t' e_base base_TExp base_expN.
Qed.

Lemma dh_seed_elim2 g a b :
  ¬ is_exp g →
  a ≠ b →
  a ≠ TInv b →
  dh_seed a -∗
  dh_seed b -∗
  public (TExpN g [a; b]) -∗
  ▷ False.
Proof.
iIntros "%gXN %a_b %a_bV #aP #bP #p".
iAssert ⌜negb (is_mul a)⌝%I as %Nm_a; first by iDestruct "aP" as "(_ & $ & _)".
iAssert ⌜negb (is_mul b)⌝%I as %Nm_b; first by iDestruct "bP" as "(_ & $ & _)".
have atom_ab : is_true (atomic [a; b]).
  by rewrite /= (proj2 (is_trueP _) Nm_a) (proj2 (is_trueP _) Nm_b).
have exps_t : exps (TExpN g [a; b]) ≡ₚ [a; b].
  rewrite exps_TExpN ?exps_expN //=.
  by rewrite (cancel_invs_canceled atom_ab
    (proj2 (invs_canceled2 (proj2 (is_trueP _) Nm_a)
                           (proj2 (is_trueP _) Nm_b)) a_bV)).
have a_t : a ∈ exps (TExpN g [a; b]) by rewrite exps_t; set_solver.
have b_t : b ∈ exps (TExpN g [a; b]) by rewrite exps_t; set_solver.
iPoseProof (exp_pred_exps a_t with "p") as "[dh_a _]".
iPoseProof (exp_pred_inv with "dh_a") as "(%c & %c_t & p_c)" => //.
rewrite exps_t elem_of_cons list_elem_of_singleton in c_t.
rewrite base_TExpN base_expN //.
iDestruct "p_c" as "[p_c|(%t' & %ebase & %exps_t'S & contra)]".
  case: c_t=> ->.
  - iDestruct (dh_seed_elim0 with "aP p_c") as ">[]".
  - iDestruct (dh_seed_elim0 with "bP p_c") as ">[]".
rewrite exps_t in exps_t'S.
iAssert (▷ □ dh_publ t')%I as "[>%len_t' #H]".
  iDestruct "aP" as "(_ & _ & _ & #aP & _)".
  iDestruct "bP" as "(_ & _ & _ & #bP & _)".
  by case: c_t => ->; [iApply "aP"|iApply "bP"].
case exps_t': (exps t') => [//|d [|//]] in exps_t'S len_t'.
have ->: t' = TExp g d.
  by rewrite -[t' in LHS]base_expsK ebase exps_t' /TExpN TMulN1.
move: a_b.
have /list_elem_of_singleton ->: a ∈ [d] by set_solver.
have /list_elem_of_singleton ->: b ∈ [d] by set_solver.
congruence.
Qed.

Lemma dh_public_TExp g a :
  ¬ is_exp g →
  minted g -∗
  dh_seed a -∗
  ▷ □ P (TExp g a) -∗
  public (TExp g a).
Proof.
iIntros "%gXN #gP (#m & %Nm_a & #aP1 & #aP2 & #aPV & _) #P_a".
rewrite public_TExp_iff //; do !iSplit => //.
- iApply exp_pred_intro1. iApply "aP2"; do 2!iModIntro; iSplit => //.
  iPureIntro; suff -> : exps (TExp g a) = [a] by [].
  apply Permutation_singleton_r.
  rewrite (_ : TExp g a = TExpN g [a]); last by rewrite /TExpN TMulN1.
  rewrite exps_TExpN ?exps_expN //=;
    [by rewrite cancel_invs1
    |by rewrite ssrbool.andbT; exact: (proj2 (is_trueP _) Nm_a)].
- iModIntro; iIntros "#p".
  by iApply False_public; last iApply "aPV".
Qed.

Definition mk_dh : val := mk_nonce.

Lemma wp_mk_dh (T : gset term) g (Ψ : val → iProp) :
  ¬ is_exp g ->
  cryptis_ctx -∗
  minted g -∗
  □ (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ a, minted a -∗
        dh_seed a -∗
        term_token a ⊤ -∗
        term_token (TExp g a) ⊤ -∗
        ⌜∀ t t', t ∈ T → subterm t' t → a ≠ t' ∧ a ≠ TInv t'⌝ -∗
        Ψ a) -∗
  WP mk_dh #() {{ Ψ }}.
Proof.
iIntros "% #ctx #minted_g #minted_T post".
iApply wp_fupd.
iApply (wp_mk_nonce_freshN T (λ _, False%I) dh_publ
         (λ t, {[t; TInv t; TExp g t]})
  with "[//]" ) => //.
  iIntros "%t".
  rewrite big_sepS_forall; iIntros (t').
  rewrite !elem_of_union !elem_of_singleton; iIntros "[[->|->]|->]"; eauto.
  - by rewrite minted_TInv; iIntros "!>"; iSplit; eauto.
  - rewrite minted_TExp //; iIntros "!>"; iSplit; eauto.
    by iIntros "[??]".
iIntros (a) "%a_T %nonce_a #m_a #aP #? #sV #? token".
have Nm_a : negb (is_mul a) by case: (a) nonce_a.
have a_g: TInv a ∉ exps g.
  by rewrite exps_expN // elem_of_nil; case.
have [? [] aV_ga a_ga] := tsize_lt_TExp Nm_a a_g.
have {}a_aV : TInv a ≠ a := TInv_neq Nm_a.
have {}a_ga : a ≠ TExp g a.
  move=> contra; rewrite -contra in a_ga; lia.
have {}aV_ga : TInv a ≠ TExp g a.
  move=> contra; rewrite -contra in aV_ga; lia.
rewrite big_sepS_union ?big_sepS_singleton; last set_solver.
iDestruct "token" as "[t1 t3]".
rewrite big_sepS_union ?big_sepS_singleton; last set_solver.
iDestruct "t1" as "[t1 t2]".
iMod ("sV" $! False%I with "t2") as "#s2V" => //.
iApply ("post" with "[//] [] [$] [$]") => //.
  iFrame "#"; rewrite bi.intuitionistic_intuitionistically.
  by eauto.
iPureIntro => t t' t_T t'_t; split => contra.
- apply: (a_T _ t_T); congruence.
- rewrite -[t']TInvK -contra in t'_t.
  apply: (a_T _ t_T); apply: subterm_trans t'_t.
  by constructor => //; case: (a) => // in nonce_a *.
Qed.

End DH.
