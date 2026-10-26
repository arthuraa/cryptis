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
Abbreviation iProp := (iProp Σ).

Implicit Types t : term.

Implicit Types Ψ : val → iProp.
Implicit Types kA kB : term.

Variable P : term → iProp.

(** [t] is a Diffie-Hellman share or shared secret: it has exactly one
    exponent.  This is the whole of what the secrecy lemmas at the end of this
    file read off a seed's [exp_pred_base], and [dh_publ] is it plus whatever
    invariant [P] the protocol wants to attach. *)
Definition dh_key_share t : iProp :=
  ⌜length (elements (exps t)) = 1⌝.

Definition dh_publ t : iProp :=
  dh_key_share t ∧ P t.

Definition dh_seed t : iProp :=
  minted t ∧
  ⌜negb (is_mul t)⌝ ∧
  □ (public t ↔ ▷ False) ∧
  □ (∀ t', exp_pred_base t t' ↔ ▷ □ dh_publ t') ∧
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
  a ∈ SMS.pos (exps t) →
  dh_seed a -∗
  exp_pred_base a t -∗
  □ ▷ (⌜t = TExp (base t) a⌝ ∗ P t).
Proof.
iIntros "%a_t (_ & %Nm_a & _ & #dh & _) #base".
iSpecialize ("dh" with "base"); iModIntro; iNext.
iDestruct "dh" as "#(%l_t & p_t)"; iFrame "#"; iPureIntro.
rewrite -[t in LHS]base_expsK; congr TExp.
have -> : exps t = {[+ a +]}.
  apply: SMS.car_inj; rewrite SMS.car_singleton.
  move: l_t a_t; rewrite SMS.elements_pos_neg /SMS.pos /SMS.neg.
  case: (SMS.car (exps t)) => [[|x [|? ?]] [|y [|? ?]]] //=.
  - by move=> _ /elem_of_nil.
  - by move=> _ /list_elem_of_singleton ->.
by rewrite -(factors_Nmul _ Nm_a) factorsK.
Qed.

Lemma dh_seed_elim1 g a :
  negb (is_exp g) → negb (is_gmul g) →
  dh_seed a -∗
  public (TExp g a) -∗
  ▷ P (TExp g a).
Proof.
iIntros "%gNX %gNm #aP #p_t".
iAssert ⌜negb (is_mul a)⌝%I as %Nm_a; first by iDestruct "aP" as "(_ & $ & _)".
rewrite public_TExp_iff //.
iDestruct "p_t" as "(_ & _ & p_t & _)".
set t' := TExp g a.
have a_t' : a ∈ SMS.pos (exps t').
  rewrite /t' (exps_TExp_expN _ _ gNX gNm) factors_Nmul //.
  by rewrite SMS.pos_singleton; set_solver.
iPoseProof (exp_pred_inv_same with "p_t") as "[#contra|H]" => //.
  by iDestruct (dh_seed_elim0 with "aP contra") as ">[]".
iDestruct "H" as "(%t & %e_base & %a_t & H)".
iDestruct (dh_seed_exp_pred_base_elim with "aP H")
  as "{H} #[>-> H]" => //; iNext.
have -> : t' = TExp (base t) a; last by iApply "H".
by rewrite /t' e_base (base_TExp _ _ gNm) base_expN.
Qed.

Lemma dh_seed_elim2 g a b :
  negb (is_exp g) → negb (is_gmul g) →
  dh_seed a -∗
  dh_seed b -∗
  public (TExp g (TMul {[+ a; b +]})) -∗
  ▷ False.
Proof.
iIntros "%gXN %gNm #aP #bP #p".
iAssert ⌜negb (is_mul a)⌝%I as %Nm_a; first by iDestruct "aP" as "(_ & $ & _)".
iAssert ⌜negb (is_mul b)⌝%I as %Nm_b; first by iDestruct "bP" as "(_ & $ & _)".
have expsE : exps (TExp g (TMul {[+ a; b +]})) = SMS.make [a; b] [].
  rewrite exps_TExp_TMul // => u.
  by case/SMS.elem_of_disj_union => /SMS.elem_of_singleton ->.
have ab_t : [a; b] ⊆+ SMS.pos (exps (TExp g (TMul {[+ a; b +]}))).
  by apply: Permutation_submseteq; rewrite expsE SMS.pos_make_nil_r.
have a_ab : a ∈ [a; b] by set_solver.
have a_t : a ∈ SMS.pos (exps (TExp g (TMul {[+ a; b +]}))).
  exact: elem_of_submseteq _ _ _ a_ab ab_t.
iPoseProof (exp_pred_exps a_t with "p") as "[dh_a _]".
iPoseProof (exp_pred_inv_gen a_ab ab_t with "dh_a") as "(%c & %c_ab & p_c)".
rewrite elem_of_cons list_elem_of_singleton in c_ab.
iDestruct "p_c" as "[p_c|(%t' & _ & %ab_t' & contra)]".
  case: c_ab => ->.
  - iDestruct (dh_seed_elim0 with "aP p_c") as ">[]".
  - iDestruct (dh_seed_elim0 with "bP p_c") as ">[]".
iAssert (▷ □ dh_publ t')%I as "[>%len_t' _]".
  iDestruct "aP" as "(_ & _ & _ & #aP & _)".
  iDestruct "bP" as "(_ & _ & _ & #bP & _)".
  by case: c_ab => ->; [iApply "aP"|iApply "bP"].
move: len_t' (submseteq_length _ _ ab_t').
by rewrite SMS.elements_pos_neg length_app /=; lia.
Qed.

Lemma dh_public_TExp g a :
  negb (is_exp g) → negb (is_gmul g) →
  minted g -∗
  dh_seed a -∗
  ▷ □ P (TExp g a) -∗
  public (TExp g a).
Proof.
iIntros "%gXN %gNm #gP (#m & %Nm_a & #aP1 & #aP2 & _) #P_a".
rewrite public_TExp_iff //; do !iSplit => //.
- iApply exp_pred_intro1. iApply "aP2"; do 2!iModIntro; iSplit => //.
  iPureIntro.
  by rewrite (exps_TExp_expN _ _ gXN gNm) factors_Nmul.
- iModIntro; iIntros "#p".
  by iApply False_public; last iApply "aP1".
Qed.

Definition mk_dh : val := mk_nonce.

Lemma wp_mk_dh (T : gset term) g (Ψ : val → iProp) :
  negb (is_exp g) -> negb (is_gmul g) ->
  cryptis_ctx -∗
  minted g -∗
  □ (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
  (∀ a, minted a -∗
        dh_seed a -∗
        term_token a ⊤ -∗
        term_token (TExp g a) ⊤ -∗
        ⌜∀ t t', t ∈ T → subterm t' t → a ≠ TInv t'⌝ -∗
        Ψ a) -∗
  WP mk_dh #() {{ Ψ }}.
Proof.
iIntros "%gNX %gNm #ctx #minted_g #minted_T post".
iApply (wp_mk_nonce_freshN T (λ _, False%I) dh_publ
         (λ t : nonce, {[t : term; TExp g t]})
  with "[//]" ) => //.
  iIntros "%t".
  rewrite big_sepS_forall; iIntros (t').
  rewrite elem_of_union !elem_of_singleton; iIntros "[->|->]"; eauto.
  rewrite minted_TExp //; iIntros "!>"; iSplit; eauto.
  by iIntros "[??]".
iIntros (a) "%a_T #m_a #aP #? #? token".
have Nm_a : negb (is_mul a) by [].
have a_g : TNonce a ∉ SMS.neg (exps g).
  rewrite /exps (expo_expN _ gNX) factors_TMul_empty; exact: not_elem_of_nil.
have [_ a_ga] := tsize_lt_TExp _ _ gNm Nm_a a_g.
have {}a_ga : TNonce a ≠ TExp g a.
  move=> contra; rewrite -contra in a_ga; lia.
rewrite big_sepS_union ?big_sepS_singleton; last set_solver.
iDestruct "token" as "[t1 t3]".
iApply ("post" with "[$] [] [$] [$]") => //.
  iFrame "#"; rewrite bi.intuitionistic_intuitionistically.
  by eauto.
iPureIntro => t t' t_T t'_t contra.
rewrite -[t']TInvK -contra in t'_t.
apply: (a_T _ t_T); apply: subterm_trans t'_t.
apply: (@subterm_factors _ _ (TNonce a)); last exact: STRefl.
by rewrite elem_of_factors_TInv (elem_of_factors_Nmul _ Nm_a).
Qed.

End DH.

(** [P] plays no role below, so these live outside [Section DH]: inside it the
    unused section variable would be generalised into every statement. *)
Section DHKeyShare.

Context `{!cryptisGS Σ, !heapGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types t : term.

(** ** Shares and secrets of a [dh_key_share] seed

    A protocol that does not want [dh_seed]'s "the seed is never public" clause
    -- ISO-DH and OPAQUE both need a weaker, conditional secrecy -- still gets
    the two facts that matter from the bare
    [∀ t, exp_pred_base a t ↔ ▷ □ dh_key_share t]: its share [g^a] is public,
    and [g^ab] stays secret as long as both seeds do. *)

(* [dh_public_TExp] without [dh_seed]'s secrecy clause on [a].  That clause is
   what discharges [public a → public g] by absurdity, so without it the
   generator has to be public -- which it always is. *)
Lemma public_dh_share g a :
  negb (is_exp g) → negb (is_gmul g) →
  negb (is_mul a) →
  public g -∗
  minted a -∗
  □ (∀ t, exp_pred_base a t ↔ ▷ □ dh_key_share t) -∗
  public (TExp g a).
Proof.
move=> gNx gNm Nm; iIntros "#p_g #m_a #pred_a".
iPoseProof (public_minted with "p_g") as "#m_g".
rewrite public_TExp_iff //.
do !iSplit => //; last by iIntros "!> _".
iApply exp_pred_intro1. iApply "pred_a". iPureIntro. rewrite /dh_key_share.
by rewrite (exps_TExp_expN _ _ gNx gNm) factors_Nmul // SMS.elements_singleton.
Qed.

(* Either seed being public makes the shared secret public. *)
Lemma public_dh_secret1 g a b :
  negb (is_exp g) → negb (is_gmul g) →
  negb (is_mul a) →
  negb (is_mul b) →
  public g -∗
  minted a -∗
  minted b -∗
  □ (∀ t, exp_pred_base a t ↔ ▷ □ dh_key_share t) -∗
  □ (∀ t, exp_pred_base b t ↔ ▷ □ dh_key_share t) -∗
  public a ∨ public b -∗
  public (TExp g (TMul {[+ a; b +]})).
Proof.
move=> gNx gNm Nm_a Nm_b.
iIntros "#p_g #m_a #m_b #pred_a #pred_b #[H|H]".
- rewrite -TExpA TExpC.
  iApply public_TExp => //. by iApply (public_dh_share gNx gNm Nm_b).
- rewrite -TExpA.
  iApply public_TExp => //. by iApply (public_dh_share gNx gNm Nm_a).
Qed.

(* The general form of [public_dh_secret2]: [a] and [b] need only *occur* among
   the exponents of [t], not exhaust them.  [exp_pred_inv_gen] already takes an
   arbitrary sub-multiset of [exps t], so the other exponents -- which may well
   be public, as HMQV's hash multipliers are -- are simply skipped.  A version
   that concluded only "*some* exponent of [t] is public" would be vacuous
   there.  Since multiplicities count, [a] may equal [b]: a share has a single
   exponent, so it never contains [a] twice. *)
Lemma public_dh_secret_gen2 a b t :
  [a; b] ⊆+ SMS.pos (exps t) →
  □ (∀ u, exp_pred_base a u ↔ ▷ □ dh_key_share u) -∗
  □ (∀ u, exp_pred_base b u ↔ ▷ □ dh_key_share u) -∗
  public t -∗
  public a ∨ public b.
Proof.
iIntros "%ab_t #pred_a #pred_b #p".
have a_t : a ∈ SMS.pos (exps t).
  by apply: (elem_of_submseteq _ _ _ _ ab_t); set_solver.
have b_t : b ∈ SMS.pos (exps t).
  by apply: (elem_of_submseteq _ _ _ _ ab_t); set_solver.
iPoseProof (public_minted with "p") as "#m".
iAssert (minted a ∧ minted b)%I as "#[ma mb]".
  iEval (rewrite minted_base_exps) in "m"; iDestruct "m" as "[_ #mes]".
  iEval (rewrite SMS.elements_pos_neg big_sepL_app) in "mes".
  iDestruct "mes" as "[mes _]".
  by iSplit; iApply (big_sepL_elem_of with "mes").
iAssert (◇ (public a ∨ public b))%I as "[H|H]"; first last.
- by iRight; iApply except_0_public.
- by iLeft; iApply except_0_public.
iPoseProof (exp_pred_exps a_t with "p") as "[#dh_a _]".
have a_ab : a ∈ [a; b] by set_solver.
iPoseProof (exp_pred_inv_gen a_ab ab_t with "dh_a") as "(%c & %c_ab & H)".
rewrite elem_of_cons list_elem_of_singleton in c_ab.
iDestruct "H" as "[H|(%t3 & %e_base & %exps_sub & base)]".
  by case: c_ab => ->; eauto.
iAssert (▷ □ dh_key_share t3)%I as ">%contra".
  by case: c_ab => ->; [iApply "pred_a"|iApply "pred_b"].
move: contra (submseteq_length _ _ exps_sub).
by rewrite SMS.elements_pos_neg length_app /=; lia.
Qed.

Lemma public_dh_secret_gen a b t (Q : iProp) :
  [a; b] ⊆+ SMS.pos (exps t) →
  □ (public a ↔ Q) -∗
  □ (∀ u, exp_pred_base a u ↔ ▷ □ dh_key_share u) -∗
  □ (public b ↔ Q) -∗
  □ (∀ u, exp_pred_base b u ↔ ▷ □ dh_key_share u) -∗
  (public t → Q).
Proof.
move=> ab_t.
iIntros "#s_a #pred_a #s_b #pred_b #p".
iPoseProof (public_dh_secret_gen2 ab_t with "pred_a pred_b p") as "H".
by iDestruct "H" as "[H|H]"; [iApply "s_a"|iApply "s_b"].
Qed.

Lemma public_dh_secret2 g a b :
  negb (is_exp g) → negb (is_gmul g) →
  negb (is_mul a) →
  negb (is_mul b) →
  □ (∀ t, exp_pred_base a t ↔ ▷ □ dh_key_share t) -∗
  □ (∀ t, exp_pred_base b t ↔ ▷ □ dh_key_share t) -∗
  public (TExp g (TMul {[+ a; b +]})) -∗
  public a ∨ public b.
Proof.
move=> gNx gNm Nm_a Nm_b; iIntros "#pred_a #pred_b #p".
have expsE : exps (TExp g (TMul {[+ a; b +]})) = SMS.make [a; b] [].
  rewrite exps_TExp_TMul // => u.
  by case/SMS.elem_of_disj_union => /SMS.elem_of_singleton ->.
have ab_t : [a; b] ⊆+ SMS.pos (exps (TExp g (TMul {[+ a; b +]}))).
  by apply: Permutation_submseteq; rewrite expsE SMS.pos_make_nil_r.
by iApply (public_dh_secret_gen2 ab_t with "pred_a pred_b p").
Qed.

Lemma public_dh_secret' g a b (Q : iProp) :
  negb (is_exp g) → negb (is_gmul g) →
  negb (is_mul a) →
  negb (is_mul b) →
  □ (public a ↔ Q) -∗
  □ (∀ t, exp_pred_base a t ↔ ▷ □ dh_key_share t) -∗
  □ (public b ↔ Q) -∗
  □ (∀ t, exp_pred_base b t ↔ ▷ □ dh_key_share t) -∗
  (public (TExp g (TMul {[+ a; b +]})) → Q).
Proof.
move=> gNx gNm Nm_a Nm_b.
iIntros "#s_a #pred_a #s_b #pred_b #p_share".
iPoseProof (public_dh_secret2 gNx gNm Nm_a Nm_b
              with "pred_a pred_b p_share") as "H".
by iDestruct "H" as "[H|H]"; [iApply "s_a"|iApply "s_b"].
Qed.

End DHKeyShare.
