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

(** [t] is a Diffie-Hellman share or shared secret: it has exactly one
    exponent.  This is the whole of what the secrecy lemmas at the end of this
    file read off a seed's [exp_pred_base], and [dh_publ] is it plus whatever
    invariant [P] the protocol wants to attach. *)
Definition dh_key_share t : iProp :=
  ⌜length (exps t) = 1⌝.

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
  negb (is_exp g) → negb (is_gmul g) → negb (is_ginv g) →
  dh_seed a -∗
  public (TExp g a) -∗
  ▷ P (TExp g a).
Proof.
iIntros "%gNX %gNm %gNi #aP #p_t".
iAssert ⌜negb (is_mul a)⌝%I as %Nm_a; first by iDestruct "aP" as "(_ & $ & _)".
rewrite public_TExp_iff //.
iDestruct "p_t" as "(_ & _ & p_t & _)".
set t' := TExp g a.
have exps_t': exps t' = [a].
  apply Permutation_singleton_r.
  rewrite /t' (_ : TExp g a = TExpN g [a]); last by rewrite /TExpN TMulN1.
  by rewrite (exps_TExpN gNX gNm gNi (invs_canceled1 Nm_a)).
have a_t' : a ∈ exps t' by rewrite exps_t'; set_solver.
iPoseProof (exp_pred_inv_same with "p_t") as "[#contra|H]" => //.
  by iDestruct (dh_seed_elim0 with "aP contra") as ">[]".
iDestruct "H" as "(%t & %e_base & %a_t & H)".
iDestruct (dh_seed_exp_pred_base_elim with "aP H")
  as "{H} #[>-> H]" => //; iNext.
have -> : t' = TExp (base t) a; last by iApply "H".
by rewrite /t' e_base (base_TExp _ _ gNm gNi) base_expN.
Qed.

Lemma dh_seed_elim2 g a b :
  negb (is_exp g) → negb (is_gmul g) → negb (is_ginv g) →
  a ≠ b →
  a ≠ TInv b →
  dh_seed a -∗
  dh_seed b -∗
  public (TExpN g [a; b]) -∗
  ▷ False.
Proof.
iIntros "%gXN %gNm %gNi %a_b %a_bV #aP #bP #p".
iAssert ⌜negb (is_mul a)⌝%I as %Nm_a; first by iDestruct "aP" as "(_ & $ & _)".
iAssert ⌜negb (is_mul b)⌝%I as %Nm_b; first by iDestruct "bP" as "(_ & $ & _)".
have ic_ab : invs_canceled [a; b] := proj2 (invs_canceled2 Nm_a Nm_b) a_bV.
have exps_t : exps (TExpN g [a; b]) ≡ₚ [a; b].
  by rewrite (exps_TExpN gXN gNm gNi ic_ab).
have baseE : base (TExpN g [a; b]) = g.
  by rewrite /TExpN (base_TExp _ _ gNm gNi) base_expN.
have a_t : a ∈ exps (TExpN g [a; b]) by rewrite exps_t; set_solver.
have b_t : b ∈ exps (TExpN g [a; b]) by rewrite exps_t; set_solver.
iPoseProof (exp_pred_exps a_t with "p") as "[dh_a _]".
iPoseProof (exp_pred_inv with "dh_a") as "(%c & %c_t & p_c)" => //.
rewrite exps_t elem_of_cons list_elem_of_singleton in c_t.
rewrite baseE.
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
  negb (is_exp g) → negb (is_gmul g) → negb (is_ginv g) →
  minted g -∗
  dh_seed a -∗
  ▷ □ P (TExp g a) -∗
  public (TExp g a).
Proof.
iIntros "%gXN %gNm %gNi #gP (#m & %Nm_a & #aP1 & #aP2 & _) #P_a".
rewrite public_TExp_iff //; do !iSplit => //.
- iApply exp_pred_intro1. iApply "aP2"; do 2!iModIntro; iSplit => //.
  iPureIntro; suff -> : exps (TExp g a) = [a] by [].
  apply Permutation_singleton_r.
  rewrite (_ : TExp g a = TExpN g [a]); last by rewrite /TExpN TMulN1.
  by rewrite (exps_TExpN gXN gNm gNi (invs_canceled1 Nm_a)).
- iModIntro; iIntros "#p".
  by iApply False_public; last iApply "aP1".
Qed.

Definition mk_dh : val := mk_nonce.

Lemma wp_mk_dh (T : gset term) g (Ψ : val → iProp) :
  negb (is_exp g) -> negb (is_gmul g) -> negb (is_ginv g) ->
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
iIntros "%gNX %gNm %gNi #ctx #minted_g #minted_T post".
iApply (wp_mk_nonce_freshN T (λ _, False%I) dh_publ
         (λ t, {[t; TExp g t]})
  with "[//]" ) => //.
  iIntros "%t".
  rewrite big_sepS_forall; iIntros (t').
  rewrite elem_of_union !elem_of_singleton; iIntros "[->|->]"; eauto.
  rewrite minted_TExp //; iIntros "!>"; iSplit; eauto.
  by iIntros "[??]".
iIntros (a) "%a_T #m_a #aP #? #? token".
have Nm_a : negb (is_mul a) by [].
have a_g: TInv a ∉ exps g.
  by rewrite /exps (expo_expN _ gNX) factors_TMulN0 elem_of_nil; case.
have [? [] aV_ga a_ga] := tsize_lt_TExp gNm gNi Nm_a a_g.
have {}a_ga : TNonce a ≠ TExp g a.
  move=> contra; rewrite -contra in a_ga; lia.
rewrite big_sepS_union ?big_sepS_singleton; last set_solver.
iDestruct "token" as "[t1 t3]".
iApply ("post" with "[$] [] [$] [$]") => //.
  iFrame "#"; rewrite bi.intuitionistic_intuitionistically.
  by eauto.
iPureIntro => t t' t_T t'_t; split => contra.
- apply: (a_T _ t_T); congruence.
- rewrite -[t']TInvK -contra in t'_t.
  apply: (a_T _ t_T); apply: subterm_trans t'_t.
  by constructor => //; case: (a) => //.
Qed.

End DH.

(** [P] plays no role below, so these live outside [Section DH]: inside it the
    unused section variable would be generalised into every statement. *)
Section DHKeyShare.

Context `{!cryptisGS Σ, !heapGS Σ}.
Notation iProp := (iProp Σ).

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
  negb (is_exp g) → negb (is_gmul g) → negb (is_ginv g) →
  negb (is_mul a) →
  public g -∗
  minted a -∗
  □ (∀ t, exp_pred_base a t ↔ ▷ □ dh_key_share t) -∗
  public (TExp g a).
Proof.
move=> gNx gNm gNi Nm; iIntros "#p_g #m_a #pred_a".
iPoseProof (public_minted with "p_g") as "#m_g".
rewrite public_TExp_iff //.
do !iSplit => //; last by iIntros "!> _".
iApply exp_pred_intro1. iApply "pred_a". iPureIntro. rewrite /dh_key_share.
rewrite (_ : TExp g a = TExpN g [a]); last by rewrite /TExpN TMulN1.
by rewrite (exps_TExpN gNx gNm gNi (invs_canceled1 Nm)).
Qed.

(* Either seed being public makes the shared secret public. *)
Lemma public_dh_secret1 g a b :
  negb (is_exp g) → negb (is_gmul g) → negb (is_ginv g) →
  negb (is_mul a) →
  negb (is_mul b) →
  public g -∗
  minted a -∗
  minted b -∗
  □ (∀ t, exp_pred_base a t ↔ ▷ □ dh_key_share t) -∗
  □ (∀ t, exp_pred_base b t ↔ ▷ □ dh_key_share t) -∗
  public a ∨ public b -∗
  public (TExpN g [a; b]).
Proof.
move=> gNx gNm gNi Nm_a Nm_b.
iIntros "#p_g #m_a #m_b #pred_a #pred_b #[H|H]".
- rewrite -TExp_TExpN /TExpN TMulN1.
  iApply public_TExp => //. by iApply (public_dh_share gNx gNm gNi Nm_b).
- rewrite TExpNC2 -TExp_TExpN /TExpN TMulN1.
  iApply public_TExp => //. by iApply (public_dh_share gNx gNm gNi Nm_a).
Qed.

(* The general form of [public_dh_secret2]: [a] and [b] need only *occur* among
   the exponents of [t], not exhaust them.  [exp_pred_inv_gen] already takes an
   arbitrary sublist of [exps t], so the other exponents -- which may well be
   public, as HMQV's hash multipliers are -- are simply skipped.  A version that
   concluded only "*some* exponent of [t] is public" would be vacuous there. *)
Lemma public_dh_secret_gen2 a b t :
  a ≠ b →
  a ∈ exps t →
  b ∈ exps t →
  □ (∀ u, exp_pred_base a u ↔ ▷ □ dh_key_share u) -∗
  □ (∀ u, exp_pred_base b u ↔ ▷ □ dh_key_share u) -∗
  public t -∗
  public a ∨ public b.
Proof.
iIntros "%a_b %a_t %b_t #pred_a #pred_b #p".
iPoseProof (public_minted with "p") as "#m".
iAssert (minted a ∧ minted b)%I as "#[ma mb]".
  iEval (rewrite minted_base_exps) in "m"; iDestruct "m" as "[_ #mes]".
  by iSplit; iApply (big_sepL_elem_of with "mes").
iAssert (◇ (public a ∨ public b))%I as "[H|H]"; first last.
- by iRight; iApply except_0_public.
- by iLeft; iApply except_0_public.
iPoseProof (exp_pred_exps a_t with "p") as "[#dh_a _]".
have a_ab : a ∈ [a; b] by set_solver.
have ab_t : [a; b] ⊆ exps t by set_solver.
iPoseProof (exp_pred_inv_gen a_ab ab_t with "dh_a") as "(%c & %c_ab & H)".
rewrite elem_of_cons list_elem_of_singleton in c_ab.
iDestruct "H" as "[H|(%t3 & %e_base & %exps_sub & base)]".
  by case: c_ab => ->; eauto.
iAssert (▷ □ dh_key_share t3)%I as ">%contra".
  by case: c_ab => ->; [iApply "pred_a"|iApply "pred_b"].
case: (exps t3) => // c' [|//] in exps_sub contra.
have [a_c b_c]: a ∈ [c'] ∧ b ∈ [c'] by set_solver.
rewrite !list_elem_of_singleton in a_c b_c; congruence.
Qed.

Lemma public_dh_secret_gen a b t (Q : iProp) :
  a ≠ b →
  a ∈ exps t →
  b ∈ exps t →
  □ (public a ↔ Q) -∗
  □ (∀ u, exp_pred_base a u ↔ ▷ □ dh_key_share u) -∗
  □ (public b ↔ Q) -∗
  □ (∀ u, exp_pred_base b u ↔ ▷ □ dh_key_share u) -∗
  (public t → Q).
Proof.
move=> a_b a_t b_t.
iIntros "#s_a #pred_a #s_b #pred_b #p".
iPoseProof (public_dh_secret_gen2 a_b a_t b_t with "pred_a pred_b p") as "H".
by iDestruct "H" as "[H|H]"; [iApply "s_a"|iApply "s_b"].
Qed.

Lemma public_dh_secret2 g a b :
  negb (is_exp g) → negb (is_gmul g) → negb (is_ginv g) →
  negb (is_mul a) →
  negb (is_mul b) →
  a ≠ b →
  a ≠ TInv b →
  □ (∀ t, exp_pred_base a t ↔ ▷ □ dh_key_share t) -∗
  □ (∀ t, exp_pred_base b t ↔ ▷ □ dh_key_share t) -∗
  public (TExpN g [a; b]) -∗
  public a ∨ public b.
Proof.
move=> gNx gNm gNi Nm_a Nm_b; iIntros "%a_b %a_bV #pred_a #pred_b #p".
have ic_ab : invs_canceled [a; b] := proj2 (invs_canceled2 Nm_a Nm_b) a_bV.
have exps_share : exps (TExpN g [a; b]) ≡ₚ [a; b].
  by rewrite (exps_TExpN gNx gNm gNi ic_ab).
have a_t : a ∈ exps (TExpN g [a; b]) by rewrite exps_share; set_solver.
have b_t : b ∈ exps (TExpN g [a; b]) by rewrite exps_share; set_solver.
by iApply (public_dh_secret_gen2 a_b a_t b_t with "pred_a pred_b p").
Qed.

Lemma public_dh_secret' g a b (Q : iProp) :
  negb (is_exp g) → negb (is_gmul g) → negb (is_ginv g) →
  negb (is_mul a) →
  negb (is_mul b) →
  a ≠ b →
  a ≠ TInv b →
  □ (public a ↔ Q) -∗
  □ (∀ t, exp_pred_base a t ↔ ▷ □ dh_key_share t) -∗
  □ (public b ↔ Q) -∗
  □ (∀ t, exp_pred_base b t ↔ ▷ □ dh_key_share t) -∗
  (public (TExpN g [a; b]) → Q).
Proof.
move=> gNx gNm gNi Nm_a Nm_b a_b a_bV.
iIntros "#s_a #pred_a #s_b #pred_b #p_share".
iPoseProof (public_dh_secret2 gNx gNm gNi Nm_a Nm_b a_b a_bV
              with "pred_a pred_b p_share") as "H".
by iDestruct "H" as "[H|H]"; [iApply "s_a"|iApply "s_b"].
Qed.

End DHKeyShare.
