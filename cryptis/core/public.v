From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import invariants.
From iris.bi Require Import fixpoint_mono.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta nown saved_prop size_rec_pred sms.
From cryptis.core Require Import term minted term_meta.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class publicGpreS Σ := PublicGPreS {
  publicGpreS_nonce : savedPredG Σ term;
  publicGpreS_seal  : savedPredG Σ (term * term);
  publicGpreS_prop  : savedPropG Σ;
  publicGpreS_meta  : metaGS Σ;
}.

Local Existing Instance publicGpreS_nonce.
Local Existing Instance publicGpreS_seal.
Local Existing Instance publicGpreS_prop.
Local Existing Instance publicGpreS_meta.

Class publicGS Σ := PublicGS {
  public_inG : publicGpreS Σ;
  public_hash_name  : gname;
  public_aenc_name  : gname;
  public_sign_name  : gname;
  public_senc_name  : gname;
}.

Global Existing Instance public_inG.

Definition publicΣ : gFunctors :=
  #[savedPredΣ term;
    savedPredΣ (term * term);
    savedPropΣ;
    metaΣ].

Global Instance subG_publicGpreS Σ : subG publicΣ Σ → publicGpreS Σ.
Proof. solve_inG. Qed.

Section Public.

Context `{!heapGS Σ, !publicGS Σ, !term_metaGS Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).

Notation iPropI := (iPropI Σ).

Definition pnonce a : iProp :=
  ∃ γ P, meta (nonce_loc a) (nroot.@"nonce") γ ∧
         own γ (saved_pred DfracDiscarded P) ∧
         ▷ □ P (TNonce a).

Global Instance Persistent_pnonce a : Persistent (pnonce a).
Proof. apply _. Qed.

Definition exp_pred_base (t t' : term) : iProp :=
  match t with
  | TNonce a =>
    ∃ γ φ, meta (nonce_loc a) (nroot.@"dh") γ ∧
           own γ (saved_pred DfracDiscarded φ) ∧
           ▷ □ φ t'
  | _ => ▷ False
  end.

Lemma exp_pred_base_TInv t t' :
  ¬ is_inv t →
  exp_pred_base (TInv t) t' ⊣⊢ ▷ False.
Proof.
move => Ninv; rewrite /exp_pred_base.
case E: (TInv t) => [n|t1 t2|a|kt k|k m|h|pt wf nf] //=.
exfalso; apply: Ninv.
have -> : t = TInv (TNonce a) by rewrite -E TInvK.
by rewrite is_inv_TInv.
Qed.

Global Instance exp_pred_base_persistent t t' :
  Persistent (exp_pred_base t t').
Proof. by case: t; apply _. Qed.

Definition exp_pred0_pre Plater P DH ts : iProp :=
  (∃ ts', exp_pred_base ts.1 (TExpN ts.2 ts') ∗
    ⌜invs_canceled ts'⌝ ∗
    ⌜∀ t, t ∈ ts' → TInv t ∉ exps ts.2⌝ ∗
    [∗ list] t ∈ ts', Plater t) ∨
  P ts.1 ∨
  ∃ t2' t, ⌜ts.2 = TExp t2' t⌝ ∗ ⌜negb (is_mul t)⌝ ∗ ⌜TInv t ∉ exps t2'⌝ ∗
  DH (ts.1, t2') ∗ DH (t, ts.2).

Local Instance exp_pred0_pre_mono Plater P :
  BiMonoPred (exp_pred0_pre Plater P).
Proof.
constructor; last by move=> ??; solve_proper.
iIntros (DH1 DH2 _ _) "#H %ts dh"; rewrite /exp_pred0_pre.
iDestruct "dh" as "[? | [? | dh]]"; eauto.
iDestruct "dh" as (t2 t') "(#p & #Nm & #? & dh1 & dh2)".
iRight; iRight; iExists t2, t'; iFrame "#".
by iSplitL "dh1"; iApply "H".
Qed.

Local Definition exp_pred0_def :
  (term → iProp) → (term → iProp) → term * term → iProp :=
  λ Plater P, bi_least_fixpoint (exp_pred0_pre Plater P).
Local Definition exp_pred0_aux : seal exp_pred0_def. Proof. by eexists. Qed.
Definition exp_pred0 := exp_pred0_aux.(unseal).
Local Lemma exp_pred0_unseal : exp_pred0 = exp_pred0_def.
Proof. by rewrite -exp_pred0_aux.(seal_eq). Qed.

Lemma exp_pred0_unfold Plater P ts :
  exp_pred0 Plater P ts ⊣⊢
  (∃ ts', exp_pred_base ts.1 (TExpN ts.2 ts') ∗
    ⌜invs_canceled ts'⌝ ∗
    ⌜∀ t, t ∈ ts' → TInv t ∉ exps ts.2⌝ ∗
    [∗ list] t ∈ ts', Plater t) ∨
  P ts.1 ∨
  ∃ t2' t, ⌜ts.2 = TExp t2' t⌝ ∗ ⌜negb (is_mul t)⌝ ∗ ⌜TInv t ∉ exps t2'⌝ ∗
  exp_pred0 Plater P (ts.1, t2') ∗ exp_pred0 Plater P (t, ts.2).
Proof. by rewrite exp_pred0_unseal /exp_pred0_def least_fixpoint_unfold. Qed.

Lemma exp_pred0_ind Plater P φ :
  □ (∀ ts, exp_pred0_pre Plater P (λ ts, φ ts ∧ exp_pred0 Plater P ts) ts -∗ φ ts) -∗
  ∀ ts, exp_pred0 Plater P ts -∗ φ ts.
Proof.
rewrite exp_pred0_unseal; iApply least_fixpoint_ind; solve_proper.
Qed.

Global Instance exp_pred0_ne n :
  Proper (pointwise_relation _ (dist n) ==>
          pointwise_relation _ (dist n) ==>
          dist n ==> dist n) exp_pred0.
Proof.
move=> Plater1 Plater2 HPlater P1 P2 HP ts1 ts2 e.
have -> : ts1 = ts2 by apply leibniz_equiv_iff.
rewrite exp_pred0_unseal; apply least_fixpoint_ne; solve_proper.
Qed.

Global Instance exp_pred0_proper :
  Proper (pointwise_relation _ (≡) ==>
          pointwise_relation _ (≡) ==> (≡) ==> (≡)) exp_pred0.
Proof.
move=> Plater1 Plater2 HPlater P1 P2 HP ts1 ts2 e.
have -> : ts1 = ts2 by apply leibniz_equiv_iff.
apply equiv_dist => n.
by apply exp_pred0_ne => // ts'; apply equiv_dist; eauto.
Qed.

Global Instance exp_pred0_persistent Plater P :
  (∀ ts, Persistent (Plater ts)) →
  (∀ ts, Persistent (P ts)) →
  ∀ ts, Persistent (exp_pred0 Plater P ts).
Proof.
rewrite {3}/Persistent => HPlater HP ts; iIntros "H".
iRevert (ts) "H".
iApply exp_pred0_ind; iIntros "!> %ts [#H | [#H | H]]"; eauto.
- rewrite exp_pred0_unfold; eauto.
- rewrite exp_pred0_unfold; eauto.
- iDestruct "H" as (t2' t) "(% & % & % & [#? _] & [#? _])".
  iModIntro; rewrite [exp_pred0 Plater P ts]exp_pred0_unfold.
  by iRight; iRight; iExists t2', t; iFrame "#".
Qed.

Lemma exp_pred0_wand Plater1 Plater2 P1 P2 :
  □ (∀ t, Plater1 t -∗ Plater2 t) -∗
  □ (∀ t, P1 t -∗ P2 t) -∗
  ∀ ts, exp_pred0 Plater1 P1 ts -∗ exp_pred0 Plater2 P2 ts.
Proof.
iIntros "#monolater #mono".
iApply exp_pred0_ind; iIntros "!> %ts [H | [H | H]]"; eauto.
- rewrite exp_pred0_unfold; iLeft.
  iDestruct "H" as (ts') "(H & % & % & Hts')".
  iFrame; do 2!(iSplit => //); iApply (big_sepL_impl with "Hts'").
  iIntros "!> % % %"; iApply "monolater".
- by rewrite exp_pred0_unfold; iRight; iLeft; iApply "mono".
- iDestruct "H" as (t2' t) "(% & % & % & [? _] & [? _])".
  rewrite [exp_pred0 Plater2 P2 ts]exp_pred0_unfold.
  by iRight; iRight; iExists t2', t; iFrame.
Qed.

Lemma exp_pred0_mono Plater P1 P2 ts :
  (∀ t, t = ts.1 ∨ t ∈ exps ts.2 → P1 t ≡ P2 t) →
  exp_pred0 Plater P1 ts ⊢ exp_pred0 Plater P2 ts.
Proof.
iIntros "%HP dh"; iRevert (HP); iRevert (ts) "dh".
iApply exp_pred0_ind; iIntros "!> %ts [H | [H | H]] %HP".
- by rewrite exp_pred0_unfold; eauto.
- by rewrite exp_pred0_unfold HP; eauto.
- iDestruct "H" as (t2' t e Nm t_t2') "([IH1 _] & [IH2 _])".
  rewrite [exp_pred0 Plater P2 ts]exp_pred0_unfold.
  iRight; iRight; iExists t2', t.
  do 3!iSplit => //; iSplitL "IH1".
  + iApply "IH1"; iPureIntro => t' /= [->|t'_t2']; eauto.
    apply: HP; right.
    have t'_tV : t' ≠ TInv t by move=> e'; apply: t_t2'; rewrite -e'.
    have := exps_count_TExpW t' t2' t Nm t'_tV.
    move: t'_t2'; rewrite e /exps -!count_gt0; lia.
  + iApply "IH2"; iPureIntro => t' /= [->|t'_t2']; eauto.
    apply: HP; right; move: t_t2'.
    rewrite e /exps -!count_gt0 (count_expo_TExp_eq t _ Nm) count_TInv_l; lia.
Qed.

Lemma exp_pred0_proper' Plater P1 P2 ts :
  (∀ t, t = ts.1 ∨ t ∈ exps ts.2 → P1 t ≡ P2 t) →
  exp_pred0 Plater P1 ts ≡ exp_pred0 Plater P2 ts.
Proof.
move=> H; apply (anti_symm _); apply: exp_pred0_mono => //.
by move=> ??; symmetry; apply: H.
Qed.

Definition name_of_functionality F :=
  match F with
  | AENC => public_aenc_name
  | SIGN => public_sign_name
  | SENC => public_senc_name
  end.

Definition seal_pred F N Φ : iProp :=
  nown (name_of_functionality F) N
    (saved_pred DfracDiscarded (fun '(k, t) => Φ k t)).

Definition aenc_pred N (Φ : aenc_key → term → iProp) :=
  seal_pred AENC N (λ k t, ∃ k' : aenc_key, ⌜k = k'⌝ ∗ Φ k' t)%I.

Definition sign_pred N (Φ : sign_key → term → iProp) :=
  seal_pred SIGN N (λ k t, ∃ k' : sign_key, ⌜k = k'⌝ ∗ Φ k' t)%I.

Definition senc_pred N (Φ : senc_key → term → iProp) :=
  seal_pred SENC N (λ k t, ∃ k' : senc_key, ⌜k = k'⌝ ∗ Φ k' t)%I.

Definition seal_pred_token F E :=
  gmeta_token (name_of_functionality F) E.

Lemma seal_pred_token_difference F E1 E2 :
  E1 ⊆ E2 →
  seal_pred_token F E2 ⊣⊢ seal_pred_token F E1 ∗ seal_pred_token F (E2 ∖ E1).
Proof.
move=> sub; rewrite /seal_pred_token; exact: gmeta_token_difference.
Qed.

Lemma seal_pred_token_drop E1 E2 F :
  E1 ⊆ E2 →
  seal_pred_token F E2 -∗
  seal_pred_token F E1.
Proof.
iIntros (sub) "t".
rewrite seal_pred_token_difference //.
by iDestruct "t" as "[t _]".
Qed.

Global Instance seal_pred_persistent F N Φ : Persistent (seal_pred F N Φ).
Proof. apply _. Qed.

Lemma seal_pred_agree k t F N Φ1 Φ2 :
  seal_pred F N Φ1 -∗
  seal_pred F N Φ2 -∗
  ▷ (Φ1 k t ≡ Φ2 k t).
Proof.
rewrite /seal_pred. iIntros "#own1 #own2".
iPoseProof (nown_valid_2 with "own1 own2") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #agree]".
by iApply ("agree" $! (k, t)).
Qed.

Lemma seal_pred_set F E (N : namespace) Φ :
  ↑N ⊆ E →
  seal_pred_token F E ==∗
  seal_pred F N Φ ∗
  seal_pred_token F (E ∖ ↑N).
Proof. iIntros (?) "token". by iApply nown_alloc. Qed.

Lemma aenc_pred_set E N Φ :
  ↑N ⊆ E →
  seal_pred_token AENC E ==∗
  aenc_pred N Φ ∗
  seal_pred_token AENC (E ∖ ↑N).
Proof. move=> ?. by iApply seal_pred_set. Qed.

Lemma sign_pred_set E N Φ :
  ↑N ⊆ E →
  seal_pred_token SIGN E ==∗
  sign_pred N Φ ∗
  seal_pred_token SIGN (E ∖ ↑N).
Proof. move=> ?. by iApply seal_pred_set. Qed.

Lemma senc_pred_set E N Φ :
  ↑N ⊆ E →
  seal_pred_token SENC E ==∗
  senc_pred N Φ ∗
  seal_pred_token SENC (E ∖ ↑N).
Proof. move=> ?. by iApply seal_pred_set. Qed.

Definition wf_seal F k t : iProp :=
  ∃ N t' Φ, ⌜t = Spec.tag (Tag N) t'⌝ ∧ seal_pred F N Φ ∧ □ ▷ Φ k t'.

Global Instance wf_seal_persistent F k t : Persistent (wf_seal F k t).
Proof. by apply _. Qed.

Lemma wf_seal_elim F k N t Φ :
  wf_seal F k (Spec.tag (Tag N) t) -∗
  seal_pred F N Φ -∗
  □ ▷ Φ k t.
Proof.
iDestruct 1 as (N' t' Φ') "(%t_t' & #HΦ' & #inv)"; iIntros "#HΦ".
case/Spec.tag_inj: t_t' => /Tag_inj <- <-.
iPoseProof (seal_pred_agree k t with "HΦ HΦ'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Definition hash_pred N (P : term → iProp) : iProp :=
  nown public_hash_name N (saved_pred DfracDiscarded P).

Definition hash_pred_token E :=
  gmeta_token public_hash_name E.

Lemma hash_pred_token_difference E1 E2 :
  E1 ⊆ E2 →
  hash_pred_token E2 ⊣⊢ hash_pred_token E1 ∗ hash_pred_token (E2 ∖ E1).
Proof.
move=> sub; rewrite /hash_pred_token; exact: gmeta_token_difference.
Qed.

Lemma hash_pred_token_drop E1 E2 :
  E1 ⊆ E2 →
  hash_pred_token E2 -∗
  hash_pred_token E1.
Proof.
iIntros (sub) "t".
rewrite hash_pred_token_difference //.
by iDestruct "t" as "[t _]".
Qed.

Global Instance hash_pred_persistent N P : Persistent (hash_pred N P).
Proof. apply _. Qed.

Lemma hash_pred_agree t N P₁ P₂ :
  hash_pred N P₁ -∗
  hash_pred N P₂ -∗
  ▷ (P₁ t ≡ P₂ t).
Proof.
rewrite /hash_pred. iIntros "#own1 #own2".
iPoseProof (nown_valid_2 with "own1 own2") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #agree]".
by iApply ("agree" $! t).
Qed.

Lemma hash_pred_set E N P :
  ↑N ⊆ E →
  hash_pred_token E ==∗
  hash_pred N P ∗
  hash_pred_token (E ∖ ↑N).
Proof. iIntros (?) "token". by iApply nown_alloc. Qed.

Definition wf_hash t : iProp :=
  ∃ N t' P, ⌜t = Spec.tag (Tag N) t'⌝ ∧ hash_pred N P ∧ □ ▷ P t'.

Global Instance wf_hash_persistent t : Persistent (wf_hash t).
Proof. by apply _. Qed.

Lemma wf_hash_elim N t P :
  wf_hash (Spec.tag (Tag N) t) -∗
  hash_pred N P -∗
  □ ▷ P t.
Proof.
iDestruct 1 as (N' t' P') "(%t_t' & #HP' & #inv)"; iIntros "#HP".
case/Spec.tag_inj: t_t' => /Tag_inj <- <-.
iPoseProof (hash_pred_agree t with "HP HP'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Lemma is_inv_Nmul t : is_inv t -> is_mul t = false.
Proof.
rewrite is_inv_unfold is_mul_unfold.
by case: (unfold_term t) => [?|[?| |]?|???|?] //=.
Qed.

Lemma is_inv_Nexp t : is_inv t -> is_exp t = false.
Proof.
rewrite is_inv_unfold is_exp_unfold.
by case: (unfold_term t) => [?|[?| |]?|???|?] //=.
Qed.

Inductive decompose (T : gset term) (t : term) : Prop :=
| DInt n of T = ∅ & t = TInt n

| DPair t1 t2 of T = {[t1; t2]} & t = TPair t1 t2

| DKey kt t' of T = {[t']} & t = TKey kt t'

| DSeal k t' of T = {[k; t']} & t = TSeal k t'

| DHash t' of T = {[t']} & t = THash t'

| DInv t' of T = {[t']} & ¬ is_inv t' & is_inv t & t = TInv t'.

Lemma decompose_tsize T t t' : decompose T t → t' ∈ T → tsize t' < tsize t.
Proof.
case; try by move =>> -> -> //;
          try move => /elem_of_union [];
          move => /elem_of_singleton ->;
          rewrite [tsize (_ _)]tsize_eq;
          lia.
move => t'' -> Ninv inv_t E; rewrite E in inv_t *.
move => /elem_of_singleton ->.
have NmI : negb (is_mul (TInv t'')) by rewrite (is_inv_Nmul inv_t).
have Nm : negb (is_mul t'') by move: NmI; rewrite is_mul_TInv.
have Ninv' : negb (is_inv t'') by apply/negb_True.
rewrite (tsize_TInv t'' Nm Ninv'); lia.
Qed.

Lemma decompose_is_mul T t : decompose T t → is_mul t = false.
Proof.
case => *; subst => //=.
by apply: is_inv_Nmul.
Qed.

Lemma decompose_is_exp T t : decompose T t → is_exp t = false.
Proof.
case => *; subst => //=.
by apply: is_inv_Nexp.
Qed.

Definition public_pre_aux Plater P t : iProp :=
  minted t ∧ (
   (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, P t')
   ∨ (⌜is_mul t⌝ ∧ [∗ list] t' ∈ factors t, P t')
   ∨ (⌜is_exp t⌝ ∧
      [∗ list] t' ∈ exps t,
        ⌜negb (is_mul (TInv t'))⌝ ∧
        exp_pred0 Plater P (t', t) ∧
        □ (P t' → P (TExp t (TInv t'))))
   ∨ match t with
     | TNonce a => ◇ pnonce a
     | TKey kt t => ⌜Spec.public_key_type kt⌝
     | THash t => wf_hash t
     | TSeal k t =>
         match func_of_term k with
         | Some F =>
             ⌜Spec.is_seal_key k⌝ ∧
             wf_seal F (Spec.skey k) t ∧
             match Spec.open_key k with
             | Some k' => □ (P k' → P t)
             | None => True
             end
         | None => True
         end
     | _ => False
     end%I
  ).

Definition public_pre Plater t :=
  size_rec_pred tsize (public_pre_aux Plater) t.

Lemma public_pre_aux_wf Plater :
  (∀ P1 P2 t,
    (∀ t', tsize t' < tsize t → P1 t' ≡ P2 t') →
    public_pre_aux Plater P1 t ≡ public_pre_aux Plater P2 t).
Proof.
move => P1 P2 {}t HP; rewrite /public_pre_aux.
f_equiv.
f_equiv; last (f_equiv; last f_equiv).
- f_equiv => T; apply: and_proper_L => T_t.
  apply: big_sepS_proper => t' T_t'.
  by move: (decompose_tsize T_t T_t') => ?; eauto.
- apply: and_proper_L => mul_t.
  apply: big_sepL_proper => _ t' /(list_elem_of_lookup_2 _ _ _) t'_in.
  apply: HP.
  exact: (tsize_factors_lt t' t mul_t t'_in).
- apply: and_proper_L => exp_t.
  apply: big_sepL_proper => _ t' /(list_elem_of_lookup_2 _ _ _) t'_in.
  apply: and_proper_L => Nm.
  case: (@tsize_TExp_TInv t t' Nm t'_in) => lt1 [] lt2 lt3; f_equiv.
  + apply: exp_pred0_proper' => /= t'' t''_ts; apply: HP.
    case: t''_ts => [->|t''_in]; first exact: lt1.
    exact: (tsize_exps_lt t'' t t''_in).
  + by f_equiv; f_equiv; apply: HP.
- case: t => // k t in HP *.
  case: func_of_term => // F; f_equiv; f_equiv.
  case e_k: Spec.open_key => [k'|] //=.
  have ? := Spec.open_key_tsize e_k.
  have ?: tsize (TSeal k t) = S (tsize k + tsize t).
    by rewrite tsize_eq.
  f_equiv; f_equiv; apply: HP; lia.
Qed.

Global Instance public_pre_aux_proper Plater :
  Proper (pointwise_relation _ (≡) ==> pointwise_relation _ (≡))
   (public_pre_aux Plater).
Proof. by move=> ????; apply: public_pre_aux_wf. Qed.

Lemma public_pre_aux_persistent Plater P :
  □ (∀ t, Plater t -∗ <pers> Plater t) -∗
  □ (∀ t, P t -∗ <pers> P t) -∗
  ∀ t, public_pre_aux Plater P t -∗ <pers> public_pre_aux Plater P t.
Proof.
iIntros "#wand1 #wand2 %t [#m [H | [H | [H | H]]]]"; iSplit => //.
- iDestruct "H" as (T ?) "H"; iLeft; iExists T; iSplit; eauto.
  iAssert ([∗ set] t' ∈ T, <pers> P t')%I as "{H} #H".
  { iApply (big_sepS_impl with "H"); iIntros "!> %t' _".
    by iApply "wand2". }
  by iModIntro; iApply (big_sepS_impl with "H"); eauto.
- iDestruct "H" as "(% & H)"; iRight; iLeft.
  iAssert ([∗ list] t' ∈ factors t, <pers> P t')%I as "{H} #H".
  { iApply (big_sepL_impl with "H"); iIntros "!> %k %t' _".
    by iApply "wand2". }
  by iModIntro; iSplit => //; iApply (big_sepL_impl with "H"); eauto.
- iDestruct "H" as "(% & H)"; iRight; iRight; iLeft.
  iAssert ([∗ list] t' ∈ exps t,
    ⌜negb (is_mul (TInv t'))⌝ ∧
    <pers> exp_pred0 Plater P (t', t) ∧
    □ (P t' → P (TExp t (TInv t'))))%I as "{H} #H".
  { iApply (big_sepL_impl with "H").
    iIntros "!> %k %t' _ [%Nm [dh #?]]"; iSplit => //; iSplit => //.
    iAssert (exp_pred0 (λ t'', <pers> Plater t'')%I
                      (λ t'', <pers> P t'')%I (t', t)) as "{dh} #dh".
    { by iApply (exp_pred0_wand with "[] [] dh"); eauto. }
    by iModIntro; iApply (exp_pred0_wand with "[] [] dh"); iIntros "!> % #?". }
  iModIntro; iSplit => //.
  by iApply (big_sepL_impl with "H"); iIntros "!> % % _ [% [#? #?]]"; eauto.
- iRight; iRight; iRight; case: t; by move=> *; iPoseProof "H" as "#H".
Qed.

Lemma public_pre_unfold Plater t :
  public_pre Plater t ≡ public_pre_aux Plater (public_pre Plater) t.
Proof. apply: size_rec_pred_unfold; exact: public_pre_aux_wf. Qed.

Lemma public_pre_persistent Plater :
  □ (∀ t, Plater t -∗ <pers> Plater t) -∗
  ∀ t, public_pre Plater t -∗ <pers> public_pre Plater t.
Proof.
iIntros "#HPlater"; rewrite /public_pre.
iApply size_rec_pred_persistent.
iIntros "!> %P #HP".
by iApply public_pre_aux_persistent.
Qed.

Global Instance public_pre_aux_ne n :
  Proper (pointwise_relation _ (dist n) ==>
          pointwise_relation _ (dist n) ==> dist n ==> dist n) public_pre_aux.
Proof.
move=> Plater1 Plater2 HPlater P1 P2 HP t _ <-; rewrite /public_pre_aux.
solve_contractive.
Qed.

Global Instance public_pre_ne n :
  Proper (pointwise_relation _ (dist n) ==> dist n ==> dist n) public_pre.
Proof.
rewrite /public_pre => Plater1 Plater2 HPlater t _ <-; f_equiv.
by f_equiv.
Qed.

Definition public_pre' (P : term -d> iProp) : term -d> iProp :=
  public_pre (λ t, ▷ P t)%I.

Local Instance public_pre'_contractive : Contractive public_pre'.
Proof. rewrite /public_pre'; solve_contractive. Qed.

Definition public_def := fixpoint public_pre'.
Local Definition public_aux : seal (@public_def). Proof. by eexists. Qed.
Definition public := public_aux.(unseal).
Local Lemma public_unseal : public = public_def.
Proof. rewrite -public_aux.(seal_eq) //. Qed.

Definition exp_pred_def := λ t1 t2, exp_pred0 (λ t, ▷ public t)%I public (t1, t2).
Local Definition exp_pred_aux : seal (@exp_pred_def). Proof. by eexists. Qed.
Definition exp_pred := exp_pred_aux.(unseal).
Local Lemma exp_pred_unseal : exp_pred = exp_pred_def.
Proof. rewrite -exp_pred_aux.(seal_eq) //. Qed.

Lemma public_eq t :
  public t ⊣⊢
  minted t ∧ (
      (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, public t')
     ∨ (⌜is_mul t⌝ ∧ [∗ list] t' ∈ factors t, public t')
     ∨ (⌜is_exp t⌝ ∧
        [∗ list] t' ∈ exps t,
          ⌜negb (is_mul (TInv t'))⌝ ∧
          exp_pred t' t ∧ □ (public t' → public (TExp t (TInv t'))))
     ∨ match t with
       | TNonce a => ◇ pnonce a
       | TKey kt t => ⌜Spec.public_key_type kt⌝
       | THash t => wf_hash t
       | TSeal k t =>
           match func_of_term k with
           | Some F =>
               ⌜Spec.is_seal_key k⌝ ∧
               wf_seal F (Spec.skey k) t ∧
               match Spec.open_key k with
               | Some k' => □ (public k' → public t)
               | None => True
               end
           | None => True
           end
       | _ => False
       end%I
  ).
Proof.
have ->: public t ⊣⊢ public_pre_aux (λ t, ▷ public t)%I public t; last first.
  by rewrite /public_pre_aux exp_pred_unseal.
rewrite public_unseal /public_def {1}(fixpoint_unfold public_pre' t).
rewrite {1}/public_pre' public_pre_unfold; apply: public_pre_aux_proper => t'.
by rewrite (fixpoint_unfold public_pre' t').
Qed.

Global Instance Persistent_public t : Persistent (public t).
Proof.
rewrite /Persistent; rewrite public_unseal /public_def.
iIntros "H"; iLöb as "IH" forall (t).
rewrite (fixpoint_unfold public_pre' t) {3 4}/public_pre'.
iApply (public_pre_persistent with "[] H").
iIntros "!> % H"; rewrite -bi.later_persistently; iModIntro.
by iApply "IH".
Qed.

Global Instance Persistent_exp_pred t1 t2 : Persistent (exp_pred t1 t2).
Proof. rewrite exp_pred_unseal /exp_pred_def. by apply _. Qed.

Lemma exp_pred_intro1_gen t1 t2 ts :
  invs_canceled ts ->
  (∀ t, t ∈ ts → TInv t ∉ exps t2) →
  ([∗ list] t ∈ ts, ▷ public t) -∗
  exp_pred_base t1 (TExpN t2 ts) -∗ exp_pred t1 t2.
Proof.
iIntros "%atom %ts_t2 #p_ts #dh".
rewrite exp_pred_unseal /exp_pred_def exp_pred0_unfold /=.
by eauto 10.
Qed.

Lemma exp_pred_intro1 t1 t2 : exp_pred_base t1 t2 -∗ exp_pred t1 t2.
Proof.
have atom0 : invs_canceled (@nil term) := invs_canceled0.
have hexps : ∀ t, t ∈ (@nil term) → TInv t ∉ exps t2.
{ by move=> ?; rewrite elem_of_nil. }
rewrite -{1}[t2]TExpN0.
by iApply (@exp_pred_intro1_gen t1 t2 [] atom0 hexps).
Qed.

Lemma exp_pred_intro2 t t1 t2 :
  negb (is_mul t) ->
  TInv t ∉ exps t2 →
  exp_pred t1 t2 -∗ exp_pred t (TExp t2 t) -∗ exp_pred t1 (TExp t2 t).
Proof.
rewrite exp_pred_unseal /exp_pred_def (exp_pred0_unfold _ _ (t1, TExp t2 t)) /=.
by iIntros "%Nm % #H1 #H2"; iRight; iRight; iExists _, _; iFrame "#"; eauto.
Qed.

Lemma exp_pred_intro3 t1 t2 : public t1 -∗ exp_pred t1 t2.
Proof.
rewrite exp_pred_unseal /exp_pred_def exp_pred0_unfold /=.
by eauto.
Qed.

Lemma exp_pred_ind (φ : term → term → iProp) :
  (□ ∀ ts t1 t2,
    ⌜invs_canceled ts⌝ -∗
    ⌜∀ t, t ∈ ts → TInv t ∉ exps t2⌝ -∗
    ([∗ list] t ∈ ts, ▷ public t) -∗
    exp_pred_base t1 (TExpN t2 ts) -∗ φ t1 t2) -∗
  (□ ∀ t t1 t2, ⌜negb (is_mul t)⌝ -∗ ⌜TInv t ∉ exps t2⌝ -∗
                exp_pred t1 t2 -∗ □ φ t1 t2 -∗
                exp_pred t (TExp t2 t) -∗ □ φ t (TExp t2 t) -∗
                φ t1 (TExp t2 t)) -∗
  (□ ∀ t1 t2, public t1 -∗ φ t1 t2) -∗
  ∀ t1 t2, exp_pred t1 t2 -∗ φ t1 t2.
Proof.
iIntros "#H1 #H2 #H3 %t1 %t2 dh".
iAssert (□ φ t1 t2)%I as "#?"; eauto.
rewrite exp_pred_unseal /exp_pred_def; set ts := (t1, t2).
rewrite -[t1]/ts.1 -[t2]/ts.2; move: ts => ts.
iRevert (ts) "dh"; iApply exp_pred0_ind.
iIntros "!> %ts [#H | [#H | #H]]".
- iDestruct "H" as "(%ts' & #? & % & % & #?)"; iModIntro.
  by iApply "H1"; eauto.
- by iModIntro; iApply "H3".
- iDestruct "H" as (t2' t) "/= (-> & % & % & [#H11 #H12] & [#H21 #H22])".
  by iModIntro; iApply ("H2" with "[//] [//] H12 H11 [$]").
Qed.

Lemma exp_pred_inv_gen ts t1 t2 :
  t1 ∈ ts →
  ts ⊆ exps t2 →
  exp_pred t1 t2 -∗
  ∃ t, ⌜t ∈ ts⌝ ∧ (
    public t ∨
    ∃ t3, ⌜base t3 = base t2⌝ ∧ ⌜ts ⊆ exps t3⌝ ∧ exp_pred_base t t3).
Proof.
iIntros "%t1_ts %ts_t2 dh"; iRevert (ts t1_ts ts_t2); iRevert (t1 t2) "dh".
iApply exp_pred_ind; eauto 10.
- iIntros "!> %ts %t1 %t2 %atom_ts %ts_t2 #p_ts #base %ts' %t1_ts' %ts'_t2".
  iExists t1; iSplit=> //; iRight; iExists (TExpN t2 ts).
  have baseE : base (TExpN t2 ts) = base t2 by rewrite /TExpN base_TExp.
  rewrite baseE; do !iSplit => //; iPureIntro => t t_ts'.
  have ts_t: ∀ t', t' ∈ ts → t ≠ TInv t'.
    by move=> t' /ts_t2 t'_t2 t'_t; apply: t'_t2; rewrite -t'_t; eauto.
  move/ts'_t2: t_ts'; rewrite /exps -!count_gt0 => t_ts'.
  have Hmono := @exps_count_TExpNW t t2 ts atom_ts ts_t.
  move: t_ts' Hmono; lia.
- iIntros "!> %t %t1 %t2 %Nm_t %t_t2 #dh_t1 IH_t1 #dh_t IH_t %ts %t1_ts %ts_t2'".
  rewrite base_TExp; case: (decide (t ∈ ts)) => t_ts; first by iApply "IH_t".
  iApply "IH_t1"; iPureIntro => // t3 t3_ts.
  have t3_nin : t3 ∉ factors t.
    by rewrite factors_Nmul // list_elem_of_singleton; congruence.
  have := not_elem_of_count _ _ t3_nin.
  move: (ts_t2' _ t3_ts); rewrite /exps -!count_gt0 count_expo_TExp; lia.
Qed.

Lemma exp_pred_inv t1 t2 :
  t1 ∈ exps t2 →
  exp_pred t1 t2 -∗
  ∃ t, ⌜t ∈ exps t2⌝ ∧ (
    public t ∨
    ∃ t3, ⌜base t3 = base t2⌝ ∧ ⌜exps t2 ⊆ exps t3⌝ ∧ exp_pred_base t t3).
Proof. by move=> t1_t2; iApply exp_pred_inv_gen. Qed.

Lemma exp_pred_inv_same t1 t2 :
  t1 ∈ exps t2 →
  exp_pred t1 t2 -∗
  public t1 ∨
  ∃ t2', ⌜base t2' = base t2⌝ ∗ ⌜t1 ∈ exps t2'⌝ ∗ exp_pred_base t1 t2'.
Proof.
iIntros "%t1_t2 #dh"; have {}t1_t2: [t1] ⊆ exps t2 by set_solver.
have t1_t1: t1 ∈ [t1] by set_solver.
iPoseProof (exp_pred_inv_gen t1_t1 t1_t2 with "dh") as "(%t & %t_t1 & H)".
move: t_t1; rewrite list_elem_of_singleton => {t} ->.
iDestruct "H" as "[H|(%t3 & #? & %t1_t3 & #base)]"; first by eauto.
iRight; iExists t3; iFrame "#"; iPureIntro; set_solver.
Qed.

Lemma public_minted t : public t ⊢ minted t.
Proof. rewrite public_eq; by iIntros "[??]". Qed.

Lemma public_TInt n : public (TInt n) ⊣⊢ True.
Proof.
apply: (anti_symm _); iIntros "_" => //.
rewrite public_eq minted_TInt; iSplit => //.
iLeft; iExists ∅; rewrite big_sepS_empty; iSplit => //.
by iPureIntro; econstructor.
Qed.

Lemma public_TPair t1 t2 : public (TPair t1 t2) ⊣⊢ public t1 ∧ public t2.
Proof.
apply: (anti_symm _); iIntros "#Ht" => //.
- rewrite public_eq minted_TPair.
  iDestruct "Ht" as "([Ht1 Ht2] & publ)".
  iDestruct "publ" as "[publ | [(? & _) | [(? & _) | publ]]]" => //=.
  iDestruct "publ" as (T) "[%dec publ]".
  case: dec => //= {}t1 {}t2 -> [-> ->].
  by rewrite big_sepS_union_pers !big_sepS_singleton.
- iDestruct "Ht" as "[Ht1 Ht2]".
  rewrite [public (TPair t1 t2)]public_eq minted_TPair -!public_minted.
  iSplit; eauto.
  iLeft; iExists _; iSplit.
    iPureIntro; by econstructor.
  by rewrite big_sepS_union_pers !big_sepS_singleton; eauto.
Qed.

Lemma public_TNonce a :
  public (TNonce a) ⊣⊢ ◇ pnonce a ∗ meta (nonce_loc a) (nroot.@"minted") ().
Proof.
apply: (anti_symm _); iIntros "Ht".
- rewrite public_eq; iDestruct "Ht" as "[? Ht]".
  rewrite minted_TNonce. iFrame.
  iDestruct "Ht" as "[publ | [ (? & _) | [ (? & _) | ? ] ]]" => //.
  iDestruct "publ" as (T) "[%dec _]".
  by case: dec.
- rewrite public_eq minted_TNonce /pnonce.
  iDestruct "Ht" as "[Ht ?]". iFrame.
Qed.

Lemma public_TInv_Nmul t : negb (is_mul t) → public (TInv t) ⊣⊢ public t.
Proof.
wlog: t / negb (is_inv t).
{ move => H Nm.
  case Einv: (is_inv t); last by apply: H => //; rewrite Einv.
  have Nm' : negb (is_mul t) := Nm.
  have NmI : negb (is_mul (TInv t)) by rewrite is_mul_TInv.
  have NinvI : negb (is_inv (TInv t)) by rewrite (is_inv_TInv t Nm') Einv.
  by move: (H (TInv t) NinvI NmI);
     rewrite TInvK => <-. }
move => Ninv Nm.
have Nm' : negb (is_mul t) := Nm.
have Ninv' : negb (is_inv t) := Ninv.
apply: anti_symm.
- rewrite [public (TInv t)]public_eq minted_TInv.
  iIntros "[_ [dec | [ [%mul _] | [ [%exp _] | Hstr]]]]".
  + iDestruct "dec" as (T) "[%d publ]".
    have invI : is_inv (TInv t) by rewrite (is_inv_TInv t Nm').
    case: d => [n eT et|t1 t2 eT et|kt t0 eT et|k t0 eT et|t0 eT et|s eT Ns Hi et];
      try by move: invI; rewrite et.
    move: et => /TInv_inj ->; rewrite eT big_sepS_singleton. by [].
  + by move: Nm'; rewrite -is_mul_TInv (proj2 (is_trueP _) mul).
  + by move: (is_exp_TInv t Nm' Ninv'); rewrite (proj2 (is_trueP _) exp).
  + have invI : is_inv (TInv t) by rewrite (is_inv_TInv t Nm').
    iRevert "Hstr".
    case E: (TInv t) invI => [n|t1 t2|a|kt k|k m|h|pt wf nf] //= _;
      by iIntros "[]".
- iIntros "#publ".
  rewrite [public (TInv t)]public_eq minted_TInv.
  iSplit; first by iApply public_minted.
  iLeft. iExists {[t]}. iSplit; last by rewrite big_sepS_singleton.
  iPureIntro. apply: DInv => //.
  + by move=> H; move: Ninv'; rewrite (proj2 (is_trueP _) H).
  + by rewrite (is_inv_TInv t Nm').
Qed.

Lemma public_TMulN t :
  is_mul t ->
  public t ⊢ [∗ list] t' ∈ factors t, public t'.
Proof.
move=> mul_t; rewrite public_eq.
iIntros "[_ [publ | [ [_ Hfs] | [ (%exp_t & _) | Hstr ]]]]".
- iDestruct "publ" as (T) "[%dec _]".
  by move: mul_t; rewrite (decompose_is_mul dec).
- by iApply "Hfs".
- by move: mul_t exp_t;
     rewrite is_mul_unfold is_exp_unfold; case: (unfold_term t).
- by case: (t) mul_t => // *; iDestruct "Hstr" as "[]".
Qed.

Lemma public_factors t :
  public t ⊣⊢ minted t ∧ [∗ list] t' ∈ factors t, public t'.
Proof.
case Emul: (is_mul t); last first.
- rewrite factors_Nmul; last by rewrite Emul.
  rewrite big_sepL_singleton.
  apply: (anti_symm _).
  + by iIntros "#p"; iSplit; first iApply public_minted.
  + by iIntros "[_ $]".
- have mulI : is_mul t by rewrite Emul.
  apply: (anti_symm _).
  + iIntros "#p"; iSplit; first by iApply public_minted.
    by iApply (public_TMulN mulI with "p").
  + iIntros "[#m #fs]"; rewrite [public t]public_eq; iSplit => //.
    by iRight; iLeft; iSplit.
Qed.

Lemma public_TInv t : public (TInv t) ⊣⊢ public t.
Proof.
have key : forall l, invs_canceled l ->
  ([∗ list] u ∈ map TInv l, public u) ⊣⊢ [∗ list] u ∈ l, public u.
{ elim => [//|u us IH] /invs_canceled_cons [_ [Nmu atom]].
  rewrite (_ : map TInv (u :: us) = TInv u :: map TInv us) //.
  by rewrite !big_sepL_cons (public_TInv_Nmul Nmu) (IH atom). }
rewrite (public_factors (TInv t)) (public_factors t) minted_TInv.
f_equiv.
setoid_rewrite (factors_TInv t).
by rewrite (key _ (invs_canceled_factors t)).
Qed.

Lemma public_TKey kt t :
  public (TKey kt t) ⊣⊢ public t ∨ minted t ∧ ⌜Spec.public_key_type kt⌝.
Proof.
apply: (anti_symm _).
- rewrite public_eq minted_TKey; iDestruct 1 as "[Ht publ]".
  iDestruct "publ" as "[publ | [(? & _) | [(? & _) | publ]]]" => //.
  + iDestruct "publ" as (T) "[%dec publ]".
    case: dec => //= {}kt {}t -> [-> ->].
    by rewrite big_sepS_singleton; eauto.
  + by eauto.
- iDestruct 1 as "# [publ | [s_t publ]]".
    rewrite [public (TKey _ _)]public_eq minted_TKey -public_minted.
    iSplit => //; iLeft.
    iExists {[t]}; iSplit; first by iPureIntro; econstructor.
    by rewrite big_sepS_singleton.
  rewrite public_eq; iSplit; eauto.
  by rewrite minted_TKey.
Qed.

Lemma public_TSeal k t :
  public (TSeal k t) ⊣⊢
  public k ∧ public t ∨
  minted (TSeal k t) ∧
  match func_of_term k with
  | Some F =>
      ⌜Spec.is_seal_key k⌝ ∧
      wf_seal F (Spec.skey k) t ∧
      match Spec.open_key k with
      | Some k' => □ (public k' → public t)
      | None => True
      end
  | None => True
  end.
Proof.
apply: (anti_symm _).
- rewrite public_eq minted_TSeal.
  iDestruct 1 as "[[Hk Ht] publ]".
  iDestruct "publ" as "[publ | [(? & _) | [(? & _) | publ]]]" => //.
  + iDestruct "publ" as (T) "[%dec ?]".
    case: dec => // {}k {}t -> [-> ->].
    by rewrite big_sepS_union_pers !big_sepS_singleton; iLeft.
  + iRight. iSplit; first by eauto.
    by case: k => // kt k.
- iDestruct 1 as "[#[Hk Ht] | (#Ht & inv)]".
  { rewrite [public (TSeal _ _)]public_eq minted_TSeal.
    rewrite -!public_minted.
    iSplit; eauto; iLeft.
    iExists {[k; t]}; rewrite big_sepS_union_pers !big_sepS_singleton.
    iSplit; eauto; iPureIntro; by econstructor. }
  rewrite [public (TSeal _ _)]public_eq; iSplit => //. by eauto.
Qed.

Lemma public_open k t t' :
  Spec.open k t = Some t' →
  public k -∗
  public t -∗
  public t'.
Proof.
rewrite /Spec.open.
case: t => // k_t t.
rewrite public_TSeal.
case: decide => // k_t_k [<-]. rewrite k_t_k.
iIntros "p_k [[??]|(? & p_t)] //".
case e: func_of_term => [F|].
- iDestruct "p_t" as "(_ & _ & p_t)". by iApply "p_t".
- by case: k_t => // ?? in k_t_k e *.
Qed.

Lemma public_THash t :
  public (THash t) ⊣⊢ public t ∨ minted t ∧ wf_hash t.
Proof.
apply: (anti_symm _).
- rewrite public_eq minted_THash.
  iDestruct 1 as "[Ht [publ | [(? & _) | [(? & _) | publ]]]]" => //; eauto.
  iDestruct "publ" as (T) "[%dec ?]".
  case: dec => //= {}t -> [->].
  by rewrite big_sepS_singleton; eauto.
- iDestruct 1 as "[Ht | [? publ]]".
    rewrite [public (THash _)]public_eq minted_THash -public_minted.
    iSplit => //=; iLeft.
    iExists {[t]}; rewrite big_sepS_singleton; iSplit => //.
    iPureIntro; by econstructor.
  rewrite public_eq; iSplit.
    by rewrite minted_THash.
  by eauto.
Qed.

Lemma public_THashIS N φ t :
  hash_pred N φ -∗
  minted t -∗
  ▷ □ φ t -∗
  public (THash (Spec.tag (Tag N) t)).
Proof.
  iIntros "#Hpred #Hminted #Hφ".
  rewrite public_THash.
  iRight.
  rewrite minted_tag. iSplit => //.
  iExists _, _, _.
  eauto.
Qed.

Lemma public_TExpN t ts :
  negb (is_exp t) →
  invs_canceled ts ->
  ts ≠ [] →
  public (TExpN t ts) ⊣⊢
  minted (TExpN t ts) ∧
  [∗ list] t' ∈ ts,
    exp_pred t' (TExpN t ts) ∧ □ (public t' → public (TExp (TExpN t ts) (TInv t'))).
Proof.
move => Nx ic tsN0.
have expE : expo (TExpN t ts) = TMulN ts.
  by rewrite /TExpN expo_TExp (expo_expN _ Nx) TMulN_cat /= TMulN1.
have ttsX: is_exp (TExpN t ts).
  rewrite is_expE expE => contra; apply: tsN0.
  by apply/Permutation_nil; rewrite -(factors_TMulN ic) contra factors_TMulN0.
apply: anti_symm; last first.
- iIntros "#[m dhp]".
  rewrite public_eq; setoid_rewrite (exps_TExpN Nx ic).
  iSplit; first done.
  iRight; iRight; iLeft.
  iSplit; first done.
  iApply (big_sepL_mono with "dhp").
  iIntros (k t' Hk) "H"; iSplit; last by [].
  iPureIntro; rewrite is_mul_TInv.
  exact: proj2 (ic t' (list_elem_of_lookup_2 _ _ _ Hk)).
- rewrite public_eq !(minted_TExpN Nx ic).
  setoid_rewrite (exps_TExpN Nx ic).
  iIntros "#[[mt mts] Hdisj]".
  iSplit; first by iSplit.
  iDestruct "Hdisj" as "[c1 | [c2 | [c3 | c4]]]".
  + iDestruct "c1" as (T) "[%dec _]".
    by move: ttsX; rewrite (decompose_is_exp dec).
  + iDestruct "c2" as "(%mul_c & _)".
    by move: ttsX mul_c;
       rewrite is_exp_unfold is_mul_unfold; case: (unfold_term (TExpN t ts)).
  + iDestruct "c3" as "(_ & exp)".
    iApply (big_sepL_mono with "exp"). by iIntros (k t' _) "(_ & $)".
  + iRevert "c4"; case: (TExpN t ts) ttsX => // *; by iIntros "[]".
Qed.

Lemma public_TExpN' t :
  is_exp t ->
  public t ⊣⊢
  minted t ∧
  [∗ list] t' ∈ exps t,
    exp_pred t' t ∧ □ (public t' → public (TExp t (TInv t'))).
Proof.
move => expt; apply: anti_symm; last first.
- iIntros "#[m dhp]".
  rewrite public_eq.
  iSplit; first done.
  iRight; iRight; iLeft.
  iSplit; first done.
  iApply (big_sepL_mono with "dhp").
  iIntros (k t' Hk) "H"; iSplit; last by [].
  iPureIntro; rewrite is_mul_TInv.
  have t'_t : t' ∈ exps t by exact: list_elem_of_lookup_2 Hk.
  exact: proj2 (invs_canceled_factors (expo t) _ t'_t).
- rewrite public_eq.
  iIntros "#[m Hdisj]".
  iSplit; first done.
  iDestruct "Hdisj" as "[c1 | [c2 | [c3 | c4]]]".
  + iDestruct "c1" as (T) "[%dec _]".
    by move: expt; rewrite (decompose_is_exp dec).
  + iDestruct "c2" as "(%mul_c & _)".
    by move: expt mul_c;
       rewrite is_exp_unfold is_mul_unfold; case: (unfold_term t).
  + iDestruct "c3" as "(_ & exp)".
    iApply (big_sepL_mono with "exp"). by iIntros (k t' _) "(_ & $)".
  + by case: (t) expt => // *; iDestruct "c4" as "[]".
Qed.

Lemma public_TExp_iff t1 t2 :
  negb (is_exp t1) →
  negb (is_mul t2) ->
  public (TExp t1 t2) ⊣⊢
  minted t1 ∧ minted t2 ∧ exp_pred t2 (TExp t1 t2) ∧ □ (public t2 → public t1).
Proof.
move=> Nexp Nm2.
have eq12 : TExp t1 t2 = TExpN t1 [t2] by rewrite /TExpN TMulN1.
have ic2 : invs_canceled [t2] := invs_canceled1 Nm2.
rewrite {1}eq12 (public_TExpN Nexp ic2) //=.
rewrite -eq12 TExpK minted_TExp //.
by rewrite bi.sep_emp -!bi.and_assoc.
Qed.

Lemma public_TExp2_iff t1 t2 t3 :
  negb (is_exp t1) →
  negb (is_mul t2) ->
  negb (is_mul t3) ->
  t2 ≠ TInv t3 ->
  public (TExpN t1 [t2; t3]) ⊣⊢
  minted (TExpN t1 [t2; t3]) ∧
  exp_pred t2 (TExpN t1 [t2; t3]) ∧
  exp_pred t3 (TExpN t1 [t2; t3]) ∧
  □ (public t2 → public (TExp t1 t3)) ∧
  □ (public t3 → public (TExp t1 t2)).
Proof.
move => Nexp Nm2 Nm3 t2t3.
have Nm2' : negb (is_mul t2) := Nm2.
have Nm3' : negb (is_mul t3) := Nm3.
have ic23 : invs_canceled [t2; t3] := proj2 (invs_canceled2 Nm2' Nm3') t2t3.
have e2 : TExp (TExpN t1 [t2; t3]) (TInv t2) = TExp t1 t3.
  by rewrite -TExp_TExpN /TExpN TMulN1 TExpK.
have e3 : TExp (TExpN t1 [t2; t3]) (TInv t3) = TExp t1 t2.
  by rewrite TExpNC2 -TExp_TExpN /TExpN TMulN1 TExpK.
rewrite (public_TExpN Nexp ic23) //= e2 e3.
apply: anti_symm; iIntros "#H";
  [iDestruct "H" as "(m & [p2 d2] & [p3 d3] & _)"
  |iDestruct "H" as "(m & p2 & p3 & d2 & d3)"];
  by iFrame "#".
Qed.

Lemma exp_pred_exps t1 t2 :
  t2 ∈ exps t1 ->
  public t1 -∗
  exp_pred t2 t1 ∧ □ (public t2 → public (TExp t1 (TInv t2))).
Proof.
have [exp_t1|contra] := decide (is_exp t1); last first.
  have nX : negb (is_exp t1) by apply/negb_True.
  by rewrite /exps (expo_expN _ nX) factors_TMulN0 elem_of_nil.
move => t2_t1. iIntros "#p".
rewrite public_TExpN' // big_sepL_elem_of //.
by iDestruct "p" as "[_ [dh ?]]" => //; eauto.
Qed.

Lemma public_TExp_Nmul t1 t2 :
  negb (is_mul t2) ->
  public t1 -∗
  public t2 -∗
  public (TExp t1 t2).
Proof.
move=> Nm2; have Nm2' : negb (is_mul t2) := Nm2.
elim /term_lt_ind: t1 => t1 IH; iIntros "#p1 #p2".
have [t2_t1|t2_t1] := decide (TInv t2 ∈ exps t1).
  iPoseProof (exp_pred_exps t2_t1 with "p1") as "[_ #p1']".
  by rewrite public_TInv TInvK; iApply "p1'".
have [exp_t1|nexp_t1] := decide (is_exp (TExp t1 t2)); last first.
  have nX : negb (is_exp (TExp t1 t2)) by apply/negb_True.
  by move/not_elem_of_TInv_exps: t2_t1;
     rewrite /exps (expo_expN _ nX) factors_TMulN0 elem_of_nil.
rewrite [public (TExp _ _)]public_TExpN' //; iSplit.
  by iApply all_minted_TExp; iSplit; iApply public_minted.
rewrite big_sepL_forall; iIntros (? t t_t1'%list_elem_of_lookup_2).
have [->|t_t2] := decide (t = t2).
  by rewrite TExpK; iSplit; eauto; iApply exp_pred_intro3.
have t_t1: t ∈ exps t1.
  have t_nin : t ∉ factors t2 by rewrite factors_Nmul // list_elem_of_singleton.
  have := not_elem_of_count _ _ t_nin.
  move: t_t1'; rewrite /exps -!count_gt0 count_expo_TExp; lia.
have Nmt' : negb (is_mul t) := proj2 (invs_canceled_factors (expo t1) _ t_t1).
iPoseProof (exp_pred_exps t_t1 with "p1") as "[dh #p]"; iSplit.
  by iApply exp_pred_intro2 => //; iApply exp_pred_intro3.
iIntros "!> #pt"; iSpecialize ("p" with "pt").
have comm : TExp (TExp t1 t2) (TInv t) = TExp (TExp t1 (TInv t)) t2.
  rewrite (_ : TExp t1 t2 = TExpN t1 [t2]); last by rewrite /TExpN TMulN1.
  rewrite (_ : TExp t1 (TInv t) = TExpN t1 [TInv t]); last by rewrite /TExpN TMulN1.
  by rewrite !TExp_TExpN TExpNC2.
rewrite comm; iApply (IH with "p p2").
have NmTt : negb (is_mul (TInv t)) by rewrite is_mul_TInv.
by have [?[??]] := tsize_TExp_TInv NmTt t_t1.
Qed.

Lemma public_TExpN_intro t ts :
  invs_canceled ts ->
  public t -∗ ([∗ list] t' ∈ ts, public t') -∗ public (TExpN t ts).
Proof.
elim: ts => [|u us IH] ic; iIntros "#p #pus".
- by rewrite TExpN0.
- move: ic => /invs_canceled_cons [_ [Nu atom_us]].
  rewrite -TExp_TExpN big_sepL_cons; iDestruct "pus" as "[#pu #pus']".
  iApply (public_TExp_Nmul _ Nu with "[] pu").
  by iApply (IH atom_us with "p pus'").
Qed.

Lemma public_TExp t1 t2 :
  public t1 -∗ public t2 -∗ public (TExp t1 t2).
Proof.
rewrite (_ : TExp t1 t2 = TExpN t1 (factors t2)); last by rewrite /TExpN factorsK.
iIntros "#p1 #p2".
iApply (public_TExpN_intro _ (invs_canceled_factors t2) with "p1").
case E: (is_mul t2).
- by iApply (public_TMulN (proj1 (is_trueP _) E) with "p2").
- have Hmul : negb (is_mul t2) by rewrite E.
  by rewrite (factors_Nmul _ Hmul) /= bi.sep_emp; iApply "p2".
Qed.

Lemma public_TMulN_intro ts :
  invs_canceled ts ->
  ([∗ list] t' ∈ ts, public t') ⊢ public (TMulN ts).
Proof.
move => ic.
rewrite public_factors (factors_TMulN ic) minted_TMulN //.
iIntros "#H"; iSplit; last done.
iApply (big_sepL_mono with "H"); iIntros (k t' _) "?"; by iApply public_minted.
Qed.

Lemma mem_factors_TMulN2 t1 t2 t' :
  t' ∈ factors (TMulN (t1 :: t2 :: nil)) → t' ∈ factors t1 ++ factors t2.
Proof.
by rewrite elem_of_app -!count_gt0 count_TMulN /fmap /=; lia.
Qed.

Lemma big_sepL_factors_TMulN2 (Φ : term → iProp) `{!∀ t, Persistent (Φ t)} t1 t2 :
  ([∗ list] t' ∈ factors t1, Φ t') -∗
  ([∗ list] t' ∈ factors t2, Φ t') -∗
  [∗ list] t' ∈ factors (TMulN (t1 :: t2 :: nil)), Φ t'.
Proof.
iIntros "#H1 #H2"; iApply big_sepL_intro; iIntros "!>" (k u Hk).
move: (mem_factors_TMulN2 (list_elem_of_lookup_2 _ _ _ Hk)) => /elem_of_app[Hin|Hin].
- by iApply (big_sepL_elem_of with "H1").
- by iApply (big_sepL_elem_of with "H2").
Qed.

Lemma public_TMulN2 t1 t2 :
  public t1 -∗ public t2 -∗ public (TMulN (t1 :: t2 :: nil)).
Proof.
iIntros "#p1 #p2".
iDestruct (public_factors t1 with "p1") as "#[m1 f1]".
iDestruct (public_factors t2 with "p2") as "#[m2 f2]".
iEval (rewrite minted_factors) in "m1".
iEval (rewrite minted_factors) in "m2".
iApply public_factors; iSplit.
- rewrite minted_factors. by iApply (big_sepL_factors_TMulN2 with "m1 m2").
- by iApply (big_sepL_factors_TMulN2 with "f1 f2").
Qed.

Lemma public_TMul0 : ⊢ public (TMulN nil).
Proof.
by iApply (public_TMulN_intro invs_canceled0).
Qed.

Lemma False_public t :
  minted t -∗
  ▷ False -∗
  public t.
Proof.
elim/term_lt_ind: t => t IH;
case: t IH => [n|ta tb|a|kt tt|kk tt|tt|pt wf nf] IH.
- iIntros "_ _"; by rewrite public_TInt.
- have H1 : tsize ta < tsize (TPair ta tb) by rewrite [X in _ < X]tsize_eq /=; lia.
  have H2 : tsize tb < tsize (TPair ta tb) by rewrite [X in _ < X]tsize_eq /=; lia.
  rewrite minted_TPair public_TPair.
  iIntros "#[m1 m2] #contra"; iSplit.
  + iApply (IH ta H1 with "m1 contra").
  + iApply (IH tb H2 with "m2 contra").
- iIntros "#m #contra".
  rewrite minted_TNonce public_TNonce; iSplit => //.
  iDestruct "contra" as ">[]".
- have H1 : tsize tt < tsize (TKey kt tt) by rewrite [X in _ < X]tsize_eq /=; lia.
  rewrite minted_TKey public_TKey.
  iIntros "#m #contra"; iLeft.
  iApply (IH tt H1 with "m contra").
- have H1 : tsize kk < tsize (TSeal kk tt) by rewrite [X in _ < X]tsize_eq /=; lia.
  have H2 : tsize tt < tsize (TSeal kk tt) by rewrite [X in _ < X]tsize_eq /=; lia.
  rewrite minted_TSeal public_TSeal.
  iIntros "#[m1 m2] #contra"; iLeft; iSplit.
  + iApply (IH kk H1 with "m1 contra").
  + iApply (IH tt H2 with "m2 contra").
- have H1 : tsize tt < tsize (THash tt) by rewrite [X in _ < X]tsize_eq /=; lia.
  rewrite minted_THash public_THash.
  iIntros "#m #contra"; iLeft.
  iApply (IH tt H1 with "m contra").
- case: pt wf nf IH => [o|[kt'||] operand|[||] b e|ts] wf nf IH.
  1,2,3,5,6: by move: {IH} nf; rewrite /is_non_free /=.
  + have /andb_True [/andb_True [Ninvpt Nmpt] wfpt] := wf.
    have E : TNonFree (PreTerm.PT1 O1Inv operand) wf nf = TInv (fold_term operand).
      apply: unfold_term_inj.
      by rewrite unfold_TInv (fold_termK operand wfpt) (PreTerm.inv_Nmul operand Nmpt)
         (PreTerm.inv_invN operand Ninvpt).
    have Ninv : negb (is_inv (fold_term operand)) by rewrite is_inv_unfold (fold_termK operand wfpt).
    have Nmf : negb (is_mul (fold_term operand)) by rewrite is_mul_unfold (fold_termK operand wfpt).
    have Hlt : tsize (fold_term operand) < tsize (TInv (fold_term operand)).
      rewrite (tsize_TInv _ Nmf Ninv); lia.
    rewrite E in IH *.
    iIntros "#m #contra".
    iEval (rewrite minted_TInv) in "m".
    rewrite public_TInv.
    iApply (IH (fold_term operand) Hlt with "m contra").
  + set t := TNonFree (PreTerm.PTExp b e) wf nf.
    have xt : is_exp t by [].
    have Nxb : negb (is_exp (base t)) := base_Nexp t.
    have icx : invs_canceled (exps t) := invs_canceled_factors (expo t).
    iIntros "#mt #contra".
    iEval (rewrite -(base_expsK t) (minted_TExpN Nxb icx)) in "mt".
    iDestruct "mt" as "[#mb #mes]".
    iAssert (public (base t)) as "#pb".
    { iApply (IH (base t) (tsize_base_lt t xt) with "mb contra"). }
    iEval (rewrite -(base_expsK t)).
    iApply (public_TExpN_intro (base t) icx with "pb").
    iApply (big_sepL_impl with "mes").
    iIntros "!>" (k e' e'_lk) "#me'".
    iApply (IH e' (tsize_exps_lt _ _ (list_elem_of_lookup_2 _ _ _ e'_lk)) with "me' contra").
  + set t := TNonFree (PreTerm.PTMul ts) wf nf.
    have xt : is_mul t by [].
    have wfl : invs_canceled (factors t) := invs_canceled_factors t.
    iIntros "#mt #contra".
    iEval (rewrite -(factorsK t)).
    iApply (public_TMulN_intro wfl).
    iEval (rewrite -(factorsK t) (minted_TMulN wfl)) in "mt".
    iApply (big_sepL_impl with "mt").
    iIntros "!>" (k ff ff_lk) "#mff".
    iApply (IH ff (tsize_factors_lt _ _ xt (list_elem_of_lookup_2 _ _ _ ff_lk)) with "mff contra").
Qed.

Lemma except_0_public t :
  minted t -∗
  ◇ public t -∗
  public t.
Proof.
rewrite /bi_except_0.
by iIntros "#m #[contra|?]"; eauto; iApply False_public.
Qed.

Local Lemma exp_pred_intro4_aux t1 t2 t3 :
  t1 ≠ t3 →
  t3 ∈ exps t2 →
  TInv t1 ∉ exps t2 →
  TInv t1 ∉ exps (TExp t2 (TInv t3)).
Proof.
move=> t1_t3 t3_t2 t1V_t2.
have Nm3 : negb (is_mul t3) := proj2 (invs_canceled_factors (expo t2) _ t3_t2).
have t1_nin : t1 ∉ factors t3 by rewrite factors_Nmul // list_elem_of_singleton.
have := not_elem_of_count _ _ t1_nin.
move: t1V_t2.
rewrite /exps -!count_gt0 count_expo_TExp !count_TInv_l count_TInv.
lia.
Qed.

Lemma exp_pred_intro4 t1 t2 t3 :
  t3 ∈ exps t2 →
  exp_pred t1 t2 -∗
  public t3 -∗
  exp_pred t1 (TExp t2 (TInv t3)).
Proof.
iIntros (t3_t2) "dh"; iRevert (t3_t2); iRevert (t1 t2) "dh".
iApply exp_pred_ind.
- iIntros "!> %ts %t1 %t2 %atom_ts %ts_t2 #pts #dh %t3_t2 #p3".
  have Nm3 : negb (is_mul t3) := proj2 (invs_canceled_factors (expo t2) _ t3_t2).
  have t3V_nin : TInv t3 ∉ ts.
    move=> t3V_ts; move: (ts_t2 _ t3V_ts); rewrite TInvK => H.
    exact: H t3_t2.
  iApply (@exp_pred_intro1_gen _ _ (t3 :: ts)).
  + by apply/invs_canceled_cons; split; last split.
  + move=> t t_ts; case: (decide (t = t3)) => [->|t_t3].
      rewrite not_elem_of_TInv_exps; last exact: Nm3.
      by rewrite TExpKV.
    have {}t_ts: t ∈ ts by case/elem_of_cons: t_ts => //; congruence.
    have t_t2 := ts_t2 _ t_ts.
    exact: exp_pred_intro4_aux.
  + by rewrite /=; eauto.
  + have e : TExpN (TExp t2 (TInv t3)) (t3 :: ts) = TExpN t2 ts.
      rewrite -TExp_TExpN (_ : TExpN (TExp t2 (TInv t3)) ts = TExp (TExpN t2 ts) (TInv t3)).
        by rewrite TExpKV.
      by rewrite TExp_TExpN (_ : TExp t2 (TInv t3) = TExpN t2 [TInv t3]) ?TExpNA /TExpN ?TMulN1 //.
    rewrite e; iApply "dh".
- iIntros "!> %t %t1 %t2 %Nm_t %t_t2 #dh1 #IH1 #dh2 #IH2 %t3_t2' #p3".
  have Nmt : negb (is_mul t) := Nm_t.
  case: (decide (t3 = t)) => [->|t_t3].
    by rewrite TExpK; iApply "dh1".
  have t3_t2: t3 ∈ exps t2.
    have t3_nin : t3 ∉ factors t by rewrite factors_Nmul // list_elem_of_singleton.
    have := not_elem_of_count _ _ t3_nin.
    move: t3_t2'; rewrite /exps -!count_gt0 count_expo_TExp; lia.
  have comm : TExp (TExp t2 t) (TInv t3) = TExp (TExp t2 (TInv t3)) t.
    rewrite (_ : TExp t2 t = TExpN t2 [t]); last by rewrite /TExpN TMulN1.
    rewrite (_ : TExp t2 (TInv t3) = TExpN t2 [TInv t3]); last by rewrite /TExpN TMulN1.
    by rewrite !TExp_TExpN TExpNC2.
  rewrite comm; iApply exp_pred_intro2.
  + exact: Nmt.
  + exact: (exp_pred_intro4_aux (not_eq_sym t_t3) t3_t2 t_t2).
  + by iApply "IH1" => //.
  + by iApply "IH2" => //.
- by iIntros "!> %t1 %t2 #p1 %t3_t2 #p3"; iApply exp_pred_intro3.
Qed.

Lemma public_TExp_add t1 t2 :
  negb (is_mul t2) →
  TInv t2 ∉ exps t1 →
  public t1 -∗
  minted t2 -∗
  exp_pred t2 (TExp t1 t2) -∗
  public (TExp t1 t2).
Proof.
move=> Nm2; have Nm2' : negb (is_mul t2) := Nm2.
elim/term_lt_ind: t1 => t1 IH in t2 Nm2 Nm2' *.
iIntros "%t2_t1 #p1 #m #dh".
rewrite [public (TExp _ _)]public_TExpN' //; last first.
  case: (decide (is_exp (TExp t1 t2))) => [//|nX].
  have nX' : negb (is_exp (TExp t1 t2)) by apply/negb_True.
  by rewrite not_elem_of_TInv_exps // /exps (expo_expN _ nX') factors_TMulN0
     elem_of_nil in t2_t1.
iSplit.
  by rewrite public_minted; iApply all_minted_TExp; iSplit.
iApply big_sepL_forall; iIntros (k t t_t1').
have {}t_t1': t ∈ exps (TExp t1 t2) by apply: list_elem_of_lookup_2.
have [->|t_t2] := decide (t = t2).
  by iSplit => //; iIntros "!> #p2"; rewrite TExpK.
have t_t1: t ∈ exps t1.
  have t_nin : t ∉ factors t2 by rewrite factors_Nmul // list_elem_of_singleton.
  have := not_elem_of_count _ _ t_nin.
  move: t_t1'; rewrite /exps -!count_gt0 count_expo_TExp; lia.
iPoseProof (exp_pred_exps t_t1 with "p1") as "[dh_t #p1']".
iSplit; first by iApply exp_pred_intro2.
iIntros "!> #p"; iSpecialize ("p1'" with "p").
have Nmt : negb (is_mul t) := proj2 (invs_canceled_factors (expo t1) _ t_t1).
have NmIt : negb (is_mul (TInv t)) by rewrite is_mul_TInv.
rewrite TExpC; iApply (IH with "p1' m []").
- by have [_ [_ ?]] := tsize_TExp_TInv NmIt t_t1.
- exact: Nm2.
- exact: Nm2'.
- have t2_tV : t2 ≠ TInv t by move=> contra; apply: t2_t1; rewrite contra TInvK.
  move=> contra; apply: t2_t1.
  have t2_tVV : t2 ≠ TInv (TInv t) by rewrite TInvK; exact: not_eq_sym t_t2.
  have Hmono := exps_count_TExpW t2 t1 (TInv t) NmIt t2_tVV.
  move: contra; rewrite /exps -!count_gt0 !count_TInv_l; lia.
- by rewrite -TExpC; iApply exp_pred_intro4 => //.
Qed.

Lemma public_TExp_exp_pred t1 t2 :
  negb (is_mul t2) →
  public t1 -∗
  minted t2 -∗
  exp_pred t2 (TExp t1 t2) -∗
  □ (∀ t, exp_pred_base (TInv t2) t ↔ ▷ False) -∗
  public (TExp t1 t2).
Proof.
move=> Nm2; have Nm2' : negb (is_mul t2) := Nm2.
iIntros "#p1 #m2 #dh #dhV"; iApply except_0_public.
  by iApply all_minted_TExp; iSplit; rewrite // public_minted.
case: (decide (TInv t2 ∈ exps t1)) => in_exps; last first.
  by iModIntro; iApply (public_TExp_add Nm2).
iPoseProof (exp_pred_exps in_exps with "p1") as "[dh' #?]"; rewrite TInvK.
iPoseProof (exp_pred_inv_same in_exps with "dh'") as "[p2|H]".
- iModIntro.
  iEval (rewrite public_TInv) in "p2".
  by iApply (public_TExp with "p1 p2").
- iDestruct "H" as "(%t2' & _ & _ & contra)".
  by iDestruct ("dhV" with "contra") as ">[]".
Qed.

Lemma public_to_list t ts :
  Spec.to_list t = Some ts →
  public t -∗ [∗ list] t' ∈ ts, public t'.
Proof.
elim/term_ind': t ts => //=.
  by case=> // ts [<-] /=; iIntros "?".
move=> t _ tl IH ts.
case e: (Spec.to_list tl) => [ts'|] // [<-] /=.
rewrite public_TPair /=; iIntros "[??]"; iFrame.
by iApply IH.
Qed.

Lemma public_of_list ts :
  public (Spec.of_list ts) ⊣⊢
  [∗ list] t ∈ ts, public t.
Proof.
rewrite Spec.of_list_unseal.
elim: ts => [|t ts IH]; first by rewrite public_TInt.
by rewrite public_TPair /= IH bi.persistent_and_sep.
Qed.

Lemma public_Tag N : public (Tag N) ⊣⊢ True.
Proof. by rewrite Tag_unseal public_TInt. Qed.

Lemma public_tag N t : public (Spec.tag (Tag N) t) ⊣⊢ public t.
Proof.
by rewrite Spec.tag_unseal public_TPair public_Tag bi.emp_and.
Qed.

Lemma public_THashE N φ t :
  hash_pred N φ -∗
  public (THash (Spec.tag (Tag N) t)) -∗
  public t ∨ minted t ∗ ▷ □ φ t.
Proof.
  iIntros "#Hpred #Hpub".
  rewrite public_THash.
  iDestruct "Hpub" as "[Hpub | [Hmint Hwfhash]]".
  rewrite public_tag.
  by iLeft.
  rewrite minted_tag.
  iRight.
  iSplit => //.
  iDestruct (wf_hash_elim N t φ with "Hwfhash Hpred") as "H".
  by iNext.
Qed.

Lemma public_TSeal_tag k N t :
public (TSeal k (Spec.tag (Tag N) t)) ⊣⊢
public k ∧ public t ∨
minted k ∧ minted t ∧
match func_of_term k with
| Some F => ∃ Φ,
      ⌜Spec.is_seal_key k⌝ ∧
      seal_pred F N Φ ∧
      □ ▷ Φ (Spec.skey k) t ∧
      match Spec.open_key k with
      | Some k' => □ (public k' → public t)
      | None => True
      end
  | None => True
  end.
Proof.
rewrite public_TSeal {1}public_tag minted_TSeal minted_tag.
rewrite [(_ ∧ _ ∧ _)%I]assoc.
apply: bi.or_proper => //.
apply: bi.and_proper => //.
case: func_of_term => // F.
apply (anti_symm _).
- iIntros "(? & (%N' & %t' & %Φ & %e & ? & ?) & ?)".
  case/Spec.tag_inj: e => [/Tag_inj <- <-].
  iExists Φ. do !iSplit => //.
  case: Spec.open_key => // k'. by rewrite public_tag.
- iIntros "(%Φ & ? & ? & ? & ?)".
  do !iSplit => //.
  + iExists N, t, Φ. by eauto.
  + case: Spec.open_key => // k'. by rewrite public_tag.
Qed.

Lemma public_TSealE N Φ k t F :
  public (TSeal k (Spec.tag (Tag N) t)) -∗
  ⌜func_of_term k = Some F ∧ Spec.is_seal_key k⌝ -∗
  seal_pred F N Φ -∗
  public k ∧ public t ∨
  □ ▷ Φ (Spec.skey k) t ∧
  match Spec.open_key k with
  | Some k' => □ (public k' → public t)
  | None => True
  end.
Proof.
iIntros "#Ht %kP #HΦ"; rewrite public_TSeal; case: kP => [-> k_seal].
iDestruct "Ht" as "[[? Ht] | [_ Ht]]"; first by rewrite public_tag; eauto.
iDestruct "Ht" as "(_ & inv & ?)".
iPoseProof (wf_seal_elim with "inv HΦ") as "?".
iRight. iSplit => //. case: Spec.open_key => // ?.
by rewrite public_tag.
Qed.

Lemma public_TSealIS F N Φ k t :
  ⌜func_of_term k = Some F ∧ Spec.is_seal_key k⌝ -∗
  seal_pred F N Φ -∗
  □ Φ (Spec.skey k) t -∗
  minted k -∗
  minted t -∗
  match Spec.open_key k with
  | Some k' => □ (public k' → public t)
  | None => True
  end -∗
  public (TSeal k (Spec.tag (Tag N) t)).
Proof.
iIntros "[%k_F %kP] #HΦ #HΦt #m_k #m_t #Hopenl".
rewrite public_TSeal k_F. iRight. rewrite minted_TSeal minted_tag.
iSplit; first by eauto. iSplit => //. iSplit; last first.
{ case: Spec.open_key => // ?. by rewrite public_tag. }
iExists N, t, Φ. eauto.
Qed.

Lemma public_TSealIP k t :
  public k -∗
  public t -∗
  public (TSeal k t).
Proof. by iIntros "? ?"; rewrite public_TSeal; eauto. Qed.

Lemma nonce_alloc P Q a :
  meta_token (nonce_loc a) ⊤ -∗
  (minted (TNonce a) -∗ False) ∧
  |==> minted (TNonce a) ∗
    □ (public (TNonce a) ↔ ▷ □ P (TNonce a)) ∗
    □ (∀ t, exp_pred_base (TNonce a) t ↔ ▷ □ Q t).
Proof.
iIntros "token".
iSplit.
{ rewrite minted_TNonce. iIntros "contra".
  by iDestruct (meta_meta_token with "token contra") as "[]". }
iMod (own_alloc (saved_pred DfracDiscarded P)) as (γP) "#own_P" => //.
iMod (own_alloc (saved_pred DfracDiscarded Q)) as (γQ) "#own_Q" => //.
rewrite (meta_token_difference (nonce_loc a) (↑nroot.@"nonce")) //.
iDestruct "token" as "[nonce token]".
iMod (meta_set _ _ γP with "nonce") as "#nonce"; eauto.
rewrite (meta_token_difference (nonce_loc a) (↑nroot.@"dh")); last solve_ndisj.
iDestruct "token" as "[dh token]".
iMod (meta_set _ _ γQ with "dh") as "#dh"; eauto.
rewrite (meta_token_difference (nonce_loc a) (↑nroot.@"minted")); last solve_ndisj.
iDestruct "token" as "[minted token]".
iMod (meta_set _ _ () (nroot.@"minted") with "minted") as "#minted" => //.
iSplitR.
  by rewrite minted_TNonce.
iSplitR.
  rewrite public_TNonce; do 2!iModIntro; iSplit.
  + iIntros "[#public _]".
    iDestruct "public" as (γP' P') ">(#meta_γP' & #own_P' & ?)".
    iPoseProof (meta_agree with "nonce meta_γP'") as "->".
    iPoseProof (own_valid_2 with "own_P own_P'") as "valid".
    iPoseProof (saved_pred_op_validI with "valid") as "[_ #e]".
    iSpecialize ("e" $! (TNonce a)). iModIntro. by iRewrite "e".
  + iIntros "#?". iSplit => //. iExists γP, P; eauto.
iIntros "!> !> %t"; iSplit.
- iDestruct 1 as (γQ' Q') "(#meta_γQ' & #own_Q' & ?)".
  iPoseProof (meta_agree with "dh meta_γQ'") as "->".
  iPoseProof (own_valid_2 with "own_Q own_Q'") as "valid".
  iPoseProof (saved_pred_op_validI with "valid") as "[_ #e]".
  iSpecialize ("e" $! t). iModIntro. by iRewrite "e".
- by iIntros "#?"; iExists _, _; eauto.
Qed.

Lemma public_pkey k : public k ⊢ public (Spec.pkey k).
Proof.
iIntros "#p_k".
iPoseProof (public_minted with "p_k") as "m_k".
case: k => // - [] // t; iClear "p_k";
rewrite minted_TKey public_TKey /=; eauto.
Qed.

Lemma public_senc_key k : public (SEncKey k) ⊣⊢ public k.
Proof.
rewrite [term_of_senc_key]unlock public_TKey /=.
iSplit; eauto.
by iIntros "[#p_k|[? []]]"; eauto.
Qed.

Lemma public_senc_key' (sk : senc_key) :
  public sk ⊣⊢ public (seed_of_senc_key sk).
Proof.
case: sk => seed. by rewrite public_senc_key.
Qed.

Lemma public_aenc_key (sk : aenc_key) : public (Spec.pkey sk) ⊣⊢ minted sk.
Proof.
rewrite [term_of_aenc_key]unlock; case: sk => [seed] /=.
rewrite public_TKey /= minted_TKey. iSplit; eauto.
iIntros "[#p_k|[? ?]]"; eauto.
by iApply public_minted.
Qed.

Lemma public_adec_key k : public (AEncKey k) ⊣⊢ public k.
Proof.
rewrite [term_of_aenc_key]unlock public_TKey /=.
iSplit; eauto.
by iIntros "[#p_k|[? []]]"; eauto.
Qed.

Lemma public_adec_key' (sk : aenc_key) :
  public sk ⊣⊢ public (seed_of_aenc_key sk).
Proof. case: sk => seed. by rewrite public_adec_key. Qed.

Lemma public_verify_key (sk : sign_key) : public (Spec.pkey sk) ⊣⊢ minted sk.
Proof.
rewrite [term_of_sign_key]unlock; case: sk => seed /=. rewrite public_TKey /= minted_TKey.
iSplit; eauto.
iIntros "[#p_k|[? ?]]"; eauto.
by iApply public_minted.
Qed.

Lemma public_sign_key k : public (SignKey k) ⊣⊢ public k.
Proof.
rewrite [term_of_sign_key]unlock public_TKey /=.
iSplit; eauto.
by iIntros "[#p_k|[? []]]"; eauto.
Qed.

Lemma public_sign_key' (sk : sign_key) :
  public sk ⊣⊢ public (seed_of_sign_key sk).
Proof.
case: sk => seed. by rewrite public_sign_key.
Qed.

Definition pending γ : iProp :=
  gmeta_token γ ⊤.

Definition shot γ (x : positive) : iProp :=
  gmeta γ nroot x.

Global Instance persistent_shot γ x : Persistent (shot γ x).
Proof. apply _. Qed.

Global Instance timeless_shot γ x : Timeless (shot γ x).
Proof. apply _. Qed.

Lemma pending_alloc : ⊢ |==> ∃ γ, pending γ.
Proof. apply gmeta_token_alloc. Qed.

Lemma shot_alloc γ x : pending γ ==∗ shot γ x.
Proof. by apply gmeta_set. Qed.

Lemma pending_shot γ x : pending γ -∗ shot γ x -∗ False.
Proof. by apply gmeta_gmeta_token. Qed.

Lemma shot_agree γ x y : shot γ x -∗ shot γ y -∗ ⌜x = y⌝.
Proof. apply gmeta_agree. Qed.

Definition secret t : iProp :=
  (|==> public t) ∧
  (|==> □ (public t ↔ ▷ False)) ∧
  (public t -∗ ▷ False).

Lemma secret_alloc t γ :
  □ (public t ↔ ▷ shot γ 1) -∗ pending γ -∗ secret t.
Proof.
iIntros "#s_t pending"; do 2?iSplit.
- iMod (shot_alloc with "pending") as "#shot".
  by iSpecialize ("s_t" with "shot").
- iMod (shot_alloc _ 2 with "pending") as "#shot".
  iIntros "!> !>". iSplit.
  + iIntros "#p_t".
    iPoseProof ("s_t" with "p_t") as ">#shot'".
    by iPoseProof (shot_agree with "shot shot'") as "%".
  + iIntros "#contra".
    iApply "s_t". by iDestruct "contra" as ">[]".
- iIntros "#p_t".
  iPoseProof ("s_t" with "p_t") as ">#shot".
  by iPoseProof (pending_shot with "[$] [//]") as "[]".
Qed.

Lemma secret_not_public t : secret t -∗ public t -∗ ▷ False.
Proof. by iIntros "(_ & _ & contra)". Qed.

Lemma secret_public t : secret t ==∗ public t.
Proof. by iIntros "(? & _)". Qed.

Lemma freeze_secret t : secret t ==∗ □ (public t ↔ ▷ False).
Proof. by iIntros "(_ & ? & _)". Qed.

Lemma public_aencIS (sk : aenc_key) N Φ t :
  aenc_pred N Φ -∗
  minted sk -∗
  minted t -∗
  □ Φ sk t -∗
  □ (public sk → public t) -∗
  public (TSeal (Spec.pkey sk) (Spec.tag (Tag N) t)).
Proof.
rewrite [term_of_aenc_key]unlock; case: sk => seed /=.
rewrite minted_TKey. iIntros "#? #m_k #m_t #inv #p_t".
iApply public_TSealIS => //.
- iModIntro. iExists (AEncKey _). rewrite [term_of_aenc_key]unlock. by eauto.
- by rewrite minted_TKey.
Qed.

Lemma public_sencIS (k : senc_key) N Φ t :
  senc_pred N Φ -∗
  minted k -∗
  minted t -∗
  □ Φ k t -∗
  □ (public k → public t) -∗
  public (TSeal k (Spec.tag (Tag N) t)).
Proof.
rewrite [term_of_senc_key]unlock; case: k => seed /=.
iIntros "#? #m_k #m_t #inv #p_t".
iApply public_TSealIS => //.
iModIntro. iExists (SEncKey _). rewrite [term_of_senc_key]unlock. by eauto.
Qed.

Lemma public_signIS (sk : sign_key) N Φ t :
  sign_pred N Φ -∗
  minted sk -∗
  public t -∗
  □ Φ sk t -∗
  public (TSeal sk (Spec.tag (Tag N) t)).
Proof.
rewrite [term_of_sign_key]unlock; case: sk => seed /=.
rewrite minted_TKey.
iIntros "#? #m_k #p_t #inv".
iApply public_TSealIS => //.
- iModIntro. iExists (SignKey _). rewrite [term_of_sign_key]unlock; by eauto.
- by rewrite minted_TKey.
- by iApply public_minted.
- by iIntros "!> _".
Qed.

Lemma public_aencE (sk : aenc_key) N Φ t :
  public (TSeal (Spec.pkey sk) (Spec.tag (Tag N) t)) -∗
  aenc_pred N Φ -∗
  minted t ∧ (public t ∨ □ ▷ Φ sk t ∧ □ (public sk → public t)).
Proof.
rewrite keysE; case: sk => seed /=.
iIntros "#p_t #?". iSplit => //.
{ iPoseProof (public_minted with "p_t") as "#m_t".
  rewrite minted_TSeal minted_tag. by iDestruct "m_t" as "[_ ?]". }
iPoseProof (public_TSealE with "p_t [//] [//]") as "[[_ comp]|inv]"; eauto.
rewrite /=. iDestruct "inv" as "[#inv #?]". iRight. iSplit => //.
iIntros "!> !>". iDestruct "inv" as "(%k' & %e & inv)".
rewrite keysE in e. by case: k' e => seed' // [<-].
Qed.

Lemma public_signE (sk : sign_key) N Φ t :
  public (TSeal sk (Spec.tag (Tag N) t)) -∗
  sign_pred N Φ -∗
  public t ∧ (public sk ∨ □ ▷ Φ sk t).
Proof.
rewrite keysE; case: sk => seed /=.
iIntros "#p_t #?". iPoseProof (public_minted with "p_t") as "m_t".
rewrite minted_TSeal minted_TKey. iDestruct "m_t" as "[? _]".
iPoseProof (public_TSealE with "p_t [//] [//]") as "[[??]|inv]"; eauto.
iDestruct "inv" as "{p_t} (#inv & #p_t)". iSplit => //.
- iApply "p_t". iApply public_TKey. iRight. by iSplit => //.
- iRight. iIntros "!> !>". iDestruct "inv" as "(%k' & %e & inv)".
  rewrite keysE in e; by case: k' e => seed' // [<-].
Qed.

Lemma public_sencE (k : senc_key) N Φ t :
  public (TSeal k (Spec.tag (Tag N) t)) -∗
  senc_pred N Φ -∗
  minted t ∧ (public k ∨ □ ▷ Φ k t) ∧ □ (public k → public t).
Proof.
rewrite keysE; case: k => seed /=.
iIntros "#p_t #?". iSplit => //.
{ iPoseProof (public_minted with "p_t") as "#m_t".
  rewrite minted_TSeal minted_tag. by iDestruct "m_t" as "[_ ?]". }
iPoseProof (public_TSealE with "p_t [//] [//]") as "[[??]|[#inv #p_t']]";
eauto. iSplit => //. iRight.
iIntros "!> !>". iDestruct "inv" as "(%k' & %e & inv)".
rewrite keysE in e; by case: k' e => seed' // [<-].
Qed.
End Public.

Arguments public_aenc_name {Σ _}.
Arguments public_sign_name {Σ _}.
Arguments public_senc_name {Σ _}.
Arguments seal_pred {Σ _} F N Φ.
Arguments seal_pred_set {Σ _} F {_} N Φ.
Arguments seal_pred_token_difference {Σ _} F E1 E2.
Arguments public_hash_name {Σ _}.
Arguments hash_pred {Σ _} N P.
Arguments hash_pred_set {Σ _ _} N P.
Arguments hash_pred_token_difference {Σ _} E1 E2.

Lemma publicGS_alloc `{!heapGS Σ} E :
  publicGpreS Σ →
  ⊢ |={E}=> ∃ (H : publicGS Σ),
             seal_pred_token AENC ⊤ ∗
             seal_pred_token SIGN ⊤ ∗
             seal_pred_token SENC ⊤ ∗
             hash_pred_token ⊤.
Proof.
move=> ?; iStartProof.
iMod gmeta_token_alloc as (γ_aenc) "own_aenc".
iMod gmeta_token_alloc as (γ_sign) "own_sign".
iMod gmeta_token_alloc as (γ_senc) "own_senc".
iMod gmeta_token_alloc as (γ_hash) "own_hash".
pose (H := PublicGS _ γ_aenc γ_sign γ_senc γ_hash).
iExists H. by iFrame.
Qed.
