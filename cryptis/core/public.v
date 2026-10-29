From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta nown saved_prop size_rec_pred sms.
From cryptis.lib Require Import list_sort.
From cryptis.core Require Import term minted term_meta.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class publicGpreS Σ := PublicGPreS {
  #[local] publicGpreS_nonce :: savedPredG Σ nonce;
  #[local] publicGpreS_term  :: savedPredG Σ term;
  #[local] publicGpreS_seal  :: savedPredG Σ (term * term);
  #[local] publicGpreS_meta  :: metaGS Σ;
}.

Class publicGS Σ := PublicGS {
  #[global] public_inG :: publicGpreS Σ;
  public_hash_name  : gname;
  public_aenc_name  : gname;
  public_sign_name  : gname;
  public_senc_name  : gname;
}.

Definition publicΣ : gFunctors :=
  #[savedPredΣ nonce;
    savedPredΣ term;
    savedPredΣ (term * term);
    metaΣ].

#[global] Instance subG_publicGpreS Σ : subG publicΣ Σ → publicGpreS Σ.
Proof. solve_inG. Qed.

Section Public.

Context `{!heapGS Σ, !publicGS Σ, !term_metaGS Σ}.
Abbreviation iProp := (iProp Σ).
Abbreviation iPropO := (iPropO Σ).

Abbreviation iPropI := (iPropI Σ).

Definition pnonce a : iProp :=
  ∃ γ P, meta (nonce_loc a) (nroot.@"nonce") γ ∧
         own γ (saved_pred DfracDiscarded P) ∧
         ▷ □ P a.

#[global] Instance Persistent_pnonce a : Persistent (pnonce a).
Proof. apply _. Qed.

Definition exp_pred (t t' : term) : iProp :=
  match t with
  | TNonce a =>
    ∃ γ φ, meta (nonce_loc a) (nroot.@"dh") γ ∧
           own γ (saved_pred DfracDiscarded φ) ∧
           ▷ □ φ t'
  | _ => ▷ False
  end.

Lemma exp_pred_TInv t t' :
  negb (is_mul t) →
  exp_pred (TInv t) t' ⊣⊢ ▷ False.
Proof.
move=> /is_mul_TInv_atom; rewrite /exp_pred.
by case: (TInv t).
Qed.

#[global] Instance exp_pred_persistent t t' :
  Persistent (exp_pred t t').
Proof. by case: t; apply _. Qed.

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

#[global] Instance seal_pred_persistent F N Φ : Persistent (seal_pred F N Φ).
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

#[global] Instance wf_seal_persistent F k t : Persistent (wf_seal F k t).
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

#[global] Instance hash_pred_persistent N P : Persistent (hash_pred N P).
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

#[global] Instance wf_hash_persistent t : Persistent (wf_hash t).
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

Inductive decompose (T : gset term) (t : term) : Prop :=
| DInt n of T = ∅ & t = TInt n

| DPair t1 t2 of T = {[t1; t2]} & t = TPair t1 t2

| DKey kt t' of T = {[t']} & t = TKey kt t'

| DSeal k t' of T = {[k; t']} & t = TSeal k t'

| DHash t' of T = {[t']} & t = THash t'.

Lemma decompose_tsize T t t' : decompose T t → t' ∈ T → tsize t' < tsize t.
Proof.
case; try by move =>> -> -> //;
          try move => /elem_of_union [];
          move => /elem_of_singleton ->;
          rewrite [X in _ < X]tsize_eq;
          lia.
Qed.

Lemma decompose_Nmul T t : decompose T t → negb (is_mul t).
Proof. by case => *; subst. Qed.

Lemma decompose_Ngmul T t : decompose T t → negb (is_gmul t).
Proof. by case => *; subst. Qed.

Lemma decompose_Nexp T t : decompose T t → negb (is_exp t).
Proof. by case => *; subst. Qed.

(* The attacker can strip an exponent it knows.  Otherwise, the last exponent
   of an exponential was added by the attacker or by its owner, unless all the
   owners of its positive exponents agree to publish it. *)
Definition public_pre_aux P t : iProp :=
  minted t ∧ (
   (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, P t')
   ∨ (⌜is_mul t⌝ ∧ [∗ list] t' ∈ elements (factors t), P t')
   ∨ (⌜is_gmul t⌝ ∧ [∗ list] t' ∈ elements (gfactors t), P t')
   ∨ (⌜is_exp t⌝ ∧
      ([∗ list] t' ∈ SMS.pos (exps t), □ (P t' → P (TExp t (TInv t')))) ∧
      ([∗ list] t' ∈ SMS.neg (exps t), P t' ∧ P (TExp t t')) ∧
      (⌜SMS.neg (exps t) ≠ []⌝ ∨
       (∃ t', ⌜t' ∈ SMS.pos (exps t)⌝ ∧
          (P t' ∨ exp_pred t' t) ∧ P (TExp t (TInv t'))) ∨
       [∗ list] t' ∈ SMS.pos (exps t), exp_pred t' t))
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

Lemma public_pre_aux_wf :
  (∀ P1 P2 t,
    (∀ t', tsize t' < tsize t → P1 t' ≡ P2 t') →
    public_pre_aux P1 t ≡ public_pre_aux P2 t).
Proof.
move => P1 P2 {}t HP; rewrite /public_pre_aux.
f_equiv.
f_equiv; last (f_equiv; last (f_equiv; last f_equiv)).
- f_equiv => T; apply: and_proper_L => T_t.
  apply: big_sepS_proper => t' T_t'.
  by move: (decompose_tsize T_t T_t') => ?; eauto.
- apply: and_proper_L => mul_t.
  apply: big_sepL_proper => _ t' /(list_elem_of_lookup_2 _ _ _) t'_in.
  apply: HP.
  exact: (tsize_factors_lt t' t mul_t t'_in).
- apply: and_proper_L => mul_t.
  apply: big_sepL_proper => _ t' /(list_elem_of_lookup_2 _ _ _) t'_in.
  apply: HP.
  exact: (tsize_gfactors_lt t' t mul_t t'_in).
- apply: and_proper_L => exp_t.
  have Hpos t' : t' ∈ SMS.pos (exps t) →
      P1 t' ≡ P2 t' ∧ P1 (TExp t (TInv t')) ≡ P2 (TExp t (TInv t')).
    by case/tsize_TExp_pos => ??; split; apply: HP.
  have Hneg t' : t' ∈ SMS.neg (exps t) →
      P1 t' ≡ P2 t' ∧ P1 (TExp t t') ≡ P2 (TExp t t').
    by case/tsize_TExp_neg => ??; split; apply: HP.
  f_equiv; [|f_equiv; [|f_equiv; f_equiv]].
  + apply: big_sepL_proper => _ t' /(list_elem_of_lookup_2 _ _ _) /Hpos.
    by case=> -> ->.
  + apply: big_sepL_proper => _ t' /(list_elem_of_lookup_2 _ _ _) /Hneg.
    by case=> -> ->.
  + f_equiv => t'; apply: and_proper_L => /Hpos [-> ->] //.
- case: t => // k t in HP *.
  case: func_of_term => // F; f_equiv; f_equiv.
  case e_k: Spec.open_key => [k'|] //=.
  have ? := Spec.open_key_tsize e_k.
  have ?: tsize (TSeal k t) = S (tsize k + tsize t).
    by rewrite tsize_eq.
  f_equiv; f_equiv; apply: HP; lia.
Qed.

Lemma public_pre_aux_persistent P :
  □ (∀ t, P t -∗ <pers> P t) -∗
  ∀ t, public_pre_aux P t -∗ <pers> public_pre_aux P t.
Proof.
iIntros "#wand %t [#m [H | [H | [H | [H | H]]]]]"; iSplit => //.
- iDestruct "H" as (T ?) "H"; iLeft; iExists T; iSplit; eauto.
  iAssert ([∗ set] t' ∈ T, <pers> P t')%I as "{H} #H".
  { iApply (big_sepS_impl with "H"); iIntros "!> %t' _".
    by iApply "wand". }
  by iModIntro; iApply (big_sepS_impl with "H"); eauto.
- iDestruct "H" as "(% & H)"; iRight; iLeft.
  iAssert ([∗ list] t' ∈ elements (factors t), <pers> P t')%I
    as "{H} #H".
  { iApply (big_sepL_impl with "H"); iIntros "!> %k %t' _".
    by iApply "wand". }
  by iModIntro; iSplit => //; iApply (big_sepL_impl with "H"); eauto.
- iDestruct "H" as "(% & H)"; iRight; iRight; iLeft.
  iAssert ([∗ list] t' ∈ elements (gfactors t), <pers> P t')%I
    as "{H} #H".
  { iApply (big_sepL_impl with "H"); iIntros "!> %k %t' _".
    by iApply "wand". }
  by iModIntro; iSplit => //; iApply (big_sepL_impl with "H"); eauto.
- iDestruct "H" as "(% & H)"; iRight; iRight; iRight; iLeft.
  iAssert ([∗ list] t' ∈ SMS.pos (exps t),
    □ (P t' → P (TExp t (TInv t'))))%I with "[H]" as "#Hpos".
  { by iDestruct "H" as "(#H & _)". }
  iAssert ([∗ list] t' ∈ SMS.neg (exps t), <pers> P t' ∧ <pers> P (TExp t t'))%I
    with "[H]" as "#Hneg".
  { iDestruct "H" as "(_ & H & _)"; iApply (big_sepL_impl with "H").
    iIntros "!> %k %t' _ H"; iSplit.
    - by iDestruct "H" as "[H _]"; iApply "wand".
    - by iDestruct "H" as "[_ H]"; iApply "wand". }
  iAssert (<pers> (⌜SMS.neg (exps t) ≠ []⌝ ∨
    (∃ t', ⌜t' ∈ SMS.pos (exps t)⌝ ∧
       (P t' ∨ exp_pred t' t) ∧ P (TExp t (TInv t'))) ∨
    [∗ list] t' ∈ SMS.pos (exps t), exp_pred t' t))%I
    with "[H]" as "#Hlast".
  { iDestruct "H" as "(_ & _ & [% | [(%t' & %t'_t & H) | #H]])".
    - by iModIntro; iLeft.
    - iAssert (<pers> P (TExp t (TInv t')))%I with "[H]" as "#Hp".
      { by iDestruct "H" as "[_ H]"; iApply "wand". }
      iAssert (<pers> (P t' ∨ exp_pred t' t))%I with "[H]" as "#Ht'".
      { iDestruct "H" as "[[H | #H] _]"; last by iModIntro; iRight.
        by iDestruct ("wand" with "H") as "#?"; iModIntro; iLeft. }
      iModIntro; iRight; iLeft; iExists t'.
      by iSplit; [iPureIntro|iSplit].
    - by iModIntro; iRight; iRight. }
  iModIntro; iSplit => //; iSplit => //; iSplit => //.
  by iApply (big_sepL_impl with "Hneg"); iIntros "!> % % _ [#? #?]"; eauto.
- iRight; iRight; iRight; iRight; case: t; by move=> *; iPoseProof "H" as "#H".
Qed.

Definition public_def := size_rec_pred tsize public_pre_aux.
#[local] Definition public_aux : seal (@public_def). Proof. by eexists. Qed.
Definition public := public_aux.(unseal).
#[local] Lemma public_unseal : public = public_def.
Proof. rewrite -public_aux.(seal_eq) //. Qed.

Lemma public_eq t :
  public t ⊣⊢
  minted t ∧ (
      (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, public t')
     ∨ (⌜is_mul t⌝ ∧ [∗ list] t' ∈ elements (factors t), public t')
     ∨ (⌜is_gmul t⌝ ∧ [∗ list] t' ∈ elements (gfactors t), public t')
     ∨ (⌜is_exp t⌝ ∧
        ([∗ list] t' ∈ SMS.pos (exps t),
          □ (public t' → public (TExp t (TInv t')))) ∧
        ([∗ list] t' ∈ SMS.neg (exps t), public t' ∧ public (TExp t t')) ∧
        (⌜SMS.neg (exps t) ≠ []⌝ ∨
         (∃ t', ⌜t' ∈ SMS.pos (exps t)⌝ ∧
            (public t' ∨ exp_pred t' t) ∧ public (TExp t (TInv t'))) ∨
         [∗ list] t' ∈ SMS.pos (exps t), exp_pred t' t))
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
rewrite public_unseal /public_def.
exact: (size_rec_pred_unfold public_pre_aux_wf t).
Qed.

#[global] Instance Persistent_public t : Persistent (public t).
Proof.
rewrite /Persistent public_unseal /public_def; iIntros "H".
iApply (size_rec_pred_persistent with "[] H"); iIntros "!> %P #HP".
by iApply public_pre_aux_persistent.
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
  iDestruct "publ" as "[publ | [(? & _) | [(? & _) | [(? & _) | publ]]]]" => //=.
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
  iDestruct "Ht" as "[publ | [ (? & _) | [ (? & _) | [ (? & _) | ? ] ] ]]" => //.
  iDestruct "publ" as (T) "[%dec _]".
  by case: dec.
- rewrite public_eq minted_TNonce /pnonce.
  iDestruct "Ht" as "[Ht ?]". iFrame.
Qed.

Lemma public_mul_factors t :
  is_mul t ->
  public t ⊢ [∗ list] t' ∈ elements (factors t), public t'.
Proof.
move=> mul_t; rewrite public_eq.
iIntros "[_ [publ | [ [_ Hfs] | [ [%gmul_t _] | [ (%exp_t & _) | Hstr ]]]]]".
- iDestruct "publ" as (T) "[%dec _]".
  by case: (is_mul t) (decompose_Nmul dec) mul_t.
- by iApply "Hfs".
- by move: mul_t gmul_t;
     rewrite is_mul_unfold is_gmul_unfold;
     case: (unfold_term t) => [|||[|] ? ?].
- by move: mul_t exp_t;
     rewrite is_mul_unfold is_exp_unfold;
     case: (unfold_term t) => [|||[|] ? ?].
- by case: (t) mul_t => // *; iDestruct "Hstr" as "[]".
Qed.

Lemma public_factors t :
  public t ⊣⊢
  minted t ∧ [∗ list] t' ∈ elements (factors t), public t'.
Proof.
case Emul: (is_mul t); last first.
- rewrite factors_Nmul; last by rewrite Emul.
  rewrite SMS.elements_singleton big_sepL_singleton.
  apply: (anti_symm _).
  + by iIntros "#p"; iSplit; first iApply public_minted.
  + by iIntros "[_ $]".
- have mulI : is_mul t by rewrite Emul.
  apply: (anti_symm _).
  + iIntros "#p"; iSplit; first by iApply public_minted.
    by iApply (public_mul_factors mulI with "p").
  + iIntros "[#m #fs]"; rewrite [public t]public_eq; iSplit => //.
    by iRight; iLeft; iSplit.
Qed.

(** The group product and the group inverse get exactly the treatment the
    exponent product and inverse get: [public] of a group product is the
    conjunction over its group factors, and [public (TGInv t) ⊣⊢ public t]. *)

Lemma public_gmul_gfactors t :
  is_gmul t ->
  public t ⊢ [∗ list] t' ∈ elements (gfactors t), public t'.
Proof.
move=> mul_t; rewrite public_eq.
iIntros "[_ [publ | [ [%mul_t' _] | [ [_ Hfs] | [ (%exp_t & _) | Hstr ]]]]]".
- iDestruct "publ" as (T) "[%dec _]".
  by case: (is_gmul t) (decompose_Ngmul dec) mul_t.
- by move: mul_t mul_t';
     rewrite is_mul_unfold is_gmul_unfold;
     case: (unfold_term t) => [|||[|] ? ?].
- by iApply "Hfs".
- by move: mul_t exp_t;
     rewrite is_gmul_unfold is_exp_unfold;
     case: (unfold_term t) => [|||[|] ? ?].
- by case: (t) mul_t => // *; iDestruct "Hstr" as "[]".
Qed.

Lemma public_gfactors t :
  public t ⊣⊢
  minted t ∧ [∗ list] t' ∈ elements (gfactors t), public t'.
Proof.
case Emul: (is_gmul t); last first.
- rewrite gfactors_Ngmul; last by rewrite Emul.
  rewrite SMS.elements_singleton big_sepL_singleton.
  apply: (anti_symm _).
  + by iIntros "#p"; iSplit; first iApply public_minted.
  + by iIntros "[_ $]".
- have mulI : is_gmul t by rewrite Emul.
  apply: (anti_symm _).
  + iIntros "#p"; iSplit; first by iApply public_minted.
    by iApply (public_gmul_gfactors mulI with "p").
  + iIntros "[#m #fs]"; rewrite [public t]public_eq; iSplit => //.
    by iRight; iRight; iLeft; iSplit.
Qed.

Lemma public_TGInv t : public (TGInv t) ⊣⊢ public t.
Proof.
rewrite (public_gfactors (TGInv t)) (public_gfactors t) minted_TGInv.
by rewrite gfactors_TGInv SMS.elements_inv.
Qed.

Lemma public_TInv t : public (TInv t) ⊣⊢ public t.
Proof.
rewrite (public_factors (TInv t)) (public_factors t) minted_TInv.
by rewrite factors_TInv SMS.elements_inv.
Qed.

Lemma public_TKey kt t :
  public (TKey kt t) ⊣⊢ public t ∨ minted t ∧ ⌜Spec.public_key_type kt⌝.
Proof.
apply: (anti_symm _).
- rewrite public_eq minted_TKey; iDestruct 1 as "[Ht publ]".
  iDestruct "publ" as "[publ | [(? & _) | [(? & _) | [(? & _) | publ]]]]" => //.
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
  iDestruct "publ" as "[publ | [(? & _) | [(? & _) | [(? & _) | publ]]]]" => //.
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
  iDestruct 1 as "[Ht [publ | [(? & _) | [(? & _) | [(? & _) | publ]]]]]" => //; eauto.
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

Lemma public_exp_iff t :
  is_exp t ->
  public t ⊣⊢
  minted t ∧
  ([∗ list] t' ∈ SMS.pos (exps t),
    □ (public t' → public (TExp t (TInv t')))) ∧
  ([∗ list] t' ∈ SMS.neg (exps t), public t' ∧ public (TExp t t')) ∧
  (⌜SMS.neg (exps t) ≠ []⌝ ∨
   (∃ t', ⌜t' ∈ SMS.pos (exps t)⌝ ∧
      (public t' ∨ exp_pred t' t) ∧ public (TExp t (TInv t'))) ∨
   [∗ list] t' ∈ SMS.pos (exps t), exp_pred t' t).
Proof.
move => expt; apply: anti_symm; last first.
- iIntros "#[m dhp]".
  rewrite public_eq.
  iSplit; first done.
  by iRight; iRight; iRight; iLeft; iSplit.
- rewrite public_eq.
  iIntros "#[m Hdisj]".
  iSplit; first done.
  iDestruct "Hdisj" as "[c1 | [c2 | [c2' | [c3 | c4]]]]".
  + iDestruct "c1" as (T) "[%dec _]".
    by case: (is_exp t) (decompose_Nexp dec) expt.
  + iDestruct "c2" as "(%mul_c & _)".
    by move: expt mul_c;
       rewrite is_exp_unfold is_mul_unfold;
       case: (unfold_term t) => [|||[|] ? ?].
  + iDestruct "c2'" as "(%mul_c & _)".
    by move: expt mul_c;
       rewrite is_exp_unfold is_gmul_unfold;
       case: (unfold_term t) => [|||[|] ? ?].
  + by iDestruct "c3" as "(_ & $)".
  + by case: (t) expt => // *; iDestruct "c4" as "[]".
Qed.

Lemma public_TExp_iff t1 t2 :
  negb (is_exp t1) → negb (is_gmul t1) →
  negb (is_mul t2) ->
  public (TExp t1 t2) ⊣⊢
  minted t1 ∧ minted t2 ∧ (public t2 ∨ exp_pred t2 (TExp t1 t2)) ∧
  □ (public t2 → public t1).
Proof.
move=> Nexp Nm1 Nm2.
have expsE : exps (TExp t1 t2) = {[+ t2 +]}.
  by rewrite exps_TExp_expN // factors_Nmul.
have xt : is_exp (TExp t1 t2).
  by apply: (@is_exp_of_exps _ t2); rewrite expsE SMS.elem_of_singleton.
rewrite public_exp_iff // expsE SMS.pos_singleton SMS.neg_singleton.
rewrite !big_sepL_singleton TExpK minted_TExp //.
apply: anti_symm.
- iIntros "#([m1 m2] & p & _ & J)".
  iDestruct "J" as "[%neg | [(%t & %t_t2 & j & _) | j]]"; first done.
  + move: t_t2; rewrite list_elem_of_singleton => ->.
    by iFrame "m1 m2 p j".
  + by iFrame "m1 m2 p j".
- iIntros "#(m1 & m2 & j & p)"; iFrame "m1 m2 p"; iSplit => //.
  iDestruct "j" as "[j | j]"; last by iRight; iRight.
  iRight; iLeft; iExists t2; rewrite TExpK; iSplit.
    by iPureIntro; exact: list_elem_of_here.
  by iSplit; [iLeft|iApply "p"].
Qed.

Lemma public_exps_pos t1 t2 :
  t2 ∈ SMS.pos (exps t1) ->
  public t1 -∗ □ (public t2 → public (TExp t1 (TInv t2))).
Proof.
move=> t2_t1; have exp_t1 := is_exp_of_exps (SMS.elem_of_pos _ _ t2_t1).
iIntros "#p"; iEval (rewrite public_exp_iff //) in "p".
iDestruct "p" as "(_ & p & _)".
by iApply (big_sepL_elem_of _ _ _ t2_t1 with "p").
Qed.

Lemma public_exps_neg t1 t2 :
  t2 ∈ SMS.neg (exps t1) ->
  public t1 -∗ public t2 ∧ public (TExp t1 t2).
Proof.
move=> t2_t1; have exp_t1 := is_exp_of_exps (SMS.elem_of_neg _ _ t2_t1).
iIntros "#p"; iEval (rewrite public_exp_iff //) in "p".
iDestruct "p" as "(_ & _ & p & _)".
by iApply (big_sepL_elem_of _ _ _ t2_t1 with "p").
Qed.

Lemma public_exp_inv_gen ts t1 t2 :
  t1 ∈ ts →
  ts ⊆+ SMS.pos (exps t2) →
  public t2 -∗
  ∃ t, ⌜t ∈ ts⌝ ∧ (
    public t ∨
    ∃ t3, ⌜base t3 = base t2⌝ ∧ ⌜ts ⊆+ SMS.pos (exps t3)⌝ ∧
      exp_pred t t3).
Proof.
move=> t1_ts; elim/term_lt_ind: t2 => t2 IH ts_t2; iIntros "#p".
have t1_t2 : t1 ∈ SMS.pos (exps t2).
  exact: elem_of_submseteq _ _ _ t1_ts ts_t2.
have xt2 := is_exp_of_exps (SMS.elem_of_pos _ _ t1_t2).
have Nm2 := is_exp_Ngmul _ xt2.
iEval (rewrite public_exp_iff //) in "p".
iDestruct "p" as "(_ & _ & #p_neg & [%neg | [#last | #all]])".
- have [t t_t2] : ∃ t, t ∈ SMS.neg (exps t2).
    case: (SMS.neg (exps t2)) neg => [|t ?] // _.
    by exists t; exact: list_elem_of_here.
  iDestruct (big_sepL_elem_of _ _ _ t_t2 with "p_neg") as "[_ p]".
  have [_ lt] := tsize_TExp_neg _ _ t_t2.
  have Nm_t := Nmul_factors _ _ (SMS.elem_of_neg _ _ t_t2).
  rewrite -(base_TExp _ t Nm2); iApply (IH _ lt with "p").
  apply/submseteq_count_mem => u; move/submseteq_count_mem/(_ u): ts_t2.
  have := count_mem_exps_pos u t2; have := count_mem_exps_pos u (TExp t2 t).
  move: t_t2; rewrite /exps -count_lt0 (count_expo_TExp _ _ _ Nm2).
  case: (decide (u = t)) => [->|ne].
  + rewrite count_atom_diag //; lia.
  + rewrite (count_atom_ne Nm_t ne); lia.
- iDestruct "last" as (t) "(%t_t2 & #j & #p)".
  case: (decide (t ∈ ts)) => t_ts.
    iExists t; iSplit => //; iDestruct "j" as "[j|j]"; first by iLeft.
    by iRight; iExists t2; iFrame "j".
  have [_ lt] := tsize_TExp_pos _ _ t_t2.
  have Nm_t := Nmul_factors _ _ (SMS.elem_of_pos _ _ t_t2).
  rewrite -(base_TExp _ (TInv t) Nm2); iApply (IH _ lt with "p").
  apply/submseteq_count_mem => u; move/submseteq_count_mem/(_ u): ts_t2.
  have := count_mem_exps_pos u t2.
  have := count_mem_exps_pos u (TExp t2 (TInv t)).
  rewrite (count_expo_TExp _ _ _ Nm2) count_TInv.
  case: (decide (u ∈ ts)) => [u_ts|/not_elem_of_count_mem ->]; last lia.
  have u_t : u ≠ t by move=> e; apply: t_ts; rewrite -e.
  rewrite (count_atom_ne Nm_t u_t); lia.
- iExists t1; iSplit => //; iRight; iExists t2; do 2!iSplit => //.
  by iApply (big_sepL_elem_of _ _ _ t1_t2 with "all").
Qed.

Lemma public_exp_inv_gen_set ts t1 t2 :
  t1 ∈ ts →
  ts ⊆ SMS.pos (exps t2) →
  public t2 -∗
  ∃ t, ⌜t ∈ ts⌝ ∧ (
    public t ∨
    ∃ t3, ⌜base t3 = base t2⌝ ∧ ⌜ts ⊆ SMS.pos (exps t3)⌝ ∧
      exp_pred t t3).
Proof.
iIntros "%t1_ts %ts_t2 #p".
have t1_ts' : t1 ∈ remove_dups ts by rewrite elem_of_remove_dups.
have ts_t2' : remove_dups ts ⊆+ SMS.pos (exps t2).
  apply: NoDup_submseteq; first exact: NoDup_remove_dups.
  by move=> t /elem_of_remove_dups /ts_t2.
iDestruct (public_exp_inv_gen t1_ts' ts_t2' with "p") as "(%t & %t_ts & #H)".
rewrite elem_of_remove_dups in t_ts; iExists t; iSplit => //.
iDestruct "H" as "[H|(%t3 & %e & %ts_t3 & #H)]"; first by iLeft.
iRight; iExists t3; do !iSplit => //; iPureIntro => t' t'_ts.
by apply: (elem_of_submseteq _ _ _ _ ts_t3); rewrite elem_of_remove_dups.
Qed.

Lemma public_exp_inv t1 t2 :
  t1 ∈ SMS.pos (exps t2) →
  public t2 -∗
  ∃ t, ⌜t ∈ SMS.pos (exps t2)⌝ ∧ (
    public t ∨
    ∃ t3, ⌜base t3 = base t2⌝ ∧
      ⌜SMS.pos (exps t2) ⊆ SMS.pos (exps t3)⌝ ∧
      exp_pred t t3).
Proof. by move=> t1_t2; iApply public_exp_inv_gen_set. Qed.

Lemma public_exp_inv_same t1 t2 :
  t1 ∈ SMS.pos (exps t2) →
  public t2 -∗
  public t1 ∨
  ∃ t2', ⌜base t2' = base t2⌝ ∗ ⌜t1 ∈ SMS.pos (exps t2')⌝ ∗
    exp_pred t1 t2'.
Proof.
iIntros "%t1_t2 #p".
have {}t1_t2: [t1] ⊆ SMS.pos (exps t2) by set_solver.
have t1_t1: t1 ∈ [t1] by set_solver.
iPoseProof (public_exp_inv_gen_set t1_t1 t1_t2 with "p") as "(%t & %t_t1 & H)".
move: t_t1; rewrite list_elem_of_singleton => {t} ->.
iDestruct "H" as "[H|(%t3 & #? & %t1_t3 & #base)]"; first by eauto.
iRight; iExists t3; iFrame "#"; iPureIntro; set_solver.
Qed.

(* [t2] is the last exponent of [TExp t1 t2], added by the attacker or by the
   owner of [t2]. *)
#[local] Lemma public_TExp_last t1 t2 :
  negb (is_gmul t1) → negb (is_mul t2) →
  minted t2 -∗
  □ (∀ t, public t -∗ public t2 ∨ exp_pred t2 (TExp t t2)) -∗
  public t1 -∗
  public (TExp t1 t2).
Proof.
move=> Nm1 Nm2; move: t1 Nm1; elim/term_lt_ind => t1 IH Nm1.
iIntros "#m2 #j #p1".
case: (Z.lt_ge_cases (count t2 (expo t1)) 0) => [/count_lt0 t2_t1|t2_t1].
  by iDestruct (public_exps_neg t2_t1 with "p1") as "[_ $]".
have cntE x : count x (expo (TExp t1 t2)) = (count x (expo t1) + count x t2)%Z.
  exact: count_expo_TExp.
have t2_t : t2 ∈ SMS.pos (exps (TExp t1 t2)).
  by rewrite /exps -count_gt0 cntE count_atom_diag //; lia.
have exp_t := is_exp_of_exps (SMS.elem_of_pos _ _ t2_t).
rewrite [public (TExp _ _)]public_exp_iff //; iSplit.
  by iApply all_minted_TExp; iSplit => //; iApply public_minted.
iSplit; [|iSplit].
- iApply big_sepL_forall; iIntros (? t t_t%list_elem_of_lookup_2) "!> #pt".
  have [->|t_t2] := decide (t = t2); first by rewrite TExpK.
  have t_t1 : t ∈ SMS.pos (exps t1).
    move: t_t; rewrite /exps -!count_gt0 cntE (count_atom_ne Nm2 t_t2); lia.
  iPoseProof (public_exps_pos t_t1 with "p1 pt") as "p".
  rewrite TExpC; iApply (IH with "m2 j p").
  + by case: (tsize_TExp_pos _ _ t_t1).
  + exact: Ngmul_TExp.
- iApply big_sepL_forall; iIntros (? t t_t%list_elem_of_lookup_2).
  have t_t1 : t ∈ SMS.neg (exps t1).
    move: t_t t2_t1; rewrite /exps -!count_lt0 cntE.
    case: (decide (t = t2)) => [->|t_t2].
    + rewrite count_atom_diag //; lia.
    + rewrite (count_atom_ne Nm2 t_t2); lia.
  iDestruct (public_exps_neg t_t1 with "p1") as "[#pt #p]"; iSplit => //.
  rewrite TExpC; iApply (IH with "m2 j p").
  + by case: (tsize_TExp_neg _ _ t_t1).
  + exact: Ngmul_TExp.
- iRight; iLeft; iExists t2; rewrite TExpK; iSplit => //.
  by iSplit; [iApply "j"|].
Qed.

Lemma public_TExp_Nmul t1 t2 :
  negb (is_gmul t1) -> negb (is_mul t2) ->
  public t1 -∗
  public t2 -∗
  public (TExp t1 t2).
Proof.
move=> Nm1 Nm2; iIntros "#p1 #p2".
iApply (public_TExp_last Nm1 Nm2 with "[] [] p1").
- by iApply public_minted.
- by iIntros "!> %t _"; iLeft.
Qed.

(* The owner of [t2] raises any public term to [t2], as in an oblivious
   PRF. *)
Lemma public_TExp_consent t1 t2 :
  negb (is_gmul t1) → negb (is_mul t2) →
  minted t2 -∗
  □ (∀ t, public t -∗ exp_pred t2 (TExp t t2)) -∗
  public t1 -∗
  public (TExp t1 t2).
Proof.
move=> Nm1 Nm2; iIntros "#m2 #c #p1".
iApply (public_TExp_last Nm1 Nm2 with "m2 [] p1").
by iIntros "!> %t #p"; iRight; iApply "c".
Qed.

Lemma public_TExp_TInv t1 t2 :
  negb (is_gmul t1) -> negb (is_mul t2) ->
  public t1 -∗
  public t2 -∗
  public (TExp t1 (TInv t2)).
Proof.
move=> Nm1 Nm2; move: t1 Nm1; elim/term_lt_ind => t1 IH Nm1.
iIntros "#p1 #p2".
case: (decide (t2 ∈ SMS.pos (exps t1))) => t2_t1.
  by iApply (public_exps_pos t2_t1 with "p1 p2").
have cntE x :
    count x (expo (TExp t1 (TInv t2))) = (count x (expo t1) - count x t2)%Z.
  by rewrite (count_expo_TExp _ _ _ Nm1) count_TInv.
have t2_t : t2 ∈ SMS.neg (exps (TExp t1 (TInv t2))).
  move: t2_t1; rewrite /exps -count_gt0 -count_lt0 cntE count_atom_diag //.
  lia.
have exp_t := is_exp_of_exps (SMS.elem_of_neg _ _ t2_t).
rewrite [public (TExp _ _)]public_exp_iff //; iSplit.
  iApply all_minted_TExp; iSplit; first by iApply public_minted.
  by rewrite minted_TInv; iApply public_minted.
iSplit; [|iSplit].
- iApply big_sepL_forall; iIntros (? t t_t%list_elem_of_lookup_2) "!> #pt".
  have [t_t2 t_t1] : t ≠ t2 ∧ t ∈ SMS.pos (exps t1).
    move: t_t t2_t1; rewrite /exps -!count_gt0 cntE.
    case: (decide (t = t2)) => [->|t_t2].
    + rewrite count_atom_diag //; lia.
    + by rewrite (count_atom_ne Nm2 t_t2); split => //; lia.
  iPoseProof (public_exps_pos t_t1 with "p1 pt") as "p".
  rewrite TExpC; iApply (IH with "p p2").
  + by case: (tsize_TExp_pos _ _ t_t1).
  + exact: Ngmul_TExp.
- iApply big_sepL_forall; iIntros (? t t_t%list_elem_of_lookup_2).
  case: (decide (t = t2)) => [->|t_t2].
    by iSplit => //; rewrite TExpKV.
  have t_t1 : t ∈ SMS.neg (exps t1).
    move: t_t; rewrite /exps -!count_lt0 cntE (count_atom_ne Nm2 t_t2); lia.
  iDestruct (public_exps_neg t_t1 with "p1") as "[#pt #p]"; iSplit => //.
  rewrite TExpC; iApply (IH with "p p2").
  + by case: (tsize_TExp_neg _ _ t_t1).
  + exact: Ngmul_TExp.
- iLeft; iPureIntro => E; move: t2_t; rewrite E; exact: not_elem_of_nil.
Qed.

Lemma public_TExp_make_intro t X Y :
  negb (is_gmul t) ->
  Forall (λ u, negb (is_mul u)) (X ++ Y) ->
  public t -∗ ([∗ list] t' ∈ X ++ Y, public t') -∗
  public (TExp t (TMul (SMS.make X Y))).
Proof.
move=> Nm; elim: X => [|x X IHX] /=.
- elim: Y => [|y Y IHY] HY; iIntros "#p #pY"; first by rewrite TExp_unit.
  move: HY => /Forall_cons [Ny HY].
  iEval (rewrite big_sepL_cons) in "pY"; iDestruct "pY" as "[#py #pY']".
  rewrite TExp_TMul_cons_r.
  iApply (public_TExp_TInv (Ngmul_TExp _ _ Nm) Ny with "[] py").
  by iApply (IHY HY with "p pY'").
- move=> /Forall_cons [Nx HXY]; iIntros "#p #pXY".
  iDestruct "pXY" as "[#px #pXY']"; rewrite TExp_TMul_cons_l.
  iApply (public_TExp_Nmul (Ngmul_TExp _ _ Nm) Nx with "[] px").
  by iApply (IHX HXY with "p pXY'").
Qed.

(* Unconditional in both arguments.  A group product base distributes, and every
   group factor of the result comes from a group factor of [t1]; otherwise the
   exponent is applied one signed atom at a time ([public_TExp_make_intro]). *)
Lemma public_TExp t1 t2 :
  public t1 -∗ public t2 -∗ public (TExp t1 t2).
Proof.
move: t1; elim/term_lt_ind => t1 IH; iIntros "#p1 #p2".
case Em: (is_gmul t1).
  have Xm : is_gmul t1 by rewrite Em.
  rewrite [public (TExp t1 t2)]public_gfactors; iSplit.
    by iApply all_minted_TExp; iSplit; iApply public_minted.
  rewrite big_sepL_forall; iIntros (k x Hx).
  have x_in : x ∈ gfactors (TExp t1 t2).
    by exact: list_elem_of_lookup_2 _ _ _ Hx.
  move: x_in; rewrite gfactors_TExp.
  move=> /SMS.elem_of_map [u [-> u_t1]].
  iApply (IH u (tsize_gfactors_lt _ _ Xm u_t1) with "[] p2").
  rewrite (public_gfactors t1); iDestruct "p1" as "[_ #fs]".
  by iApply (big_sepL_elem_of with "fs").
have Nm : negb (is_gmul t1) by rewrite Em.
have Hfs : Forall (λ u, negb (is_mul u))
              (SMS.pos (factors t2) ++ SMS.neg (factors t2)).
  apply/Forall_forall => x /elem_of_app [] x_in.
  - exact: Nmul_factors _ _ (SMS.elem_of_pos _ _ x_in).
  - exact: Nmul_factors _ _ (SMS.elem_of_neg _ _ x_in).
iDestruct (public_factors t2 with "p2") as "[_ #fs]".
iEval (rewrite SMS.elements_pos_neg) in "fs".
have -> : TExp t1 t2 =
  TExp t1 (TMul (SMS.make (SMS.pos (factors t2)) (SMS.neg (factors t2)))).
  by rewrite SMS.make_pos_neg factorsK.
by iApply (public_TExp_make_intro Nm Hfs with "p1 fs").
Qed.

(* Distributivity, as a publicity principle: [TExp t1 t2] is the group product
   of the [TExp u t2] for [u] a group factor of [t1], so it is public exactly
   when each of those is.  For a group-atom-headed [t1] this degenerates to the
   single factor [t1] itself ([gfactors_Ngmul]), so it subsumes the atomic
   reasoning. *)
Lemma public_TExp_gfactors t1 t2 :
  ([∗ list] u ∈ elements (gfactors t1), public (TExp u t2)) -∗
  public (TExp t1 t2).
Proof.
iIntros "#H".
have factE : forall x, x ∈ gfactors (TExp t1 t2) ->
    exists u, x = TExp u t2 /\ u ∈ gfactors t1.
  move=> x; rewrite gfactors_TExp.
  by move=> /SMS.elem_of_map [u [-> u_t1]]; eauto.
rewrite [public (TExp t1 t2)]public_gfactors [minted (TExp t1 t2)]minted_gfactors.
iSplit; iApply big_sepL_forall; iIntros (k x Hx);
  case: (factE x (list_elem_of_lookup_2 _ _ _ Hx)) => u [-> u_t1].
- by iApply public_minted; iApply (big_sepL_elem_of with "H").
- by iApply (big_sepL_elem_of with "H").
Qed.

Lemma public_TMul_intro s :
  (∀ u, u ∈ s → negb (is_mul u)) ->
  ([∗ list] t' ∈ elements s, public t') ⊢ public (TMul s).
Proof.
move => Hs.
rewrite public_factors (factors_TMul_atoms _ Hs) (minted_TMul Hs).
iIntros "#H"; iSplit; last done.
iApply (big_sepL_mono with "H"); iIntros (k t' _) "?"; by iApply public_minted.
Qed.

Lemma big_sepL_factors_TMul2 (Φ : term → iProp) `{!∀ t, Persistent (Φ t)}
  t1 t2 :
  ([∗ list] t' ∈ elements (factors t1), Φ t') -∗
  ([∗ list] t' ∈ elements (factors t2), Φ t') -∗
  [∗ list] t' ∈ elements (factors (TMul {[+ t1; t2 +]})), Φ t'.
Proof.
iIntros "#H1 #H2"; iApply big_sepL_intro; iIntros "!>" (k u Hk).
move: (elem_of_factors_TMul2 _ _ _ (list_elem_of_lookup_2 _ _ _ Hk)).
case=> [Hin|Hin].
- by iApply (big_sepL_elem_of with "H1").
- by iApply (big_sepL_elem_of with "H2").
Qed.

Lemma public_TMul2 t1 t2 :
  public t1 -∗ public t2 -∗ public (TMul {[+ t1; t2 +]}).
Proof.
iIntros "#p1 #p2".
iDestruct (public_factors t1 with "p1") as "#[m1 f1]".
iDestruct (public_factors t2 with "p2") as "#[m2 f2]".
iEval (rewrite minted_factors) in "m1".
iEval (rewrite minted_factors) in "m2".
iApply public_factors; iSplit.
- rewrite minted_factors. by iApply (big_sepL_factors_TMul2 with "m1 m2").
- by iApply (big_sepL_factors_TMul2 with "f1 f2").
Qed.

Lemma public_TMul0 : ⊢ public (TMul ∅).
Proof.
have H : ∀ u, u ∈ (∅ : tsms) → negb (is_mul u).
  by move=> u; rewrite -SMS.elem_of_elements SMS.elements_empty => /elem_of_nil.
by iApply (public_TMul_intro H); rewrite SMS.elements_empty.
Qed.

Lemma public_TGMul_intro s :
  (∀ u, u ∈ s → negb (is_gmul u)) ->
  ([∗ list] t' ∈ elements s, public t') ⊢ public (TGMul s).
Proof.
move => Hs.
rewrite public_gfactors (gfactors_TGMul_atoms _ Hs) (minted_TGMul Hs).
iIntros "#H"; iSplit; last done.
iApply (big_sepL_mono with "H"); iIntros (k t' _) "?"; by iApply public_minted.
Qed.

Lemma big_sepL_gfactors_TGMul2
  (Φ : term → iProp) `{!∀ t, Persistent (Φ t)} t1 t2 :
  ([∗ list] t' ∈ elements (gfactors t1), Φ t') -∗
  ([∗ list] t' ∈ elements (gfactors t2), Φ t') -∗
  [∗ list] t' ∈ elements (gfactors (TGMul {[+ t1; t2 +]})), Φ t'.
Proof.
iIntros "#H1 #H2"; iApply big_sepL_intro; iIntros "!>" (k u Hk).
move: (elem_of_gfactors_TGMul2 _ _ _ (list_elem_of_lookup_2 _ _ _ Hk)).
case=> [Hin|Hin].
- by iApply (big_sepL_elem_of with "H1").
- by iApply (big_sepL_elem_of with "H2").
Qed.

Lemma public_TGMul2 t1 t2 :
  public t1 -∗ public t2 -∗ public (TGMul {[+ t1; t2 +]}).
Proof.
iIntros "#p1 #p2".
iDestruct (public_gfactors t1 with "p1") as "#[m1 f1]".
iDestruct (public_gfactors t2 with "p2") as "#[m2 f2]".
iEval (rewrite minted_gfactors) in "m1".
iEval (rewrite minted_gfactors) in "m2".
iApply public_gfactors; iSplit.
- rewrite minted_gfactors. by iApply (big_sepL_gfactors_TGMul2 with "m1 m2").
- by iApply (big_sepL_gfactors_TGMul2 with "f1 f2").
Qed.

Lemma public_TGMul0 : ⊢ public (TGMul ∅).
Proof.
have H : ∀ u, u ∈ (∅ : tsms) → negb (is_gmul u).
  by move=> u; rewrite -SMS.elem_of_elements SMS.elements_empty => /elem_of_nil.
by iApply (public_TGMul_intro H); rewrite SMS.elements_empty.
Qed.

Lemma False_public t :
  minted t -∗
  ▷ False -∗
  public t.
Proof.
elim: t.
- by move=> n; iIntros "_ _"; rewrite public_TInt.
- move=> t1 IH1 t2 IH2; rewrite minted_TPair public_TPair.
  iIntros "#[m1 m2] #contra"; iSplit.
  + iApply (IH1 with "m1 contra").
  + iApply (IH2 with "m2 contra").
- move=> a; rewrite minted_TNonce public_TNonce.
  iIntros "#m #contra"; iSplit => //.
  iDestruct "contra" as ">[]".
- move=> kt t IH; rewrite minted_TKey public_TKey.
  iIntros "#m #contra"; iLeft.
  iApply (IH with "m contra").
- move=> k IHk t IHt; rewrite minted_TSeal public_TSeal.
  iIntros "#[m1 m2] #contra"; iLeft; iSplit.
  + iApply (IHk with "m1 contra").
  + iApply (IHt with "m2 contra").
- move=> t IH; rewrite minted_THash public_THash.
  iIntros "#m #contra"; iLeft.
  iApply (IH with "m contra").
- move=> t1 IH1 t2 IH2 Nx1 Nm1 _; rewrite minted_TExp //.
  iIntros "#[m1 m2] #contra".
  iApply (public_TExp with "[] []").
  + iApply (IH1 with "m1 contra").
  + iApply (IH2 with "m2 contra").
- move=> s IH Hs _.
  rewrite public_factors minted_factors (factors_TMul_atoms _ Hs).
  iIntros "#ms #contra"; iSplit => //.
  iApply big_sepL_forall; iIntros (k x Hx).
  have x_s : x ∈ s.
    by exact: list_elem_of_lookup_2 _ _ _ Hx.
  iApply (IH x x_s with "[] contra").
  by iApply (big_sepL_elem_of with "ms").
- move=> s IH Hs _.
  rewrite public_gfactors minted_gfactors (gfactors_TGMul_atoms _ Hs).
  iIntros "#ms #contra"; iSplit => //.
  iApply big_sepL_forall; iIntros (k x Hx).
  have x_s : x ∈ s.
    by exact: list_elem_of_lookup_2 _ _ _ Hx.
  iApply (IH x x_s with "[] contra").
  by iApply (big_sepL_elem_of with "ms").
Qed.

Lemma except_0_public t :
  minted t -∗
  ◇ public t -∗
  public t.
Proof.
rewrite /bi_except_0.
by iIntros "#m #[contra|?]"; eauto; iApply False_public.
Qed.

Lemma public_to_list t ts :
  Spec.to_list t = Some ts →
  public t -∗ [∗ list] t' ∈ ts, public t'.
Proof.
elim/term_ind': t ts => //=.
  by case=> // [] ts [<-] /=; iIntros "?".
move=> t _ tl IH ts.
case e: (Spec.to_list tl) => [ts'|] // [<-] /=.
rewrite public_TPair /=; iIntros "[??]"; iFrame.
by iApply IH.
Qed.

Lemma public_of_list ts :
  public (Spec.of_list ts) ⊣⊢
  [∗ list] t ∈ ts, public t.
Proof.
rewrite [Spec.of_list]unlock.
elim: ts => [|t ts IH]; first by rewrite public_TInt.
by rewrite public_TPair /= IH bi.persistent_and_sep.
Qed.

Lemma public_Tag N : public (Tag N) ⊣⊢ True.
Proof. by rewrite [Tag]unlock public_TInt. Qed.

Lemma public_tag N t : public (Spec.tag (Tag N) t) ⊣⊢ public t.
Proof.
by rewrite [Spec.tag]unlock public_TPair public_Tag bi.emp_and.
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
    □ (public (TNonce a) ↔ ▷ □ P a) ∗
    □ (∀ t, exp_pred (TNonce a) t ↔ ▷ □ Q t).
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
    iSpecialize ("e" $! a). iModIntro. by iRewrite "e".
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

#[global] Instance persistent_shot γ x : Persistent (shot γ x).
Proof. apply _. Qed.

#[global] Instance timeless_shot γ x : Timeless (shot γ x).
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
rewrite [term_of_aenc_key]unlock; case: sk => seed /=.
iIntros "#p_t #?". iSplit => //.
{ iPoseProof (public_minted with "p_t") as "#m_t".
  rewrite minted_TSeal minted_tag. by iDestruct "m_t" as "[_ ?]". }
iPoseProof (public_TSealE with "p_t [//] [//]") as "[[_ comp]|inv]"; eauto.
rewrite /=. iDestruct "inv" as "[#inv #?]". iRight. iSplit => //.
iIntros "!> !>". iDestruct "inv" as "(%k' & %e & inv)".
rewrite [term_of_aenc_key]unlock in e. by case: k' e => seed' // [<-].
Qed.

Lemma public_signE (sk : sign_key) N Φ t :
  public (TSeal sk (Spec.tag (Tag N) t)) -∗
  sign_pred N Φ -∗
  public t ∧ (public sk ∨ □ ▷ Φ sk t).
Proof.
rewrite [term_of_sign_key]unlock; case: sk => seed /=.
iIntros "#p_t #?". iPoseProof (public_minted with "p_t") as "m_t".
rewrite minted_TSeal minted_TKey. iDestruct "m_t" as "[? _]".
iPoseProof (public_TSealE with "p_t [//] [//]") as "[[??]|inv]"; eauto.
iDestruct "inv" as "{p_t} (#inv & #p_t)". iSplit => //.
- iApply "p_t". iApply public_TKey. iRight. by iSplit => //.
- iRight. iIntros "!> !>". iDestruct "inv" as "(%k' & %e & inv)".
  rewrite [term_of_sign_key]unlock in e; by case: k' e => seed' // [<-].
Qed.

Lemma public_sencE (k : senc_key) N Φ t :
  public (TSeal k (Spec.tag (Tag N) t)) -∗
  senc_pred N Φ -∗
  minted t ∧ (public k ∨ □ ▷ Φ k t) ∧ □ (public k → public t).
Proof.
rewrite [term_of_senc_key]unlock; case: k => seed /=.
iIntros "#p_t #?". iSplit => //.
{ iPoseProof (public_minted with "p_t") as "#m_t".
  rewrite minted_TSeal minted_tag. by iDestruct "m_t" as "[_ ?]". }
iPoseProof (public_TSealE with "p_t [//] [//]") as "[[??]|[#inv #p_t']]";
eauto. iSplit => //. iRight.
iIntros "!> !>". iDestruct "inv" as "(%k' & %e & inv)".
rewrite [term_of_senc_key]unlock in e; by case: k' e => seed' // [<-].
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
