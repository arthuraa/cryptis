From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta nown saved_prop size_rec_pred sms.
From cryptis.lib Require Import list_sort fmap poly poly_gcd frac poly_restrict.
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
  negb (is_mod t) →
  exp_pred (TInv t) t' ⊣⊢ ▷ False.
Proof.
move=> /is_mod_TInv_atom; rewrite /exp_pred.
by case: (TInv t).
Qed.

Lemma exp_pred_TInv_den_unit u t' : exp_pred (TInv (den_unit u)) t' ⊣⊢ ▷ False.
Proof.
rewrite /exp_pred; move: (@TInv_den_unit_Nnonce u).
by case: (TInv (den_unit u)) => // a /(_ a).
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

Lemma decompose_Nmod T t : decompose T t → negb (is_mod t).
Proof. by case => *; subst. Qed.

Lemma decompose_Ngmul T t : decompose T t → negb (is_gmul t).
Proof. by case => *; subst. Qed.

Lemma decompose_Nexp T t : decompose T t → negb (is_exp t).
Proof. by case => *; subst. Qed.

(* The attacker can strip an exponent it knows.  Otherwise, the last exponent
   of an exponential was added by the attacker or by its owner, unless all the
   owners of its exponents agree to publish it.  A negative exponent has no
   owner ([exp_pred_TInv]). *)
Definition public_pre_aux P t : iProp :=
  minted t ∧ (
   (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, P t')
   ∨ (⌜is_mod t⌝ ∧ [∗ list] t' ∈ atoms t, P t')
   ∨ (⌜is_gmul t⌝ ∧ [∗ list] t' ∈ elements (gfactors t), P t')
   ∨ (⌜is_exp t⌝ ∧
      ([∗ list] f ∈ satoms (exps t), □ (P f → P (TExp t (TInv f)))) ∧
      ((∃ f, ⌜f ∈ satoms (exps t)⌝ ∧
          (P f ∨ exp_pred f t) ∧ P (TExp t (TInv f))) ∨
       [∗ list] f ∈ satoms (exps t), exp_pred f t))
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
- apply: and_proper_L => mod_t.
  apply: big_sepL_proper => _ t' /(list_elem_of_lookup_2 _ _ _) t'_in.
  by apply: HP; apply: tsize_atoms_lt.
- apply: and_proper_L => mul_t.
  apply: big_sepL_proper => _ t' /(list_elem_of_lookup_2 _ _ _).
  move=> /SMS.elem_of_elements t'_in.
  apply: HP.
  exact: (tsize_gfactors_lt t' t mul_t t'_in).
- apply: and_proper_L => exp_t.
  have Hf f : f ∈ satoms (exps t) →
      P1 f ≡ P2 f ∧ P1 (TExp t (TInv f)) ≡ P2 (TExp t (TInv f)).
    by case/tsize_satoms => ??; split; apply: HP.
  f_equiv; [|f_equiv].
  + apply: big_sepL_proper => _ f /(list_elem_of_lookup_2 _ _ _) /Hf.
    by case=> -> ->.
  + f_equiv => f; apply: and_proper_L => /Hf [-> ->] //.
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
  iAssert ([∗ list] t' ∈ atoms t, <pers> P t')%I as "{H} #H".
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
  iAssert ([∗ list] f ∈ satoms (exps t), □ (P f → P (TExp t (TInv f))))%I
    with "[H]" as "#Hstrip".
  { by iDestruct "H" as "(#H & _)". }
  iAssert (<pers> ((∃ f, ⌜f ∈ satoms (exps t)⌝ ∧
      (P f ∨ exp_pred f t) ∧ P (TExp t (TInv f))) ∨
    [∗ list] f ∈ satoms (exps t), exp_pred f t))%I
    with "[H]" as "#Hlast".
  { iDestruct "H" as "(_ & [(%f & %f_t & H) | #H])".
    - iAssert (<pers> P (TExp t (TInv f)))%I with "[H]" as "#Hp".
      { by iDestruct "H" as "[_ H]"; iApply "wand". }
      iAssert (<pers> (P f ∨ exp_pred f t))%I with "[H]" as "#Hf".
      { iDestruct "H" as "[[H | #H] _]"; last by iModIntro; iRight.
        by iDestruct ("wand" with "H") as "#?"; iModIntro; iLeft. }
      iModIntro; iLeft; iExists f.
      by iSplit; [iPureIntro|iSplit].
    - by iModIntro; iRight. }
  by iModIntro; iSplit => //; iSplit.
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
     ∨ (⌜is_mod t⌝ ∧ [∗ list] t' ∈ atoms t, public t')
     ∨ (⌜is_gmul t⌝ ∧ [∗ list] t' ∈ elements (gfactors t), public t')
     ∨ (⌜is_exp t⌝ ∧
        ([∗ list] f ∈ satoms (exps t),
          □ (public f → public (TExp t (TInv f)))) ∧
        ((∃ f, ⌜f ∈ satoms (exps t)⌝ ∧
            (public f ∨ exp_pred f t) ∧ public (TExp t (TInv f))) ∨
         [∗ list] f ∈ satoms (exps t), exp_pred f t))
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

Lemma public_mod_atoms t :
  is_mod t -> public t ⊢ [∗ list] t' ∈ atoms t, public t'.
Proof.
move=> mod_t; rewrite public_eq.
iIntros "[_ [publ | [ [_ Hfs] | [ [%gmul_t _] | [ (%exp_t & _) | Hstr ]]]]]".
- iDestruct "publ" as (T) "[%dec _]".
  by case: (is_mod t) (decompose_Nmod dec) mod_t.
- by iApply "Hfs".
- by case: (is_gmul t) (is_mod_Ngmul mod_t) gmul_t.
- by case: (is_exp t) (is_mod_Nexp mod_t) exp_t.
- by case: (t) mod_t => // *; iDestruct "Hstr" as "[]".
Qed.

Lemma public_atoms t :
  public t ⊣⊢ minted t ∧ [∗ list] t' ∈ atoms t, public t'.
Proof.
case Emod: (is_mod t); last first.
- have Nm : negb (is_mod t) by rewrite Emod.
  apply: (anti_symm _).
  + iIntros "#p"; iSplit; first by iApply public_minted.
    iApply big_sepL_forall; iIntros (k x Hx).
    by move: (list_elem_of_lookup_2 _ _ _ Hx); rewrite atoms_atom // => ->.
  + iIntros "[_ #H]"; iApply (big_sepL_elem_of with "H").
    exact/atoms_atom.
- have modt : is_mod t by rewrite Emod.
  apply: (anti_symm _).
  + iIntros "#p"; iSplit; first by iApply public_minted.
    by iApply (public_mod_atoms modt with "p").
  + iIntros "[#m #fs]"; rewrite [public t]public_eq; iSplit => //.
    by iRight; iLeft; iSplit.
Qed.

(** An exponent is public exactly when its atoms are. *)
Lemma public_atoms_iff t :
  public t ⊣⊢ [∗ list] t' ∈ atoms t, public t'.
Proof.
rewrite public_atoms; apply: (anti_symm _); first by iIntros "[_ $]".
iIntros "#H"; iSplit => //; rewrite minted_atoms.
iApply (big_sepL_impl with "H"); iIntros "!> %k %x _ #p".
by iApply public_minted.
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
- by case: (is_gmul t) (is_mod_Ngmul mul_t') mul_t.
- by iApply "Hfs".
- by case: (is_gmul t) (is_exp_Ngmul exp_t) mul_t.
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
rewrite !public_atoms_iff; apply: (anti_symm _); iIntros "#H";
  iApply big_sepL_forall; iIntros (k x Hx); iApply (big_sepL_elem_of with "H");
  have := list_elem_of_lookup_2 _ _ _ Hx; by rewrite atoms_TInv.
Qed.

Lemma public_TMul0 : ⊢ public (TMul ∅).
Proof.
rewrite public_atoms_iff; iApply big_sepL_forall; iIntros (k x Hx).
move: (list_elem_of_lookup_2 _ _ _ Hx) => /elem_of_atoms [y [_]].
by rewrite /PreTerm.atoms -unfold_frac_of frac_of_TMul_empty Frac.map_one
  => /(Frac.vars_one y).
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
  ([∗ list] f ∈ satoms (exps t), □ (public f → public (TExp t (TInv f)))) ∧
  ((∃ f, ⌜f ∈ satoms (exps t)⌝ ∧
      (public f ∨ exp_pred f t) ∧ public (TExp t (TInv f))) ∨
   [∗ list] f ∈ satoms (exps t), exp_pred f t).
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
    by case: (is_mod t) (is_exp_Nmod expt) mul_c.
  + iDestruct "c2'" as "(%mul_c & _)".
    by case: (is_gmul t) (is_exp_Ngmul expt) mul_c.
  + by iDestruct "c3" as "(_ & $)".
  + by case: (t) expt => // *; iDestruct "c4" as "[]".
Qed.

Lemma public_TExp_iff t1 t2 :
  negb (is_exp t1) → negb (is_gmul t1) →
  negb (is_mod t2) ->
  public (TExp t1 t2) ⊣⊢
  minted t1 ∧ minted t2 ∧ (public t2 ∨ exp_pred t2 (TExp t1 t2)) ∧
  □ (public t2 → public t1).
Proof.
move=> Nexp Nm1 Nm2.
have m2 : mono_num t2 by apply: laurent_mono_num; apply: laurent_atom.
have nz2 : frac_of t2 ≠ Frac.zero := atom_frac_neq0 Nm2.
have expsE : exps (TExp t1 t2) = {[+ t2 +]}.
  by rewrite (exps_TExp_expN Nexp Nm1 m2) factors_Nmod.
have xt : is_exp (TExp t1 t2).
  by apply: (@is_exp_of_exps _ t2); rewrite expsE SMS.elem_of_singleton.
rewrite public_exp_iff // /satoms expsE SMS.pos_singleton SMS.neg_singleton.
rewrite MSet.elements_singleton MSet.elements_empty.
have -> : [t2] ++ (TInv <$> []) = [t2] by [].
rewrite !big_sepL_singleton (TExpK _ nz2) (minted_TExp Nexp Nm1 nz2).
apply: anti_symm.
- iIntros "#([m1 m2] & p & J)".
  iDestruct "J" as "[(%t & %t_t2 & j & _) | j]".
  + move: t_t2; rewrite list_elem_of_singleton => ->.
    by iFrame "m1 m2 p j".
  + by iFrame "m1 m2 p j".
- iIntros "#(m1 & m2 & j & p)"; iFrame "m1 m2 p".
  iDestruct "j" as "[j | j]"; last by iRight.
  iLeft; iExists t2; rewrite (TExpK _ nz2); iSplit.
    by iPureIntro; exact: list_elem_of_here.
  by iSplit; [iLeft|iApply "p"].
Qed.

Lemma public_satoms t1 f :
  f ∈ satoms (exps t1) ->
  public t1 -∗ □ (public f → public (TExp t1 (TInv f))).
Proof.
move=> f_t1; have exp_t1 := is_exp_of_satoms f_t1.
iIntros "#p"; iEval (rewrite public_exp_iff //) in "p".
iDestruct "p" as "(_ & p & _)".
by iApply (big_sepL_elem_of _ _ _ f_t1 with "p").
Qed.

Lemma minted_satoms t f :
  f ∈ satoms (exps t) → minted t ⊢ minted f.
Proof.
iIntros (f_t) "#m"; iDestruct (minted_base_exps with "m") as "[_ ms]".
move: f_t; rewrite /satoms elem_of_app list_elem_of_fmap.
case=> [/MSet.elem_of_elements f_t|[x [-> /MSet.elem_of_elements x_t]]].
- iApply (big_sepL_elem_of with "ms").
  by apply/SMS.elem_of_elements; exact: SMS.elem_of_pos.
- rewrite minted_TInv; iApply (big_sepL_elem_of with "ms").
  by apply/SMS.elem_of_elements; exact: SMS.elem_of_neg.
Qed.

Lemma False_public t :
  minted t -∗
  ▷ False -∗
  public t.
Proof.
elim/term_lt_ind: t => t IH; iIntros "#m #contra".
case Ex: (is_exp t).
  have xt : is_exp t by rewrite Ex.
  have [f f_t] := satoms_nonempty xt.
  rewrite [public t]public_exp_iff //; iSplit => //.
  iAssert (□ ∀ g, ⌜g ∈ satoms (exps t)⌝ → public (TExp t (TInv g)))%I
    as "#strip".
  { iIntros "!> %g %g_t".
    have [_ lt] := tsize_satoms _ _ g_t.
    iApply (IH _ lt with "[] contra").
    iApply all_minted_TExp; iSplit => //; rewrite minted_TInv.
    by iApply (minted_satoms g_t with "m"). }
  iSplit.
    iApply big_sepL_forall; iIntros (k g g_t%list_elem_of_lookup_2) "!> _".
    by iApply "strip".
  iLeft; iExists f; iSplit => //; iSplit; last by iApply "strip".
  iLeft; have [lt _] := tsize_satoms _ _ f_t.
  by iApply (IH _ lt with "[] contra"); iApply (minted_satoms f_t with "m").
case Em: (is_mod t).
  have mt : is_mod t by rewrite Em.
  rewrite public_atoms; iSplit => //.
  iApply big_sepL_forall; iIntros (k x x_t%list_elem_of_lookup_2).
  iApply (IH _ (tsize_atoms_lt _ _ mt x_t) with "[] contra").
  iEval (rewrite minted_atoms) in "m".
  by iApply (big_sepL_elem_of with "m").
case Eg: (is_gmul t).
  have gt : is_gmul t by rewrite Eg.
  rewrite public_gfactors; iSplit => //.
  iApply big_sepL_forall; iIntros (k x Hx).
  have x_t : x ∈ gfactors t.
    by apply/SMS.elem_of_elements; exact: list_elem_of_lookup_2 _ _ _ Hx.
  iApply (IH _ (tsize_gfactors_lt _ _ gt x_t) with "[] contra").
  iEval (rewrite minted_gfactors) in "m".
  by iApply (big_sepL_elem_of with "m"); apply/SMS.elem_of_elements.
case: t IH Ex Em Eg => [n|t1 t2|a|kt t|k t|t|pt wf nf] IH Ex Em Eg.
- by rewrite public_TInt.
- rewrite public_TPair; iEval (rewrite minted_TPair) in "m".
  iDestruct "m" as "[m1 m2]"; iSplit.
  + iApply (IH with "m1 contra"); rewrite [tsize (TPair _ _)]tsize_eq; lia.
  + iApply (IH with "m2 contra"); rewrite [tsize (TPair _ _)]tsize_eq; lia.
- rewrite public_TNonce; iEval (rewrite minted_TNonce) in "m".
  iSplit => //; iDestruct "contra" as ">[]".
- rewrite public_TKey; iEval (rewrite minted_TKey) in "m"; iLeft.
  iApply (IH with "m contra"); rewrite [tsize (TKey _ _)]tsize_eq; lia.
- rewrite public_TSeal; iEval (rewrite minted_TSeal) in "m".
  iDestruct "m" as "[m1 m2]"; iLeft; iSplit.
  + iApply (IH with "m1 contra"); rewrite [tsize (TSeal _ _)]tsize_eq; lia.
  + iApply (IH with "m2 contra"); rewrite [tsize (TSeal _ _)]tsize_eq; lia.
- rewrite public_THash; iEval (rewrite minted_THash) in "m"; iLeft.
  iApply (IH with "m contra"); rewrite [tsize (THash _)]tsize_eq; lia.
- have := nf; rewrite /is_non_free PreTerm.is_dh_exp_gmul.
  by move: Ex Em Eg; rewrite /is_mod /is_exp /is_gmul /= => -> -> ->.
Qed.

Lemma except_0_public t :
  minted t -∗
  ◇ public t -∗
  public t.
Proof.
rewrite /bi_except_0.
by iIntros "#m #[contra|?]"; eauto; iApply False_public.
Qed.

Lemma public_exp_inv_gen X t1 t2 :
  t1 ∈ X →
  X ⊆ SMS.pos (exps t2) →
  public t2 -∗
  ∃ t, ⌜t ∈ X⌝ ∧ (
    public t ∨
    ∃ t3, ⌜base t3 = base t2⌝ ∧ ⌜X ⊆ SMS.pos (exps t3)⌝ ∧
      exp_pred t t3).
Proof.
move=> t1_X; elim/term_lt_ind: t2 => t2 IH X_t2; iIntros "#p".
have t1_t2 := MSet.elem_of_subseteq _ _ _ X_t2 t1_X.
have xt2 := is_exp_of_exps (SMS.elem_of_pos _ _ t1_t2).
have Nm2 := is_exp_Ngmul xt2.
iEval (rewrite public_exp_iff //) in "p".
iDestruct "p" as "(_ & _ & [#last | #all])"; last first.
  have t1_t2' : t1 ∈ satoms (exps t2).
    by rewrite /satoms elem_of_app MSet.elem_of_elements; left.
  iExists t1; iSplit => //; iRight; iExists t2; do 2!iSplit => //.
  by iApply (big_sepL_elem_of _ _ _ t1_t2' with "all").
iDestruct "last" as (t) "(%t_t2 & #j & #p)".
case: (decide (t ∈ X)) => t_X.
  iExists t; iSplit => //; iDestruct "j" as "[j|j]"; first by iLeft.
  by iRight; iExists t2; iFrame "j".
have [_ lt] := tsize_satoms _ _ t_t2.
have t1t : t1 ≠ t by move=> e; apply: t_X; rewrite -e.
have [_ [Bt _]] := count_strip Nm2 t_t2 t1t.
have X_t2' : X ⊆ SMS.pos (exps (TExp t2 (TInv t))).
  apply/MSet.subseteq_count => u.
  have := proj1 (MSet.subseteq_count _ _) X_t2 u.
  case: (decide (u ∈ X)) => [uX|/MSet.not_elem_of_count -> //]; last lia.
  have ut : u ≠ t by move=> e; apply: t_X; rewrite -e.
  have [_ [_ le]] := count_strip Nm2 t_t2 ut.
  have := count_exps_pos u t2; have := count_exps_pos u (TExp t2 (TInv t)).
  lia.
rewrite -Bt; iApply (IH _ lt X_t2' with "p").
Qed.

Lemma public_exp_inv t1 t2 :
  t1 ∈ SMS.pos (exps t2) →
  public t2 -∗
  ∃ t, ⌜t ∈ SMS.pos (exps t2)⌝ ∧ (
    public t ∨
    ∃ t3, ⌜base t3 = base t2⌝ ∧
      ⌜SMS.pos (exps t2) ⊆ SMS.pos (exps t3)⌝ ∧
      exp_pred t t3).
Proof. move=> t1_t2; exact: public_exp_inv_gen t1_t2 (reflexivity _). Qed.

Lemma public_exp_inv_same t1 t2 :
  t1 ∈ SMS.pos (exps t2) →
  public t2 -∗
  public t1 ∨
  ∃ t2', ⌜base t2' = base t2⌝ ∗ ⌜t1 ∈ SMS.pos (exps t2')⌝ ∗
    exp_pred t1 t2'.
Proof.
iIntros "%t1_t2 #p".
have t1_t1 : t1 ∈ ({[+ t1 +]} : MSet.mset term).
  exact/MSet.elem_of_singleton.
move/MSet.singleton_subseteq: t1_t2 => t1_t2.
iPoseProof (public_exp_inv_gen t1_t1 t1_t2 with "p") as "(%t & %t_t1 & H)".
move: t_t1; rewrite MSet.elem_of_singleton => {t} ->.
iDestruct "H" as "[H|(%t3 & #? & %t1_t3 & #base)]"; first by eauto.
iRight; iExists t3; iFrame "#"; iPureIntro.
exact/MSet.singleton_subseteq.
Qed.

(* [f], an atom or the inverse of one, is the last exponent of [TExp t1 f],
   added by the attacker or by the owner of [f].  Stripping [t1] keeps its
   base, so the owner need only consent for that base. *)
#[local] Lemma public_TExp_last t1 f :
  negb (is_gmul t1) → laurent (expo t1) →
  negb (is_mod f) ∨ negb (is_mod (TInv f)) →
  TInv f ∉ satoms (exps t1) →
  minted f -∗
  □ (∀ t, ⌜base t = base t1⌝ -∗ public t -∗
          public f ∨ exp_pred f (TExp t f)) -∗
  public t1 -∗
  public (TExp t1 f).
Proof.
move=> + + Af; move: t1; elim/term_lt_ind => t1 IH Nm1 L1 f_t1.
iIntros "#mf #j #p1".
have Lf := laurent_satom Af.
have nzf : frac_of f ≠ Frac.zero := laurent_frac_neq0 _ Lf.
have [Nm1' [L1' _]] := laurent_TExp_satom Nm1 L1 Af.
have cntE g :
    scount g (expo (TExp t1 f)) = (scount g (expo t1) + scount g f)%Z.
  exact: scount_expo_TExp.
have f_t : f ∈ satoms (exps (TExp t1 f)).
  move: f_t1; rewrite /exps !elem_of_satoms // cntE !scount_TInv_l.
  rewrite (scount_satom_diag Af); lia.
rewrite [public (TExp _ _)]public_exp_iff; last exact: is_exp_of_satoms f_t.
iSplit.
  by iApply all_minted_TExp; iSplit => //; iApply public_minted.
iSplit; last first.
  iLeft; iExists f; rewrite (TExpK _ nzf); iSplit => //.
  by iSplit; [iApply ("j" with "[//] p1")|].
iApply big_sepL_forall; iIntros (? g g_t%list_elem_of_lookup_2) "!> #pg".
have [->|gf] := decide (g = f); first by rewrite (TExpK _ nzf).
have gTf : g ≠ TInv f.
  move=> e; move: g_t f_t1; rewrite /exps !elem_of_satoms // e cntE.
  rewrite !scount_TInv_l (scount_satom_diag Af); lia.
have g_t1 : g ∈ satoms (exps t1).
  move: g_t; rewrite /exps !elem_of_satoms // cntE.
  rewrite (scount_satom_ne Af gf gTf); lia.
iPoseProof (public_satoms g_t1 with "p1 pg") as "p".
have Ag := satoms_satom L1 g_t1.
have ATg : negb (is_mod (TInv g)) ∨ negb (is_mod (TInv (TInv g))).
  by rewrite TInvK; case: Ag; [right|left].
have [Nmg [Lg Bg]] := laurent_TExp_satom Nm1 L1 ATg.
iAssert (□ (∀ t, ⌜base t = base (TExp t1 (TInv g))⌝ -∗ public t -∗
                 public f ∨ exp_pred f (TExp t f)))%I as "#j'".
  by rewrite Bg.
rewrite TExpC; iApply (IH with "mf j' p").
- by case: (tsize_satoms _ _ g_t1).
- exact: Nmg.
- exact: Lg.
- have Tfg : TInv f ≠ g by move=> e; apply: f_t1; rewrite e.
  have TfTg : TInv f ≠ TInv g by move=> /(inj TInv) e; apply: gf; rewrite e.
  move: f_t1; rewrite /exps !elem_of_satoms // scount_expo_TExp //;
    last exact: laurent_satom.
  rewrite scount_TInv_r; last exact: laurent_satom.
  rewrite (scount_satom_ne Ag Tfg TfTg); lia.
Qed.

(* The attacker raises a public term to a public atom or inverse of one. *)
Lemma public_TExp_satom t1 f :
  negb (is_gmul t1) → laurent (expo t1) →
  negb (is_mod f) ∨ negb (is_mod (TInv f)) →
  public t1 -∗
  public f -∗
  public (TExp t1 f).
Proof.
move=> Nm1 L1 Af; iIntros "#p1 #pf".
case: (decide (TInv f ∈ satoms (exps t1))) => f_t1.
  have -> : TExp t1 f = TExp t1 (TInv (TInv f)) by rewrite TInvK.
  by iApply (public_satoms f_t1 with "p1"); rewrite public_TInv.
iApply (public_TExp_last Nm1 L1 Af f_t1 with "[] [] p1").
- by iApply public_minted.
- by iIntros "!> %t _ _"; iLeft.
Qed.

Lemma public_TExp_make_intro t X Y :
  negb (is_gmul t) → laurent (expo t) →
  (∀ u, u ∈ X ∨ u ∈ Y → negb (is_mod u)) →
  public t -∗ □ (∀ u, ⌜u ∈ X ∨ u ∈ Y⌝ → public u) -∗
  public (TExp t (TMul (SMS.make X Y))).
Proof.
have inE x (X' : MSet.mset term) u : u ∈ {[+ x +]} ⊎ X' ↔ u = x ∨ u ∈ X'.
  by rewrite MSet.elem_of_disj_union MSet.elem_of_singleton.
move=> Nm L.
have LT Z W : (∀ u, u ∈ Z ∨ u ∈ W → negb (is_mod u)) →
    negb (is_gmul (TExp t (TMul (SMS.make Z W)))) ∧
    laurent (expo (TExp t (TMul (SMS.make Z W)))).
  move=> h; have Le : laurent (TMul (SMS.make Z W)).
    by apply: laurent_TMul_atoms => u /SMS.elem_of_make; exact: h.
  have me := laurent_mono_num _ Le.
  split; first exact: Ngmul_TExp.
  by rewrite (expo_TExp Nm me); exact: laurent_TMul2.
elim/MSet.mset_ind: X => [|x X IHX].
- elim/MSet.mset_ind: Y => [|y Y IHY] HY; iIntros "#p #pY".
    by rewrite TExp_unit.
  have Ny : negb (is_mod (TInv (TInv y))).
    by rewrite TInvK; apply: HY; right; apply/inE; left.
  have HY' u : u ∈ (∅ : MSet.mset term) ∨ u ∈ Y → negb (is_mod u).
    by case=> ?; apply: HY; [left|right; apply/inE; right].
  have [Nm' L'] := LT _ _ HY'.
  rewrite TExp_TMul_singleton_r; last first.
    by move=> z zE; case: (MSet.not_elem_of_empty _ zE).
  iApply (public_TExp_satom Nm' L' (or_intror Ny) with "[] []").
  + iApply (IHY HY' with "p"); iIntros "!> %u %u_Y"; iApply "pY".
    by iPureIntro; case: u_Y => ?; [left|right; apply/inE; right].
  + by rewrite public_TInv; iApply "pY"; iPureIntro; right; apply/inE; left.
- move=> HXY; iIntros "#p #pXY".
  have Nx : negb (is_mod x) by apply: HXY; left; apply/inE; left.
  have HXY' u : u ∈ X ∨ u ∈ Y → negb (is_mod u).
    by case=> ?; apply: HXY; [left; apply/inE; right|right].
  have [Nm' L'] := LT _ _ HXY'.
  rewrite TExp_TMul_singleton_l; last first.
    by move=> z zY; apply: atom_frac_neq0; apply: HXY; right.
  iApply (public_TExp_satom Nm' L' (or_introl Nx) with "[] []").
  + iApply (IHX HXY' with "p"); iIntros "!> %u %u_XY"; iApply "pXY".
    by iPureIntro; case: u_XY => ?; [left; apply/inE; right|right].
  + by iApply "pXY"; iPureIntro; left; apply/inE; left.
Qed.

(* Raising a Laurent power to a Laurent exponent with public atoms. *)
Lemma public_TExp_laurent t e :
  negb (is_gmul t) → laurent (expo t) → laurent e →
  public t -∗ ([∗ list] a ∈ atoms e, public a) -∗ public (TExp t e).
Proof.
move=> Nm Lt Le; iIntros "#pt #pe".
have Hfs u :
    u ∈ SMS.pos (factors e) ∨ u ∈ SMS.neg (factors e) → negb (is_mod u).
  by move=> /SMS.elem_of_pos_neg; exact: Le.
have -> : TExp t e =
          TExp t (TMul (SMS.make (SMS.pos (factors e)) (SMS.neg (factors e)))).
  by rewrite SMS.make_pos_neg factorsK.
iApply (public_TExp_make_intro Nm Lt Hfs with "pt"); iIntros "!> %u %u_e".
iApply (big_sepL_elem_of with "pe").
apply: factors_atoms; last exact: Hfs.
exact/SMS.elem_of_pos_neg.
Qed.

Lemma public_exps_neg t1 t2 :
  laurent (expo t1) → t2 ∈ SMS.neg (exps t1) → public t1 -∗ public t2.
Proof.
move=> + t2_t1; move: t1 t2_t1; elim/term_lt_ind => t1 IH t2_t1 L1.
iIntros "#p1".
have Nm2 : negb (is_mod t2) := L1 _ (SMS.elem_of_neg _ _ t2_t1).
have t2_t1' : TInv t2 ∈ satoms (exps t1) by rewrite /exps elem_of_satoms_TInv.
have xt1 := is_exp_of_satoms t2_t1'.
have Nm1 := is_exp_Ngmul xt1.
iAssert (minted t2) as "#m2".
{ iDestruct (public_minted with "p1") as "m1".
  iPoseProof (minted_satoms t2_t1' with "m1") as "m".
  by rewrite minted_TInv. }
iEval (rewrite public_exp_iff //) in "p1".
iDestruct "p1" as "(_ & _ & [(%f & %f_t1 & j & p) | all])"; last first.
  iApply (False_public with "m2").
  iPoseProof (big_sepL_elem_of _ _ _ t2_t1' with "all") as "j".
  by rewrite exp_pred_TInv.
case: (decide (f = TInv t2)) => [->|ne].
  iDestruct "j" as "[j | j]"; first by iEval (rewrite public_TInv) in "j".
  by iApply (False_public with "m2"); rewrite exp_pred_TInv.
have [_ lt] := tsize_satoms _ _ f_t1.
have Af := satoms_satom L1 f_t1.
have AfI : negb (is_mod (TInv f)) ∨ negb (is_mod (TInv (TInv f))).
  by rewrite TInvK; case: Af; [right|left].
have [_ [L1' _]] := laurent_TExp_satom Nm1 L1 AfI.
have t2f : TInv t2 ≠ TInv f.
  move=> /(inj TInv) e; move: f_t1 t2_t1'.
  rewrite -e /exps !elem_of_satoms // scount_TInv_l; lia.
have mem : t2 ∈ SMS.neg (exps (TExp t1 (TInv f))).
  rewrite /exps -elem_of_satoms_TInv // elem_of_satoms //.
  rewrite scount_expo_TExp //; last exact: laurent_satom.
  rewrite scount_TInv_r; last exact: laurent_satom.
  rewrite (scount_satom_ne Af (not_eq_sym ne) t2f).
  by move: t2_t1'; rewrite /exps elem_of_satoms //; lia.
iApply (IH _ lt mem L1' with "p").
Qed.

(** ** Unit parts

    A power with exponent [M / (C · U)], for the monomial content [C] of the
    denominator and its unit part [U], is public exactly when [U] and the
    Laurent power with exponent [M / C] are ([public_den_unit]): [TInv U] has no
    owner, so a public power was raised to it by the attacker. *)

Lemma public_den_unit_aux u :
  negb (is_gmul u) → PolyGcd.unit_part (Frac.den (expo_frac u)) ≠ Poly.one →
  public u -∗ public (den_unit u).
Proof.
move=> + +; move: u; elim/term_lt_ind => u IH Nu U1; iIntros "#pu".
have [xu [Wn Wm]] := den_unit_neg Nu U1.
have Wsat : TInv (den_unit u) ∈ satoms (exps u).
  rewrite /satoms elem_of_app list_elem_of_fmap; right.
  by exists (den_unit u); split=> //; apply/MSet.elem_of_elements.
iAssert (minted (den_unit u)) as "#mw".
{ iPoseProof (public_minted with "pu") as "mu".
  iPoseProof (minted_satoms Wsat with "mu") as "m".
  by rewrite minted_TInv. }
iEval (rewrite public_exp_iff //) in "pu".
iDestruct "pu" as "(_ & _ & [(%f & %f_u & j & p) | all])"; last first.
  iApply (False_public with "mw").
  iPoseProof (big_sepL_elem_of _ _ _ Wsat with "all") as "j".
  by rewrite exp_pred_TInv_den_unit.
case: (decide (f = TInv (den_unit u))) => [->|ne].
  iDestruct "j" as "[j | j]"; first by iEval (rewrite public_TInv) in "j".
  by iApply (False_public with "mw"); rewrite exp_pred_TInv_den_unit.
have [_ lt] := tsize_satoms _ _ f_u.
have [Nu' EU] := strip_den_unit Nu f_u ne.
have -> : den_unit u = den_unit (TExp u (TInv f)) by rewrite /den_unit EU.
by iApply (IH _ lt Nu' with "p"); rewrite EU.
Qed.

Lemma public_den_unit_elim u :
  negb (is_gmul u) → public u ⊢ public (den_unit u) ∧ public (laurent_part u).
Proof.
move=> Nu; iIntros "#pu".
case: (decide (PolyGcd.unit_part (Frac.den (expo_frac u)) = Poly.one)) => U1.
  rewrite /laurent_part (den_unit_one U1) TExp_unit; iSplit => //.
  by iApply public_TMul0.
iPoseProof (public_den_unit_aux Nu U1 with "pu") as "#pw".
iSplit => //.
have [xu [Wn Wm]] := den_unit_neg Nu U1.
have Wsat : TInv (den_unit u) ∈ satoms (exps u).
  rewrite /satoms elem_of_app list_elem_of_fmap; right.
  by exists (den_unit u); split=> //; apply/MSet.elem_of_elements.
iPoseProof (public_satoms Wsat with "pu") as "c".
have -> : laurent_part u = TExp u (TInv (TInv (den_unit u))) by rewrite TInvK.
by iApply "c"; rewrite public_TInv.
Qed.

Lemma public_den_unit_intro u :
  negb (is_gmul u) → public (den_unit u) -∗ public (laurent_part u) -∗ public u.
Proof.
move=> Nu; move: {2}(tsize (laurent_part u)) (eq_refl (tsize (laurent_part u)))
  => n.
elim/lt_wf_ind: n u Nu => n IH u Nu En; iIntros "#pw #pl".
case: (decide (PolyGcd.unit_part (Frac.den (expo_frac u)) = Poly.one)) => U1.
  by iEval (rewrite /laurent_part (den_unit_one U1) TExp_unit) in "pl".
have [xu [Wn Wm]] := den_unit_neg Nu U1.
have [Nl _] := laurent_part_spec Nu.
rewrite [public u]public_exp_iff //.
iSplit.
  iEval (rewrite -(laurent_partK u)); iApply all_minted_TExp; iSplit.
    by iApply public_minted.
  by rewrite minted_TInv; iApply public_minted.
iSplit; last first.
  iLeft; iExists (TInv (den_unit u)); iSplit.
    iPureIntro; rewrite /satoms elem_of_app list_elem_of_fmap; right.
    by exists (den_unit u); split=> //; apply/MSet.elem_of_elements.
  by iSplit; [iLeft; rewrite public_TInv|rewrite TInvK].
iApply big_sepL_forall; iIntros (? g g_u%list_elem_of_lookup_2) "!> #pg".
case: (decide (g = TInv (den_unit u))) => [->|gW]; first by rewrite TInvK.
have g_l := satoms_laurent_part Nu g_u gW.
have [Nu' EU] := strip_den_unit Nu g_u gW.
have Eu' : den_unit (TExp u (TInv g)) = den_unit u by rewrite /den_unit EU.
have El : laurent_part (TExp u (TInv g)) = TExp (laurent_part u) (TInv g).
  by rewrite /laurent_part Eu' TExpC.
have [_ lt] := tsize_satoms _ _ g_l.
have lt' : tsize (laurent_part (TExp u (TInv g))) < n by rewrite El -En.
iApply (IH _ lt' _ Nu' eq_refl).
- by rewrite Eu'.
- by rewrite El; iApply (public_satoms g_l with "pl pg").
Qed.

Lemma public_den_unit u :
  negb (is_gmul u) → public u ⊣⊢ public (den_unit u) ∧ public (laurent_part u).
Proof.
move=> Nu; apply: (anti_symm _); first exact: public_den_unit_elim.
by iIntros "[#pw #pl]"; iApply (public_den_unit_intro Nu with "pw pl").
Qed.

(** ** Group elements

    A group element is public when the unit and Laurent parts of its group
    factors are ([public_dh_intro]).  Conversely, the variables of the
    denominators of the logarithms of a public element are public
    ([public_den_vars]), and so is the Laurent part of the power
    [k ^ (ν / D)] for each monomial [ν] of a numerator
    ([public_laurent_part_shift], which also shifts it by public atoms). *)

Lemma public_gfactor_parts t u :
  u ∈ gfactors t → public t ⊢ public (den_unit u) ∧ public (laurent_part u).
Proof.
move=> ut; iIntros "#pt".
iEval (rewrite public_gfactors) in "pt"; iDestruct "pt" as "[_ #fs]".
iApply public_den_unit_elim; first exact: Ngmul_gfactors ut.
by iApply (big_sepL_elem_of with "fs"); apply/SMS.elem_of_elements.
Qed.

Lemma public_dh_intro t :
  minted t -∗
  □ (∀ u, ⌜u ∈ gfactors t⌝ → public (den_unit u) ∧ public (laurent_part u)) -∗
  public t.
Proof.
iIntros "#m #H"; rewrite public_gfactors; iSplit => //.
iApply big_sepL_forall; iIntros (k u Hu).
have ut : u ∈ gfactors t.
  by apply/SMS.elem_of_elements; exact: list_elem_of_lookup_2 _ _ _ Hu.
iDestruct ("H" $! u with "[//]") as "[pw pl]".
by iApply (public_den_unit_intro with "pw pl"); exact: Ngmul_gfactors ut.
Qed.

Lemma public_den_vars t k y :
  y ∈ Poly.vars (Frac.den (dh_map t !!! k)) →
  public t -∗ public (fold_term y).
Proof.
move=> yD; have nr := Frac.den_vars_neq0 _ _ yD.
set r := dh_map t !!! k in nr yD *.
iIntros "#pt".
have [ν νN] := Frac.num_car_exists _ nr.
case: (PolyGcd.vars_split _ _ yD) => [yC|yU].
- have [ν' [ν'N yν']] := Frac.content_den_missing _ _ nr yC.
  have [u [ut G]] := gfactors_of_log ν'N.
  have [yn [ny ey]] := gfactor_content_neg G yC yν'.
  have [Nu _] := gfactor_of_spec G.
  iDestruct (public_gfactor_parts ut with "pt") as "[_ pl]".
  have sat : TInv (fold_term y) ∈ satoms (exps u).
    rewrite /satoms elem_of_app list_elem_of_fmap; right.
    by exists (fold_term y); split=> //; apply/MSet.elem_of_elements.
  have ne : TInv (fold_term y) ≠ TInv (den_unit u).
    move=> /(inj TInv) e; move: ny; rewrite e.
    by move: (is_mod_den_unit u); case: (is_mod (den_unit u)).
  have Ll := laurent_expo_laurent_part Nu.
  have yl : fold_term y ∈ SMS.neg (exps (laurent_part u)).
    by rewrite /exps -elem_of_satoms_TInv //; exact: satoms_laurent_part.
  by iApply (public_exps_neg Ll yl with "pl").
- have [u [ut G]] := gfactors_of_log νN.
  have [Nu [_ [Eu _]]] := gfactor_of_spec G.
  iDestruct (public_gfactor_parts ut with "pt") as "[pw _]".
  iEval (rewrite public_atoms_iff) in "pw".
  iApply (big_sepL_elem_of with "pw").
  apply/elem_of_atoms; exists y; split=> //.
  rewrite /PreTerm.atoms Eu /Frac.vars Frac.num_of_poly.
  by apply/elem_of_app; left.
Qed.

Lemma public_laurent_part_shift t' k μ v ν C (A : list PreTerm.pre_term) :
  let pub y := bool_decide (y ∈ A) in
  μ ∈ Poly.car (Frac.num (dh_map t' !!! k)) →
  dh_map v = {[k := Frac.make (Poly.mono ν) (Poly.mono C)]} →
  PolyRestrict.secret_part pub μ = PolyRestrict.secret_part pub ν →
  (∀ y, y ∈ Poly.vars (Frac.den (dh_map t' !!! k)) → y ∈ A) →
  (∀ y, y ∈ C → y ∈ A) →
  (∀ y, y ∈ ν ∨ y ∈ C → PreTerm.wf y && negb (PreTerm.is_mod y)) →
  public t' -∗ □ (∀ y, ⌜y ∈ A⌝ → public (fold_term y)) -∗ public v.
Proof.
move=> pub μr ev es hD hC hw; iIntros "#pt #pA".
have nr := Frac.num_car_neq0 _ _ μr.
have [w [wt G]] := gfactors_of_log μr.
have [Nw [_ [_ Elw]]] := gfactor_of_spec G.
iDestruct (public_gfactor_parts wt with "pt") as "[_ pl]".
set r := dh_map t' !!! k in nr μr hD Elw.
have [wk [gk ar]] := PreTerm.wf_dh_map _ (wf_unfold_term t') k nr.
have hw' y : y ∈ μ ∨ y ∈ ν ∨ y ∈ PolyGcd.content (Frac.den r) ∨ y ∈ C →
    PreTerm.wf y && negb (PreTerm.is_mod y).
  case=> [yμ|[yν|[yC1|yC]]]; try by apply: hw; tauto.
  - by apply: (ar μ y) => //; left.
  - have [m [mD ym]] := PolyGcd.elem_of_content _ _ yC1.
    by apply: (ar m y) => //; right.
have [π [Lπ [Aπ ->]]] := laurent_shift Elw ev es hw'.
have [Nl _] := laurent_part_spec Nw.
iApply (public_TExp_laurent Nl (laurent_expo_laurent_part Nw) Lπ with "pl").
iApply big_sepL_forall; iIntros (? y y_π%list_elem_of_lookup_2).
have [a [-> ha]] := Aπ y y_π.
iApply "pA"; iPureIntro.
case: ha => [aC1|[aC|pa]].
- by apply: hD; apply: PolyGcd.content_vars.
- exact: hC.
- exact: bool_decide_unpack pa.
Qed.

(** ** Closure under the attacker's group operations *)

Lemma public_TGMul2 t1 t2 :
  public t1 -∗ public t2 -∗ public (TGMul {[+ t1; t2 +]}).
Proof.
iIntros "#p1 #p2"; iApply public_dh_intro.
  by iApply all_minted_TGMul2; iSplit; iApply public_minted.
iIntros "!> %u %ut".
have [k [ν G]] := elem_of_gfactors_log ut.
have [Nu [_ [Eu El]]] := gfactor_of_spec G.
have [νr _] := G; have nr := Frac.num_car_neq0 _ _ νr.
set r := dh_map (TGMul {[+ t1; t2 +]}) !!! k in nr νr Eu El.
set r1 := dh_map t1 !!! k; set r2 := dh_map t2 !!! k.
have Er : r = Frac.add r1 r2.
  by rewrite /r dh_map_TGMul Frac.ssum_disj_union !Frac.ssum_singleton.
set A := Poly.vars (Frac.den r1) ++ Poly.vars (Frac.den r2).
have vD y : y ∈ Poly.vars (Frac.den r) → y ∈ A.
  rewrite Er => yD.
  by case: (Frac.vars_den_add _ _ _ yD) => ?;
    apply/elem_of_app; [left|right].
iAssert (□ ∀ y, ⌜y ∈ A⌝ → public (fold_term y))%I as "#pA".
{ iIntros "!> %y %yA"; case/elem_of_app: yA => yA.
  - by iApply (public_den_vars yA with "p1").
  - by iApply (public_den_vars yA with "p2"). }
set pub := λ y, bool_decide (y ∈ A).
have opub D : (∀ y, y ∈ Poly.vars D → y ∈ A) → PolyRestrict.over_pub pub D.
  move=> h; apply: PolyRestrict.over_pub_vars => y /h yA.
  exact: bool_decide_pack.
have [wk [gk ar]] := PreTerm.wf_dh_map _ (wf_unfold_term _) k nr.
iSplit.
- iEval (rewrite public_atoms_iff); iApply big_sepL_forall.
  iIntros (? z z_u%list_elem_of_lookup_2).
  move: z_u => /elem_of_atoms [a [-> au]].
  move: au; rewrite /PreTerm.atoms Eu /Frac.vars Frac.num_of_poly.
  rewrite Frac.den_of_poly => /elem_of_app [aZ|/(Poly.vars_one a) []].
  iApply "pA"; iPureIntro; apply: vD; exact: PolyGcd.unit_part_vars.
- have res : PolyRestrict.restrict pub (PolyRestrict.secret_part pub ν)
               (Frac.num r) ≠ Poly.zero.
    by apply/PolyRestrict.restrict_neq0; exists ν.
  rewrite Er in res.
  have o1 : PolyRestrict.over_pub pub (Frac.den r1).
    by apply: opub => y yD; apply/elem_of_app; left.
  have o2 : PolyRestrict.over_pub pub (Frac.den r2).
    by apply: opub => y yD; apply/elem_of_app; right.
  have hC : ∀ y, y ∈ PolyGcd.content (Frac.den r) → y ∈ A.
    by move=> y /(PolyGcd.content_vars _ y); exact: vD.
  have hw : ∀ y, y ∈ ν ∨ y ∈ PolyGcd.content (Frac.den r) →
      PreTerm.wf y && negb (PreTerm.is_mod y).
    move=> y; case=> [yν|yC]; first by apply: (ar ν y) => //; left.
    have [m [mD ym]] := PolyGcd.elem_of_content _ _ yC.
    by apply: (ar m y) => //; right.
  have hD1 : ∀ y, y ∈ Poly.vars (Frac.den r1) → y ∈ A.
    by move=> y yD; apply/elem_of_app; left.
  have hD2 : ∀ y, y ∈ Poly.vars (Frac.den r2) → y ∈ A.
    by move=> y yD; apply/elem_of_app; right.
  case: (PolyRestrict.restrict_add_frac _ _ _ _ o1 o2 res)
    => /PolyRestrict.restrict_neq0 [μ [μN eμ]].
  + by iApply (public_laurent_part_shift μN El eμ hD1 hC hw with "p1 pA").
  + by iApply (public_laurent_part_shift μN El eμ hD2 hC hw with "p2 pA").
Qed.

(* Unconditional in both arguments. *)
Lemma public_TExp t1 t2 :
  public t1 -∗ public t2 -∗ public (TExp t1 t2).
Proof.
iIntros "#p1 #p2"; iApply public_dh_intro.
  by iApply all_minted_TExp; iSplit; iApply public_minted.
iIntros "!> %u %ut".
have [k [ν G]] := elem_of_gfactors_log ut.
have [Nu [_ [Eu El]]] := gfactor_of_spec G.
have [νr _] := G; have nr := Frac.num_car_neq0 _ _ νr.
set r := dh_map (TExp t1 t2) !!! k in nr νr Eu El.
set r1 := dh_map t1 !!! k; set ε := pre_frac t2.
have Er : r = Frac.mul r1 ε by rewrite /r dh_map_TExp unfold_frac_of.
set A := Poly.vars (Frac.den r1) ++ Frac.vars ε.
have vD y : y ∈ Poly.vars (Frac.den r) → y ∈ A.
  rewrite Er => yD.
  case: (Frac.vars_den_mul _ _ _ yD) => ?; apply/elem_of_app;
    [left|right] => //.
  by rewrite /Frac.vars; apply/elem_of_app; right.
iAssert (□ ∀ y, ⌜y ∈ A⌝ → public (fold_term y))%I as "#pA".
{ iIntros "!> %y %yA"; case/elem_of_app: yA => yA.
  - by iApply (public_den_vars yA with "p1").
  - iEval (rewrite public_atoms_iff) in "p2".
    iApply (big_sepL_elem_of with "p2").
    by apply/elem_of_atoms; exists y. }
set pub := λ y, bool_decide (y ∈ A).
have opub D : (∀ y, y ∈ Poly.vars D → y ∈ A) → PolyRestrict.over_pub pub D.
  move=> h; apply: PolyRestrict.over_pub_vars => y /h yA.
  exact: bool_decide_pack.
have [wk [gk ar]] := PreTerm.wf_dh_map _ (wf_unfold_term _) k nr.
iSplit.
- iEval (rewrite public_atoms_iff); iApply big_sepL_forall.
  iIntros (? z z_u%list_elem_of_lookup_2).
  move: z_u => /elem_of_atoms [a [-> au]].
  move: au; rewrite /PreTerm.atoms Eu /Frac.vars Frac.num_of_poly.
  rewrite Frac.den_of_poly => /elem_of_app [aZ|/(Poly.vars_one a) []].
  iApply "pA"; iPureIntro; apply: vD; exact: PolyGcd.unit_part_vars.
- have res : PolyRestrict.restrict pub (PolyRestrict.secret_part pub ν)
               (Frac.num r) ≠ Poly.zero.
    by apply/PolyRestrict.restrict_neq0; exists ν.
  rewrite Er in res.
  have o1 : PolyRestrict.over_pub pub (Frac.den r1).
    by apply: opub => y yD; apply/elem_of_app; left.
  have on : PolyRestrict.over_pub pub (Frac.num ε).
    apply: opub => y yD; apply/elem_of_app; right.
    by rewrite /Frac.vars; apply/elem_of_app; left.
  have od : PolyRestrict.over_pub pub (Frac.den ε).
    apply: opub => y yD; apply/elem_of_app; right.
    by rewrite /Frac.vars; apply/elem_of_app; right.
  have hC : ∀ y, y ∈ PolyGcd.content (Frac.den r) → y ∈ A.
    by move=> y /(PolyGcd.content_vars _ y); exact: vD.
  have hw : ∀ y, y ∈ ν ∨ y ∈ PolyGcd.content (Frac.den r) →
      PreTerm.wf y && negb (PreTerm.is_mod y).
    move=> y; case=> [yν|yC]; first by apply: (ar ν y) => //; left.
    have [m [mD ym]] := PolyGcd.elem_of_content _ _ yC.
    by apply: (ar m y) => //; right.
  have hD1 : ∀ y, y ∈ Poly.vars (Frac.den r1) → y ∈ A.
    by move=> y yD; apply/elem_of_app; left.
  move: (PolyRestrict.restrict_mul_frac _ _ _ _ o1 on od res).
  move=> /PolyRestrict.restrict_neq0 [μ [μN eμ]].
  by iApply (public_laurent_part_shift μN El eμ hD1 hC hw with "p1 pA").
Qed.

(* The owner of [t2] raises a public term to [t2], as in an oblivious PRF.  It
   need only consent for the terms with the base of a group factor of [t1]. *)
Lemma public_TExp_consent t1 t2 :
  negb (is_mod t2) →
  minted t2 -∗
  □ (∀ t, ⌜base t ∈ base <$> elements (gfactors t1)⌝ -∗ public t -∗
          exp_pred t2 (TExp t t2)) -∗
  public t1 -∗
  public (TExp t1 t2).
Proof.
move=> Nm2; iIntros "#m2 #c #p1"; iApply public_dh_intro.
  by iApply all_minted_TExp; iSplit => //; iApply public_minted.
iIntros "!> %u %ut".
have [k [ν G]] := elem_of_gfactors_log ut.
have [Nu [_ [Eu El]]] := gfactor_of_spec G.
have [νr _] := G; have nr := Frac.num_car_neq0 _ _ νr.
set r := dh_map (TExp t1 t2) !!! k in nr νr Eu El.
set r1 := dh_map t1 !!! k; set x := unfold_term t2.
have ex : pre_frac t2 = Frac.var x.
  by apply: PreTerm.frac_of_Nmod; rewrite -is_mod_unfold.
have Er : r = Frac.mul r1 (Frac.var x)
  by rewrite /r dh_map_TExp unfold_frac_of ex.
set A := Poly.vars (Frac.den r1).
have vD y : y ∈ Poly.vars (Frac.den r) → y ∈ A.
  rewrite Er => yD.
  case: (Frac.vars_den_mul _ _ _ yD) => // yx.
  by move: yx; rewrite Frac.varE Frac.den_of_poly => /(Poly.vars_one y).
iAssert (□ ∀ y, ⌜y ∈ A⌝ → public (fold_term y))%I as "#pA".
{ iIntros "!> %y %yA".
  by iApply (public_den_vars yA with "p1"). }
set pub := λ y, bool_decide (y ∈ A).
have [wk [gk ar]] := PreTerm.wf_dh_map _ (wf_unfold_term _) k nr.
iSplit.
  iEval (rewrite public_atoms_iff); iApply big_sepL_forall.
  iIntros (? z z_u%list_elem_of_lookup_2).
  move: z_u => /elem_of_atoms [a [-> au]].
  move: au; rewrite /PreTerm.atoms Eu /Frac.vars Frac.num_of_poly.
  rewrite Frac.den_of_poly => /elem_of_app [aZ|/(Poly.vars_one a) []].
  iApply "pA"; iPureIntro; apply: vD; exact: PolyGcd.unit_part_vars.
have res : PolyRestrict.restrict pub (PolyRestrict.secret_part pub ν)
             (Frac.num r) ≠ Poly.zero.
  by apply/PolyRestrict.restrict_neq0; exists ν.
rewrite Er in res.
have o1 : PolyRestrict.over_pub pub (Frac.den r1).
  apply: PolyRestrict.over_pub_vars => y yD; exact: bool_decide_pack.
have od : PolyRestrict.over_pub pub (Frac.den (Frac.var x)).
  apply: PolyRestrict.over_pub_vars => y.
  by rewrite Frac.varE Frac.den_of_poly => /(Poly.vars_one y).
move: (PolyRestrict.restrict_mul_frac_num _ _ _ _ o1 od res).
rewrite Frac.varE Frac.num_of_poly Poly.varE (comm Poly.mul).
move=> /PolyRestrict.restrict_mul_mono [μ [μN eμ]].
have nr1 : r1 ≠ Frac.zero := Frac.num_car_neq0 _ _ μN.
have [w [wt Gw]] := gfactors_of_log μN.
have [Nw [_ [_ Elw]]] := gfactor_of_spec Gw.
iDestruct (public_gfactor_parts wt with "p1") as "[_ pl]".
have [Nl [Bl _]] := laurent_part_spec Nw.
have Ll := laurent_expo_laurent_part Nw.
iAssert (public (TExp (laurent_part w) t2)) as "#pe".
{ case: (decide (TInv t2 ∈ satoms (exps (laurent_part w)))) => f_w.
  - iApply (public_TExp_satom Nl Ll (or_introl Nm2) with "pl").
    iApply (public_exps_neg Ll with "pl").
    by rewrite /exps -elem_of_satoms_TInv.
  - iApply (public_TExp_last Nl Ll (or_introl Nm2) f_w with "m2 [] pl").
    iIntros "!> %t %bt #pt"; iRight; iApply ("c" with "[] pt"); iPureIntro.
    rewrite bt Bl list_elem_of_fmap.
    by exists w; split => //; apply/SMS.elem_of_elements. }
set C1 := PolyGcd.content (Frac.den r1).
have Ev : dh_map (TExp (laurent_part w) t2) =
          {[k := Frac.make (Poly.mono (μ ⊎ {[+ x +]})) (Poly.mono C1)]}.
  apply/FMap.fmap_eq => k'.
  rewrite dh_map_TExp unfold_frac_of ex Elw !FMap.lookup_singleton.
  case: bool_decide; last by rewrite Frac.mul_zero_l.
  rewrite Frac.varE -Frac.of_poly_make.
  rewrite (Frac.mul_make _ _ _ _ (PolyGcd.mono_neq0 _) Poly.one_neq0).
  apply: Frac.make_eq.
  - exact: PolyGcd.mul_neq0 (PolyGcd.mono_neq0 _) Poly.one_neq0.
  - exact: PolyGcd.mono_neq0.
  - rewrite Poly.varE !Poly.mul_mono (right_id Poly.one Poly.mul).
    by rewrite Poly.mul_mono.
have es : PolyRestrict.secret_part pub (μ ⊎ {[+ x +]}) =
  PolyRestrict.secret_part pub ν.
  rewrite PolyRestrict.secret_part_disj_union -eμ.
  by apply: MSet.count_inj => z; rewrite !MSet.count_disj_union; lia.
have wx : PreTerm.wf x && negb (PreTerm.is_mod x).
  by apply/andb_True; split; [exact: wf_unfold_term|rewrite -is_mod_unfold].
have hw' y : y ∈ μ ⊎ {[+ x +]} ∨ y ∈ ν ∨ y ∈ C1 ∨
             y ∈ PolyGcd.content (Frac.den r) →
    PreTerm.wf y && negb (PreTerm.is_mod y).
  have [_ [_ ar1]] := PreTerm.wf_dh_map _ (wf_unfold_term t1) k nr1.
  case=> [/MSet.elem_of_disj_union [yμ|/MSet.elem_of_singleton ->]|
          [yν|[yC1|yC]]] //.
  - by apply: (ar1 μ y) => //; left.
  - by apply: (ar ν y) => //; left.
  - have [m [mD ym]] := PolyGcd.elem_of_content _ _ yC1.
    by apply: (ar1 m y) => //; right.
  - have [m [mD ym]] := PolyGcd.elem_of_content _ _ yC.
    by apply: (ar m y) => //; right.
have [π [Lπ [Aπ ->]]] := laurent_shift Ev El es hw'.
have [Ne [Le _]] := laurent_TExp_satom Nl Ll (or_introl Nm2).
iApply (public_TExp_laurent Ne Le Lπ with "pe").
iApply big_sepL_forall; iIntros (? y y_π%list_elem_of_lookup_2).
have [a [-> ha]] := Aπ y y_π.
iApply "pA"; iPureIntro.
case: ha => [aC1|[aC|pa]].
- exact: PolyGcd.content_vars _ _ aC1.
- by apply: vD; apply: PolyGcd.content_vars.
- exact: bool_decide_unpack pa.
Qed.

Lemma public_TMul_intro s :
  ([∗ list] t' ∈ elements s, public t') ⊢ public (TMul s).
Proof.
iIntros "#H"; rewrite public_atoms_iff; iApply big_sepL_forall.
iIntros (k y y_s%list_elem_of_lookup_2).
have [u [us yu]] := atoms_TMul_sub y_s.
iAssert (public u) as "pu".
  by iApply (big_sepL_elem_of with "H"); apply/SMS.elem_of_elements.
iEval (rewrite public_atoms_iff) in "pu".
by iApply (big_sepL_elem_of with "pu").
Qed.

Lemma public_TSum_intro s :
  ([∗ list] t' ∈ elements s, public t') ⊢ public (TSum s).
Proof.
iIntros "#H"; rewrite public_atoms_iff; iApply big_sepL_forall.
iIntros (k y y_s%list_elem_of_lookup_2).
have [u [us yu]] := atoms_TSum_sub y_s.
iAssert (public u) as "pu".
  by iApply (big_sepL_elem_of with "H"); apply/SMS.elem_of_elements.
iEval (rewrite public_atoms_iff) in "pu".
by iApply (big_sepL_elem_of with "pu").
Qed.

#[local] Lemma big_sepL_pair (Φ : term → iProp) `{!∀ t, Persistent (Φ t)} t1 t2
  :
  Φ t1 -∗ Φ t2 -∗ [∗ list] t' ∈ elements ({[+ t1; t2 +]} : tsms), Φ t'.
Proof.
iIntros "#H1 #H2"; iApply big_sepL_intro; iIntros "!>" (k u Hk).
move: (list_elem_of_lookup_2 _ _ _ Hk) => /SMS.elem_of_elements.
by case/SMS.elem_of_disj_union => /SMS.elem_of_singleton ->.
Qed.

Lemma public_TMul2 t1 t2 :
  public t1 -∗ public t2 -∗ public (TMul {[+ t1; t2 +]}).
Proof.
iIntros "#p1 #p2"; iApply public_TMul_intro.
by iApply (big_sepL_pair with "p1 p2").
Qed.

Lemma public_TSum2 t1 t2 :
  public t1 -∗ public t2 -∗ public (TSum {[+ t1; t2 +]}).
Proof.
iIntros "#p1 #p2"; iApply public_TSum_intro.
by iApply (big_sepL_pair with "p1 p2").
Qed.

Lemma public_TGMul0 : ⊢ public (TGMul ∅).
Proof.
rewrite public_gfactors gfactors_TGMul_empty SMS.elements_empty /=.
rewrite minted_gfactors gfactors_TGMul_empty SMS.elements_empty /=.
by iSplit.
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
