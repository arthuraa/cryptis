From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib gmeta.
From cryptis.core Require Import term minted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class publicGpreS Σ := PublicGPreS {
  publicGpreS_nonce : savedPredG Σ term;
  publicGpreS_key   : savedPredG Σ (key_type * term);
  publicGpreS_seal  : savedPredG Σ (term * term);
  publicGpreS_meta  : metaGS Σ;
}.

Local Existing Instance publicGpreS_nonce.
Local Existing Instance publicGpreS_key.
Local Existing Instance publicGpreS_seal.
Local Existing Instance publicGpreS_meta.

Class publicGS Σ := PublicGS {
  public_inG : publicGpreS Σ;
  public_key_name   : gname;
  public_hash_name  : gname;
  public_seal_name  : gname;
}.

Global Existing Instance public_inG.

Definition publicΣ : gFunctors :=
  #[savedPredΣ term;
    savedPredΣ (key_type * term);
    savedPredΣ (term * term);
    metaΣ].

Global Instance subG_publicGpreS Σ : subG publicΣ Σ → publicGpreS Σ.
Proof. solve_inG. Qed.

Section Public.

Context `{!heapGS Σ, !publicGS Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Definition pnonce a : iProp :=
  ∃ γ P, meta a (nroot.@"nonce") γ ∧
         saved_pred_own γ DfracDiscarded P ∧
         ▷ □ P (TNonce a).

Global Instance Persistent_pnonce a : Persistent (pnonce a).
Proof. apply _. Qed.

Definition dh_pred (t t' : term) : iProp :=
  match t with
  | TNonce a =>
    ∃ γ φ, meta a (nroot.@"dh") γ ∧
           saved_pred_own γ DfracDiscarded φ ∧
           ▷ □ φ t'
  | _ => False
  end.

Global Instance Persistent_dh_pred t t' : Persistent (dh_pred t t').
Proof. case: t => *; apply _. Qed.

Definition seal_pred N Φ : iProp :=
  ∃ γ, gmeta public_seal_name N γ ∧
       saved_pred_own γ DfracDiscarded (fun '(k, t) => Φ k t).

Definition seal_pred_token E :=
  gmeta_token public_seal_name E.

Lemma seal_pred_token_difference E1 E2 :
  E1 ⊆ E2 →
  seal_pred_token E2 ⊣⊢ seal_pred_token E1 ∗ seal_pred_token (E2 ∖ E1).
Proof.
move=> sub; rewrite /seal_pred_token; exact: gmeta_token_difference.
Qed.

Lemma seal_pred_token_drop E1 E2 :
  E1 ⊆ E2 →
  seal_pred_token E2 -∗
  seal_pred_token E1.
Proof.
iIntros (sub) "t".
rewrite seal_pred_token_difference //.
by iDestruct "t" as "[t _]".
Qed.

Global Instance seal_pred_persistent N Φ : Persistent (seal_pred N Φ).
Proof. apply _. Qed.

Lemma seal_pred_agree k t N Φ1 Φ2 :
  seal_pred N Φ1 -∗
  seal_pred N Φ2 -∗
  ▷ (Φ1 k t ≡ Φ2 k t).
Proof.
iDestruct 1 as (γm1) "[#meta1 #own1]".
iDestruct 1 as (γm2) "[#meta2 #own2]".
iPoseProof (gmeta_agree with "meta1 meta2") as "->".
by iApply (saved_pred_agree _ _ _ _ _ (k, t) with "own1 own2").
Qed.

Lemma seal_pred_set E (N : namespace) Φ :
  ↑N ⊆ E →
  seal_pred_token E ==∗
  seal_pred N Φ ∗
  seal_pred_token (E ∖ ↑N).
Proof.
iIntros (?) "token".
iMod (saved_pred_alloc (λ '(k, t), Φ k t) DfracDiscarded) as (γ) "own" => //.
rewrite (@seal_pred_token_difference (↑N)) //.
iDestruct "token" as "[token ?]".
iMod (gmeta_set _ _ _ γ with "token") as "?" => //.
by iModIntro; iFrame; iExists γ; iSplit.
Qed.

Definition wf_seal k t : iProp :=
  ∃ N t' Φ, ⌜t = Spec.tag (Tag N) t'⌝ ∧ seal_pred N Φ ∧ □ ▷ Φ k t'.

Global Instance wf_seal_persistent k t : Persistent (wf_seal k t).
Proof. by apply _. Qed.

Lemma wf_seal_elim k N t Φ :
  wf_seal k (Spec.tag (Tag N) t) -∗
  seal_pred N Φ -∗
  □ ▷ Φ k t.
Proof.
iDestruct 1 as (N' t' Φ') "(%t_t' & #HΦ' & #inv)"; iIntros "#HΦ".
case/Spec.tag_inj: t_t' => /Tag_inj <- <-.
iPoseProof (seal_pred_agree k t with "HΦ HΦ'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Definition key_pred N (φ : key_type → term → iProp) : iProp :=
  ∃ γ, gmeta public_key_name N γ ∧
       saved_pred_own γ DfracDiscarded (λ '(kt, t), φ kt t).

Definition key_pred_token E :=
  gmeta_token public_key_name E.

Lemma key_pred_token_difference E1 E2 :
  E1 ⊆ E2 →
  key_pred_token E2 ⊣⊢ key_pred_token E1 ∗ key_pred_token (E2 ∖ E1).
Proof.
move=> sub; rewrite /key_pred_token; exact: gmeta_token_difference.
Qed.

Lemma key_pred_token_drop E1 E2 :
  E1 ⊆ E2 →
  key_pred_token E2 -∗
  key_pred_token E1.
Proof.
iIntros (sub) "t".
rewrite key_pred_token_difference //.
by iDestruct "t" as "[t _]".
Qed.

Global Instance key_pred_persistent N φ : Persistent (key_pred N φ).
Proof. apply _. Qed.

Lemma key_pred_agree kt t N P₁ P₂ :
  key_pred N P₁ -∗
  key_pred N P₂ -∗
  ▷ (P₁ kt t ≡ P₂ kt t).
Proof.
iDestruct 1 as (γm1) "[#meta1 #own1]".
iDestruct 1 as (γm2) "[#meta2 #own2]".
iPoseProof (gmeta_agree with "meta1 meta2") as "->".
by iApply (saved_pred_agree _ _ _ _ _ (kt, t) with "own1 own2").
Qed.

Lemma key_pred_set E N P :
  ↑N ⊆ E →
  key_pred_token E ==∗
  key_pred N P ∗
  key_pred_token (E ∖ ↑N).
Proof.
iIntros (?) "token".
rewrite (@key_pred_token_difference (↑N)) //.
iDestruct "token" as "[token ?]".
iMod (saved_pred_alloc (λ '(kt, t), P kt t) DfracDiscarded) as (γ) "own" => //.
iMod (gmeta_set _ _ _ γ with "token") => //.
by iModIntro; iFrame; iExists γ; iSplit.
Qed.

Definition wf_key kt t : iProp :=
  ∃ N t' P, ⌜t = Spec.tag (Tag N) t'⌝ ∧ key_pred N P ∧ □ ▷ P kt t'.

Global Instance wf_key_persistent kt t : Persistent (wf_key kt t).
Proof. by apply _. Qed.

Lemma wf_key_elim N kt t P :
  wf_key kt (Spec.tag (Tag N) t) -∗
  key_pred N P -∗
  □ ▷ P kt t.
Proof.
iDestruct 1 as (N' t' P') "(%t_t' & #HP' & #inv)"; iIntros "#HP".
case/Spec.tag_inj: t_t' => /Tag_inj <- <-.
iPoseProof (key_pred_agree kt t with "HP HP'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Definition hash_pred N (P : term → iProp) : iProp :=
  ∃ γ, gmeta public_hash_name N γ ∧
       saved_pred_own γ DfracDiscarded P.

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
iDestruct 1 as (γm1) "[#meta1 #own1]".
iDestruct 1 as (γm2) "[#meta2 #own2]".
iPoseProof (gmeta_agree with "meta1 meta2") as "->".
by iApply (saved_pred_agree _ _ _ _ _ t with "own1 own2").
Qed.

Lemma hash_pred_set E N P :
  ↑N ⊆ E →
  hash_pred_token E ==∗
  hash_pred N P ∗
  hash_pred_token (E ∖ ↑N).
Proof.
iIntros (?) "token".
rewrite (@hash_pred_token_difference (↑N)) //.
iDestruct "token" as "[token ?]".
iMod (saved_pred_alloc P DfracDiscarded) as (γ) "own" => //.
iMod (gmeta_set _ _ _ γ with "token") => //.
by iModIntro; iFrame; iExists γ; iSplit.
Qed.

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

Inductive decompose (T : gset term) (t : term) : Prop :=
| DInt n of T = ∅ & t = TInt n

| DPair t1 t2 of T = {[t1; t2]} & t = TPair t1 t2

| DKey kt t' of T = {[t']} & t = TKey kt t'

| DSeal k t' of T = {[k; t']} & t = TSeal k t'

| DHash t' of T = {[t']} & t = THash t'

| DExp t1 t2 of T = {[t1; t2]} & is_exp t & t = TExp t1 t2.

Lemma decompose_tsize T t t' : decompose T t → t' ∈ T → tsize t' < tsize t.
Proof.
case.
- by move=> n -> -> //.
- move=> t1 t2 -> ->.
  case/elem_of_union => /elem_of_singleton ->;
  rewrite [tsize (TPair _ _)]tsize_eq -ssrnat.plusE; lia.
- move=> kt ? -> -> /elem_of_singleton ->.
  rewrite [tsize (TKey _ _)]tsize_eq; lia.
- move=> ?? -> -> /elem_of_union [] /elem_of_singleton ->;
  rewrite ?[tsize (TKey _ _)]tsize_eq [tsize (TSeal _ _)]tsize_eq
    -ssrnat.plusE; lia.
- move=> ? -> -> /elem_of_singleton ->; rewrite [tsize (THash _)]tsize_eq; lia.
- move=> t1 t2 -> _ ->.
  rewrite tsize_TExpN /= -ssrnat.plusE /=.
  move/(ssrbool.elimT ssrnat.leP): (tsize_gt0 t1) => ?.
  move/(ssrbool.elimT ssrnat.leP): (tsize_gt0 t2) => ?.
  by move=> /elem_of_union [] /elem_of_singleton ->; lia.
Qed.

Fixpoint public_aux n t : iProp :=
  if n is S n then
    minted t ∧ (
     (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, public_aux n t')
     ∨ match t with
       | TNonce a => pnonce a
       | TKey kt t => wf_key kt t
       | THash t => wf_hash t
       | TSeal (TKey Seal k) t =>
         wf_seal k t ∧ □ (public_aux n (TKey Open k) → public_aux n t)
       | TSeal _ t => True
       | TExpN' _ _ _ => [∗ list] t' ∈ exps t, dh_pred t' t
       | _ => False
       end%I
    )
  else False.

Global Instance Persistent_public_aux n t : Persistent (public_aux n t).
Proof.
elim: n t => [|n IH] /=; first by apply _.
case; try by move=> *; apply _.
Qed.

(** [public t] holds when the term [t] can be declared public. *)

Fact public_key : unit. Proof. exact: tt. Qed.
Definition public : term → iProp :=
  locked_with public_key (λ t, public_aux (tsize t) t).
Canonical public_unlock := [unlockable of public].

Global Instance Persistent_public t : Persistent (public t).
Proof. rewrite unlock; apply _. Qed.

Lemma public_aux_eq n t : tsize t ≤ n → public_aux n t ⊣⊢ public t.
Proof.
rewrite unlock.
elim: n / (lt_wf n) t => - [|n] _ IH t t_n /=;
move: (ssrbool.elimT ssrnat.ltP (tsize_gt0 t)) => ?;
first lia.
case e_st: (tsize t) => [|m] /=; first lia.
apply: bi.and_proper => //.
apply: bi.or_proper.
- apply: bi.exist_proper => T.
  apply: and_proper_L => T_t.
  apply: big_sepS_proper => t' T_t'.
  move: (decompose_tsize T_t T_t') => ?.
  rewrite (IH n) ?(IH m) //; lia.
- case: (t) t_n e_st => //= k.
  case: k => //= - [] //= k t'.
  rewrite tsize_eq (tsize_eq (TKey Seal k)) -ssrnat.plusE => t_n e_st.
  apply: bi.and_proper => //.
  rewrite !(IH n) ?(IH m) // ?[tsize (TKey _ _)]tsize_eq /=; try lia.
Qed.

(* TODO: Merge with public_aux_eq *)
Lemma public_eq t :
  public t ⊣⊢
  minted t ∧ (
      (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, public t')
     ∨ match t with
       | TNonce a => pnonce a
       | TKey kt t => wf_key kt t
       | THash t => wf_hash t
       | TSeal (TKey Seal k) t => wf_seal k t ∧ □ (public (TKey Open k) → public t)
       | TSeal _ t => True
       | TExpN' _ _ _ => [∗ list] t' ∈ exps t, dh_pred t' t
       | _ => False
       end%I
  ).
Proof.
rewrite {1}[public]unlock.
case e_st: (tsize t) => [|m] /=.
  move: (ssrbool.elimT ssrnat.ltP (tsize_gt0 t)) => ?; lia.
apply: bi.and_proper => //.
apply: bi.or_proper.
- apply: bi.exist_proper => T.
  apply: and_proper_L => T_t.
  apply: big_sepS_proper => t' T_t'.
  move: (decompose_tsize T_t T_t') => ?.
  rewrite public_aux_eq //; lia.
- case: (t) e_st => //= k t' e_st.
  rewrite tsize_eq -ssrnat.plusE in e_st.
  case: k => // kt k in e_st *.
  rewrite (tsize_eq (TKey _ _)) in e_st.
  case: kt => //.
  apply: bi.and_proper => //.
  rewrite !public_aux_eq  ?[tsize (TKey _ _)]tsize_eq //=; lia.
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
  iDestruct "publ" as "[publ | publ]" => //=.
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
  public (TNonce a) ⊣⊢ pnonce a ∗ meta a (nroot.@"minted") ().
Proof.
apply: (anti_symm _); iIntros "Ht".
- rewrite public_eq; iDestruct "Ht" as "[? Ht]".
  rewrite minted_TNonce. iFrame.
  iDestruct "Ht" as "[publ | ?]" => //.
  iDestruct "publ" as (T) "[%dec _]".
  by case: dec.
- rewrite public_eq minted_TNonce /pnonce.
  iDestruct "Ht" as "[Ht ?]". iFrame.
Qed.

Lemma public_TKey kt t :
  public (TKey kt t) ⊣⊢ public t ∨ minted t ∧ wf_key kt t.
Proof.
apply: (anti_symm _).
- rewrite public_eq minted_TKey; iDestruct 1 as "[Ht publ]".
  iDestruct "publ" as "[publ | publ]" => //.
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
  match k with
  | TKey Seal k' => wf_seal k' t ∧ □ (public (TKey Open k') → public t)
  | _ => True
  end.
Proof.
apply: (anti_symm _).
- rewrite public_eq minted_TSeal.
  iDestruct 1 as "[[Hk Ht] publ]".
  iDestruct "publ" as "[publ | publ]".
  + iDestruct "publ" as (T) "[%dec ?]".
    case: dec => // {}k {}t -> [-> ->].
    by rewrite big_sepS_union_pers !big_sepS_singleton; iLeft.
  + iRight. iSplit; first by eauto.
    case: k => // - [] k; eauto.
- iDestruct 1 as "[#[Hk Ht] | (#Ht & inv)]".
  { rewrite [public (TSeal _ _)]public_eq minted_TSeal.
    rewrite -!public_minted.
    iSplit; eauto; iLeft.
    iExists {[k; t]}; rewrite big_sepS_union_pers !big_sepS_singleton.
    iSplit; eauto; iPureIntro; by econstructor. }
  rewrite [public (TSeal _ _)]public_eq; iSplit => //. by eauto.
Qed.

Lemma public_THash t :
  public (THash t) ⊣⊢ public t ∨ minted t ∧ wf_hash t.
Proof.
apply: (anti_symm _).
- rewrite public_eq minted_THash.
  iDestruct 1 as "[Ht [publ | publ]]" => //; eauto.
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

Lemma public_TExpN t ts :
  ¬ is_exp t →
  ts ≠ [] →
  public (TExpN t ts) ⊣⊢
  (∃ t' ts', ⌜ts ≡ₚ t' :: ts'⌝ ∧ public (TExpN t ts') ∧ public t') ∨
  minted (TExpN t ts) ∧ [∗ list] t' ∈ ts, dh_pred t' (TExpN t ts).
Proof.
move=> tNX tsN0.
have ttsX : is_exp (TExpN t ts).
  by rewrite is_exp_TExpN; case: (ts) tsN0.
have [? [] ? [] H etts] : ∃ t' ts' H, TExpN t ts = TExpN' t' ts' H.
  case: (TExpN t ts) ttsX => //=; eauto.
apply: (anti_symm _).
- rewrite public_eq minted_TExpN {2}etts {H etts}.
  iDestruct 1 as "[# [Ht Hts] [#publ | #publ]]".
  + iDestruct "publ" as (T) "[%dec publ]".
    move e: (TExpN t ts) => t' in dec ttsX *.
    case: dec ttsX; try by move=> * {e}; subst t'.
    rewrite -{}e {t'}.
    move=> t1 t2 -> _ e _.
    rewrite big_sepS_union_pers !big_sepS_singleton.
    iDestruct "publ" as "[publ1 publ2]".
    iLeft. iExists t2, (exps t1).
    have -> : TExpN t (exps t1) = t1.
      apply: base_exps_inj.
      * by move/(f_equal base): e; rewrite !base_TExpN.
      * by rewrite exps_TExpN exps_expN //=.
    do !iSplit => //. iPureIntro.
    have ->: ts ≡ₚ exps (TExpN t ts).
      by rewrite exps_TExpN exps_expN //; apply/is_trueP.
    by rewrite e exps_TExpN [_ ++ _]comm.
  + iRight; do 2?iSplit => //.
    by rewrite exps_TExpN exps_expN.
- iDestruct 1 as "# [publ | publ]".
  + iDestruct "publ" as (t' ts') "[%e [Ht1 Ht2]]".
    rewrite e in ttsX *.
    rewrite [public (TExpN _ (_ :: _))]public_eq minted_TExpN /=.
    iSplit.
      rewrite !public_minted minted_TExpN /=.
      by iDestruct "Ht1" as "[??]"; eauto.
    iLeft.
    iExists {[TExpN t ts'; t']}.
    rewrite big_sepS_union_pers !big_sepS_singleton.
    do !iSplit => //.
    iPureIntro.
    rewrite -TExp_TExpN; apply: DExp; eauto.
    by rewrite TExp_TExpN.
  + iDestruct "publ" as "[s p]"; rewrite public_eq [minted]unlock; iSplit=> //.
    rewrite {4}etts; iRight.
    by rewrite exps_TExpN exps_expN //.
Qed.

Lemma public_TExp_iff t1 t2 :
  ¬ is_exp t1 →
  public (TExp t1 t2) ⊣⊢
  public t1 ∧ public t2 ∨
  minted t1 ∧ minted t2 ∧ dh_pred t2 (TExp t1 t2).
Proof.
move=> ?; rewrite public_TExpN //=.
apply: (anti_symm _); iIntros "#pub".
- iDestruct "pub" as "[pub | pub]" => //.
    iDestruct "pub" as (??) "(%e & p_t1 & p_t2)".
    symmetry in e.
    case/Permutation_singleton_r: e => -> ->; eauto.
    rewrite TExp0; eauto.
  by rewrite minted_TExp /=; iDestruct "pub" as "[[??] [??]]"; eauto.
- iDestruct "pub" as "[[p1 p2] | (s1 & s2 & pub)]".
    by iLeft; iExists t2, []; rewrite TExp0; eauto.
  by iRight; rewrite /= minted_TExp; do !iSplit => //=.
Qed.

Lemma public_TExp2_iff t1 t2 t3 :
  ¬ is_exp t1 →
  public (TExpN t1 [t2; t3]) ⊣⊢
  public (TExpN t1 [t2]) ∧ public t3 ∨
  public (TExpN t1 [t3]) ∧ public t2 ∨
  minted (TExpN t1 [t2; t3]) ∧
  dh_pred t2 (TExpN t1 [t2; t3]) ∧
  dh_pred t3 (TExpN t1 [t2; t3]).
Proof.
move=> t1NX. rewrite public_TExpN //.
apply: (anti_symm _); iIntros "#pub".
- rewrite /=; iDestruct "pub" as "[pub | (? & ? & ? & _)]" => //; eauto.
  iDestruct "pub" as (??) "(%e & p_t1 & p_t2)".
  by case: (Permutation_length_2_inv e) => [[-> ->] | [-> ->]]; eauto.
- iDestruct "pub" as "[[? ?] | [[? ?] | (? & ? & ?)]]".
  + iLeft; iExists t3, [t2]; do !iSplit => //.
    iPureIntro; apply: perm_swap.
  + by iLeft; iExists t2, [t3]; do !iSplit => //.
  + iRight; do !iSplit => //=.
Qed.

Lemma public_TExp t1 t2 :
  public t1 -∗
  public t2 -∗
  public (TExp t1 t2).
Proof.
iIntros "#p1 #p2".
rewrite -{2}(base_expsK t1) TExp_TExpN public_TExpN //.
by iLeft; iExists t2, (exps t1); rewrite base_expsK; eauto.
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

Lemma public_derive_key t : public (Spec.derive_key t) ⊣⊢ public t.
Proof. exact: public_tag. Qed.

Lemma public_TSealE N Φ k t :
  public (TSeal (TKey Seal k) (Spec.tag (Tag N) t)) -∗
  seal_pred N Φ -∗
  public (TKey Seal k) ∧ public t ∨
  □ ▷ Φ k t ∧ minted t ∧ □ (public (TKey Open k) → public t).
Proof.
iIntros "#Ht #HΦ"; rewrite public_TSeal -(public_tag N t).
iDestruct "Ht" as "[[? Ht] | Ht]"; first by eauto.
rewrite minted_TSeal minted_tag.
iDestruct "Ht" as "([??] & inv & ?)".
iRight; iSplit; eauto; by iApply wf_seal_elim.
Qed.

Lemma public_TSealI N Φ k t :
  seal_pred N Φ -∗
  minted k -∗
  minted t -∗
  (∀ k',
    ⌜k = TKey Seal k'⌝ -∗
    □ Φ k' t ∗
    □ (public (TKey Open k') → public t)) -∗
  public (TSeal k (Spec.tag (Tag N) t)).
Proof.
iIntros "#HΦ #m_k #m_t Hseal".
rewrite public_TSeal minted_TSeal minted_tag.
iRight. do !iSplit => //.
case: k => //; case=> // k.
iDestruct ("Hseal" $! k with "[//]") as "[#H1 #H2]".
rewrite public_tag; iSplit => //.
iExists N, t, Φ; eauto.
Qed.

Lemma public_TSealIS N Φ k t :
  minted (TKey Seal k) -∗
  seal_pred N Φ -∗
  □ Φ k t -∗
  minted t -∗
  □ (public (TKey Open k) → public t) -∗
  public (TSeal (TKey Seal k) (Spec.tag (Tag N) t)).
Proof.
iIntros "#Hseal #HΦ #HΦt #Ht #Hopenl".
rewrite public_TSeal; iRight.
rewrite minted_TSeal minted_tag.
iSplit; first by rewrite minted_TKey; eauto.
rewrite public_tag. iSplit; eauto.
iExists N, t, Φ; eauto.
Qed.

Lemma public_TSealIP k t :
  public k -∗
  public t -∗
  public (TSeal k t).
Proof. by iIntros "? ?"; rewrite public_TSeal; eauto. Qed.

Lemma nonce_alloc P Q a :
  meta_token a ⊤ -∗
  (minted (TNonce a) -∗ False) ∧
  |==> minted (TNonce a) ∗
    □ (public (TNonce a) ↔ ▷ □ P (TNonce a)) ∗
    □ (∀ t, dh_pred (TNonce a) t ↔ ▷ □ Q t).
Proof.
iIntros "token".
iSplit.
{ rewrite minted_TNonce. iIntros "contra".
  by iDestruct (meta_meta_token with "token contra") as "[]". }
iMod (saved_pred_alloc P DfracDiscarded) as (γP) "#own_P" => //.
iMod (saved_pred_alloc Q DfracDiscarded) as (γQ) "#own_Q" => //.
rewrite (meta_token_difference a (↑nroot.@"nonce")) //.
iDestruct "token" as "[nonce token]".
iMod (meta_set _ _ γP with "nonce") as "#nonce"; eauto.
rewrite (meta_token_difference a (↑nroot.@"dh")); last solve_ndisj.
iDestruct "token" as "[dh token]".
iMod (meta_set _ _ γQ with "dh") as "#dh"; eauto.
rewrite (meta_token_difference a (↑nroot.@"minted")); last solve_ndisj.
iDestruct "token" as "[minted token]".
iMod (meta_set _ _ () (nroot.@"minted") with "minted") as "#minted" => //.
iSplitR.
  by rewrite minted_TNonce.
iSplitR.
  rewrite public_TNonce; do 2!iModIntro; iSplit.
  + iIntros "[#public _]".
    iDestruct "public" as (γP' P') "(#meta_γP' & #own_P' & ?)".
    iPoseProof (meta_agree with "nonce meta_γP'") as "->".
    iPoseProof (saved_pred_agree _ _ _ _ _ (TNonce a) with "own_P own_P'") as "e".
    by iModIntro; iRewrite "e".
  + iIntros "#?". iSplit => //. iExists γP, P; eauto.
iIntros "!> !> %t"; iSplit.
- iDestruct 1 as (γQ' Q') "(#meta_γQ' & #own_Q' & ?)".
  iPoseProof (meta_agree with "dh meta_γQ'") as "->".
  iPoseProof (saved_pred_agree _ _ _ _ _ t with "own_Q own_Q'") as "e".
  by iModIntro; iRewrite "e".
- by iIntros "#?"; iExists _, _; eauto.
Qed.

Definition public_ctx : iProp :=
  key_pred (nroot.@"keys".@"sym") (λ _  _, False%I) ∗
  key_pred (nroot.@"keys".@"enc") (λ kt _, ⌜kt = Seal⌝)%I ∗
  key_pred (nroot.@"keys".@"sig") (λ kt _, ⌜kt = Open⌝)%I.

#[global]
Instance public_ctx_persistent : Persistent public_ctx.
Proof. apply _. Qed.

Class HasPublicCtx (ctx : iProp) := {
  has_public_ctx : ctx ⊢ public_ctx;
  has_public_ctx_persistent : Persistent ctx;
}.

Local Existing Instance has_public_ctx_persistent.

Context `{!HasPublicCtx ctx}.

Lemma public_sym_keyE kt k :
  ctx -∗
  public (TKey kt (Spec.tag (Tag $ nroot.@"keys".@"sym") k)) -∗
  ◇ public k.
Proof.
iIntros "ctx #p_k".
iDestruct (has_public_ctx with "ctx") as "(#sym & _)".
rewrite public_TKey public_tag. iDestruct "p_k" as "[p_k|[_ p_k]]"; eauto.
by iDestruct (wf_key_elim with "[//] [//]") as "#>[]".
Qed.

Lemma public_sym_key kt k :
  ctx -∗
  public (TKey kt (Spec.tag (Tag $ nroot.@"keys".@"sym") k)) ↔
  minted k ∧ ◇ public k.
Proof.
iIntros "ctx".
iDestruct (has_public_ctx with "ctx") as "(#sym & _)".
rewrite public_TKey !public_tag minted_tag.
iSplit.
- iIntros "[#p_k|[#m_k #wf]]"; eauto.
  + iSplit => //. by iApply public_minted.
  + iSplit => //. by iDestruct (wf_key_elim with "[//] [//]") as "#>%".
- rewrite /bi_except_0. iIntros "[#m_k [#fail|#p_k]]".
  + iRight; iSplit => //.
    by iExists _, _, _; iSplit => //; iSplit => //.
  + by iLeft.
Qed.

Lemma public_key_derive_key kt k :
  ctx -∗
  minted k -∗
  public (TKey kt (Spec.derive_key k)) ↔ ◇ public k.
Proof.
iIntros "#ctx #m_k".
iApply (bi.iff_trans _ (minted k ∧ ◇ public k)).
iSplit; first by iApply public_sym_key.
by iSplit; [iIntros "[??]"|iIntros "#?"; iSplit].
Qed.

Lemma public_enc_key kt k :
  ctx -∗
  public (TKey kt (Spec.tag (Tag $ nroot.@"keys".@"enc") k)) ↔
  minted k ∧ ◇ (⌜kt = Seal⌝ ∨ public k).
Proof.
iIntros "ctx".
iDestruct (has_public_ctx with "ctx") as "(_ & #enc & _)".
rewrite public_TKey !public_tag minted_tag.
iSplit.
- iIntros "[#p_k|[#m_k #wf]]"; eauto.
  + iSplit; eauto. by iApply public_minted.
  + iSplit => //.
    iDestruct (wf_key_elim with "[//] [//]") as "#>%".
    by eauto.
- rewrite /bi_except_0. iIntros "[#m_k [#fail|[->|#p_k]]]".
  + iRight; iSplit => //.
    iExists _, _, _; iSplit => //; iSplit => //.
    iIntros "!> !>". by iDestruct "fail" as "[]".
  + iRight. iSplit => //.
    by iExists _, _, _; eauto.
  + by iLeft.
Qed.

Lemma public_sig_key kt k :
  ctx -∗
  public (TKey kt (Spec.tag (Tag $ nroot.@"keys".@"sig") k)) ↔
  minted k ∧ ◇ (⌜kt = Open⌝ ∨ public k).
Proof.
iIntros "ctx".
iDestruct (has_public_ctx with "ctx") as "(_ & _ & #sig)".
rewrite public_TKey !public_tag minted_tag.
iSplit.
- iIntros "[#p_k|[#m_k #wf]]"; eauto.
  + iSplit; eauto. by iApply public_minted.
  + iSplit => //.
    iDestruct (wf_key_elim with "[//] [//]") as "#>%".
    by eauto.
- rewrite /bi_except_0. iIntros "[#m_k [#fail|[->|#p_k]]]".
  + iRight; iSplit => //.
    iExists _, _, _; iSplit => //; iSplit => //.
    iIntros "!> !>". by iDestruct "fail" as "[]".
  + iRight. iSplit => //.
    by iExists _, _, _; eauto.
  + by iLeft.
Qed.

Lemma public_enc_keyE k :
  ctx -∗
  public (TKey Open (Spec.tag (Tag $ nroot.@"keys".@"enc") k)) -∗
  ◇ public k.
Proof.
iIntros "#ctx #p_k".
iDestruct (has_public_ctx with "ctx") as "#(_ & enc & _)".
rewrite public_TKey public_tag. iDestruct "p_k" as "[p_k|[_ p_k]]"; eauto.
by iDestruct (wf_key_elim with "[//] [//]") as "#>%".
Qed.

Lemma public_sig_keyE k :
  ctx -∗
  public (TKey Seal (Spec.tag (Tag $ nroot.@"keys".@"sig") k)) -∗
  ◇ public k.
Proof.
iIntros "#ctx #p_k".
iDestruct (has_public_ctx with "ctx") as "#(_ & _ & sig)".
rewrite public_TKey public_tag. iDestruct "p_k" as "[p_k|[_ p_k]]"; eauto.
by iDestruct (wf_key_elim with "[//] [//]") as "#>%".
Qed.

Definition compromised_key k : iProp :=
  public (TKey Seal k) ∧
  public (TKey Open k).

Definition aenc_key k : iProp :=
  public (TKey Seal k) ∧
  □ (public (TKey Open k) ↔ ◇ public k).

Lemma aenc_key_public k : aenc_key k -∗ public (TKey Seal k).
Proof. by iIntros "(? & _)". Qed.

Lemma aenc_key_compromised_keyI k :
  aenc_key k -∗ public (TKey Open k) -∗ compromised_key k.
Proof. iIntros "(#? & _) #?". by iSplit. Qed.

Lemma aenc_key_compromised_keyE k :
  aenc_key k -∗ compromised_key k -∗ ◇ public k.
Proof. iIntros "(_ & #s_k) [_ #p_k]". by iApply "s_k". Qed.

Definition sign_key k : iProp :=
  public (TKey Open k) ∧
  □ (public (TKey Seal k) ↔ ◇ public k).

Lemma sign_key_public k : sign_key k -∗ public (TKey Open k).
Proof. by iIntros "(? & _)". Qed.

Lemma sign_key_compromised_keyI k :
  sign_key k -∗ public (TKey Seal k) -∗ compromised_key k.
Proof. iIntros "(#? & _) #?". by iSplit. Qed.

Lemma sign_key_compromised_keyE k :
  sign_key k -∗ compromised_key k -∗ ◇ public k.
Proof. iIntros "(_ & #s_k) [#p_k _]". by iApply "s_k". Qed.

Definition senc_key k : iProp :=
  minted k ∧
  □ (∀ kt, public (TKey kt k) ↔ ◇ public k).

Lemma senc_key_compromised_keyI k kt :
  senc_key k -∗ public (TKey kt k) -∗ compromised_key k.
Proof.
iIntros "[_ #senc] #p".
iPoseProof ("senc" with "p") as "p_k".
iPoseProof ("senc" $! Seal with "p_k") as "?".
iPoseProof ("senc" $! Open with "p_k") as "?".
by iSplit.
Qed.

Lemma senc_key_compromised_keyE k :
  senc_key k -∗ compromised_key k -∗ ◇ public k.
Proof. iIntros "#s_k [#p_k _]". by iApply "s_k". Qed.

Definition secret t : iProp :=
  (|==> public t) ∧
  (|==> □ (public t ↔ ▷ False)) ∧
  (public t -∗ ▷ False).

Lemma secret_not_public t : secret t -∗ public t -∗ ▷ False.
Proof. by iIntros "(_ & _ & contra)". Qed.

Lemma secret_public t : secret t ==∗ public t.
Proof. by iIntros "(? & _)". Qed.

Lemma freeze_secret t : secret t ==∗ □ (public t ↔ ▷ False).
Proof. by iIntros "(_ & ? & _)". Qed.

Lemma aenc_freeze_secret t :
  secret t -∗ aenc_key t ==∗ □ (compromised_key t → ▷ False).
Proof.
iIntros "sec_t (#p_seal & #p_open)".
iMod (freeze_secret with "sec_t") as "#p_t".
iIntros "!> !> [_ #contra]".
iPoseProof ("p_open" with "contra") as ">?".
by iApply "p_t".
Qed.

Lemma aenc_secret_not_compromised_key t :
  secret t -∗ aenc_key t -∗ compromised_key t -∗ ▷ False.
Proof.
iIntros "sec_t (#p_seal & #p_open) [_ #comp]".
iMod ("p_open" with "comp") as "?".
by iApply (secret_not_public with "sec_t").
Qed.

Lemma senc_freeze_secret t :
  secret t -∗ senc_key t ==∗ □ (compromised_key t → ▷ False).
Proof.
iIntros "sec_t (_ & #p_keys)".
iMod (freeze_secret with "sec_t") as "#p_t".
iIntros "!> !> [_ #contra]".
iPoseProof ("p_keys" with "contra") as ">?".
by iApply "p_t".
Qed.

Lemma senc_secret_not_compromised_key t :
  secret t -∗ senc_key t -∗ compromised_key t -∗ ▷ False.
Proof.
iIntros "sec_t (#p_seal & #p_open) [_ #comp]".
iMod ("p_open" with "comp") as "?".
by iApply (secret_not_public with "sec_t").
Qed.

Lemma sign_freeze_secret t :
  secret t -∗ sign_key t ==∗ □ (compromised_key t → ▷ False).
Proof.
iIntros "sec_t (#p_open & #p_seal)".
iMod (freeze_secret with "sec_t") as "#p_t".
iIntros "!> !> [#contra _]".
iPoseProof ("p_seal" with "contra") as ">?".
by iApply "p_t".
Qed.

Lemma sign_secret_not_compromised_key t :
  secret t -∗ sign_key t -∗ compromised_key t -∗ ▷ False.
Proof.
iIntros "sec_t (#p_open & #p_seal) [#comp _]".
iMod ("p_seal" with "comp") as "?".
by iApply (secret_not_public with "sec_t").
Qed.

Lemma public_compromised_key k : public k -∗ compromised_key k.
Proof.
iIntros "#p_k". iSplit; iApply public_TKey; eauto.
Qed.

Lemma public_aencIS pk N Φ t :
  seal_pred N Φ -∗
  public pk -∗
  minted t -∗
  (∀ sk, ⌜pk = TKey Seal sk⌝ -∗
         □ Φ sk t ∗
         □ (compromised_key sk → public t)) -∗
  public (TSeal pk (Spec.tag (Tag N) t)).
Proof.
iIntros "#? #p_pk #m_t inv".
iApply public_TSealI => //.
- by iApply public_minted.
- iIntros "%sk #e".
  iPoseProof ("inv" with "e") as "[#inv #p_t]".
  iSplit => //.
  iIntros "!> #p_dk". iPoseProof "e" as "->".
  iApply "p_t". iSplit => //.
Qed.

Lemma public_sencIS sk N Φ t :
  seal_pred N Φ -∗
  senc_key sk -∗
  minted t -∗
  □ Φ sk t -∗
  □ (compromised_key sk → public t) -∗
  public (TSeal (TKey Seal sk) (Spec.tag (Tag N) t)).
Proof.
iIntros "#? #p_sk #m_t #inv #p_t".
iApply public_TSealIS => //.
- rewrite minted_TKey. by iDestruct "p_sk" as "[??]".
- iIntros "!> #p_sk'".
  iApply "p_t".
  by iApply senc_key_compromised_keyI.
Qed.

Lemma public_encE sk N Φ t :
  public (TSeal (TKey Seal sk) (Spec.tag (Tag N) t)) -∗
  seal_pred N Φ -∗
  minted t ∧ (public t ∨ □ ▷ Φ sk t ∧ □ (compromised_key sk → public t)).
Proof.
iIntros "#p_t #?". iSplit => //.
{ iPoseProof (public_minted with "p_t") as "#m_t".
  rewrite minted_TSeal minted_tag. by iDestruct "m_t" as "[_ ?]". }
iPoseProof (public_TSealE with "p_t [//]") as "[[_ comp]|inv]"; eauto.
iDestruct "inv" as "{p_t} (#? & _ & #p_t)".
iRight. iSplit => //. iIntros "!> #[??]". by iApply "p_t".
Qed.

Lemma public_signIS sk N Φ t :
  sign_key sk -∗
  seal_pred N Φ -∗
  □ Φ sk t -∗
  public t -∗
  public (TSeal (TKey Seal sk) (Spec.tag (Tag N) t)).
Proof.
iIntros "#[??] #? #? #?".
iApply public_TSealIS => //=.
- by rewrite public_minted !minted_TKey.
- by iApply public_minted.
- by iIntros "!> _".
Qed.

Lemma public_signE sk N Φ t :
  public (TSeal (TKey Seal sk) (Spec.tag (Tag N) t)) -∗
  seal_pred N Φ -∗
  public (TKey Open sk) -∗
  public t ∧ (compromised_key sk ∨ □ ▷ Φ sk t).
Proof.
iIntros "#p_m #? #p_vk".
iDestruct (public_TSealE with "[//] [//]") as "#[[? ?]|(#? & _ & #p_t)]".
- iSplit => //. iLeft. by iSplit.
- iSplit => //; eauto; by iApply "p_t".
Qed.

End Public.

Arguments public_seal_name {Σ _}.
Arguments seal_pred {Σ _} N Φ.
Arguments seal_pred_set {Σ _ _} N Φ.
Arguments seal_pred_token_difference {Σ _} E1 E2.
Arguments public_hash_name {Σ _}.
Arguments hash_pred {Σ _} N P.
Arguments hash_pred_set {Σ _ _} N P.
Arguments hash_pred_token_difference {Σ _} E1 E2.
Arguments public_key_name {Σ _}.
Arguments key_pred {Σ _} N φ.
Arguments key_pred_set {Σ _ _} N P.
Arguments key_pred_token_difference {Σ _} E1 E2.

Lemma publicGS_alloc `{!heapGS Σ} E :
  publicGpreS Σ →
  ⊢ |={E}=> ∃ (H : publicGS Σ),
             public_ctx ∗
             seal_pred_token ⊤ ∗
             key_pred_token (⊤ ∖ ↑nroot.@"keys") ∗
             hash_pred_token ⊤.
Proof.
move=> ?; iStartProof.
iMod gmeta_token_alloc as (γ_seal) "own_seal".
iMod gmeta_token_alloc as (γ_key) "own_key".
iMod gmeta_token_alloc as (γ_hash) "own_hash".
pose (H := PublicGS _ γ_seal γ_key γ_hash).
iExists H. iFrame.
iAssert (key_pred_token ⊤) with "[own_seal]" as "token".
  by iFrame.
rewrite (key_pred_token_difference (↑nroot.@"keys")) //.
iDestruct "token" as "[token ?]"; iFrame.
iMod (key_pred_set (nroot.@"keys".@"sym") (λ _ _, False%I) with "token")
    as "[#? token]"; try solve_ndisj.
iMod (key_pred_set (nroot.@"keys".@"enc") (λ kt _, ⌜kt = Seal⌝)%I with "token")
    as "[#? token]"; try solve_ndisj.
iMod (key_pred_set (nroot.@"keys".@"sig") (λ kt _, ⌜kt = Open⌝)%I with "token")
    as "[#? token]"; try solve_ndisj.
iModIntro. rewrite /public_ctx. eauto.
Qed.
