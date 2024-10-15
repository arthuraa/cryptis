From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown comp_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cryptisN := nroot.@"cryptis".

Section Cryptis.

Definition mint_mapUR := discrete_funUR (fun _ : nat => authUR (gsetUR term)).

Class cryptisGpreS Σ := CryptisGPreS {
  cryptisGpreS_nonce : savedPredG Σ term;
  cryptisGpreS_key   : savedPredG Σ (key_type * term);
  cryptisGpreS_enc   : savedPredG Σ (term * term);
  cryptisGpreS_hon   : inG Σ comp_mapR;
  cryptisGpreS_mint  : inG Σ mint_mapUR;
  cryptisGpreS_meta  : metaGS Σ;
  cryptisGpreS_maps  : inG Σ (reservation_mapR (agreeR positiveO));
  cryptisGpreS_names : inG Σ (authR (gmapUR term (agreeR gnameO)));
}.

Local Existing Instance cryptisGpreS_nonce.
Local Existing Instance cryptisGpreS_key.
Local Existing Instance cryptisGpreS_enc.
Local Existing Instance cryptisGpreS_hon.
Local Existing Instance cryptisGpreS_mint.
Global Existing Instance cryptisGpreS_meta.
Local Existing Instance cryptisGpreS_maps.
Local Existing Instance cryptisGpreS_names.

Class cryptisGS Σ := CryptisGS {
  cryptis_inG : cryptisGpreS Σ;
  cryptis_key_name   : gname;
  cryptis_hash_name  : gname;
  cryptis_enc_name   : gname;
  cryptis_hon_name   : gname;
  cryptis_mint_name  : gname;
  cryptis_names_name : gname;
}.

Global Existing Instance cryptis_inG.

Definition cryptisΣ : gFunctors :=
  #[savedPredΣ term;
    savedPredΣ (key_type * term);
    savedPredΣ (term * term);
    GFunctor comp_mapR;
    GFunctor mint_mapUR;
    metaΣ;
    GFunctor (reservation_mapR (agreeR positiveO));
    GFunctor (authR (gmapUR term (agreeR gnameO)))].

Global Instance subG_cryptisGpreS Σ : subG cryptisΣ Σ → cryptisGpreS Σ.
Proof. solve_inG. Qed.

Notation nonce := loc.
Implicit Types a : loc.
Implicit Types γ : gname.
Implicit Types N : namespace.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Definition pnonce a : iProp :=
  ∃ γ P, meta a (nroot.@"nonce") γ ∧
         saved_pred_own γ DfracDiscarded P ∧
         ▷ □ P (TNonce a).

Global Instance Persistent_pnonce a : Persistent (pnonce a).
Proof. apply _. Qed.

Definition mnonce a : iProp :=
  meta a (nroot.@"minted") ().

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

Definition enc_pred N Φ : iProp :=
  ∃ γ, own cryptis_enc_name (namespace_map_data N (to_agree γ)) ∧
       saved_pred_own γ DfracDiscarded (fun '(k, t) => Φ k t).

Definition enc_pred_token E :=
  own cryptis_enc_name (reservation_map_token E).

Lemma enc_pred_token_difference E1 E2 :
  E1 ⊆ E2 →
  enc_pred_token E2 ⊣⊢ enc_pred_token E1 ∗ enc_pred_token (E2 ∖ E1).
Proof.
move=> sub; rewrite /enc_pred_token.
by rewrite (reservation_map_token_difference E1 E2) // own_op.
Qed.

Lemma enc_pred_token_drop E1 E2 :
  E1 ⊆ E2 →
  enc_pred_token E2 -∗
  enc_pred_token E1.
Proof.
iIntros (sub) "t".
rewrite enc_pred_token_difference //.
by iDestruct "t" as "[t _]".
Qed.

Global Instance enc_pred_persistent N Φ : Persistent (enc_pred N Φ).
Proof. apply _. Qed.

Lemma enc_pred_agree k t N Φ1 Φ2 :
  enc_pred N Φ1 -∗
  enc_pred N Φ2 -∗
  ▷ (Φ1 k t ≡ Φ2 k t).
Proof.
iDestruct 1 as (γm1) "[#meta1 #own1]".
iDestruct 1 as (γm2) "[#meta2 #own2]".
iPoseProof (own_valid_2 with "meta1 meta2") as "%valid".
move: valid; rewrite -reservation_map_data_op reservation_map_data_valid.
move=> /to_agree_op_inv_L ->.
by iApply (saved_pred_agree _ _ _ _ _ (k, t) with "own1 own2").
Qed.

Lemma enc_pred_set E (N : namespace) Φ :
  ↑N ⊆ E →
  enc_pred_token E ==∗
  enc_pred N Φ ∗
  enc_pred_token (E ∖ ↑N).
Proof.
iIntros (?) "token".
iMod (saved_pred_alloc (λ '(k, t), Φ k t) DfracDiscarded) as (γ) "own" => //.
rewrite (@enc_pred_token_difference (↑N)) //.
iDestruct "token" as "[token ?]".
iMod (own_update with "token").
  eapply (namespace_map_alloc_update _ _ (to_agree γ)) => //.
by iModIntro; iFrame; iExists γ; iSplit.
Qed.

Definition wf_enc k t : iProp :=
  ∃ N t' Φ, ⌜t = Spec.tag N t'⌝ ∧ enc_pred N Φ ∧ □ ▷ Φ k t'.

Global Instance wf_enc_persistent k t : Persistent (wf_enc k t).
Proof. by apply _. Qed.

Lemma wf_enc_elim k N t Φ :
  wf_enc k (Spec.tag N t) -∗
  enc_pred N Φ -∗
  □ ▷ Φ k t.
Proof.
iDestruct 1 as (N' t' Φ') "(%t_t' & #HΦ' & #inv)"; iIntros "#HΦ".
case/Spec.tag_inj: t_t' => <- <-.
iPoseProof (enc_pred_agree k t with "HΦ HΦ'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Definition key_pred N (φ : key_type → term → iProp) : iProp :=
  ∃ γ, own cryptis_key_name (namespace_map_data N (to_agree γ)) ∧
       saved_pred_own γ DfracDiscarded (λ '(kt, t), φ kt t).

Definition key_pred_token E :=
  own cryptis_key_name (reservation_map_token E).

Lemma key_pred_token_difference E1 E2 :
  E1 ⊆ E2 →
  key_pred_token E2 ⊣⊢ key_pred_token E1 ∗ key_pred_token (E2 ∖ E1).
Proof.
move=> sub; rewrite /key_pred_token.
by rewrite (reservation_map_token_difference E1 E2) // own_op.
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
iPoseProof (own_valid_2 with "meta1 meta2") as "%valid".
move: valid; rewrite -reservation_map_data_op reservation_map_data_valid.
move=> /to_agree_op_inv_L ->.
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
iMod (own_update with "token").
  by eapply (namespace_map_alloc_update _ _ (to_agree γ)) => //.
by iModIntro; iFrame; iExists γ; iSplit.
Qed.

Definition wf_key kt t : iProp :=
  ∃ N t' P, ⌜t = Spec.tag N t'⌝ ∧ key_pred N P ∧ □ ▷ P kt t'.

Global Instance wf_key_persistent kt t : Persistent (wf_key kt t).
Proof. by apply _. Qed.

Lemma wf_key_elim N kt t P :
  wf_key kt (Spec.tag N t) -∗
  key_pred N P -∗
  □ ▷ P kt t.
Proof.
iDestruct 1 as (N' t' P') "(%t_t' & #HP' & #inv)"; iIntros "#HP".
case/Spec.tag_inj: t_t' => <- <-.
iPoseProof (key_pred_agree kt t with "HP HP'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Definition hash_pred N (P : term → iProp) : iProp :=
  ∃ γ, own cryptis_hash_name (namespace_map_data N (to_agree γ)) ∧
       saved_pred_own γ DfracDiscarded P.

Definition hash_pred_token E :=
  own cryptis_hash_name (reservation_map_token E).

Lemma hash_pred_token_difference E1 E2 :
  E1 ⊆ E2 →
  hash_pred_token E2 ⊣⊢ hash_pred_token E1 ∗ hash_pred_token (E2 ∖ E1).
Proof.
move=> sub; rewrite /hash_pred_token.
by rewrite (reservation_map_token_difference E1 E2) // own_op.
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
iPoseProof (own_valid_2 with "meta1 meta2") as "%valid".
move: valid; rewrite -reservation_map_data_op reservation_map_data_valid.
move=> /to_agree_op_inv_L ->.
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
iMod (own_update with "token").
  by eapply (namespace_map_alloc_update _ _ (to_agree γ)) => //.
by iModIntro; iFrame; iExists γ; iSplit.
Qed.

Definition wf_hash t : iProp :=
  ∃ N t' P, ⌜t = Spec.tag N t'⌝ ∧ hash_pred N P ∧ □ ▷ P t'.

Global Instance wf_hash_persistent t : Persistent (wf_hash t).
Proof. by apply _. Qed.

Lemma wf_hash_elim N t P :
  wf_hash (Spec.tag N t) -∗
  hash_pred N P -∗
  □ ▷ P t.
Proof.
iDestruct 1 as (N' t' P') "(%t_t' & #HP' & #inv)"; iIntros "#HP".
case/Spec.tag_inj: t_t' => <- <-.
iPoseProof (hash_pred_agree t with "HP HP'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Fact minted_key : unit. Proof. exact: tt. Qed.

Definition minted : term → iProp :=
  locked_with minted_key (
    λ t, [∗ set] a ∈ nonces_of_term t, mnonce a
  )%I.

Canonical minted_unlock := [unlockable of minted].

Global Instance Persistent_minted t : Persistent (minted t).
Proof. rewrite unlock; apply _. Qed.

Global Instance Timeless_minted t : Timeless (minted t).
Proof. rewrite unlock; apply _. Qed.

Lemma subterm_minted t1 t2 :
  subterm t1 t2 → minted t2 -∗ minted t1.
Proof.
rewrite unlock !big_sepS_forall; iIntros "%sub m_t2 %t %t_t1".
move/subterm_nonces_of_term in sub.
iApply "m_t2". iPureIntro. set_solver.
Qed.

Inductive decompose (T : gset term) (t : term) : Prop :=
| DInt n of T = ∅ & t = TInt n

| DPair t1 t2 of T = {[t1; t2]} & t = TPair t1 t2

| DKey kt t' of T = {[t']} & t = TKey kt t'

| DEnc k t' of T = {[TKey Enc k; t']} & t = TEnc k t'

| DHash t' of T = {[t']} & t = THash t'

| DExp0 t' of T = {[t']} & t = TExp t' [] & is_exp t

| DExp1 t1 ts1 t2 of T = {[TExp t1 ts1; t2]} & t = TExp t1 (t2 :: ts1) & is_exp t.

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
  rewrite ?[tsize (TKey _ _)]tsize_eq [tsize (TEnc _ _)]tsize_eq -ssrnat.plusE;
  lia.
- move=> ? -> -> /elem_of_singleton ->; rewrite [tsize (THash _)]tsize_eq; lia.
- move=> ? -> -> _ /elem_of_singleton ->.
  rewrite tsize_TExp /= -ssrnat.plusE; lia.
- move=> t1 ts1 t2 -> -> _.
  case: (tsize_TExp_lt t1 ts1 t2) => ??.
  by move=> /elem_of_union [] /elem_of_singleton ->.
Qed.

Fixpoint public_aux n t : iProp :=
  if n is S n then
    minted t ∧ (
     (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, public_aux n t')
     ∨ match t with
       | TNonce a => pnonce a
       | TKey kt t => wf_key kt t
       | THash t => wf_hash t
       | TEnc k t => wf_enc k t ∧ □ (public_aux n (TKey Dec k) → public_aux n t)
       | TExp' _ pts _ => [∗ list] pt ∈ pts, dh_pred (fold_term pt) t
       | _ => False
       end%I
    )
  else False.

Global Instance Persistent_public_aux n t : Persistent (public_aux n t).
Proof.
elim: n t => [|n IH] /=; first by apply _.
by case=>>; apply _.
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
- case: (t) t_n e_st =>> //= t_n e_st.
  rewrite tsize_eq -ssrnat.plusE in t_n e_st.
  apply: bi.and_proper => //.
  rewrite !(IH n) ?(IH m) // ?[tsize (TKey _ _)]tsize_eq /=; lia.
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
       | TEnc k t => wf_enc k t ∧ □ (public (TKey Dec k) → public t)
       | TExp' _ pts _ =>
         [∗ list] pt ∈ pts, dh_pred (fold_term pt) t
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
- case: (t) e_st =>> //= e_st.
  rewrite tsize_eq -ssrnat.plusE in e_st.
  apply: bi.and_proper => //.
  rewrite !public_aux_eq  ?[tsize (TKey _ _)]tsize_eq //=; lia.
Qed.

Lemma public_minted t : public t -∗ minted t.
Proof. rewrite public_eq; by iIntros "[??]". Qed.

Lemma minted_TInt n : minted (TInt n) ⊣⊢ True.
Proof. by rewrite unlock nonces_of_term_unseal /= big_sepS_empty. Qed.

Lemma minted_TPair t1 t2 : minted (TPair t1 t2) ⊣⊢ minted t1 ∧ minted t2.
Proof.
by rewrite unlock nonces_of_term_unseal /= !big_sepS_union_pers.
Qed.

Lemma minted_TNonce a : minted (TNonce a) ⊣⊢ mnonce a.
Proof.
by rewrite unlock nonces_of_term_unseal /= big_sepS_singleton.
Qed.

Lemma minted_TKey kt t : minted (TKey kt t) ⊣⊢ minted t.
Proof. by rewrite unlock nonces_of_term_unseal /=. Qed.

Lemma minted_TEnc k t : minted (TEnc k t) ⊣⊢ minted k ∧ minted t.
Proof.
by rewrite unlock nonces_of_term_unseal /= !big_sepS_union_pers.
Qed.

Lemma minted_THash t : minted (THash t) ⊣⊢ minted t.
Proof. by rewrite unlock nonces_of_term_unseal /=. Qed.

Lemma minted_TExp t ts : minted (TExp t ts) ⊣⊢ minted t ∧ [∗ list] t' ∈ ts, minted t'.
Proof.
rewrite unlock nonces_of_term_TExp big_sepS_union_pers.
by rewrite big_sepS_union_list_pers big_sepL_fmap.
Qed.

Lemma minted_texp t1 t2 :
  minted t1 -∗
  minted t2 -∗
  minted (Spec.texp t1 t2).
Proof.
elim: t1;
try by move=> *; rewrite /= !minted_TInt; iIntros "*"; eauto.
move=> t1 _ ts1 _ _ /=; rewrite Spec.texpA.
iIntros "s_1 s_2".
rewrite !minted_TExp /=.
by iDestruct "s_1" as "[??]"; eauto.
Qed.

Lemma minted_nonces_of_term t :
  minted t ⊣⊢ [∗ set] a ∈ nonces_of_term t, minted (TNonce a).
Proof.
rewrite {1}unlock !big_sepS_forall; iSplit; iIntros "#H %a %a_t".
- by rewrite minted_TNonce; iApply "H".
- by rewrite -minted_TNonce; iApply "H".
Qed.

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

Lemma public_TNonce a : public (TNonce a) ⊣⊢ pnonce a ∗ mnonce a.
Proof.
apply: (anti_symm _); iIntros "Ht".
- rewrite public_eq; iDestruct "Ht" as "[? Ht]".
  rewrite minted_TNonce. iFrame.
  iDestruct "Ht" as "[publ | ?]" => //.
  iDestruct "publ" as (T) "[%dec _]".
  by case: dec.
- rewrite public_eq minted_TNonce /pnonce /mnonce.
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
  by rewrite unlock nonces_of_term_unseal /=.
Qed.

Lemma public_TEnc k t :
  public (TEnc k t) ⊣⊢
  public (TKey Enc k) ∧ public t ∨
  minted (TEnc k t) ∧ wf_enc k t ∧ □ (public (TKey Dec k) → public t).
Proof.
apply: (anti_symm _).
- rewrite public_eq minted_TEnc.
  iDestruct 1 as "[[Hk Ht] publ]".
  iDestruct "publ" as "[publ | publ]".
  + iDestruct "publ" as (T) "[%dec ?]".
    case: dec => // {}k {}t -> [-> ->].
    by rewrite big_sepS_union_pers !big_sepS_singleton; iLeft.
  + by eauto.
- iDestruct 1 as "# [[Hk Ht] | (Ht & inv & #impl)]".
  + rewrite [public (TEnc _ _)]public_eq minted_TEnc.
    rewrite -[minted k](minted_TKey Enc k) -!public_minted.
    iSplit; eauto; iLeft.
    iExists {[TKey Enc k; t]}; rewrite big_sepS_union_pers !big_sepS_singleton.
    iSplit; eauto; iPureIntro; by econstructor.
  + rewrite [public (TEnc k t)]public_eq; iSplit => //=.
    by eauto.
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
  rewrite public_eq unlock; iSplit.
    by rewrite nonces_of_term_unseal //=.
  by eauto.
Qed.

Lemma public_TExp t ts :
  public (TExp t ts) ⊣⊢
  (∃ t' ts', ⌜ts ≡ₚ t' :: ts'⌝ ∧ public (TExp t ts') ∧ public t') ∨
  minted (TExp t ts) ∧ [∗ list] t' ∈ ts, dh_pred t' (TExp t ts).
Proof.
apply: (anti_symm _).
- rewrite public_eq minted_TExp.
  iDestruct 1 as "[# [Ht Hts] [#publ | publ]]".
  + iDestruct "publ" as (T) "[%dec publ]".
    case: dec; try by move=>>; rewrite !unlock.
    * move=> {}t -> /TExp_inj [-> e_ts] _.
      rewrite big_sepS_singleton; iRight; iSplit => //.
        by iSplit.
      by rewrite [ts]Permutation_nil //.
    * move=> {}t ts1 t2 -> /TExp_inj [-> e_ts] _.
      iLeft; rewrite big_sepS_union_pers !big_sepS_singleton.
      by eauto.
  + case: TExpP => pts wf_pts e_pts; iRight; do 2?iSplit => //.
    rewrite [in X in ([∗ list] _ ∈ X, dh_pred _ _)%I]e_pts big_sepL_fmap.
    iApply (big_sepL_mono with "publ") => k t' _ /=.
    by rewrite unfold_termK.
- iDestruct 1 as "# [publ | publ]".
  + iDestruct "publ" as (t' ts') "[-> [Ht1 Ht2]]".
    rewrite [public (TExp _ (_ :: _))]public_eq minted_TExp /=.
    iSplit.
      rewrite !public_minted minted_TExp /=.
      by iDestruct "Ht1" as "[??]"; eauto.
    iLeft.
    iExists {[TExp t ts'; t']}; rewrite big_sepS_union_pers !big_sepS_singleton.
    do !iSplit => //.
    iPureIntro.
    by apply: DExp1; eauto; rewrite is_exp_TExp.
  + iDestruct "publ" as "[s p]"; rewrite public_eq [minted]unlock; iSplit=> //.
    case: TExpP => pts wf_pts e_pts; iRight.
    move: (TExp' _ _ _) => ?; rewrite e_pts big_sepL_fmap.
    by iApply (big_sepL_mono with "p") => ?? _ /=; rewrite unfold_termK.
Qed.

Lemma public_TExp0 t : public (TExp t []) ⊣⊢ minted t.
Proof.
rewrite public_TExp; apply (anti_symm _); iIntros "#pub".
- iDestruct "pub" as "[pub | [pub ?]]"; eauto.
    iDestruct "pub" as (??) "[%contra _]".
    by move/Permutation_length: contra.
  by rewrite minted_TExp; iDestruct "pub" as "[??]".
- iRight; iSplit => //.
  by rewrite minted_TExp; iSplit.
Qed.

Lemma public_TExp1 t1 t2 :
  public (TExp t1 [t2]) ⊣⊢
  minted t1 ∧ minted t2 ∧ (public t2 ∨ dh_pred t2 (TExp t1 [t2])).
Proof.
rewrite public_TExp; apply: (anti_symm _); iIntros "#pub".
- iDestruct "pub" as "[pub | pub]" => //.
    iDestruct "pub" as (??) "(%e & p_t1 & p_t2)".
    symmetry in e.
    case/Permutation_singleton_r: e => -> ->; eauto.
    rewrite public_TExp0; iSplit => //.
    iSplit => //; eauto.
    by iApply public_minted.
  by rewrite minted_TExp /=; iDestruct "pub" as "[[?[??]] [??]]"; eauto.
- iDestruct "pub" as "(s1 & s2 & [pub | pub])".
    iLeft; iExists t2, []; rewrite public_TExp0; eauto.
  by iRight; rewrite /= minted_TExp; do !iSplit => //=.
Qed.

Lemma public_TExp2 t1 t2 t3 :
  public (TExp t1 [t2; t3]) ⊣⊢
  public (TExp t1 [t2]) ∧ public t3 ∨
  public (TExp t1 [t3]) ∧ public t2 ∨
  minted (TExp t1 [t2; t3]) ∧
  dh_pred t2 (TExp t1 [t2; t3]) ∧
  dh_pred t3 (TExp t1 [t2; t3]).
Proof.
rewrite public_TExp; apply: (anti_symm _); iIntros "#pub".
- rewrite /=; iDestruct "pub" as "[pub | (? & ? & ? & _)]" => //; eauto.
  iDestruct "pub" as (??) "(%e & p_t1 & p_t2)".
  by case: (Permutation_length_2_inv e) => [[-> ->] | [-> ->]]; eauto.
- iDestruct "pub" as "[[? ?] | [[? ?] | (? & ? & ?)]]".
  + iLeft; iExists t3, [t2]; do !iSplit => //.
    iPureIntro; apply: perm_swap.
  + by iLeft; iExists t2, [t3]; do !iSplit => //.
  + iRight; do !iSplit => //=.
Qed.

Lemma public_texp t1 t2 :
  public t1 -∗
  public t2 -∗
  public (Spec.texp t1 t2).
Proof.
elim: t1;
try by move=> *; rewrite /= !public_TInt; iIntros "*"; eauto.
move=> t1 _ ts1 _ _; iIntros "#p_t1 #p_t2".
rewrite Spec.texpA [public (TExp t1 (t2 :: ts1))]public_TExp.
by iLeft; iExists t2, ts1; eauto.
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

Lemma minted_to_list t ts :
  Spec.to_list t = Some ts →
  minted t -∗ [∗ list] t' ∈ ts, minted t'.
Proof.
elim/term_ind': t ts => //=.
  by case=> // ts [<-] /=; iIntros "?".
move=> t _ tl IH ts.
case e: (Spec.to_list tl) => [ts'|] // [<-] /=.
rewrite minted_TPair /=; iIntros "[??]"; iFrame.
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

Lemma minted_of_list ts :
  minted (Spec.of_list ts) ⊣⊢
  [∗ list] t ∈ ts, minted t.
Proof.
rewrite Spec.of_list_unseal.
elim: ts => [|t ts IH]; first by rewrite minted_TInt.
by rewrite minted_TPair /= IH bi.persistent_and_sep.
Qed.

Lemma public_tag N t : public (Spec.tag N t) ⊣⊢ public t.
Proof.
by rewrite Spec.tag_unseal public_TPair public_TInt bi.emp_and.
Qed.

Lemma minted_tag N t : minted (Spec.tag N t) ⊣⊢ minted t.
Proof.
by rewrite Spec.tag_unseal minted_TPair minted_TInt bi.emp_and.
Qed.

Lemma public_TEncE N Φ k t :
  public (TEnc k (Spec.tag N t)) -∗
  enc_pred N Φ -∗
  public (TKey Enc k) ∧ public t ∨
  □ ▷ Φ k t ∧ minted t ∧ □ (public (TKey Dec k) → public t).
Proof.
iIntros "#Ht #HΦ"; rewrite public_TEnc public_tag.
iDestruct "Ht" as "[[? Ht] | Ht]"; first by eauto.
rewrite minted_TEnc minted_tag.
iDestruct "Ht" as "([??] & inv & ?)".
iRight; iSplit; eauto; by iApply wf_enc_elim.
Qed.

Lemma public_TEncIS N Φ k t :
  minted (TKey Enc k) -∗
  enc_pred N Φ -∗
  □ Φ k t -∗
  minted t -∗
  □ (public (TKey Dec k) → public t) -∗
  public (TEnc k (Spec.tag N t)).
Proof.
iIntros "#Henc #HΦ #HΦt #Ht #Hdecl".
rewrite public_TEnc; iRight.
rewrite minted_TEnc minted_tag public_tag.
iSplit; first by rewrite minted_TKey; eauto.
iSplit; eauto.
iExists N, t, Φ; eauto.
Qed.

Lemma public_TEncIP k t :
  public (TKey Enc k) -∗
  public t -∗
  public (TEnc k t).
Proof. by iIntros "? ?"; rewrite public_TEnc; eauto. Qed.

Definition term_name_inv : iProp :=
  ∃ names : gmap term gname,
    own cryptis_names_name (● ((to_agree <$> names) : gmap _ _)) ∗
    [∗ set] t ∈ dom names, minted t.

Global Instance term_name_inv_timeless : Timeless term_name_inv.
Proof. rewrite /term_name_inv. apply _. Qed.

Definition term_name t γ : iProp :=
  own cryptis_names_name (◯ {[t := to_agree γ]}).

Global Instance term_name_persistent t γ : Persistent (term_name t γ).
Proof. apply _. Qed.

Global Instance term_name_timeless t γ : Timeless (term_name t γ).
Proof. apply _. Qed.

Lemma term_name_agree t γ1 γ2 :
  term_name t γ1 -∗
  term_name t γ2 -∗
  ⌜γ1 = γ2⌝.
Proof.
iIntros "name1 name2".
iPoseProof (own_valid_2 with "name1 name2") as "%valid".
rewrite -auth_frag_op auth_frag_valid in valid.
move/(_ t): valid.
rewrite lookup_op !lookup_singleton -Some_op Some_valid.
by move=> /to_agree_op_inv_L ->.
Qed.

Definition term_token t E : iProp :=
  ∃ γ, term_name t γ ∗ gmeta_token γ E.

Definition term_meta `{Countable L} t N (x : L) : iProp :=
  ∃ γ, term_name t γ ∗ gmeta γ N x.

Global Instance term_token_timeless t E : Timeless (term_token t E).
Proof. apply _. Qed.

Global Instance term_meta_timeless `{Countable L} t N (x : L) :
  Timeless (term_meta t N x).
Proof. apply _. Qed.

Global Instance term_meta_persistent `{Countable L} t N (x : L) :
  Persistent (term_meta t N x).
Proof. apply _. Qed.

Lemma term_token_drop E1 E2 t :
  E1 ⊆ E2 → term_token t E2 -∗ term_token t E1.
Proof.
iIntros "% (%γ & #name & token)".
iExists γ. iSplit => //. by iApply gmeta_token_drop.
Qed.

Lemma term_token_disj E1 E2 t :
  term_token t E1 -∗ term_token t E2 -∗ ⌜E1 ## E2⌝.
Proof.
iIntros "(% & #name1 & token1) (% & #name2 & token2)".
iPoseProof (term_name_agree with "name1 name2") as "<-".
iApply (gmeta_token_disj with "token1 token2").
Qed.

Lemma term_token_difference t E1 E2 :
  E1 ⊆ E2 → term_token t E2 ⊣⊢ term_token t E1 ∗ term_token t (E2 ∖ E1).
Proof.
move=> sub. iSplit.
- iIntros "(% & #name & token)".
  rewrite (gmeta_token_difference _ _ _ sub).
  iDestruct "token" as "[token1 token2]".
  by iSplitL "token1"; iExists _; iFrame.
- iIntros "[(% & #name1 & token1) (% & #name2 & token2)]".
  iPoseProof (term_name_agree with "name1 name2") as "<-".
  iExists _; iSplit => //.
  rewrite (gmeta_token_difference _ _ _ sub). by iFrame.
Qed.

Lemma term_meta_token `{Countable L} t (x : L) N E :
  ↑N ⊆ E → term_token t E -∗ term_meta t N x -∗ False.
Proof.
move=> sub.
iIntros "(% & #name1 & token) (% & #name2 & #meta)".
iPoseProof (term_name_agree with "name1 name2") as "<-".
by iApply (gmeta_gmeta_token with "token meta").
Qed.

Lemma term_meta_set' `{Countable L} N (x : L) E t :
  ↑N ⊆ E → term_token t E ==∗ term_meta t N x ∗ term_token t (E ∖ ↑N).
Proof.
iIntros "%sub (%γ & #name & token)".
iMod (gmeta_set' _ _ _ x sub with "token") as "[#meta token]".
iModIntro.
by iSplit; iExists _; iSplit => //.
Qed.

Lemma term_meta_set `{Countable L} N (x : L) E t :
  ↑N ⊆ E → term_token t E ==∗ term_meta t N x.
Proof.
iIntros "%sub token".
iMod (term_meta_set' x _ sub with "token") as "[#meta token]".
by iModIntro.
Qed.

Lemma term_meta_agree `{Countable L} t N (x1 x2 : L) :
  term_meta t N x1 -∗ term_meta t N x2 -∗ ⌜x1 = x2⌝.
Proof.
iIntros "(% & #name1 & #meta1) (% & #name2 & #meta2)".
iPoseProof (term_name_agree with "name1 name2") as "<-".
iApply (gmeta_agree with "meta1 meta2").
Qed.

Lemma term_token_switch t N' Q : ⊢ switch (term_token t (↑N')) Q.
Proof.
iExists (term_meta t N' ()). iSplit; iModIntro.
- iIntros "[token #meta]".
  by iDestruct (term_meta_token with "token meta") as "[]".
- iIntros "token".
  by iMod (term_meta_set () with "token") as "#meta".
Qed.

Section TermOwn.

Context `{inG Σ A}.

Definition term_own t N (x : A) : iProp :=
  ∃ γ, term_name t γ ∗ nown γ N x.

Lemma term_own_alloc t N {E} (a : A) :
  ↑N ⊆ E → ✓ a → term_token t E ==∗ term_own t N a ∗ term_token t (E ∖ ↑N).
Proof.
iIntros "%sub %val (% & #name & token)".
iMod (nown_alloc _ _ sub val with "token") as "[own token]".
iModIntro.
by iSplitL "own"; iExists _; iFrame.
Qed.

Lemma term_own_valid t N (a : A) : term_own t N a -∗ ✓ a.
Proof.
iIntros "(%γ' & #own_γ & own)". iApply (nown_valid with "own").
Qed.

Lemma term_own_valid_2 t N (a1 a2 : A) :
  term_own t N a1 -∗ term_own t N a2 -∗ ✓ (a1 ⋅ a2).
Proof.
iIntros "(%γ1 & #own_γ1 & own1) (%γ2 & #own_γ2 & own2)".
iPoseProof (term_name_agree with "own_γ1 own_γ2") as "<-".
by iApply (nown_valid_2 with "own1 own2").
Qed.

Lemma term_own_update t N (a a' : A) :
  a ~~> a' → term_own t N a ==∗ term_own t N a'.
Proof.
iIntros (?) "(%γ' & #? & own)".
iMod (nown_update with "own") as "own"; eauto.
iModIntro. iExists γ'. eauto.
Qed.

#[global]
Instance term_own_core_persistent t N (a : A) :
  CoreId a → Persistent (term_own t N a).
Proof. apply _. Qed.

#[global]
Instance term_own_timeless t N (a : A) :
  Discrete a → Timeless (term_own t N a).
Proof. apply _. Qed.

#[global]
Instance term_own_ne t N : NonExpansive (term_own t N).
Proof. solve_proper. Qed.

#[global]
Instance term_own_proper t N : Proper ((≡) ==> (≡)) (term_own t N).
Proof. solve_proper. Qed.

Lemma term_own_op t N (a1 a2 : A) :
  term_own t N (a1 ⋅ a2) ⊣⊢ term_own t N a1 ∗ term_own t N a2.
Proof.
iSplit.
- iIntros "(%γ' & #? & [own1 own2])".
  by iSplitL "own1"; iExists γ'; iSplit.
- iIntros "[(%γ1 & #own_γ1 & own1) (%γ2 & #own_γ2 & own2)]".
  iPoseProof (term_name_agree with "own_γ1 own_γ2") as "<-".
  iExists γ1. iSplit => //. by iSplitL "own1".
Qed.

#[global]
Instance from_sep_term_own t N (a b1 b2 : A) :
  IsOp a b1 b2 → FromSep (term_own t N a) (term_own t N b1) (term_own t N b2).
Proof.
by rewrite /IsOp /FromSep => ->; rewrite term_own_op.
Qed.

#[global]
Instance into_sep_term_own t N (a b1 b2 : A) :
  IsOp a b1 b2 → IntoSep (term_own t N a) (term_own t N b1) (term_own t N b2).
Proof.
by rewrite /IsOp /IntoSep => ->; rewrite term_own_op.
Qed.

Lemma term_own_mono t N (a1 a2 : A) : a1 ≼ a2 → term_own t N a2 -∗ term_own t N a1.
Proof.
case => ? ->.
rewrite term_own_op.
by iIntros "[??]".
Qed.

Lemma term_own_update_2 t N (a1 a2 a' : A) :
  a1 ⋅ a2 ~~> a' →
  term_own t N a1 -∗
  term_own t N a2 ==∗
  term_own t N a'.
Proof.
iIntros "% H1 H2".
iMod (term_own_update with "[H1 H2]") as "H" => //.
by iSplitL "H1".
Qed.

End TermOwn.

#[global] Typeclasses Opaque term_own.

Lemma term_token_alloc (T : gset term) (P Q : iProp) E :
  (∀ t, ⌜t ∈ T⌝ -∗ P -∗ minted t -∗ False) -∗
  (∀ t, ⌜t ∈ T⌝ -∗ Q -∗ minted t) -∗
  (P ∧ |={E}=> Q) -∗
  term_name_inv ={E}=∗
  term_name_inv ∗ Q ∗ [∗ set] t ∈ T, term_token t ⊤.
Proof.
assert (∀ names : gmap term gname,
  dom names ## T →
  own cryptis_names_name (● ((to_agree <$> names) : gmap term _)) ==∗
  ∃ names' : gmap term gname,
  ⌜dom names' = dom names ∪ T⌝ ∗
  own cryptis_names_name (● ((to_agree <$> names') : gmap term _)) ∗
  [∗ set] t ∈ T, term_token t ⊤) as names_alloc.
{ induction T as [|t T fresh IH] using set_ind_L.
  - iIntros "%names _ own !>". iExists names.
    by rewrite right_id_L big_sepS_empty; iFrame.
  - iIntros "%names %dis own".
    have t_names : t ∉ dom names by set_solver.
    have {}dis : dom names ## T by set_solver.
    iMod gmeta_token_alloc as "(%γ & token)".
    iMod (own_update with "own") as "[own frag]".
    { eapply auth_update_alloc.
      apply (alloc_singleton_local_update _ t (to_agree γ)) => //.
      by rewrite lookup_fmap (_ : names !! t = None) // -not_elem_of_dom. }
    rewrite -fmap_insert.
    have {}dis: dom (<[t := γ]>names) ## T.
      rewrite dom_insert; set_solver.
    iMod (IH _ dis with "own") as "(%names' & %dom_names' & own & tokens)".
    iModIntro. iExists names'. iFrame.
    rewrite dom_names' dom_insert_L. iSplit; first by iPureIntro; set_solver.
    rewrite big_sepS_union; last by set_solver.
    iFrame. rewrite big_sepS_singleton. iExists γ. iFrame. }
iIntros "PE QE PQ (%names & own & #minted_names)".
iAssert (⌜dom names ## T⌝)%I as "%dis".
{ rewrite elem_of_disjoint. iIntros "%t %t_names %t_T".
  rewrite big_sepS_delete //. iDestruct "minted_names" as "[minted_t _]".
  iDestruct "PQ" as "[P _]".
  iApply ("PE" with "[//] P minted_t"). }
iMod (names_alloc _ dis with "own") as "(%names' & %dom_names & own & tokens)".
iDestruct "PQ" as "[_ >Q]".
iAssert ([∗ set] t ∈ T, minted t)%I as "#minted_T".
{ rewrite (big_sepS_forall _ T). iIntros "%t %t_T".
  by iApply ("QE" with "[//] Q"). }
iModIntro. iFrame. iExists names'. iFrame.
rewrite dom_names big_sepS_union //. by iSplit.
Qed.

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

Definition unknown γ : iProp :=
  own γ (reservation_map_token ⊤).

Definition known γ (x : positive) : iProp :=
  own γ (namespace_map_data nroot (to_agree x)).

Global Instance persistent_known γ x : Persistent (known γ x).
Proof. apply _. Qed.

Global Instance timeless_known γ x : Timeless (known γ x).
Proof. apply _. Qed.

Lemma unknown_alloc : ⊢ |==> ∃ γ, unknown γ.
Proof. iApply own_alloc. apply reservation_map_token_valid. Qed.

Lemma known_alloc γ x : unknown γ ==∗ known γ x.
Proof.
iApply own_update. by apply namespace_map_alloc_update.
Qed.

Lemma unknown_known γ x : unknown γ -∗ known γ x -∗ False.
Proof.
iIntros "no yes".
iPoseProof (own_valid_2 with "no yes") as "%valid".
by case: (namespace_map_disj _ _ _ _ valid).
Qed.

Lemma known_agree γ x y : known γ x -∗ known γ y -∗ ⌜x = y⌝.
Proof.
iIntros "own1 own2".
iPoseProof (own_valid_2 with "own1 own2") as "%valid".
rewrite -reservation_map_data_op reservation_map_data_valid in valid *.
iPureIntro. exact: to_agree_op_inv_L.
Qed.

Implicit Types dq : dfrac.

Definition phase_auth_def dq n : iProp :=
  own cryptis_hon_name (◯CM{dq|n} ({[n := ∅]}, ∅)).
Definition phase_auth_aux : seal phase_auth_def. by eexists. Qed.
Definition phase_auth := unseal phase_auth_aux.
Lemma phase_auth_unseal : phase_auth = phase_auth_def.
Proof. exact: seal_eq. Qed.

Definition honest_def n (X : gset term) : iProp :=
  own cryptis_hon_name (◯CM ({[n := X]}, ∅)) ∗
  [∗ set] t ∈ X, minted t.
Definition honest_aux : seal honest_def. by eexists. Qed.
Definition honest := unseal honest_aux.
Lemma honest_unseal : honest = honest_def.
Proof. exact: seal_eq. Qed.

Definition phase_frag_def n : iProp :=
  own cryptis_hon_name (◯CM ({[n := ∅]}, ∅)).
Definition phase_frag_aux : seal phase_frag_def. by eexists. Qed.
Definition phase_frag := unseal phase_frag_aux.
Lemma phase_frag_unseal : phase_frag = phase_frag_def.
Proof. exact: seal_eq. Qed.

Definition secret_at_def n t : iProp :=
  honest n {[t]}.
Definition secret_at_aux : seal secret_at_def. by eexists. Qed.
Definition secret_at := unseal secret_at_aux.
Lemma secret_at_unseal : secret_at = secret_at_def.
Proof. exact: seal_eq. Qed.

Definition public_at_def n t : iProp :=
  own cryptis_hon_name (◯CM (∅, {[(n, t)]})) ∗
  public t.
Definition public_at_aux : seal public_at_def. by eexists. Qed.
Definition public_at := unseal public_at_aux.
Lemma public_at_unseal : public_at = public_at_def.
Proof. exact: seal_eq. Qed.

Definition mint_map_singleton n t : mint_mapUR :=
  discrete_fun_singleton n (◯ {[t]}).

Notation "●Ph{ dq } n" :=
  (phase_auth dq n) (at level 20, format "●Ph{ dq }  n").
Notation "●Ph{# q } n" :=
  (phase_auth (DfracOwn q) n) (at level 20, format "●Ph{# q }  n").
Notation "●Ph□ n" := (phase_auth (DfracDiscarded) n)
  (at level 20, format "●Ph□  n").
Notation "●Ph n" := (phase_auth (DfracOwn 1) n)
  (at level 20, format "●Ph  n").
Notation "◯Ph n" :=
  (phase_frag n) (at level 20, format "◯Ph  n").

Definition minted_at_def n t : iProp :=
  ◯Ph n ∗
  own cryptis_mint_name (mint_map_singleton n t) ∗
  minted t.
Definition minted_at_aux : seal minted_at_def. by eexists. Qed.
Definition minted_at := unseal minted_at_aux.
Lemma minted_at_unseal : minted_at = minted_at_def.
Proof. exact: seal_eq. Qed.

Definition secret t : iProp :=
  (|==> public t) ∧
  (|==> □ (public t ↔ ◇ False)) ∧
  (public t -∗ ◇ False).

Definition to_mint_map (M : nat → gset term) n : mint_mapUR :=
  λ m, if decide (m < n) then ●□ M m
       else ● M m.

Definition phase_inv : iProp :=
  ∃ n H X C M,
    own cryptis_hon_name (●CM{n} (H, C)) ∗
    ⌜H !! n = Some X⌝ ∗
    own cryptis_mint_name (to_mint_map M n) ∗
    ([∗ set] t ∈ X, secret t) ∗
    ([∗ set] p ∈ C, public p.2) ∗
    □ (∀ m, (⌜m > n → M m = ∅⌝) ∗ [∗ set] t ∈ M m, minted t).

Lemma to_mint_map_alloc M n t :
  to_mint_map M n ~~>
  to_mint_map (discrete_fun_insert n ({[t]} ∪ M n) M) n ⋅
  mint_map_singleton n t.
Proof.
apply/cmra_discrete_update => M' valid_M k /=; move/(_ k): valid_M.
rewrite !discrete_fun_lookup_op /to_mint_map /mint_map_singleton.
case: decide => [k_n|n_k].
{ have ?: k ≠ n by lia.
  rewrite discrete_fun_lookup_singleton_ne //.
  by rewrite discrete_fun_lookup_insert_ne // ucmra_unit_right_id. }
case: (decide (k = n)) => [->|ne].
{ rewrite discrete_fun_lookup_insert discrete_fun_lookup_singleton.
  move: (M' n); apply/cmra_discrete_update.
  set T := {[t]} ∪ M n.
  trans (● T ⋅ ◯ T).
  - apply: auth_update_alloc.
    apply: gset_local_update.
    set_solver.
  - rewrite {2}/T -gset_op auth_frag_op (assoc op).
    exact: cmra_update_op_l. }
rewrite discrete_fun_lookup_insert_ne // discrete_fun_lookup_singleton_ne //.
by rewrite ucmra_unit_right_id.
Qed.

Lemma to_mint_map_bump M n : to_mint_map M n ~~> to_mint_map M (S n).
Proof.
apply/cmra_discrete_update => M' valid_M k /=; move/(_ k): valid_M.
rewrite !discrete_fun_lookup_op /to_mint_map.
case: (decide (k < n)) => [k_n|n_k].
{ rewrite decide_True //; lia. }
case: decide => [k_n|?] //.
move: (M' k). apply/cmra_discrete_update.
exact: auth_update_auth_persist.
Qed.

Definition cryptis_ctx : iProp :=
  key_pred (nroot.@"keys".@"sym") (λ _  _, False%I) ∗
  key_pred (nroot.@"keys".@"enc") (λ kt _, ⌜kt = Enc⌝)%I ∗
  key_pred (nroot.@"keys".@"sig") (λ kt _, ⌜kt = Dec⌝)%I ∗
  inv (cryptisN.@"phase") phase_inv ∗
  inv (cryptisN.@"names") term_name_inv.

#[global]
Instance cryptis_ctx_persistent : Persistent cryptis_ctx.
Proof. apply _. Qed.

Lemma cryptis_term_name_inv :
  cryptis_ctx -∗ inv (cryptisN.@"names") term_name_inv.
Proof. by iIntros "(_ & _ & _ & _ & #ctx)". Qed.

Lemma public_sym_keyE kt k :
  cryptis_ctx -∗
  public (TKey kt (Spec.tag (nroot.@"keys".@"sym") k)) -∗
  ◇ public k.
Proof.
iIntros "(#symP & _) #p_k".
rewrite public_TKey public_tag. iDestruct "p_k" as "[p_k|[_ p_k]]"; eauto.
by iDestruct (wf_key_elim with "[//] [//]") as "#>[]".
Qed.

Lemma public_enc_keyE k :
  cryptis_ctx -∗
  public (TKey Dec (Spec.tag (nroot.@"keys".@"enc") k)) -∗
  ◇ public k.
Proof.
iIntros "(_ & #encP & _) #p_k".
rewrite public_TKey public_tag. iDestruct "p_k" as "[p_k|[_ p_k]]"; eauto.
by iDestruct (wf_key_elim with "[//] [//]") as "#>%".
Qed.

Lemma public_sig_keyE k :
  cryptis_ctx -∗
  public (TKey Enc (Spec.tag (nroot.@"keys".@"sig") k)) -∗
  ◇ public k.
Proof.
iIntros "(_ & _ & #sigP & _) #p_k".
rewrite public_TKey public_tag. iDestruct "p_k" as "[p_k|[_ p_k]]"; eauto.
by iDestruct (wf_key_elim with "[//] [//]") as "#>%".
Qed.

Lemma phase_auth_dfrac_op dq1 dq2 n :
  ●Ph{dq1 ⋅ dq2} n ⊣⊢ ●Ph{dq1} n ∗ ●Ph{dq2} n.
Proof.
rewrite phase_auth_unseal /phase_auth_def; iSplit.
- iIntros "[??]"; iFrame; eauto.
- iIntros "[L ?]"; iFrame; eauto. by iSplitL "L".
Qed.

#[global]
Instance from_sep_phase_auth dq1 dq2 n :
  FromSep (●Ph{dq1 ⋅ dq2} n) (●Ph{dq1} n) (●Ph{dq2} n).
Proof. by rewrite /FromSep phase_auth_dfrac_op. Qed.

#[global]
Instance into_sep_phase_auth dq1 dq2 n :
  IntoSep (●Ph{dq1 ⋅ dq2} n) (●Ph{dq1} n) (●Ph{dq2} n).
Proof. by rewrite /IntoSep phase_auth_dfrac_op. Qed.

Lemma phase_auth_discard dq n : ●Ph{dq} n ==∗ ●Ph□ n.
Proof.
rewrite phase_auth_unseal. iIntros "own".
iMod (own_update _ _ (◯CM□{n} ({[n := ∅]}, ∅)) with "own") as "#own".
  exact: comp_map_frag_discard.
by iModIntro.
Qed.

#[global]
Instance phase_auth_discarded_persistent n : Persistent (●Ph□ n).
Proof. rewrite phase_auth_unseal. apply _. Qed.

#[global]
Instance honest_persistent n X : Persistent (honest n X).
Proof. rewrite honest_unseal. apply _. Qed.

#[global]
Instance secret_at_persistent n t : Persistent (secret_at n t).
Proof. rewrite secret_at_unseal. apply _. Qed.

#[global]
Instance public_at_persistent n t : Persistent (public_at n t).
Proof. rewrite public_at_unseal. apply _. Qed.

Lemma public_at_public n t : public_at n t -∗ public t.
Proof. rewrite public_at_unseal. by iIntros "[? ?]". Qed.

#[global]
Instance phase_frag_persistent n : Persistent (◯Ph n).
Proof. rewrite phase_frag_unseal. apply _. Qed.

#[global]
Instance minted_at_persistent n t : Persistent (minted_at n t).
Proof. rewrite minted_at_unseal. apply _. Qed.

Lemma minted_at_minted n t : minted_at n t -∗ minted t.
Proof. rewrite minted_at_unseal. by iIntros "(? & ? & ?)". Qed.

Lemma honest_minted n X : honest n X -∗ [∗ set] t ∈ X, minted t.
Proof. rewrite honest_unseal. by iIntros "(_ & ?)". Qed.

Lemma minted_at_phase_frag n t : minted_at n t -∗ ◯Ph n.
Proof. rewrite minted_at_unseal. by iIntros "(? & _ & _)". Qed.

Lemma phase_auth_frag_agree dq n m : ●Ph{dq} n -∗ ◯Ph m -∗ ⌜m ≤ n⌝.
Proof.
rewrite phase_auth_unseal phase_frag_unseal.
iIntros "auth frag".
iPoseProof (own_valid_2 with "auth frag") as "%val".
case/comp_map_frag_valid_wf: val => /(_ m) val_H _.
rewrite dom_singleton elem_of_singleton in val_H.
by move/(_ eq_refl) in val_H.
Qed.

Lemma phase_frag_honest n : ◯Ph n -∗ honest n ∅.
Proof.
rewrite phase_frag_unseal honest_unseal.
iIntros "phase". by iSplit => //.
Qed.

Lemma phase_auth_frag dq n : ●Ph{dq} n -∗ ◯Ph n.
Proof.
rewrite phase_auth_unseal phase_frag_unseal /phase_auth_def.
set X := ({[n := ∅]}, ∅); rewrite (_ : X = X ⋅ X); last first.
  by rewrite -pair_op singleton_op !gset_op !union_idemp_L.
by rewrite comp_map_frag_op; iIntros "(_ & ?)".
Qed.

Lemma phase_auth_agree dq1 dq2 n1 n2 :
  ●Ph{dq1} n1 -∗ ●Ph{dq2} n2 -∗ ⌜n1 = n2⌝.
Proof.
rewrite phase_auth_unseal.
iIntros "own1 own2".
iPoseProof (own_valid_2 with "own1 own2") as "%val".
by have <- := comp_map_frag_bound_agree val.
Qed.

Lemma honest_public_at n X m t :
  m ≤ n →
  honest n X -∗ public_at m t -∗ ⌜t ∉ X⌝.
Proof.
rewrite honest_unseal public_at_unseal.
iIntros "%m_n (#frag1 & _) (#frag2 & _)".
iPoseProof (own_valid_2 with "frag1 frag2") as "%val".
move/comp_map_frag_valid_dis/(_ n X m t): val.
rewrite lookup_singleton elem_of_singleton => dis.
iPureIntro; exact: dis.
Qed.

Lemma phase_acc E dq n X :
  ↑cryptisN.@"phase" ⊆ E →
  cryptis_ctx -∗
  honest n X -∗
  ●Ph{dq} n ={E, E ∖ ↑cryptisN.@"phase"}=∗ ∃ H C M Y,
    ●Ph{dq} n ∗
    own cryptis_hon_name (●CM{n} (H, C)) ∗
    ⌜H !! n = Some Y⌝ ∗
    ⌜X ⊆ Y⌝ ∗
    own cryptis_mint_name (to_mint_map M n) ∗
    ▷ ([∗ set] t ∈ Y, secret t) ∗
    ▷ ([∗ set] p ∈ C, public p.2) ∗
    ▷ □ (∀ m, (⌜m > n → M m = ∅⌝) ∗ [∗ set] t ∈ M m, minted t) ∗
    (▷ phase_inv ={E ∖ ↑cryptisN.@"phase",E}=∗ True).
Proof.
rewrite honest_unseal phase_auth_unseal.
iIntros "%sub (_ & _ & _ & #ctx & _) [#hon _] phase".
iMod (inv_acc with "ctx") as "[inv close]" => //.
iDestruct "inv"
  as "(%n' & %H & %Y & %C & %M &
       >verI & >%H_n & >own_M & sec_X & #pub_C & mint_M)".
iPoseProof (own_valid_2 with "verI phase") as "%val_bound".
move/comp_map_auth_frag_bound_agree: val_bound => -> {n'} in H_n *.
iPoseProof (own_valid_2 with "verI hon") as "%val".
case/comp_map_auth_frag_valid_agree: val.
rewrite H_n => _ [] [<-] X_Y.
iFrame. iModIntro. iExists H, C, M, Y. iFrame. eauto.
Qed.

Lemma honest_union n T1 T2 : honest n (T1 ∪ T2) ⊣⊢ honest n T1 ∗ honest n T2.
Proof.
rewrite honest_unseal /honest_def -gset_op -{1}[∅]ucmra_unit_right_id_L.
rewrite -singleton_op pair_op comp_map_frag_op own_op big_sepS_union_pers.
iSplit.
- iIntros "[[??][??]]". by eauto.
- iIntros "[[??][??]]". by eauto.
Qed.

Lemma secret_atI n t T : t ∈ T → honest n T -∗ secret_at n t.
Proof.
move=> ?; have -> : T = {[t]} ∪ T ∖ {[t]}.
  apply: union_difference_L; set_solver.
rewrite honest_union. iIntros "[? _]".
by rewrite secret_at_unseal.
Qed.

Lemma public_atI E dq t n :
  ↑cryptisN.@"phase" ⊆ E →
  cryptis_ctx -∗
  £ 1 -∗
  ●Ph{dq} n -∗
  public t ={E}=∗
  ●Ph{dq} n ∗
  public_at n t.
Proof.
iIntros "%sub #ctx cred phase_auth #p_t".
iPoseProof (phase_auth_frag with "phase_auth") as "#phase_frag".
iPoseProof (phase_frag_honest with "phase_frag") as "#hon".
iMod (phase_acc with "ctx hon phase_auth")
  as "(%H & %C & %M & %X & phase_auth & phaseI & %H_n & _ & own_M &
       sec_X & #pub_X & #mint_M & close)" => //.
iMod (lc_fupd_elim_later with "cred sec_X") as "sec_X".
iAssert (◇ ⌜t ∉ X⌝)%I with "[sec_X]" as "#>%t_X".
{ case: (decide (t ∈ X)) => [t_X|//].
  iClear "pub_X".
  rewrite (big_sepS_delete _ X t) //.
  iDestruct "sec_X" as "[sec_t sec_X]".
  iDestruct "sec_t" as "(_ & _ & sec_t)".
  iDestruct ("sec_t" with "p_t") as ">[]". }
iMod (own_update with "phaseI") as "phaseI".
  exact: comp_map_comp_update_last H_n t_X.
iDestruct "phaseI" as "[phaseI #comp]".
iMod ("close" with "[phaseI own_M sec_X]") as "_".
{ iModIntro. iExists n, H, X, ({[(n, t)]} ∪ C), M. iFrame.
  rewrite big_sepS_union_pers big_sepS_singleton /=.
  by eauto. }
iFrame.
by rewrite public_at_unseal; iModIntro; iSplit.
Qed.

Lemma minted_atI E dq t n :
  ↑cryptisN.@"phase" ⊆ E →
  cryptis_ctx -∗
  ●Ph{dq} n -∗
  minted t ={E}=∗
  ●Ph{dq} n ∗
  minted_at n t.
Proof.
iIntros "%sub #ctx phase_auth #m_t".
iPoseProof (phase_auth_frag with "phase_auth") as "#phase_frag".
iPoseProof (phase_frag_honest with "phase_frag") as "#hon".
iMod (phase_acc with "ctx hon phase_auth")
  as "(%H & %C & %M & %X & phase_auth & phaseI & %H_n & _ & own_M &
       sec_X & #pub_X & #mint_M & close)" => //.
iMod (own_update with "own_M") as "own_M".
{ apply: (to_mint_map_alloc t). }
iDestruct "own_M" as "[own_M #minted]".
iMod ("close" with "[phaseI own_M sec_X]") as "_".
{ iModIntro. iExists n, H, X, C, _. iFrame.
  iSplit => //.
  iSplit => //.
  iIntros "!> %m".
  iDestruct ("mint_M" $! m) as "[%finsupp #minted']". iSplit.
  - iPureIntro. move=> m_n.
    rewrite discrete_fun_lookup_insert_ne ?finsupp //.
    lia.
  - case: (decide (m = n)) => [->|ne].
    + rewrite discrete_fun_lookup_insert.
      rewrite big_sepS_union_pers big_sepS_singleton.
      by iSplit.
    + by rewrite discrete_fun_lookup_insert_ne. }
iFrame.
by rewrite minted_at_unseal; iModIntro; do !iSplit.
Qed.

Definition to_mint_map_share M n : mint_mapUR :=
  λ m, if decide (m < n) then ●□ M m else ε.

Lemma to_mint_map_split M n :
  to_mint_map M n ≡ to_mint_map M n ⋅ to_mint_map_share M n.
Proof.
rewrite /to_mint_map /to_mint_map_share => m.
rewrite discrete_fun_lookup_op.
case: decide=> // _.
apply core_id_dup.
apply _.
Qed.

Local Instance to_mint_map_split_core_id M n :
  CoreId (to_mint_map_share M n).
Proof.
apply/Some_proper => m.
rewrite /to_mint_map_share; case: decide => _; apply: core_id_core.
Qed.

Lemma minted_at_list E dq n :
  ↑cryptisN.@"phase" ⊆ E →
  cryptis_ctx -∗
  ●Ph{dq} n ={E}=∗
  ●Ph{dq} n ∗
  ▷ ∃ Y : gset term,
  ([∗ set] t ∈ Y, minted t) ∗
  □ (∀ m t, ⌜m < n⌝ -∗ minted_at m t -∗ ⌜t ∈ Y⌝).
Proof.
iIntros "%sub #ctx phase_auth".
iPoseProof (phase_auth_frag with "phase_auth") as "#phase_frag".
iPoseProof (phase_frag_honest with "phase_frag") as "#hon".
iMod (phase_acc with "ctx hon phase_auth")
  as "(%H & %C & %M & %X & phase_auth & phaseI & %H_n & _ & own_M &
       sec_X & #pub_X & #mint_M & close)" => //.
rewrite to_mint_map_split.
iDestruct "own_M" as "[own_M #split_M]".
iMod ("close" with "[phaseI own_M sec_X]") as "_".
{ iModIntro. iExists n, H, X, C, _. iFrame. eauto. }
iFrame. iIntros "!> !>".
iExists (⋃ ((λ m, M m) <$> seq 0 n)). iSplit.
- rewrite big_sepS_union_list_pers.
  rewrite big_sepL_fmap big_sepL_forall.
  iIntros "%k %x %kP".
  by iDestruct ("mint_M" $! x) as "[#? #?]".
- rewrite minted_at_unseal. iIntros "!> %m %t %m_n (_ & #minted & _)".
  iPoseProof (own_valid_2 with "split_M minted") as "%valid".
  iPureIntro.
  move/(_ m): valid.
  rewrite discrete_fun_lookup_op /to_mint_map_share /mint_map_singleton.
  rewrite decide_True // discrete_fun_lookup_singleton.
  case/auth_both_dfrac_valid_discrete => _.
  rewrite gset_included singleton_subseteq_l; case=> ??.
  rewrite elem_of_union_list. exists (M m).
  rewrite elem_of_list_fmap. split => //. exists m.
  split => //.
  apply/elem_of_seq. lia.
Qed.

Lemma honest_public E dq t n :
  ↑cryptisN.@"phase" ⊆ E →
  cryptis_ctx -∗
  secret_at n t -∗
  ●Ph{dq} n -∗
  public t ={E}=∗
  ▷ ◇ False.
Proof.
iIntros "%sub #ctx #sec phase_auth #p_t".
rewrite secret_at_unseal.
iMod (phase_acc with "ctx sec phase_auth")
  as "(%H & %C & %M & %X & phase_auth & phaseI & %H_n & %t_X & own_M &
       sec_X & #pub_X & #mint_M & close)" => //.
have ? : t ∈ X by set_solver.
iAssert (▷ ◇ False)%I with "[sec_X]" as "#contra".
{ iClear "pub_X". rewrite (big_sepS_delete _ X) //.
  iDestruct "sec_X" as "([_ I] & _)".
  iModIntro. by iApply "I". }
iMod ("close" with "[phaseI own_M sec_X]") as "_".
{ iModIntro. iExists n, H, X, C, M. iFrame. by eauto. }
by eauto.
Qed.

Lemma honest_unionE E n X Y :
  ↑cryptisN.@"phase" ⊆ E →
  X ## Y →
  cryptis_ctx -∗
  honest n (X ∪ Y) -∗
  ●Ph n ={E}=∗
  honest (S n) X ∗ ●Ph (S n) ∗ ▷ [∗ set] t ∈ Y, secret t.
Proof.
iIntros "%sub %X_Y #ctx #hon phase_auth".
iMod (phase_acc with "ctx hon phase_auth")
  as "(%H & %C & %M & %Z & phase_auth & phaseI & %H_n & %X_Z & own_M &
       sec_X & #pub_X & #mint_M & close)" => //.
rewrite phase_auth_unseal.
iPoseProof (own_valid with "phaseI") as "%val".
case/comp_map_auth_valid_dis: val => [bounds_H [] bounds_C dis].
iMod (own_update_2 with "phaseI phase_auth") as "phaseI".
  apply: (@comp_map_honest_update _ _ _ _ X).
  move=> m t t_C. have m_n: m ≤ n by apply: (bounds_C (m, t)).
  have := dis _ _ _ _ H_n t_C m_n.
  set_solver.
iDestruct "phaseI" as "[phaseI phase_auth]".
have eZ: Z = (X ∪ Y) ∪ (Z ∖ (X ∪ Y)) by apply: union_difference_L; set_solver.
rewrite eZ !big_sepS_union //; last set_solver.
iDestruct "sec_X" as "((sec_X & sec_Y) & _)".
iMod (own_update with "own_M") as "own_M".
{ exact: to_mint_map_bump. }
iMod ("close" with "[sec_X phaseI own_M]") as "_".
{ iModIntro. iExists _, _, _, _, _. iFrame.
  rewrite lookup_insert.
  do !iSplit => //. iDestruct "mint_M" as "#mint_M".
  iIntros "!> %m". iSpecialize ("mint_M" $! m).
  iDestruct "mint_M" as "[%finsupp mint_M]".
  iSplit => //.
  iPureIntro. move=> ?; apply: finsupp. lia. }
iModIntro. iFrame.
set P := ({[S n := _]}, _).
rewrite (_ : P = ({[S n := ∅]}, ∅) ⋅ P); last first.
  by rewrite -pair_op singleton_op !ucmra_unit_left_id_L.
rewrite comp_map_frag_op.
iDestruct "phase_auth" as "[phase_auth #honest]". iFrame.
rewrite honest_unseal. iSplit => //.
iDestruct "hon" as "[_ mint_XY]".
rewrite big_sepS_union //. by iDestruct "mint_XY" as "[? _]".
Qed.

Lemma honest_delete E t n X :
  ↑cryptisN.@"phase" ⊆ E →
  t ∈ X →
  cryptis_ctx -∗
  honest n X -∗
  ●Ph n ={E}=∗
  honest (S n) (X ∖ {[t]}) ∗ ●Ph (S n) ∗ ▷ secret t.
Proof.
iIntros "%sub %t_X #ctx #hon phase".
rewrite {1}[X](union_difference_singleton_L t) // [_ ∪ _]comm_L.
iMod (honest_unionE with "ctx hon phase") as "(hon' & phase & ?)" => //.
  set_solver.
rewrite big_sepS_singleton.
by iFrame.
Qed.

Lemma compromise_honest E n X :
  ↑cryptisN.@"phase" ⊆ E →
  cryptis_ctx -∗
  honest n X -∗
  ●Ph n ={E}=∗
  honest (S n) ∅ ∗ ●Ph (S n) ∗ ▷ |==> [∗ set] t ∈ X, public t.
Proof.
iIntros "%sub #ctx hon phase".
rewrite {1}(_ : X = ∅ ∪ X); last set_solver.
iMod (honest_unionE with "ctx hon phase") as "(hon & phase & sec)" => //.
iFrame. iModIntro. iModIntro. iApply big_sepS_bupd.
iApply (big_sepS_mono with "sec").
by iIntros "%t % [? _]".
Qed.

Lemma freeze_honest E n X :
  ↑cryptisN.@"phase" ⊆ E →
  cryptis_ctx -∗
  honest n X -∗
  ●Ph n ={E}=∗
  honest (S n) ∅ ∗ ●Ph (S n) ∗ ▷ |==> [∗ set] t ∈ X, □ (public t ↔ ◇ False).
Proof.
iIntros "%sub #ctx hon phase".
rewrite {1}(_ : X = ∅ ∪ X); last set_solver.
iMod (honest_unionE with "ctx hon phase") as "(hon & phase & sec)" => //.
iFrame. iModIntro. iModIntro.
iApply big_sepS_bupd. iApply (big_sepS_mono with "sec").
by iIntros "%t % (_ & ? & _)".
Qed.

Lemma honest_unionI Y E n X :
  ↑cryptisN.@"phase" ⊆ E →
  X ## Y →
  cryptis_ctx -∗
  £ 1 -∗
  honest n X -∗
  ●Ph n -∗
  ([∗ set] t ∈ Y, minted t) -∗
  ▷ ([∗ set] t ∈ Y, secret t) ={E}=∗
  honest (S n) (X ∪ Y) ∗ ●Ph (S n).
Proof.
iIntros "%sub %dis #ctx cred #hon phase #s_Y sec".
iMod (phase_acc with "ctx hon phase")
  as "(%H & %C & %M & %Z & phase & phaseI & %H_n & %X_Z & own_M &
       sec_X & #pub_X & #mint_M & close)" => //.
rewrite honest_unseal.
iCombine "pub_X sec sec_X" as "I".
iMod (lc_fupd_elim_later with "cred I") as "I".
iDestruct "I" as "{pub_X} (#pub_X & sec & sec_X)".
iDestruct "hon" as "(#hon & #min)".
iPoseProof (own_valid with "phaseI") as "%val".
case/comp_map_auth_valid_dis: val => [bounds_H [] bounds_C dis'].
iAssert (◇ ⌜∀ m t, (m, t) ∈ C → t ∉ Y⌝)%I as "#>%dis''".
{ iIntros "%m %t %t_C %t_Y".
  rewrite (big_sepS_delete _ C) // !(big_sepS_delete _ Y) //.
  iDestruct "pub_X" as "[pub_X _]".
  iDestruct "sec" as "[sec_t _]".
  iDestruct "sec_t" as "(_ & _ & sec_t)".
  by iApply "sec_t". }
rewrite phase_auth_unseal.
iMod (own_update_2 with "phaseI phase") as "phaseI".
  apply: (@comp_map_honest_update _ _ _ _ (X ∪ Y)).
  move=> m t t_C. have m_n: m ≤ n by apply: (bounds_C (m, t)).
  have := dis' _ _ _ _ H_n t_C m_n.
  have := dis'' _ _ t_C.
  set_solver.
iMod (own_update with "own_M") as "own_M".
{ exact: to_mint_map_bump. }
iDestruct "phaseI" as "[phaseI phase]".
iMod ("close" with "[sec_X sec phaseI own_M]") as "_".
{ iModIntro. iExists _, _, (X ∪ Y), _, _.
  rewrite big_sepS_union //. iFrame. rewrite lookup_insert.
  do !iSplit=> //.
  - by iApply (big_sepS_subseteq with "sec_X").
  - iIntros "!> %m".
    iDestruct ("mint_M" $! m) as "[%finsupp #minted]".
    iSplit => //.
    iPureIntro. move=> ?; apply: finsupp. lia. }
set P := ({[S n := _]}, _).
rewrite (_ : P = ({[S n := ∅]}, ∅) ⋅ P); last first.
  by rewrite -pair_op singleton_op !ucmra_unit_left_id_L.
rewrite comp_map_frag_op.
iDestruct "phase" as "[? #?]". iFrame.
iModIntro. iSplit => //. rewrite big_sepS_union //.
by eauto.
Qed.

Lemma honest_insert t E n X :
  ↑cryptisN.@"phase" ⊆ E →
  t ∉ X →
  cryptis_ctx -∗
  £ 1 -∗
  honest n X -∗
  ●Ph n -∗
  minted t -∗
  ▷ secret t ={E}=∗
  honest (S n) (X ∪ {[t]}) ∗ ●Ph (S n).
Proof.
iIntros "%sub %t_X #ctx cred #hon phase #s_t sec".
iApply (honest_unionI with "[//] [cred] [hon] [phase]") => //.
- set_solver.
- by rewrite big_sepS_singleton.
- by rewrite big_sepS_singleton.
Qed.

End Cryptis.

Arguments cryptis_enc_name {Σ _}.
Arguments enc_pred {Σ _} N Φ.
Arguments enc_pred_set {Σ _ _} N Φ.
Arguments enc_pred_token_difference {Σ _} E1 E2.
Arguments cryptis_hash_name {Σ _}.
Arguments hash_pred {Σ _} N P.
Arguments hash_pred_set {Σ _ _} N P.
Arguments hash_pred_token_difference {Σ _} E1 E2.
Arguments cryptis_key_name {Σ _}.
Arguments key_pred {Σ _} N φ.
Arguments key_pred_set {Σ _ _} N P.
Arguments key_pred_token_difference {Σ _} E1 E2.
Arguments term_meta_set {Σ _ _ _ _} N x E t.
Arguments term_token_difference {Σ _} t E1 E2.
Arguments term_name {Σ _} t γ.
Arguments term_own_alloc {Σ _ A _ t} N {_} a.
Arguments phase_inv {Σ _ _}.
Arguments cryptis_ctx {Σ _ _}.
Arguments unknown_alloc {Σ _}.
Arguments known_alloc {Σ _ γ} x.


Notation "●Ph{ dq } n" :=
  (phase_auth dq n) (at level 20, format "●Ph{ dq }  n").
Notation "●Ph{# q } n" :=
  (phase_auth (DfracOwn q) n) (at level 20, format "●Ph{# q }  n").
Notation "●Ph□ n" := (phase_auth (DfracDiscarded) n)
  (at level 20, format "●Ph□  n").
Notation "●Ph n" := (phase_auth (DfracOwn 1) n)
  (at level 20, format "●Ph  n").
Notation "◯Ph n" :=
  (phase_frag n) (at level 20, format "◯Ph  n").

Local Existing Instance cryptisGpreS_nonce.
Local Existing Instance cryptisGpreS_key.
Local Existing Instance cryptisGpreS_enc.
Local Existing Instance cryptisGpreS_hon.
Local Existing Instance cryptisGpreS_mint.
Local Existing Instance cryptisGpreS_maps.
Local Existing Instance cryptis_inG.

Lemma cryptisGS_alloc `{!heapGS Σ} E :
  cryptisGpreS Σ →
  ⊢ |={E}=> ∃ (H : cryptisGS Σ),
             cryptis_ctx ∗
             enc_pred_token ⊤ ∗
             key_pred_token (⊤ ∖ ↑nroot.@"keys") ∗
             hash_pred_token ⊤ ∗
             honest 0 ∅ ∗
             ●Ph 0.
Proof.
move=> ?; iStartProof.
iMod (own_alloc (reservation_map_token ⊤)) as (γ_enc) "own_enc".
  apply reservation_map_token_valid.
iMod (own_alloc (reservation_map_token ⊤)) as (γ_key) "own_key".
  apply reservation_map_token_valid.
iMod (own_alloc (reservation_map_token ⊤)) as (γ_hash) "own_hash".
  apply reservation_map_token_valid.
iMod (own_alloc (●CM{0} ({[0 := ∅]}, ∅) ⋅ ◯CM{0} ({[0 := ∅]}, ∅)))
    as (γ_hon) "[phaseI phase]".
  apply/view_both_valid => ? /=; do !split.
  - by move=> ?; rewrite dom_singleton elem_of_singleton => ->.
  - move=> ?; set_solver.
  - move=> *; set_solver.
  - by [].
  - by [].
iMod (own_alloc (to_mint_map (ε : discrete_fun _) 0)) as (γ_mint) "mint_auth".
{ move=> m.
  by rewrite /to_mint_map /= discrete_fun_lookup_empty auth_auth_valid. }
rewrite comp_map_frag_split.
iDestruct "phase" as "[phase_auth #phase]".
iMod (own_alloc (● (∅ : gmap term (agree gname)))) as (γ_names) "names_auth".
  by apply auth_auth_valid.
pose (H := CryptisGS _ γ_enc γ_key γ_hash γ_hon γ_mint γ_names).
iExists H; iFrame.
iAssert (key_pred_token ⊤) with "[own_enc]" as "token".
  by iFrame.
rewrite (key_pred_token_difference (↑nroot.@"keys")) //.
iDestruct "token" as "[token ?]"; iFrame.
iMod (key_pred_set (nroot.@"keys".@"sym") (λ _ _, False%I) with "token")
    as "[#? token]"; try solve_ndisj.
iMod (key_pred_set (nroot.@"keys".@"enc") (λ kt _, ⌜kt = Enc⌝)%I with "token")
    as "[#? token]"; try solve_ndisj.
iMod (key_pred_set (nroot.@"keys".@"sig") (λ kt _, ⌜kt = Dec⌝)%I with "token")
    as "[#? token]"; try solve_ndisj.
rewrite honest_unseal /honest_def big_sepS_empty. iFrame.
rewrite phase_auth_unseal /phase_auth_def. iFrame.
iSplitL; last by iFrame; eauto. do 3!iSplitR => //.
iSplitR "names_auth".
  iApply inv_alloc.
  iModIntro. iExists 0, {[0 := ∅]}, ∅, ∅, ε. iFrame.
  rewrite !big_sepS_empty. do !iSplit => //.
  iIntros "!> %m". by rewrite discrete_fun_lookup_empty big_opS_empty.
iApply inv_alloc. iExists ∅. rewrite fmap_empty /=. iFrame.
by rewrite dom_empty_L big_sepS_empty.
Qed.
