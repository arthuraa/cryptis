From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list namespace_map.
From iris.base_logic.lib Require Import auth saved_prop.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib term coGset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cryptisN := nroot.@"cryptis".

Section Resources.

Context (Σ : gFunctors).
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).
Notation nonce := loc.
Implicit Types a : loc.
Implicit Types γ : gname.

Context `{!heapG Σ}.

Class cryptoG := CryptoG {
  crypto_inG       :> savedPredG Σ term;
  crypto_nonce_inG :> savedPropG Σ;
  crypto_key_inG   :> savedPredG Σ (key_type * term);
  crypto_enc_inG   :> savedPredG Σ (term * term);
  crypto_key_name : gname;
  crypto_hash_name : gname;
  crypto_enc_name : gname;
}.

Context `{!cryptoG}.

Definition pnonce a : iProp :=
  ∃ γ P, meta a (nroot.@"nonce") γ ∧ saved_prop_own γ P ∧ ▷ □ P.

Global Instance Persistent_pnonce a : Persistent (pnonce a).
Proof. apply _. Qed.

Definition snonce a : iProp :=
  ∃ γ, meta a (nroot.@"nonce") γ.

Definition dh_pred (t t' : term) : iProp :=
  match t with
  | TNonce a =>
    ∃ γ φ, meta a (nroot.@"dh") γ ∧ saved_pred_own γ φ ∧ ▷ □ φ t'
  | _ => False
  end.

Global Instance Persistent_dh_pred t t' : Persistent (dh_pred t t').
Proof. case: t => *; apply _. Qed.

Definition enc_pred N Φ : iProp :=
  ∃ γ, own crypto_enc_name (namespace_map_data N (to_agree γ)) ∧
       saved_pred_own γ (fun '(k, t) => Φ k t).

Definition enc_pred_token E :=
  own crypto_enc_name (namespace_map_token E).

Lemma enc_pred_token_difference E1 E2 :
  E1 ⊆ E2 →
  enc_pred_token E2 ⊣⊢ enc_pred_token E1 ∗ enc_pred_token (E2 ∖ E1).
Proof.
move=> sub; rewrite /enc_pred_token.
by rewrite (namespace_map_token_difference E1 E2) // own_op.
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
move: valid; rewrite -namespace_map_data_op namespace_map_data_valid.
move=> /agree_op_invL' ->.
by iApply (saved_pred_agree _ _ _ (k, t) with "own1 own2").
Qed.

Lemma enc_pred_set E N Φ :
  ↑N ⊆ E →
  enc_pred_token E ==∗
  enc_pred N Φ.
Proof.
iIntros (?) "token".
iMod (saved_pred_alloc (λ '(k, t), Φ k t)) as (γ) "own".
iMod (own_update with "token").
  by eapply (namespace_map_alloc_update _ _ (to_agree γ)) => //.
by iModIntro; iExists γ; iSplit.
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
  ∃ γ, own crypto_key_name (namespace_map_data N (to_agree γ)) ∧
       saved_pred_own γ (λ '(kt, t), φ kt t).

Definition key_pred_token E :=
  own crypto_key_name (namespace_map_token E).

Lemma key_pred_token_difference E1 E2 :
  E1 ⊆ E2 →
  key_pred_token E2 ⊣⊢ key_pred_token E1 ∗ key_pred_token (E2 ∖ E1).
Proof.
move=> sub; rewrite /key_pred_token.
by rewrite (namespace_map_token_difference E1 E2) // own_op.
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
move: valid; rewrite -namespace_map_data_op namespace_map_data_valid.
move=> /agree_op_invL' ->.
by iApply (saved_pred_agree _ _ _ (kt, t) with "own1 own2").
Qed.

Lemma key_pred_set E N P :
  ↑N ⊆ E →
  key_pred_token E ==∗
  key_pred N P.
Proof.
iIntros (?) "token".
iMod (saved_pred_alloc (λ '(kt, t), P kt t)) as (γ) "own".
iMod (own_update with "token").
  by eapply (namespace_map_alloc_update _ _ (to_agree γ)) => //.
by iModIntro; iExists γ; iSplit.
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
  ∃ γ, own crypto_hash_name (namespace_map_data N (to_agree γ)) ∧
       saved_pred_own γ P.

Definition hash_pred_token E :=
  own crypto_hash_name (namespace_map_token E).

Lemma hash_pred_token_difference E1 E2 :
  E1 ⊆ E2 →
  hash_pred_token E2 ⊣⊢ hash_pred_token E1 ∗ hash_pred_token (E2 ∖ E1).
Proof.
move=> sub; rewrite /hash_pred_token.
by rewrite (namespace_map_token_difference E1 E2) // own_op.
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
move: valid; rewrite -namespace_map_data_op namespace_map_data_valid.
move=> /agree_op_invL' ->.
by iApply (saved_pred_agree _ _ _ t with "own1 own2").
Qed.

Lemma hash_pred_set E N P :
  ↑N ⊆ E →
  hash_pred_token E ==∗
  hash_pred N P.
Proof.
iIntros (?) "token".
iMod (saved_pred_alloc P) as (γ) "own".
iMod (own_update with "token").
  by eapply (namespace_map_alloc_update _ _ (to_agree γ)) => //.
by iModIntro; iExists γ; iSplit.
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

Fact sterm_key : unit. Proof. exact: tt. Qed.

Definition sterm : term → iProp :=
  locked_with sterm_key (
    λ t, [∗ set] a ∈ nonces_of_term t, snonce a
  )%I.

Canonical sterm_unlock := [unlockable of sterm].

Global Instance Persistent_sterm t : Persistent (sterm t).
Proof. rewrite unlock; apply _. Qed.

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

Fixpoint pterm_aux n t : iProp :=
  if n is S n then
    sterm t ∧ (
     (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, pterm_aux n t')
     ∨ match t with
       | TNonce a => pnonce a
       | TKey kt t => wf_key kt t
       | THash t => wf_hash t
       | TEnc k t => wf_enc k t ∧ □ (pterm_aux n (TKey Dec k) → pterm_aux n t)
       | TExp' _ pts _ => [∗ list] pt ∈ pts, dh_pred (fold_term pt) t
       | _ => False
       end%I
    )
  else False.

Global Instance Persistent_pterm_aux n t : Persistent (pterm_aux n t).
Proof.
elim: n t => [|n IH] /=; first by apply _.
by case=>>; apply _.
Qed.

(** [pterm t] holds when the term [t] can be declared public. *)

Fact pterm_key : unit. Proof. exact: tt. Qed.
Definition pterm : term → iProp :=
  locked_with pterm_key (λ t, pterm_aux (tsize t) t).
Canonical pterm_unlock := [unlockable of pterm].

Global Instance Persistent_pterm t : Persistent (pterm t).
Proof. rewrite unlock; apply _. Qed.

(* MOVE *)
Lemma and_proper_L (P : Prop) (φ ψ : iProp) :
  (P → φ ⊣⊢ ψ) →
  ⌜P⌝ ∧ φ ⊣⊢ ⌜P⌝ ∧ ψ.
Proof.
by move=> φ_ψ; apply: (anti_symm _); iIntros "[% ?]";
rewrite φ_ψ; eauto.
Qed.
(* /MOVE *)

Lemma pterm_aux_eq n t : tsize t ≤ n → pterm_aux n t ⊣⊢ pterm t.
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

(* TODO: Merge with pterm_aux_eq *)
Lemma pterm_eq t :
  pterm t ⊣⊢
  sterm t ∧ (
      (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, pterm t')
     ∨ match t with
       | TNonce a => pnonce a
       | TKey kt t => wf_key kt t
       | THash t => wf_hash t
       | TEnc k t => wf_enc k t ∧ □ (pterm (TKey Dec k) → pterm t)
       | TExp' _ pts _ =>
         [∗ list] pt ∈ pts, dh_pred (fold_term pt) t
       | _ => False
       end%I
  ).
Proof.
rewrite {1}[pterm]unlock.
case e_st: (tsize t) => [|m] /=.
  move: (ssrbool.elimT ssrnat.ltP (tsize_gt0 t)) => ?; lia.
apply: bi.and_proper => //.
apply: bi.or_proper.
- apply: bi.exist_proper => T.
  apply: and_proper_L => T_t.
  apply: big_sepS_proper => t' T_t'.
  move: (decompose_tsize T_t T_t') => ?.
  rewrite pterm_aux_eq //; lia.
- case: (t) e_st =>> //= e_st.
  rewrite tsize_eq -ssrnat.plusE in e_st.
  apply: bi.and_proper => //.
  rewrite !pterm_aux_eq  ?[tsize (TKey _ _)]tsize_eq //=; lia.
Qed.

Lemma pterm_sterm t : pterm t -∗ sterm t.
Proof. rewrite pterm_eq; by iIntros "[??]". Qed.

(* MOVE *)
Lemma big_sepS_union_pers (PROP : bi) `{!BiAffine PROP, !EqDecision A, !Countable A}
  (Φ : A → PROP) (X Y : gset A) :
  (∀ x, Persistent (Φ x)) →
  ([∗ set] x ∈ (X ∪ Y), Φ x) ⊣⊢ ([∗ set] x ∈ X, Φ x) ∧ ([∗ set] x ∈ Y, Φ x).
Proof.
move=> ?; rewrite !big_sepS_forall.
apply: (anti_symm _).
- iIntros "H"; iSplit; iIntros "%a %a_in"; iApply "H";
  iPureIntro; set_solver.
- iIntros "H %x %x_XY".
  case/elem_of_union: x_XY => [x_X|x_Y].
  + by iDestruct "H" as "[H _]"; iApply "H".
  + by iDestruct "H" as "[_ H]"; iApply "H".
Qed.

Lemma big_sepS_union_list_pers
  (PROP : bi) `{!BiAffine PROP, !EqDecision A, !Countable A}
  (Φ : A → PROP) (X : list (gset A)) :
  (∀ x, Persistent (Φ x)) →
  ([∗ set] x ∈ ⋃ X, Φ x) ⊣⊢ ([∗ list] X ∈ X, [∗ set] x ∈ X, Φ x).
Proof.
move=> ?; rewrite big_sepS_forall big_sepL_forall.
apply: (anti_symm _).
- iIntros "H %k %Y %X_k"; rewrite big_sepS_forall; iIntros "%x %x_Y".
  iApply "H"; iPureIntro.
  apply/elem_of_union_list; exists Y; split => //.
  by rewrite elem_of_list_lookup; eauto.
- iIntros "H %x %x_X".
  case/elem_of_union_list: x_X => Y [Y_X x_Y].
  case/elem_of_list_lookup: Y_X => k X_k.
  iSpecialize ("H" $! _ _ X_k).
  by rewrite big_sepS_forall; iApply "H".
Qed.
(* /MOVE *)

Lemma sterm_TInt n : sterm (TInt n) ⊣⊢ True.
Proof. by rewrite unlock nonces_of_term_eq /= big_sepS_empty. Qed.

Lemma sterm_TPair t1 t2 : sterm (TPair t1 t2) ⊣⊢ sterm t1 ∧ sterm t2.
Proof.
by rewrite unlock nonces_of_term_eq /= !big_sepS_union_pers.
Qed.

Lemma sterm_TNonce a : sterm (TNonce a) ⊣⊢ snonce a.
Proof.
by rewrite unlock nonces_of_term_eq /= big_sepS_singleton.
Qed.

Lemma sterm_TKey kt t : sterm (TKey kt t) ⊣⊢ sterm t.
Proof. by rewrite unlock nonces_of_term_eq /=. Qed.

Lemma sterm_TEnc k t : sterm (TEnc k t) ⊣⊢ sterm k ∧ sterm t.
Proof.
by rewrite unlock nonces_of_term_eq /= !big_sepS_union_pers.
Qed.

Lemma sterm_THash t : sterm (THash t) ⊣⊢ sterm t.
Proof. by rewrite unlock nonces_of_term_eq /=. Qed.

Lemma sterm_TExp t ts : sterm (TExp t ts) ⊣⊢ sterm t ∧ [∗ list] t' ∈ ts, sterm t'.
Proof.
rewrite unlock nonces_of_term_TExp big_sepS_union_pers.
by rewrite big_sepS_union_list_pers big_sepL_fmap.
Qed.

Lemma sterm_texp t1 t2 :
  sterm t1 -∗
  sterm t2 -∗
  sterm (Spec.texp t1 t2).
Proof.
elim: t1;
try by move=> *; rewrite /= !sterm_TInt; iIntros "*"; eauto.
move=> t1 _ ts1 _ _ /=; rewrite Spec.texpA.
iIntros "s_1 s_2".
rewrite !sterm_TExp /=.
by iDestruct "s_1" as "[??]"; eauto.
Qed.

Lemma pterm_TInt n : pterm (TInt n) ⊣⊢ True.
Proof.
apply: (anti_symm _); iIntros "_" => //.
rewrite pterm_eq sterm_TInt; iSplit => //.
iLeft; iExists ∅; rewrite big_sepS_empty; iSplit => //.
by iPureIntro; econstructor.
Qed.

Lemma pterm_TPair t1 t2 : pterm (TPair t1 t2) ⊣⊢ pterm t1 ∧ pterm t2.
Proof.
apply: (anti_symm _); iIntros "#Ht" => //.
- rewrite pterm_eq sterm_TPair.
  iDestruct "Ht" as "([Ht1 Ht2] & publ)".
  iDestruct "publ" as "[publ | publ]" => //=.
  iDestruct "publ" as (T) "[%dec publ]".
  case: dec => //= {}t1 {}t2 -> [-> ->].
  by rewrite big_sepS_union_pers !big_sepS_singleton.
- iDestruct "Ht" as "[Ht1 Ht2]".
  rewrite [pterm (TPair t1 t2)]pterm_eq sterm_TPair -!pterm_sterm.
  iSplit; eauto.
  iLeft; iExists _; iSplit.
    iPureIntro; by econstructor.
  by rewrite big_sepS_union_pers !big_sepS_singleton; eauto.
Qed.

Lemma pterm_TNonce a : pterm (TNonce a) ⊣⊢ pnonce a.
Proof.
apply: (anti_symm _); iIntros "Ht".
- rewrite pterm_eq; iDestruct "Ht" as "[_ Ht]".
  iDestruct "Ht" as "[publ | ?]" => //.
  iDestruct "publ" as (T) "[%dec _]".
  by case: dec.
- rewrite pterm_eq; iSplit; eauto.
  rewrite sterm_TNonce /pnonce /snonce.
  iDestruct "Ht" as (γ P) "# (? & ? )".
  by iExists _; eauto.
Qed.

Lemma pterm_TKey kt t :
  pterm (TKey kt t) ⊣⊢ pterm t ∨ sterm t ∧ wf_key kt t.
Proof.
apply: (anti_symm _).
- rewrite pterm_eq sterm_TKey; iDestruct 1 as "[Ht publ]".
  iDestruct "publ" as "[publ | publ]" => //.
  + iDestruct "publ" as (T) "[%dec publ]".
    case: dec => //= {}kt {}t -> [-> ->].
    by rewrite big_sepS_singleton; eauto.
  + by eauto.
- iDestruct 1 as "# [publ | [s_t publ]]".
    rewrite [pterm (TKey _ _)]pterm_eq sterm_TKey -pterm_sterm.
    iSplit => //; iLeft.
    iExists {[t]}; iSplit; first by iPureIntro; econstructor.
    by rewrite big_sepS_singleton.
  rewrite pterm_eq; iSplit; eauto.
  by rewrite unlock nonces_of_term_eq /=.
Qed.

Lemma pterm_TEnc k t :
  pterm (TEnc k t) ⊣⊢
  pterm (TKey Enc k) ∧ pterm t ∨
  sterm (TEnc k t) ∧ wf_enc k t ∧ □ (pterm (TKey Dec k) → pterm t).
Proof.
apply: (anti_symm _).
- rewrite pterm_eq sterm_TEnc.
  iDestruct 1 as "[[Hk Ht] publ]".
  iDestruct "publ" as "[publ | publ]".
  + iDestruct "publ" as (T) "[%dec ?]".
    case: dec => // {}k {}t -> [-> ->].
    by rewrite big_sepS_union_pers !big_sepS_singleton; iLeft.
  + by eauto.
- iDestruct 1 as "# [[Hk Ht] | (Ht & inv & #impl)]".
  + rewrite [pterm (TEnc _ _)]pterm_eq sterm_TEnc.
    rewrite -[sterm k](sterm_TKey Enc k) -!pterm_sterm.
    iSplit; eauto; iLeft.
    iExists {[TKey Enc k; t]}; rewrite big_sepS_union_pers !big_sepS_singleton.
    iSplit; eauto; iPureIntro; by econstructor.
  + rewrite [pterm (TEnc k t)]pterm_eq; iSplit => //=.
    by eauto.
Qed.

Lemma pterm_THash t :
  pterm (THash t) ⊣⊢ pterm t ∨ sterm t ∧ wf_hash t.
Proof.
apply: (anti_symm _).
- rewrite pterm_eq sterm_THash.
  iDestruct 1 as "[Ht [publ | publ]]" => //; eauto.
  iDestruct "publ" as (T) "[%dec ?]".
  case: dec => //= {}t -> [->].
  by rewrite big_sepS_singleton; eauto.
- iDestruct 1 as "[Ht | [? publ]]".
    rewrite [pterm (THash _)]pterm_eq sterm_THash -pterm_sterm.
    iSplit => //=; iLeft.
    iExists {[t]}; rewrite big_sepS_singleton; iSplit => //.
    iPureIntro; by econstructor.
  rewrite pterm_eq unlock; iSplit.
    by rewrite nonces_of_term_eq //=.
  by eauto.
Qed.

Lemma pterm_TExp t ts :
  pterm (TExp t ts) ⊣⊢
  (∃ t' ts', ⌜ts ≡ₚ t' :: ts'⌝ ∧ pterm (TExp t ts') ∧ pterm t') ∨
  sterm (TExp t ts) ∧ [∗ list] t' ∈ ts, dh_pred t' (TExp t ts).
Proof.
apply: (anti_symm _).
- rewrite pterm_eq sterm_TExp.
  iDestruct 1 as "[# [Ht Hts] [#publ | publ]]".
  + iDestruct "publ" as (T) "[%dec publ]".
    case: dec; try by move=>>; rewrite unlock.
    * move=> {}t -> /TExp_inj [-> e_ts] _.
      rewrite big_sepS_singleton; iRight; iSplit => //.
        by iSplit.
      by move/Permutation_nil: e_ts => ->.
    * move=> {}t ts1 t2 -> /TExp_inj [-> e_ts] _.
      iLeft; rewrite big_sepS_union_pers !big_sepS_singleton.
      by eauto.
  + case: TExpP => pts wf_pts e_pts; iRight; do 2?iSplit => //.
    rewrite [in X in ([∗ list] _ ∈ X, dh_pred _ _)%I]e_pts big_sepL_fmap.
    iApply (big_sepL_mono with "publ") => k t' _ /=.
    by rewrite unfold_termK.
- iDestruct 1 as "# [publ | publ]".
  + iDestruct "publ" as (t' ts') "[-> [Ht1 Ht2]]".
    rewrite [pterm (TExp _ (_ :: _))]pterm_eq sterm_TExp /=.
    iSplit.
      rewrite !pterm_sterm sterm_TExp /=.
      by iDestruct "Ht1" as "[??]"; eauto.
    iLeft.
    iExists {[TExp t ts'; t']}; rewrite big_sepS_union_pers !big_sepS_singleton.
    do !iSplit => //.
    iPureIntro.
    by apply: DExp1; eauto; rewrite is_exp_TExp.
  + iDestruct "publ" as "[s p]"; rewrite pterm_eq [sterm]unlock; iSplit=> //.
    case: TExpP => pts wf_pts e_pts; iRight.
    move: (TExp' _ _ _) => ?; rewrite e_pts big_sepL_fmap.
    by iApply (big_sepL_mono with "p") => ?? _ /=; rewrite unfold_termK.
Qed.

Lemma pterm_TExp0 t : pterm (TExp t []) ⊣⊢ sterm t.
Proof.
rewrite pterm_TExp; apply (anti_symm _); iIntros "#pub".
- iDestruct "pub" as "[pub | [pub ?]]"; eauto.
    iDestruct "pub" as (??) "[%contra _]".
    by move/Permutation_length: contra.
  by rewrite sterm_TExp; iDestruct "pub" as "[??]".
- iRight; iSplit => //.
  by rewrite sterm_TExp; iSplit.
Qed.

Lemma pterm_TExp1 t1 t2 :
  pterm (TExp t1 [t2]) ⊣⊢
  sterm t1 ∧ sterm t2 ∧ (pterm t2 ∨ dh_pred t2 (TExp t1 [t2])).
Proof.
rewrite pterm_TExp; apply: (anti_symm _); iIntros "#pub".
- iDestruct "pub" as "[pub | pub]" => //.
    iDestruct "pub" as (??) "(%e & p_t1 & p_t2)".
    symmetry in e.
    case/Permutation_singleton: e => -> ->; eauto.
    rewrite pterm_TExp0; iSplit => //.
    iSplit => //; eauto.
    by iApply pterm_sterm.
  by rewrite sterm_TExp /=; iDestruct "pub" as "[[?[??]] [??]]"; eauto.
- iDestruct "pub" as "(s1 & s2 & [pub | pub])".
    iLeft; iExists t2, []; rewrite pterm_TExp0; eauto.
  by iRight; rewrite /= sterm_TExp; do !iSplit => //=.
Qed.

Lemma pterm_TExp2 t1 t2 t3 :
  pterm (TExp t1 [t2; t3]) ⊣⊢
  pterm (TExp t1 [t2]) ∧ pterm t3 ∨
  pterm (TExp t1 [t3]) ∧ pterm t2 ∨
  sterm (TExp t1 [t2; t3]) ∧
  dh_pred t2 (TExp t1 [t2; t3]) ∧
  dh_pred t3 (TExp t1 [t2; t3]).
Proof.
rewrite pterm_TExp; apply: (anti_symm _); iIntros "#pub".
- rewrite /=; iDestruct "pub" as "[pub | (? & ? & ? & _)]" => //; eauto.
  iDestruct "pub" as (??) "(%e & p_t1 & p_t2)".
  by case: (Permutation_length_2_inv e) => [[-> ->] | [-> ->]]; eauto.
- iDestruct "pub" as "[[? ?] | [[? ?] | (? & ? & ?)]]".
  + iLeft; iExists t3, [t2]; do !iSplit => //.
    iPureIntro; apply: perm_swap.
  + by iLeft; iExists t2, [t3]; do !iSplit => //.
  + iRight; do !iSplit => //=.
Qed.

Lemma pterm_texp t1 t2 :
  pterm t1 -∗
  pterm t2 -∗
  pterm (Spec.texp t1 t2).
Proof.
elim: t1;
try by move=> *; rewrite /= !pterm_TInt; iIntros "*"; eauto.
move=> t1 _ ts1 _ _; iIntros "#p_t1 #p_t2".
rewrite Spec.texpA [pterm (TExp t1 (t2 :: ts1))]pterm_TExp.
by iLeft; iExists t2, ts1; eauto.
Qed.

Lemma pterm_to_list t ts :
  Spec.to_list t = Some ts →
  pterm t -∗ [∗ list] t' ∈ ts, pterm t'.
Proof.
elim/term_ind': t ts => //=.
  by case=> // ts [<-] /=; iIntros "?".
move=> t _ tl IH ts.
case e: (Spec.to_list tl) => [ts'|] // [<-] /=.
rewrite pterm_TPair /=; iIntros "[??]"; iFrame.
by iApply IH.
Qed.

Lemma sterm_to_list t ts :
  Spec.to_list t = Some ts →
  sterm t -∗ [∗ list] t' ∈ ts, sterm t'.
Proof.
elim/term_ind': t ts => //=.
  by case=> // ts [<-] /=; iIntros "?".
move=> t _ tl IH ts.
case e: (Spec.to_list tl) => [ts'|] // [<-] /=.
rewrite sterm_TPair /=; iIntros "[??]"; iFrame.
by iApply IH.
Qed.

Lemma pterm_of_list ts :
  pterm (Spec.of_list ts) ⊣⊢
  [∗ list] t ∈ ts, pterm t.
Proof.
rewrite Spec.of_list_eq.
elim: ts => [|t ts IH]; first by rewrite pterm_TInt.
by rewrite pterm_TPair /= IH bi.persistent_and_sep.
Qed.

Lemma sterm_of_list ts :
  sterm (Spec.of_list ts) ⊣⊢
  [∗ list] t ∈ ts, sterm t.
Proof.
rewrite Spec.of_list_eq.
elim: ts => [|t ts IH]; first by rewrite sterm_TInt.
by rewrite sterm_TPair /= IH bi.persistent_and_sep.
Qed.

Lemma pterm_tag N t : pterm (Spec.tag N t) ⊣⊢ pterm t.
Proof.
by rewrite Spec.tag_eq pterm_TPair pterm_TInt bi.emp_and.
Qed.

Lemma sterm_tag N t : sterm (Spec.tag N t) ⊣⊢ sterm t.
Proof.
by rewrite Spec.tag_eq sterm_TPair sterm_TInt bi.emp_and.
Qed.

Lemma pterm_TEncE N Φ k t :
  pterm (TEnc k (Spec.tag N t)) -∗
  enc_pred N Φ -∗
  pterm (TKey Enc k) ∧ pterm t ∨
  □ ▷ Φ k t ∧ sterm t ∧ □ (pterm (TKey Dec k) → pterm t).
Proof.
iIntros "#Ht #HΦ"; rewrite pterm_TEnc pterm_tag.
iDestruct "Ht" as "[[? Ht] | Ht]"; first by eauto.
rewrite sterm_TEnc sterm_tag.
iDestruct "Ht" as "([??] & inv & ?)".
iRight; iSplit; eauto; by iApply wf_enc_elim.
Qed.

Lemma pterm_TEncIS N Φ k t :
  sterm (TKey Enc k) -∗
  enc_pred N Φ -∗
  □ Φ k t -∗
  sterm t -∗
  □ (pterm (TKey Dec k) → pterm t) -∗
  pterm (TEnc k (Spec.tag N t)).
Proof.
iIntros "#Henc #HΦ #HΦt #Ht #Hdecl".
rewrite pterm_TEnc; iRight.
rewrite sterm_TEnc sterm_tag pterm_tag.
iSplit; first by rewrite sterm_TKey; eauto.
iSplit; eauto.
iExists N, t, Φ; eauto.
Qed.

Lemma pterm_TEncIP k t :
  pterm (TKey Enc k) -∗
  pterm t -∗
  pterm (TEnc k t).
Proof. by iIntros "? ?"; rewrite pterm_TEnc; eauto. Qed.

Section TermMeta.

Class TermMeta
  (term_meta : ∀ `{Countable L}, term → namespace → L → iProp)
  (term_meta_token : term → coPset → iProp) := {
  term_meta_timeless :> ∀ `{Countable L} t N (x : L),
    Timeless (term_meta t N x);
  term_meta_persistent :> ∀ `{Countable L} t N (x : L),
    Persistent (term_meta t N x);
  term_meta_set : ∀ `{Countable L} E t (x : L) N,
    ↑N ⊆ E →
    term_meta_token t E ==∗ term_meta t N x;
  term_meta_meta_token : ∀ `{Countable L} t (x : L) N E,
    ↑N ⊆ E →
    term_meta_token t E -∗ term_meta t N x -∗ False;
  term_meta_agree : ∀ `{Countable L} t N (x1 x2 : L),
    term_meta t N x1 -∗
    term_meta t N x2 -∗
    ⌜x1 = x2⌝;
  term_meta_token_difference : ∀ t (E1 E2 : coPset),
    E1 ⊆ E2 →
    term_meta_token t E2 ⊣⊢
    term_meta_token t E1 ∗ term_meta_token t (E2 ∖ E1);
}.

(* Using two locations is a bit ugly, but maybe more convenient *)

Definition nonce_meta `{Countable L} t N (x : L) : iProp :=
  match t with
  | TNonce a => ∃ a', meta a (nroot.@"meta") a' ∧ meta a' N x
  | _ => False
  end.

Definition nonce_meta_token t E : iProp :=
  match t with
  | TNonce a => ∃ a', meta a (nroot.@"meta") a' ∧ meta_token a' E
  | _ => False
  end.

Program Global Instance nonce_term_meta :
  TermMeta (@nonce_meta) nonce_meta_token.

Next Obligation. move=> ???; case=> *; apply _. Qed.

Next Obligation. move=> ???; case=> *; apply _. Qed.

Next Obligation.
move=> ??? E t x N; case: t; try by move=> *; iStartProof.
move=> a; iIntros (sub) "token"; rewrite /=.
iDestruct "token" as (a') "[meta_a' token]".
by iMod (meta_set E _ x with "token") as "meta"; eauto.
Qed.

Next Obligation.
move=> ???; case; try by move=> *; iStartProof.
move=> a x N E sub /=; iIntros "token meta".
iDestruct "token" as (a1) "[meta_a1 token]".
iDestruct "meta"  as (a2) "[meta_a2 meta]".
iPoseProof (meta_agree with "meta_a1 meta_a2") as "->".
by iDestruct (meta_meta_token with "token meta") as "[]".
Qed.

Next Obligation.
move=> ???; case; try by move=> *; iStartProof.
move=> a * /=; iIntros "meta1 meta2".
iDestruct "meta1" as (a1) "[meta_a1 meta1]".
iDestruct "meta2" as (a2) "[meta_a2 meta2]".
iPoseProof (meta_agree with "meta_a1 meta_a2") as "->".
by iApply (meta_agree with "meta1 meta2").
Qed.

Next Obligation.
case; try by move=> *; iSplit; [iIntros "[]"|iIntros "[[] ?]"].
move=> a ?? sub; iSplit.
- iDestruct 1 as (a') "[#meta_a' token]".
  rewrite meta_token_difference /=; eauto.
  iDestruct "token" as "[token1 token2]".
  by iSplitL "token1"; iExists a'; eauto.
- iDestruct 1 as "[token1 token2]".
  iDestruct "token1" as (a1) "[#meta_a1 token1]".
  iDestruct "token2" as (a2) "[#meta_a2 token2]".
  iPoseProof (meta_agree with "meta_a1 meta_a2") as "->".
  iExists a2; iSplit => //.
  by iApply meta_token_difference => //; iSplitL "token1".
Qed.

End TermMeta.

End Resources.

Arguments crypto_enc_name {Σ _}.
Arguments enc_pred {Σ _ _}.
Arguments enc_pred_set {Σ _ _ _} N Φ.
Arguments enc_pred_token_difference {Σ _ _} E1 E2.
Arguments crypto_hash_name {Σ _}.
Arguments hash_pred {Σ _ _}.
Arguments hash_pred_set {Σ _ _ _} N P.
Arguments hash_pred_token_difference {Σ _ _} E1 E2.
Arguments crypto_key_name {Σ _}.
Arguments key_pred {Σ _ _}.
Arguments key_pred_set {Σ _ _ _} N P.
Arguments key_pred_token_difference {Σ _ _} E1 E2.
Arguments term_meta_set {Σ _ _ _ _ _ _} E t x N.
Arguments term_meta_token_difference {Σ _ _ _} t E1 E2.
Arguments nonce_term_meta Σ {_}.
Arguments nonce_meta_token {Σ _}.
Arguments TermMeta Σ term_meta term_meta_token : assert.
