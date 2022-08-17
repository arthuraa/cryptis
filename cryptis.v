From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map excl.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term nown.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cryptisN := nroot.@"cryptis".

Section Cryptis.

Class cryptisG Σ := CryptisG {
  cryptis_inG       :> savedPredG Σ term;
  cryptis_key_inG   :> savedPredG Σ (key_type * term);
  cryptis_enc_inG   :> savedPredG Σ (term * term);
  cryptis_hon_inG   :> versionG Σ (gsetO term);
  cryptis_key_name  : gname;
  cryptis_hash_name : gname;
  cryptis_enc_name  : gname;
  cryptis_hon_name  : gname;
}.

Definition cryptisΣ : gFunctors :=
  #[savedPredΣ term;
    savedPredΣ (key_type * term);
    savedPredΣ (term * term);
    versionΣ (gsetO term)].

Class cryptisPreG Σ := CryptisPreG {
  cryptis_preG :> savedPredG Σ term;
  cryptis_key_preG :> savedPredG Σ (key_type * term);
  cryptis_enc_preG :> savedPredG Σ (term * term);
  cryptis_hon_preG :> versionG Σ (gsetO term);
}.

Global Instance subG_cryptisPreG Σ : subG cryptisΣ Σ → cryptisPreG Σ.
Proof. solve_inG. Qed.

Context (Σ : gFunctors).
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).
Notation nonce := loc.
Implicit Types a : loc.
Implicit Types γ : gname.
Implicit Types N : namespace.

Context `{!heapGS Σ, !cryptisG Σ}.

Definition pnonce a : iProp :=
  ∃ γ P, meta a (nroot.@"nonce") γ ∧ saved_pred_own γ P ∧ ▷ □ P (TNonce a).

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
  ∃ γ, own cryptis_enc_name (namespace_map_data N (to_agree γ)) ∧
       saved_pred_own γ (fun '(k, t) => Φ k t).

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
by iApply (saved_pred_agree _ _ _ (k, t) with "own1 own2").
Qed.

Lemma enc_pred_set E (N : namespace) Φ :
  ↑N ⊆ E →
  enc_pred_token E ==∗
  enc_pred N Φ ∗
  enc_pred_token (E ∖ ↑N).
Proof.
iIntros (?) "token".
iMod (saved_pred_alloc (λ '(k, t), Φ k t)) as (γ) "own".
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
       saved_pred_own γ (λ '(kt, t), φ kt t).

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
by iApply (saved_pred_agree _ _ _ (kt, t) with "own1 own2").
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
iMod (saved_pred_alloc (λ '(kt, t), P kt t)) as (γ) "own".
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
       saved_pred_own γ P.

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
by iApply (saved_pred_agree _ _ _ t with "own1 own2").
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
iMod (saved_pred_alloc P) as (γ) "own".
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

Lemma sterm_nonces_of_term t :
  sterm t ⊣⊢ [∗ set] a ∈ nonces_of_term t, sterm (TNonce a).
Proof.
rewrite {1}unlock !big_sepS_forall; iSplit; iIntros "#H %a %a_t".
- by rewrite sterm_TNonce; iApply "H".
- by rewrite -sterm_TNonce; iApply "H".
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
    case/Permutation_singleton_r: e => -> ->; eauto.
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
  term_meta_token_timeless :> ∀ t E,
    Timeless (term_meta_token t E);
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

Next Obligation. by case=> *; apply _. Qed.

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

Implicit Types dq : dfrac.

Definition honest_auth_def dq n (X : gset term) : iProp :=
  version_auth cryptis_hon_name dq n X ∗
  [∗ set] t ∈ X, sterm t.
Definition honest_auth_aux : seal honest_auth_def. by eexists. Qed.
Definition honest_auth := unseal honest_auth_aux.
Lemma honest_auth_eq : honest_auth = honest_auth_def.
Proof. exact: seal_eq. Qed.

Definition honest_frag_def n (X : gset term) : iProp :=
  version_frag cryptis_hon_name n X ∗
  [∗ set] t ∈ X, sterm t.
Definition honest_frag_aux : seal honest_frag_def. by eexists. Qed.
Definition honest_frag := unseal honest_frag_aux.
Lemma honest_frag_eq : honest_frag = honest_frag_def.
Proof. exact: seal_eq. Qed.

(* FIXME: Right now, we consider 1/2 to be complete ownership of the honest_auth
resource, because we want to store 1/2 of it in the invariant. It would be more
convenient for users if 1 represented complete ownership instead. *)
Notation "●H{ dq | n } a" :=
  (honest_auth dq n a) (at level 20, format "●H{ dq | n }  a").
Notation "●H{# q | n } a" :=
  (honest_auth (DfracOwn q) n a) (at level 20, format "●H{# q | n }  a").
Notation "●H□{ n } a" := (honest_auth (DfracDiscarded) n a)
  (at level 20, format "●H□{ n }  a").
Notation "●H{ n } a" := (honest_auth (DfracOwn (1 / 2)) n a)
  (at level 20, format "●H{ n }  a").
Notation "◯H{ n } a" := (honest_frag n a)
  (at level 20, format "◯H{ n }  a").

Definition secret t : iProp :=
  (|==> pterm t) ∧ (pterm t -∗ ◇ False).

Definition honest_inv : iProp :=
  ∃ n X, (●H{n} X) ∗ [∗ set] t ∈ X, secret t.

Definition cryptis_ctx : iProp :=
  key_pred (nroot.@"keys".@"sym") (λ _  _, False%I) ∗
  key_pred (nroot.@"keys".@"enc") (λ kt _, ⌜kt = Enc⌝)%I ∗
  key_pred (nroot.@"keys".@"sig") (λ kt _, ⌜kt = Dec⌝)%I ∗
  inv (cryptisN.@"honest") honest_inv.

#[global]
Instance cryptis_ctx_persistent : Persistent cryptis_ctx.
Proof. apply _. Qed.

Lemma honest_auth_dfrac_op dq1 dq2 n X :
  ●H{dq1 ⋅ dq2|n} X ⊣⊢ ●H{dq1|n} X ∗ ●H{dq2|n} X.
Proof.
rewrite honest_auth_eq /honest_auth_def; iSplit.
- by iIntros "[[??] #?]"; iFrame; eauto.
- iIntros "[[L _] [?#?]]"; iFrame; eauto.
  iSplit => //. by iSplitL "L".
Qed.

#[global]
Instance from_sep_honest_auth dq1 dq2 n X :
  FromSep (●H{dq1 ⋅ dq2|n} X) (●H{dq1|n} X) (●H{dq2|n} X).
Proof. by rewrite /FromSep honest_auth_dfrac_op. Qed.

#[global]
Instance into_sep_honest_auth dq1 dq2 n X :
  IntoSep (●H{dq1 ⋅ dq2|n} X) (●H{dq1|n} X) (●H{dq2|n} X).
Proof. by rewrite /IntoSep honest_auth_dfrac_op. Qed.

Lemma honest_auth_discard dq n X : ●H{dq|n} X ==∗ ●H□{n} X.
Proof.
rewrite honest_auth_eq. iIntros "[own #s_X]".
iMod (version_auth_discard with "own") as "own".
by iFrame.
Qed.

#[global]
Instance honest_auth_discarded_persistent n X : Persistent (●H□{n} X).
Proof. rewrite honest_auth_eq. apply _. Qed.

#[global]
Instance honest_frag_persistent n X : Persistent (◯H{n} X).
Proof. rewrite honest_frag_eq. apply _. Qed.

Lemma honest_auth_sterm dq n X : ●H{dq|n} X -∗ [∗ set] t ∈ X, sterm t.
Proof. rewrite honest_auth_eq. by iIntros "(_ & ?)". Qed.

Lemma honest_auth_frag dq n X : ●H{dq|n} X -∗ ◯H{n} X.
Proof.
rewrite honest_auth_eq honest_frag_eq.
iIntros "(ver & #s_X)". iSplit => //.
by iApply version_auth_frag.
Qed.

(* FIXME: use this formulation for version as well *)
Lemma honest_auth_frag_agree dq n m X Y :
  ●H{dq|n} X -∗ ◯H{m} Y -∗ ⌜m ≤ n ∧ (n ≤ m → X = Y)⌝.
Proof.
rewrite honest_auth_eq honest_frag_eq.
iIntros "(auth & _) (frag & _)".
iPoseProof (version_auth_frag_num with "auth frag") as "%mn".
iSplit => //. iIntros "%nm". have -> : m = n by lia.
iPoseProof (version_auth_frag_agree with "auth frag") as "%e".
iPureIntro. by apply leibniz_equiv_iff in e.
Qed.

Lemma honest_auth_frag_agree_eq dq n X Y :
  ●H{dq|n} X -∗ ◯H{n} Y -∗ ⌜X = Y⌝.
Proof.
iIntros "auth frag".
iDestruct (honest_auth_frag_agree with "auth frag") as "[_ %e]".
iPureIntro. eauto.
Qed.

Lemma honest_auth_agree dq1 dq2 n1 n2 X1 X2 :
  ●H{dq1|n1} X1 -∗ ●H{dq2|n2} X2 -∗ ⌜n1 = n2 ∧ X1 = X2⌝.
Proof.
rewrite honest_auth_eq.
iIntros "(auth1 & _) (auth2 & _)".
iDestruct (version_auth_agree with "auth1 auth2") as "[%en %eX]".
iSplit => //. iPureIntro. by apply leibniz_equiv_iff in eX.
Qed.

Lemma honest_frag_agree n X Y : ◯H{n} X -∗ ◯H{n} Y -∗ ⌜X = Y⌝.
Proof.
rewrite honest_frag_eq.
iIntros "[ver1 _] [ver2 _]".
iPoseProof (version_frag_agree with "ver1 ver2") as "%e".
iPureIntro. by apply leibniz_equiv_iff in e.
Qed.

Lemma honest_acc E dq n X :
  ↑cryptisN.@"honest" ⊆ E →
  cryptis_ctx -∗
  ●H{dq|n} X ={E, E ∖ ↑cryptisN.@"honest"}=∗
    ●H{dq|n} X ∗
    ●H{n} X ∗
    ▷ ([∗ set] t ∈ X, secret t) ∗
    (▷ honest_inv ={E ∖ ↑cryptisN.@"honest",E}=∗ True).
Proof.
rewrite honest_auth_eq.
iIntros "%sub (_ & _ & _ & #ctx) [ver #term_X]".
iMod (inv_acc with "ctx") as "[inv close]" => //.
iDestruct "inv" as "(%n' & %X' & ver' & sec_X)".
rewrite honest_auth_eq. iDestruct "ver'" as "[>ver' _]".
iPoseProof (version_auth_agree with "ver' ver") as "#[-> %e]".
rewrite leibniz_equiv_iff in e. rewrite {X'}e.
iFrame. iModIntro. by eauto.
Qed.

Lemma honest_acc_update Y E n X :
  ↑cryptisN.@"honest" ⊆ E →
  cryptis_ctx -∗
  ●H{n} X ={E, E ∖ ↑cryptisN.@"honest"}=∗
    ([∗ set] t ∈ X, sterm t) ∗
  ▷ ([∗ set] t ∈ X, secret t) ∗
  (([∗ set] t ∈ Y, sterm t) ∗ ▷ ([∗ set] t ∈ Y, secret t)
    ={E ∖ ↑cryptisN.@"honest",E}=∗ ●H{S n} Y).
Proof.
iIntros "%sub #ctx hon".
iMod (honest_acc with "ctx hon") as "(hon & hon' & sec_X & close)" => //.
iFrame.
iCombine "hon hon'" as "hon". rewrite dfrac_op_own Qp_half_half.
rewrite honest_auth_eq. iDestruct "hon" as "(ver & #s_X)".
iMod (version_update Y with "ver") as "ver".
iModIntro. iSplit => //. iIntros "[#term_Y sec_Y]".
rewrite -{1}Qp_half_half -dfrac_op_own. iDestruct "ver" as "[ver ver']".
iFrame.
iMod ("close" with "[ver sec_Y]") as "_"; last eauto.
iModIntro. iExists (S n), Y. rewrite honest_auth_eq. by iFrame.
Qed.

Lemma honest_acc_same E dq n X :
  ↑cryptisN.@"honest" ⊆ E →
  cryptis_ctx -∗
  ●H{dq|n} X ={E,E ∖ ↑cryptisN.@"honest"}=∗
    ([∗ set] t ∈ X, sterm t) ∗
  ▷ ([∗ set] t ∈ X, secret t) ∗
  (▷ ([∗ set] t ∈ X, secret t) ={E ∖ ↑cryptisN.@"honest",E}=∗ ●H{dq|n} X).
Proof.
iIntros "%sub #ctx hon".
iMod (honest_acc with "ctx hon") as "(hon & hon' & sec_X & close)" => //.
iFrame. iModIntro. iSplit => //; first by iApply honest_auth_sterm.
iIntros "sec_X". iMod ("close" with "[hon' sec_X]") as "_"; last eauto.
iModIntro. iExists n, X. by iFrame.
Qed.

Lemma honest_pterm E dq t n X :
  ↑cryptisN.@"honest" ⊆ E →
  t ∈ X →
  cryptis_ctx -∗
  ●H{dq|n} X -∗
  pterm t ={E}=∗
  ▷ ◇ False.
Proof.
iIntros "%sub %t_X #ctx hon #p_t".
iMod (honest_acc_same with "ctx hon") as "(#term_X & sec_X & close)" => //.
iAssert (▷ ◇ False)%I with "[sec_X]" as "#contra".
{ iClear "term_X". rewrite big_sepS_delete //.
  iDestruct "sec_X" as "([_ I] & _)".
  iModIntro. by iApply "I". }
iMod ("close" with "sec_X") as "hon". eauto.
Qed.

Lemma honest_unionE E n X Y :
  ↑cryptisN.@"honest" ⊆ E →
  X ## Y →
  cryptis_ctx -∗
  ●H{n} (X ∪ Y) ={E}=∗
  ●H{S n} X ∗ ▷ [∗ set] t ∈ Y, secret t.
Proof.
iIntros "%sub %X_Y #ctx hon".
iMod (honest_acc_update X with "ctx hon") as "(#s_XY & I & close)" => //.
rewrite !big_sepS_union //.
iDestruct "s_XY" as "[s_X _]".
iDestruct "I" as "[I IY]".
iMod ("close" with "[s_X I]") as "hon"; by iFrame.
Qed.

Lemma honest_delete E t n X :
  ↑cryptisN.@"honest" ⊆ E →
  t ∈ X →
  cryptis_ctx -∗
  ●H{n} X ={E}=∗
  ●H{S n} (X ∖ {[t]}) ∗ ▷ secret t.
Proof.
iIntros "%sub %t_X #ctx hon".
rewrite {1}[X](union_difference_singleton_L t) // [_ ∪ _]comm_L.
iMod (honest_unionE with "ctx hon") as "hon" => //.
  set_solver.
by rewrite big_sepS_singleton.
Qed.

Lemma compromise_honest E n X :
  ↑cryptisN.@"honest" ⊆ E →
  cryptis_ctx -∗
  ●H{n} X ={E}=∗
  ●H{S n} ∅ ∗ ▷ |==> [∗ set] t ∈ X, pterm t.
Proof.
iIntros "%sub #ctx hon".
rewrite {1}(_ : X = ∅ ∪ X); last set_solver.
iMod (honest_unionE with "ctx hon") as "[hon sec]" => //.
iFrame. iModIntro. iModIntro. iApply big_sepS_bupd.
iApply (big_sepS_mono with "sec").
by iIntros "%t % [? _]".
Qed.

Lemma honest_unionI Y E n X :
  ↑cryptisN.@"honest" ⊆ E →
  X ## Y →
  cryptis_ctx -∗
  ●H{n} X -∗
  ([∗ set] t ∈ Y, sterm t) -∗
  ▷ ([∗ set] t ∈ Y, secret t) ={E}=∗
  ●H{S n} (X ∪ Y).
Proof.
iIntros "%sub %t_X #ctx hon #s_Y sec".
iMod (honest_acc_update (X ∪ Y) with "ctx hon") as "(#s_X & I & close)" => //.
iApply "close". rewrite !big_sepS_union //. by iFrame; iSplit.
Qed.

Lemma honest_insert t E n X :
  ↑cryptisN.@"honest" ⊆ E →
  t ∉ X →
  cryptis_ctx -∗
  ●H{n} X -∗
  sterm t -∗
  ▷ secret t ={E}=∗
  ●H{S n} (X ∪ {[t]}).
Proof.
iIntros "%sub %t_X #ctx hon #s_t sec".
iApply (honest_unionI with "[//] [hon]") => //.
- set_solver.
- by rewrite big_sepS_singleton.
- by rewrite big_sepS_singleton.
Qed.

End Cryptis.

Arguments cryptis_enc_name {Σ _}.
Arguments enc_pred {Σ _ _}.
Arguments enc_pred_set {Σ _ _ _} N Φ.
Arguments enc_pred_token_difference {Σ _ _} E1 E2.
Arguments cryptis_hash_name {Σ _}.
Arguments hash_pred {Σ _ _}.
Arguments hash_pred_set {Σ _ _ _} N P.
Arguments hash_pred_token_difference {Σ _ _} E1 E2.
Arguments cryptis_key_name {Σ _}.
Arguments key_pred {Σ _ _}.
Arguments key_pred_set {Σ _ _ _} N P.
Arguments key_pred_token_difference {Σ _ _} E1 E2.
Arguments term_meta_set {Σ _ _ _ _ _ _} E t x N.
Arguments term_meta_token_difference {Σ _ _ _} t E1 E2.
Arguments nonce_term_meta Σ {_}.
Arguments nonce_meta_token {Σ _}.
Arguments honest_inv {Σ _ _}.
Arguments cryptis_ctx {Σ _ _}.
Arguments TermMeta Σ term_meta term_meta_token : assert.

Notation "●H{ dq | n } a" :=
  (honest_auth dq n a) (at level 20, format "●H{ dq | n }  a").
Notation "●H{# q | n } a" :=
  (honest_auth (DfracOwn q) n a) (at level 20, format "●H{# q | n }  a").
Notation "●H□{ n } a" := (honest_auth (DfracDiscarded) n a)
  (at level 20, format "●H□{ n }  a").
Notation "●H{ n } a" := (honest_auth (DfracOwn (1 / 2)) n a)
  (at level 20, format "●H{ n }  a").
Notation "◯H{ n } a" := (honest_frag n a)
  (at level 20, format "◯H{ n }  a").

Lemma cryptisG_alloc `{!heapGS Σ} E :
  cryptisPreG Σ →
  ⊢ |={E}=> ∃ (H : cryptisG Σ),
             cryptis_ctx ∗
             enc_pred_token ⊤ ∗
             key_pred_token (⊤ ∖ ↑nroot.@"keys") ∗
             hash_pred_token ⊤ ∗
             ●H{0} ∅.
Proof.
move=> ?; iStartProof.
iMod (own_alloc (reservation_map_token ⊤)) as (γ_enc) "own_enc".
  apply reservation_map_token_valid.
iMod (own_alloc (reservation_map_token ⊤)) as (γ_key) "own_key".
  apply reservation_map_token_valid.
iMod (own_alloc (reservation_map_token ⊤)) as (γ_hash) "own_hash".
  apply reservation_map_token_valid.
iMod (version_alloc ∅) as (γ_hon) "ver".
pose (H := CryptisG _ _ _ _ γ_enc γ_key γ_hash γ_hon).
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
rewrite -{1}Qp_half_half -dfrac_op_own.
iDestruct "ver" as "[ver ver']". rewrite honest_auth_eq. iFrame.
rewrite big_sepS_empty. iSplitL => //.
do 3!iSplitR => //.
iApply inv_alloc.
iModIntro. iExists 0, ∅.
rewrite honest_auth_eq. iFrame. by rewrite !big_sepS_empty.
Qed.
