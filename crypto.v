From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list namespace_map.
From iris.base_logic.lib Require Import auth saved_prop.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib term coGset guarded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cryptoN := nroot.@"crypto".

Section Levels.

Inductive level := Pub | Sec.

Canonical levelO := leibnizO level.

Implicit Types lvl : level.

Global Instance level_eq_dec : EqDecision level.
Proof.
refine (λ lvl1 lvl2,
          match lvl1, lvl2 with
          | Pub, Pub | Sec, Sec => left eq_refl
          | _, _ => right _
          end); abstract intuition congruence.
Defined.

Definition bool_of_level lvl :=
  if lvl is Pub then false else true.

Definition level_of_bool (b : bool) :=
  if b then Sec else Pub.

Lemma bool_of_levelK : Cancel (=) level_of_bool bool_of_level.
Proof. by case. Qed.

Global Instance level_countable : Countable level.
Proof.
eapply @inj_countable'; last by eapply bool_of_levelK.
apply _.
Qed.

Global Instance level_sqsubseteq : SqSubsetEq level := λ lvl1 lvl2,
  match lvl1, lvl2 with
  | Sec, Pub => False
  | _, _ => True
  end.

Global Instance level_sqsubseteq_refl : Reflexive level_sqsubseteq.
Proof. by case. Qed.

Global Instance level_sqsubseteq_tran : Transitive level_sqsubseteq.
Proof. by case=> [] [] []. Qed.

Global Instance level_join : Join level := λ lvl1 lvl2,
  match lvl1, lvl2 with
  | Pub, Pub => Pub
  | _, _ => Sec
  end.

Lemma level_joinP lvl1 lvl2 lvl3 :
  lvl1 ⊔ lvl2 ⊑ lvl3 ↔ (lvl1 ⊑ lvl3 ∧ lvl2 ⊑ lvl3).
Proof.
by case: lvl1 lvl2 lvl3=> [] [] []; intuition eauto.
Qed.

Lemma level_join_idemp (l : level) : l ⊔ l = l.
Proof. by case: l. Qed.

Global Instance level_meet : Meet level := λ lvl1 lvl2,
  match lvl1, lvl2 with
  | Sec, Sec => Sec
  | _, _ => Pub
  end.

Lemma level_meetP lvl1 lvl2 lvl3 :
  lvl3 ⊑ lvl1 ⊓ lvl2 ↔ (lvl3 ⊑ lvl1 ∧ lvl3 ⊑ lvl2).
Proof.
by case: lvl1 lvl2 lvl3=> [] [] []; intuition eauto.
Qed.

Global Instance level_inhabited : Inhabited level :=
  populate Pub.

End Levels.

Section Resources.

Context (Σ : gFunctors).
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).
Notation enc_pred := (term → term → iProp).
Notation nonce := loc.
Implicit Types P : term → iProp.
Implicit Types Φ : enc_pred.
Implicit Types a : loc.
Implicit Types l : level.
Implicit Types γ : gname.

Implicit Types φ ψ : iProp.

Definition atomic t :=
  match t with
  | TNonce _
  | TKey _ _
  | THash _
  | TExp' _ _ _ => true
  | _ => false
  end.

Context `{!heapG Σ}.

Class cryptoG := CryptoG {
  crypto_pub_inG :> savedPredG Σ term;
  crypto_enc_inG :> savedPredG Σ (term * term);
  crypto_enc_name : gname;
}.

Context `{!cryptoG}.

Definition crypto_enc N Φ : iProp :=
  ∃ γ, own crypto_enc_name (namespace_map_data N (to_agree γ)) ∧
       saved_pred_own γ (fun '(k, t) => Φ k t).

Definition crypto_enc_token E :=
  own crypto_enc_name (namespace_map_token E).

Global Instance crypto_enc_persistent N Φ : Persistent (crypto_enc N Φ).
Proof. apply _. Qed.

Lemma crypto_enc_agree k t N Φ1 Φ2 :
  crypto_enc N Φ1 -∗
  crypto_enc N Φ2 -∗
  ▷ (Φ1 k t ≡ Φ2 k t).
Proof.
iDestruct 1 as (γm1) "[#meta1 #own1]".
iDestruct 1 as (γm2) "[#meta2 #own2]".
iPoseProof (own_valid_2 with "meta1 meta2") as "%valid".
move: valid; rewrite -namespace_map_data_op namespace_map_data_valid.
move=> /agree_op_invL' ->.
by iApply (saved_pred_agree _ _ _ (k, t) with "own1 own2").
Qed.

Lemma crypto_enc_set E Φ N :
  ↑N ⊆ E →
  crypto_enc_token E ==∗
  crypto_enc N Φ.
Proof.
iIntros (?) "token".
iMod (saved_pred_alloc (λ '(k, t), Φ k t)) as (γ) "own".
iMod (own_update with "token").
  by eapply (namespace_map_alloc_update _ _ (to_agree γ)) => //.
by iModIntro; iExists γ; iSplit.
Qed.

Definition enc_inv k t : iProp :=
  ∃ N t' Φ, ⌜t = Spec.tag N t'⌝ ∧ crypto_enc N Φ ∧ □ Φ k t'.

Global Instance enc_inv_persistent k t : Persistent (enc_inv k t).
Proof. by apply _. Qed.

Lemma enc_inv_elim k N t Φ :
  enc_inv k (Spec.tag N t) -∗
  crypto_enc N Φ -∗
  □ ▷ Φ k t.
Proof.
iDestruct 1 as (N' t' Φ') "(%t_t' & #HΦ' & #inv)"; iIntros "#HΦ".
case/Spec.tag_inj: t_t' => <- <-.
iPoseProof (crypto_enc_agree k t with "HΦ HΦ'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Definition nonce_pred a P : iProp :=
  ∃ γ, meta a (cryptoN.@"nonce") γ ∧ saved_pred_own γ P.

Global Instance Persistent_nonce_pred a P :
  Persistent (nonce_pred a P).
Proof. apply _. Qed.

Lemma nonce_pred_set a P :
  meta_token a (↑cryptoN.@"nonce") ==∗
  nonce_pred a P.
Proof.
iIntros "token".
iMod (saved_pred_alloc P) as (γ) "#HP".
iMod (meta_set _ a γ with "token") as "#meta"; eauto.
by iModIntro; iExists γ; eauto.
Qed.

Lemma nonce_pred_agree a P Q t :
  nonce_pred a P -∗
  nonce_pred a Q -∗
  ▷ (P t ≡ Q t).
Proof.
iDestruct 1 as (γP) "[#a_γP #γP_P]".
iDestruct 1 as (γQ) "[#a_γQ #γQ_Q]".
iPoseProof (meta_agree with "a_γP a_γQ") as "->".
by iApply (saved_pred_agree with "γP_P γQ_Q").
Qed.

Definition declared_nonce a : iProp :=
  ∃ (P : term → iProp), nonce_pred a P.

Global Instance Persistent_declared_nonce a :
  Persistent (declared_nonce a).
Proof. apply _. Qed.

Definition published a t : iProp :=
  ∃ (P : term → iProp), nonce_pred a P ∧ ▷ □ P t.

Global Instance Persistent_published a t :
  Persistent (published a t).
Proof. apply _. Qed.

Lemma publishedE a P t : nonce_pred a P -∗ published a t ↔ ▷ □ P t.
Proof.
iIntros "#a_P"; iSplit.
- iDestruct 1 as (Q) "[#a_Q #Q_t]".
  iPoseProof (nonce_pred_agree _ _ _ t with "a_P a_Q") as "e".
  by iModIntro; iRewrite "e".
- by iIntros "#P_t"; iExists P; eauto.
Qed.

Fact sterm_key : unit. Proof. exact: tt. Qed.

Definition sterm : term → iProp :=
  locked_with sterm_key (
    λ t, [∗ set] a ∈ nonces_of_term t, declared_nonce a
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
     ⌜atomic t⌝ ∧ ([∗ set] a ∈ nonces_of_term t, published a t)
     ∨ (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, pterm_aux n t')
     ∨ ∃ k t', ⌜t = TEnc k t'⌝ ∧ enc_inv k t' ∧
               □ (pterm_aux n (TKey Dec k) → pterm_aux n t')
    )
  else False.

Global Instance Persistent_pterm_aux n t : Persistent (pterm_aux n t).
Proof. elim: n t => [|n IH] /=; apply _. Qed.

(** [pterm t] holds when the term [t] can be declared public. *)

Fact pterm_key : unit. Proof. exact: tt. Qed.
Definition pterm : term → iProp :=
  locked_with pterm_key (λ t, pterm_aux (tsize t) t).
Canonical pterm_unlock := [unlockable of pterm].

Global Instance Persistent_pterm t : Persistent (pterm t).
Proof. rewrite unlock; apply _. Qed.

Lemma and_proper_L (P : Prop) (φ ψ : iProp) :
  (P → φ ⊣⊢ ψ) →
  ⌜P⌝ ∧ φ ⊣⊢ ⌜P⌝ ∧ ψ.
Proof.
by move=> φ_ψ; apply: (anti_symm _); iIntros "[% ?]";
rewrite φ_ψ; eauto.
Qed.

Lemma pterm_aux_eq n t : tsize t ≤ n → pterm_aux n t ⊣⊢ pterm t.
Proof.
rewrite unlock.
elim: n / (lt_wf n) t => - [|n] _ IH t t_n /=;
move: (ssrbool.elimT ssrnat.ltP (tsize_gt0 t)) => ?;
first lia.
case e_st: (tsize t) => [|m] /=; first lia.
apply: bi.and_proper => //.
apply: bi.or_proper => //.
apply: bi.or_proper.
- apply: bi.exist_proper => T.
  apply: and_proper_L => T_t.
  apply: big_sepS_proper => t' T_t'.
  move: (decompose_tsize T_t T_t') => ?.
  rewrite (IH n) ?(IH m) //; lia.
- apply: bi.exist_proper => k.
  apply: bi.exist_proper => t'.
  apply: and_proper_L => e_t.
  apply: bi.and_proper => //.
  rewrite e_t tsize_eq -ssrnat.plusE in t_n e_st.
  rewrite !(IH n) ?(IH m) // ?[tsize (TKey _ _)]tsize_eq /=; lia.
Qed.

(* TODO: Merge with pterm_aux_eq *)
Lemma pterm_eq t :
  pterm t ⊣⊢
  sterm t ∧ (
    ⌜atomic t⌝ ∧ ([∗ set] a ∈ nonces_of_term t, published a t)
    ∨ (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, pterm t')
    ∨ ∃ k t', ⌜t = TEnc k t'⌝ ∧ enc_inv k t' ∧ □ (pterm (TKey Dec k) → pterm t')
  ).
Proof.
rewrite {1}[pterm]unlock.
case e_st: (tsize t) => [|m] /=.
  move: (ssrbool.elimT ssrnat.ltP (tsize_gt0 t)) => ?; lia.
apply: bi.and_proper => //.
apply: bi.or_proper => //.
apply: bi.or_proper.
- apply: bi.exist_proper => T.
  apply: and_proper_L => T_t.
  apply: big_sepS_proper => t' T_t'.
  move: (decompose_tsize T_t T_t') => ?.
  rewrite pterm_aux_eq //; lia.
- apply: bi.exist_proper => k.
  apply: bi.exist_proper => t'.
  apply: and_proper_L => e_t.
  apply: bi.and_proper => //.
  rewrite e_t tsize_eq -ssrnat.plusE in e_st.
  rewrite !pterm_aux_eq ?[tsize (TKey _ _)]tsize_eq //=; lia.
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

Lemma sterm_TNonce a : sterm (TNonce a) ⊣⊢ declared_nonce a.
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

Lemma pterm_TInt n : pterm (TInt n) ⊣⊢ True.
Proof.
apply: (anti_symm _); iIntros "_" => //.
rewrite pterm_eq sterm_TInt; iSplit => //.
iRight; iLeft; iExists ∅; rewrite big_sepS_empty; iSplit => //.
by iPureIntro; econstructor.
Qed.

Lemma pterm_TPair t1 t2 : pterm (TPair t1 t2) ⊣⊢ pterm t1 ∧ pterm t2.
Proof.
apply: (anti_symm _); iIntros "#Ht" => //.
- rewrite pterm_eq sterm_TPair.
  iDestruct "Ht" as "([Ht1 Ht2] & publ)".
  iDestruct "publ" as "[[% ?] | [publ | publ]]" => //=.
  + iDestruct "publ" as (T) "[%dec publ]".
    case: dec => //= {}t1 {}t2 -> [-> ->].
    by rewrite big_sepS_union_pers !big_sepS_singleton.
  + by iDestruct "publ" as (??) "[% ?]".
- iDestruct "Ht" as "[Ht1 Ht2]".
  rewrite [pterm (TPair t1 t2)]pterm_eq sterm_TPair -!pterm_sterm.
  iSplit; eauto.
  iRight; iLeft; iExists _; iSplit.
    iPureIntro; by econstructor.
  by rewrite big_sepS_union_pers !big_sepS_singleton; eauto.
Qed.

Lemma published_declared_nonce a t : published a t -∗ declared_nonce a.
Proof.
by iDestruct 1 as (P) "[H _]"; iExists P.
Qed.

Lemma pterm_TNonce a : pterm (TNonce a) ⊣⊢ published a (TNonce a).
Proof.
apply: (anti_symm _); iIntros "Ht".
- rewrite pterm_eq; iDestruct "Ht" as "[_ Ht]".
  iDestruct "Ht" as "[[_ publ] | [publ | publ]]".
  + by rewrite nonces_of_term_eq /= big_sepS_singleton.
  + iDestruct "publ" as (T) "[%dec _]".
    by case: dec.
  + by iDestruct "publ" as (k t') "[%dec _]".
- rewrite pterm_eq; iSplit.
    by rewrite sterm_TNonce published_declared_nonce.
  iLeft; iSplit => //=.
  by rewrite nonces_of_term_eq /= big_sepS_singleton.
Qed.

Lemma pterm_TKey kt t :
  pterm (TKey kt t) ⊣⊢
  pterm t ∨ [∗ set] a ∈ nonces_of_term t, published a (TKey kt t).
Proof.
apply: (anti_symm _).
- rewrite pterm_eq sterm_TKey; iDestruct 1 as "[Ht publ]".
  iDestruct "publ" as "[[_ publ] | [publ | publ]]".
  + iRight; by rewrite nonces_of_term_eq.
  + iDestruct "publ" as (T) "[%dec publ]".
    case: dec => //= {}kt {}t -> [-> ->].
    by rewrite big_sepS_singleton; eauto.
  + by iDestruct "publ" as (??) "[% _]".
- iDestruct 1 as "# [publ | publ]".
    rewrite [pterm (TKey _ _)]pterm_eq sterm_TKey -pterm_sterm.
    iSplit => //; iRight; iLeft.
    iExists {[t]}; iSplit; first by iPureIntro; econstructor.
    by rewrite big_sepS_singleton.
  rewrite pterm_eq; iSplit.
    rewrite unlock nonces_of_term_eq /=.
    iApply big_sepS_mono; last by eauto.
    move=> ??; iApply published_declared_nonce.
  iLeft; iSplit => //.
  by rewrite nonces_of_term_eq.
Qed.

Lemma pterm_TEnc k t :
  pterm (TEnc k t) ⊣⊢
  pterm (TKey Enc k) ∧ pterm t ∨
  sterm (TEnc k t) ∧ enc_inv k t ∧ □ (pterm (TKey Dec k) → pterm t).
Proof.
apply: (anti_symm _).
- rewrite pterm_eq sterm_TEnc.
  iDestruct 1 as "[[Hk Ht] publ]".
  iDestruct "publ" as "[[% ?] | [publ | publ]]"; first by [].
  + iDestruct "publ" as (T) "[%dec ?]".
    case: dec => // {}k {}t -> [-> ->].
    by rewrite big_sepS_union_pers !big_sepS_singleton; iLeft.
  + by iDestruct "publ" as (k' t') "(%e_t & ? & ?)"; case: e_t => <- <-; eauto.
- iDestruct 1 as "# [[Hk Ht] | (Ht & inv & #impl)]".
  + rewrite [pterm (TEnc _ _)]pterm_eq sterm_TEnc.
    rewrite -[sterm k](sterm_TKey Enc k) -!pterm_sterm.
    iSplit; eauto; iRight; iLeft.
    iExists {[TKey Enc k; t]}; rewrite big_sepS_union_pers !big_sepS_singleton.
    iSplit; eauto; iPureIntro; by econstructor.
  + rewrite [pterm (TEnc k t)]pterm_eq; iSplit => //=.
    iRight; iRight; by iExists k, t; eauto.
Qed.

Lemma pterm_THash t :
  pterm (THash t) ⊣⊢
  pterm t ∨ [∗ set] a ∈ nonces_of_term t, published a (THash t).
Proof.
apply: (anti_symm _).
- rewrite pterm_eq sterm_THash.
  iDestruct 1 as "[Ht [[_ publ] | [publ | publ]]]".
  + by rewrite nonces_of_term_eq /=; eauto.
  + iDestruct "publ" as (T) "[%dec ?]".
    case: dec => //= {}t -> [->].
    by rewrite big_sepS_singleton; eauto.
  + by iDestruct "publ" as (??) "[% ?]".
- iDestruct 1 as "[Ht | publ]".
    rewrite [pterm (THash _)]pterm_eq sterm_THash -pterm_sterm.
    iSplit => //=; iRight; iLeft.
    iExists {[t]}; rewrite big_sepS_singleton; iSplit => //.
    iPureIntro; by econstructor.
  rewrite pterm_eq unlock; iSplit.
    rewrite nonces_of_term_eq /=.
    iApply (big_sepS_mono with "publ") => ??.
    by iApply published_declared_nonce.
  iLeft; iSplit => //.
  by rewrite nonces_of_term_eq /=.
Qed.

Lemma pterm_TExp t ts :
  pterm (TExp t ts) ⊣⊢
  ⌜ts = []⌝ ∧ pterm t ∨
  (∃ t' ts', ⌜ts ≡ₚ t' :: ts'⌝ ∧ pterm (TExp t ts') ∧ pterm t') ∨
  [∗ set] a ∈ nonces_of_term t ∪ ⋃ (nonces_of_term <$> ts),
    published a (TExp t ts).
Proof.
apply: (anti_symm _).
- rewrite pterm_eq sterm_TExp.
  iDestruct 1 as "# [[Ht Hts] [[_ publ] | [publ | publ]]]".
  + by rewrite nonces_of_term_TExp; do 2!iRight.
  + iDestruct "publ" as (T) "[%dec publ]".
    case: dec; try by move=>>; rewrite unlock.
    * move=> {}t -> /TExp_inj [-> e_ts] _.
      rewrite big_sepS_singleton; iLeft; iSplit => //.
      iPureIntro; exact: Permutation.Permutation_nil.
    * move=> {}t ts1 t2 -> /TExp_inj [-> e_ts] _.
      iRight; iLeft; rewrite big_sepS_union_pers !big_sepS_singleton.
      by eauto.
  + iDestruct "publ" as (??) "[%e ?]".
    by rewrite unlock in e.
- iDestruct 1 as "# [[-> Ht] | [publ | publ]]".
  + rewrite [pterm (TExp _ _)]pterm_eq sterm_TExp -pterm_sterm /=.
    iSplit; eauto.
    iRight; iLeft.
    iExists {[t]}; rewrite big_sepS_singleton.
    iSplit => //; iPureIntro.
    apply: DExp0; eauto; by rewrite is_exp_TExp.
  + iDestruct "publ" as (t' ts') "[-> [Ht1 Ht2]]".
    rewrite [pterm (TExp _ (_ :: _))]pterm_eq sterm_TExp /=.
    iSplit.
      rewrite !pterm_sterm sterm_TExp /=.
      by iDestruct "Ht1" as "[??]"; eauto.
    iRight; iLeft.
    iExists {[TExp t ts'; t']}; rewrite big_sepS_union_pers !big_sepS_singleton.
    do !iSplit => //.
    iPureIntro.
    by apply: DExp1; eauto; rewrite is_exp_TExp.
  + rewrite pterm_eq [sterm]unlock; iSplit.
      rewrite nonces_of_term_TExp.
      iApply (big_sepS_mono with "publ") => ??.
      by iApply published_declared_nonce.
    iLeft; iSplit; first by rewrite unlock.
    by rewrite nonces_of_term_TExp.
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
  crypto_enc N Φ -∗
  pterm (TKey Enc k) ∧ pterm t ∨
  □ ▷ Φ k t ∧ sterm t ∧ □ (pterm (TKey Dec k) → pterm t).
Proof.
iIntros "#Ht #HΦ"; rewrite pterm_TEnc pterm_tag.
iDestruct "Ht" as "[[? Ht] | Ht]"; first by eauto.
rewrite sterm_TEnc sterm_tag.
iDestruct "Ht" as "([??] & inv & ?)".
iRight; iSplit; eauto; by iApply enc_inv_elim.
Qed.

Lemma pterm_TEncIS N Φ k t :
  sterm (TKey Enc k) -∗
  crypto_enc N Φ -∗
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

Section Meta.

Context `{!EqDecision L, !Countable L}.

Definition crypto_meta_token t E : iProp :=
  ⌜nonces_of_term t ≠ ∅⌝ ∧
  [∗ set] a ∈ nonces_of_term t, meta_token a E.

Definition crypto_meta t N (x : L) : iProp :=
  ⌜nonces_of_term t ≠ ∅⌝ ∧
  [∗ set] a ∈ nonces_of_term t, meta a N x.

Global Instance persistent_crypto_meta t N x :
  Persistent (crypto_meta t N x).
Proof. apply _. Qed.

Lemma crypto_meta_set t N E x :
  ↑N ⊆ E → crypto_meta_token t E ==∗ crypto_meta t N x.
Proof.
iIntros (sub) "[#ne token]"; rewrite /crypto_meta.
iAssert (|==> [∗ set] a ∈ nonces_of_term t, meta a N x)%I
  with "[token]" as "> ?"; last by eauto.
iApply big_sepS_bupd.
iApply (big_sepS_mono with "token") => a in_t /=.
by iApply meta_set.
Qed.

End Meta.

End Resources.

Arguments crypto_enc_name {Σ _}.
Arguments crypto_enc {Σ _ _}.
Arguments crypto_meta_set {Σ _ _ _ _} t N E x.
