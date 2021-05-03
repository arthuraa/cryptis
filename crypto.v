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
Implicit Types Φ : enc_pred.
Implicit Types a : loc.
Implicit Types l : level.
Implicit Types γ : gname.

Implicit Types P Q : iProp.

Definition atomic t : bool :=
  match t with
  | TInt _ => false
  | TPair _ _ => false
  | TNonce _ => true
  | TKey _ _ => true
  | TEnc _ _ => false
  | THash _ => false (* We do not treat hashes as atomic because they are always
    considered public *)
  end.

Fixpoint atoms t : gset term :=
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => atoms t1 ∪ atoms t2
  | TNonce _ => {[t]}
  | TKey _ _ => {[t]}
  | TEnc _ t => atoms t
  | THash _ => ∅
  end.

Lemma atoms_term_height t1 t2 :
  t1 ∈ atoms t2 →
  term_height t1 <= term_height t2.
Proof.
elim: t2 => //=.
- move=> t21 IH1 t22 IH2 /elem_of_union [] t1_atom;
  [move/(_ t1_atom) in IH1|move/(_ t1_atom) in IH2]; lia.
- by move=> a /elem_of_singleton ->.
- by move=> kt k IH /elem_of_singleton ->.
- move=> k IHk t IHt /IHt ?; lia.
Qed.

Lemma atomic_atom t1 t2 : t1 ∈ atoms t2 → atomic t1.
Proof.
elim: t2 => //=.
- by move=> t21 IH1 t22 IH2 /elem_of_union [] ?; eauto.
- by move=> ? /elem_of_singleton ->; eauto.
- by move=> ? t2 IH /elem_of_singleton ->; eauto.
Qed.

Context `{!heapG Σ}.

Definition term_data : Type := gmap term (level * gname * gname).

Global Instance term_data_inhabited : Inhabited term_data.
Proof. apply _. Qed.

Definition term_data' : Type :=
  gmap term (agree level) *
  gmap term (agree gname) *
  gmap term (agree gname).

Canonical term_data'UR :=
  (fun (sT : ucmraT) (f : term_data' -> sT) => sT) _ (fun x => x).

Definition to_term_data' (td : term_data) : term_data'UR :=
  (fmap (fun '(lvl, _    , _)     => to_agree lvl)     td,
   fmap (fun '(_  , γ_pub, _) => to_agree γ_pub)       td,
   fmap (fun '(_  , _    , γ_meta) => to_agree γ_meta) td).

Class cryptoG := CryptoG {
  crypto_inG :> inG Σ (authUR term_data'UR);
  crypto_pub_inG :> inG Σ (coGset_pairUR term);
  crypto_meta_inG :> inG Σ (namespace_mapR (agreeR positiveO));
  crypto_pred_inG :> savedPredG Σ (term * term);
  crypto_name : gname;
  crypto_inv_name : gname;
}.

Context `{!cryptoG}.

Global Instance cryptoG_authG : authG Σ term_data'UR := @AuthG _ _ _ _.

Implicit Types d : level * gname * gname.
Implicit Types td : term_data.

Definition crypto_own (td : term_data'UR) :=
  auth_own crypto_name td.

Definition atomicT lvl t :=
  crypto_own ({[t := to_agree lvl]}, ∅, ∅).

Global Instance atomicT_persistent lvl t : Persistent (atomicT lvl t).
Proof.
rewrite /atomicT /crypto_own; by apply _.
Qed.

Lemma atomicT_agree lvl1 lvl2 t :
  atomicT lvl1 t -∗
  atomicT lvl2 t -∗
  ⌜lvl1 = lvl2⌝.
Proof.
iIntros "own1 own2".
iPoseProof (own_valid_2 with "own1 own2") as "#valid".
rewrite auth_validI /= -!pair_op !uPred.prod_validI /=.
iDestruct "valid" as "[[#valid _] _]".
rewrite singleton_op gmap_validI.
iSpecialize ("valid" $! t); rewrite lookup_singleton.
rewrite uPred.option_validI agree_validI agree_equivI.
by iPoseProof "valid" as "->".
Qed.

Definition crypto_meta_name t γm : iProp :=
  crypto_own (∅, ∅, {[t := to_agree γm]}).

Global Instance crypto_meta_name_persistent t γm :
  Persistent (crypto_meta_name t γm).
Proof.
rewrite /crypto_meta_name /crypto_own; by apply _.
Qed.

Lemma crypto_meta_name_agree t γm1 γm2 :
  crypto_meta_name t γm1 -∗
  crypto_meta_name t γm2 -∗
  ⌜γm1 = γm2⌝.
Proof.
iIntros "own1 own2".
iPoseProof (own_valid_2 with "own1 own2") as "#valid".
rewrite auth_validI /= -!pair_op !uPred.prod_validI /=.
iDestruct "valid" as "(_ & #valid)".
rewrite singleton_op gmap_validI.
iSpecialize ("valid" $! t); rewrite lookup_singleton.
rewrite uPred.option_validI agree_validI agree_equivI.
by iRewrite "valid".
Qed.

Definition crypto_meta_token t E : iProp :=
  ∃ γm, crypto_meta_name t γm ∗ own γm (namespace_map_token E).

Definition crypto_meta `{Countable A} t N (x : A) : iProp :=
  ∃ γm, crypto_meta_name t γm ∗
        own γm (namespace_map_data N (to_agree (encode x))).

Global Instance crypto_meta_persistent `{Countable A} t N (x : A) :
  Persistent (crypto_meta t N x).
Proof. apply _. Qed.

Lemma crypto_meta_agree `{Countable A} t N (x1 x2 : A) :
  crypto_meta t N x1 -∗
  crypto_meta t N x2 -∗
  ⌜x1 = x2⌝.
Proof.
iDestruct 1 as (γm1) "[#meta1 #own1]".
iDestruct 1 as (γm2) "[#meta2 #own2]".
iPoseProof (crypto_meta_name_agree with "meta2 meta1") as "->".
iPoseProof (own_valid_2 with "own1 own2") as "%valid".
move: valid; rewrite -namespace_map_data_op namespace_map_data_valid.
move=> /agree_op_invL'. naive_solver.
Qed.

Lemma crypto_meta_set `{Countable A} E t (x : A) (N : namespace) :
  ↑N ⊆ E →
  crypto_meta_token t E ==∗
  crypto_meta t N x.
Proof.
iIntros (?) "token"; iDestruct "token" as (γ) "[own token]".
iMod (own_update with "token").
  by eapply (namespace_map_alloc_update _ _ (to_agree (encode x))) => //.
by iModIntro; iExists γ; iSplit.
Qed.

Lemma crypto_meta_meta_token `{Countable A} t (x : A) N E :
  ↑N ⊆ E →
  crypto_meta_token t E -∗
  crypto_meta t N x -∗
  False.
Proof.
iIntros (sub) "Htoken #Hmeta1".
pose (X := {[encode x]} : gset positive).
iMod (crypto_meta_set _ (fresh X) with "Htoken") as "#Hmeta2"=> //.
iAssert (crypto_meta t N (encode x)) as "Hmeta1'".
  by rewrite {1 3}/crypto_meta.
iPoseProof (crypto_meta_agree with "Hmeta1' Hmeta2") as "%e"; iPureIntro.
assert (contra : encode x ∈ X). { by apply/elem_of_singleton. }
destruct (is_fresh X); by rewrite -e.
Qed.

Definition crypto_inv_token E : iProp :=
  own crypto_inv_name (namespace_map_token E).

Definition crypto_inv_meta N Φ : iProp :=
  ∃ γ, own crypto_inv_name (namespace_map_data N (to_agree γ)) ∧
       saved_pred_own γ (fun '(k, t) => Φ k t).

Global Instance crypto_inv_meta_persistent N Φ :
  Persistent (crypto_inv_meta N Φ).
Proof. apply _. Qed.

Lemma crypto_inv_meta_agree k t N Φ1 Φ2 :
  crypto_inv_meta N Φ1 -∗
  crypto_inv_meta N Φ2 -∗
  ▷ (Φ1 k t ≡ Φ2 k t).
Proof.
iDestruct 1 as (γm1) "[#meta1 #own1]".
iDestruct 1 as (γm2) "[#meta2 #own2]".
iPoseProof (own_valid_2 with "meta1 meta2") as "%valid".
move: valid; rewrite -namespace_map_data_op namespace_map_data_valid.
move=> /agree_op_invL' ->.
by iApply (saved_pred_agree _ _ _ (k, t) with "own1 own2").
Qed.

Lemma crypto_inv_meta_set E Φ N :
  ↑N ⊆ E →
  crypto_inv_token E ==∗
  crypto_inv_meta N Φ.
Proof.
iIntros (?) "token".
iMod (saved_pred_alloc (λ '(k, t), Φ k t)) as (γ) "own".
iMod (own_update with "token").
  by eapply (namespace_map_alloc_update _ _ (to_agree γ)) => //.
by iModIntro; iExists γ; iSplit.
Qed.

Definition enc_inv k t : iProp :=
  ∃ N t' Φ, ⌜t = Spec.tag N t'⌝ ∧ crypto_inv_meta N Φ ∧ □ Φ k t'.

Global Instance enc_inv_persistent k t : Persistent (enc_inv k t).
Proof. by apply _. Qed.

Lemma enc_inv_elim k N t Φ :
  enc_inv k (Spec.tag N t) -∗
  crypto_inv_meta N Φ -∗
  □ ▷ Φ k t.
Proof.
iDestruct 1 as (N' t' Φ') "(%t_t' & #HΦ' & #inv)"; iIntros "#HΦ".
case/Spec.tag_inj: t_t' => <- <-.
iPoseProof (crypto_inv_meta_agree k t with "HΦ HΦ'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Definition own_publish t (Ti : coGset_pair term) : iProp :=
  ∃ γ_pub, crypto_own (∅, {[t := to_agree γ_pub]}, ∅) ∗ own γ_pub Ti.

Lemma own_publish_op t Ti1 Ti2 :
  own_publish t (Ti1 ⋅ Ti2) ⊣⊢ own_publish t Ti1 ∗ own_publish t Ti2.
Proof.
apply (anti_symm _).
- iDestruct 1 as (γ_pub) "[#own1 [H1 H2]]".
  by iSplitL "H1"; iExists γ_pub; eauto.
- iDestruct 1 as "[H1 H2]".
  iDestruct "H1" as (γ_pub1) "[#own1 H1]".
  iDestruct "H2" as (γ_pub2) "[#own2 H2]".
  iDestruct (own_valid_2 with "own1 own2") as % valid.
  move: valid.
  rewrite -auth_frag_op auth_frag_valid -!pair_op !pair_valid.
  rewrite singleton_op singleton_valid.
  case=> [] [] _ valid _.
  apply agree_op_invL' in valid; subst γ_pub2.
  by iExists γ_pub1; iSplit => //; rewrite own_op; iFrame.
Qed.

Lemma own_publish_valid t Ti : own_publish t Ti -∗ ⌜✓ Ti⌝.
Proof.
iDestruct 1 as (γ_pub) "[H1 H2]".
by iPoseProof (own_valid with "H2") as "%".
Qed.

Lemma own_publish_valid_2 t Ti1 Ti2 :
  own_publish t Ti1 -∗ own_publish t Ti2 -∗ ⌜✓ (Ti1 ⋅ Ti2)⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" as "H".
rewrite -own_publish_op.
by iApply own_publish_valid.
Qed.

Definition unpublished t Ts : iProp :=
  own_publish t (coGset_pair_unset Ts).

Definition published t Ts : iProp :=
  own_publish t (coGset_pair_set Ts).

Global Instance published_persistent t Ts : Persistent (published t Ts).
Proof. apply _. Qed.

Lemma published_op t Ts1 Ts2 :
  published t (Ts1 ⋅ Ts2) ⊣⊢ published t Ts1 ∗ published t Ts2.
Proof.
by rewrite /published coGset_pair_set_op own_publish_op.
Qed.

(** [termT lvl t] holds when the term [t] can be declared public after
encrypting it.  If [lvl = Pub], [t] is considered public and does not have to be
encrypted.  All hashes are considered public for now. *)

Fixpoint termT_def lvl t : iProp :=
  let keyT lvl_enc lvl_dec k :=
    (atomicT lvl_enc (TKey Enc k) ∗
     atomicT lvl_dec (TKey Dec k) ∗
     ([∗ set] t' ∈ atoms k, published t' {[TKey Enc k; TKey Dec k]}) ∗
     termT_def Sec k ∗
     □ (termT_def Pub k → False) ∨
     termT_def Pub k ∗
     ⌜lvl_enc = Pub⌝ ∗
     ⌜lvl_dec = Pub⌝)%I in
  match t with
  | TInt _ => True
  | TPair t1 t2 => termT_def lvl t1 ∗ termT_def lvl t2
  | TNonce a =>
    ∃ lvl', atomicT lvl' t ∗
            meta a (cryptoN.@"nonce") () ∗
            ⌜lvl' ⊑ lvl⌝
  | TKey kt k =>
    ∃ lvl_enc lvl_dec,
      keyT lvl_enc lvl_dec k ∗
      ⌜(if kt is Enc then lvl_enc else lvl_dec) ⊑ lvl⌝
  | TEnc k t =>
    ∃ lvl_enc lvl_dec,
      keyT lvl_enc lvl_dec k ∗
      (⌜lvl_enc = Pub⌝ ∗ termT_def Pub t ∨
       enc_inv k t ∗ termT_def (lvl ⊔ lvl_dec) t)
  | THash t => termT_def Sec t
  end.

Definition termT_aux : seal termT_def. by eexists. Qed.
Definition termT := unseal termT_aux.
Definition keyT lvl_enc lvl_dec k : iProp :=
  atomicT lvl_enc (TKey Enc k) ∗
  atomicT lvl_dec (TKey Dec k) ∗
  ([∗ set] t' ∈ atoms k, published t' {[TKey Enc k; TKey Dec k]}) ∗
  termT Sec k ∗
  □ (termT Pub k → False) ∨
  termT Pub k ∗
  ⌜lvl_enc = Pub⌝ ∗
  ⌜lvl_dec = Pub⌝.

Lemma termT_eq lvl t :
  termT lvl t =
  match t with
  | TInt _ => True
  | TPair t1 t2 => termT lvl t1 ∗ termT lvl t2
  | TNonce a =>
    ∃ lvl', atomicT lvl' t ∗
            meta a (cryptoN.@"nonce") () ∗
            ⌜lvl' ⊑ lvl⌝
  | TKey kt k =>
    ∃ lvl_enc lvl_dec,
      keyT lvl_enc lvl_dec k ∗
      ⌜(if kt is Enc then lvl_enc else lvl_dec) ⊑ lvl⌝
  | TEnc k t =>
    ∃ lvl_enc lvl_dec,
      keyT lvl_enc lvl_dec k ∗
      (⌜lvl_enc = Pub⌝ ∗ termT Pub t ∨
       enc_inv k t ∗ termT (lvl ⊔ lvl_dec) t)
  | THash t => termT Sec t
  end%I.
Proof. by rewrite /keyT /termT seal_eq; case: t. Qed.

Global Instance persistent_termT lvl t :
  Persistent (termT lvl t).
Proof.
elim: t lvl => /= *; rewrite termT_eq /= /keyT; apply _.
Qed.

Global Instance keyT_persistent lvl_enc lvl_dec k :
  Persistent (keyT lvl_enc lvl_dec k).
Proof. apply _. Qed.

(** A stricter version of [termT] that does not allow subtyping *)
Definition stermT lvl t : iProp :=
  termT lvl t ∗ □ ∀ lvl', termT lvl' t -∗ ⌜lvl ⊑ lvl'⌝.

Global Instance stermT_persistent lvl t : Persistent (stermT lvl t).
Proof. apply _. Qed.

Lemma stermT_eq lvl t :
  stermT lvl t ⊣⊢
  match lvl with
  | Pub => termT Pub t
  | Sec => termT Sec t ∧ □ (termT Pub t → False)
  end.
Proof.
apply (anti_symm _).
- case: lvl; first by iDestruct 1 as "[??]".
  iDestruct 1 as "# [Ht #Hmin]"; iSplit => //.
  by iIntros "!> Ht'"; iPoseProof ("Hmin" with "Ht'") as "?".
- case: lvl.
    iIntros "#Ht"; iSplit => //.
    by iIntros "!>" (lvl) "_"; case: lvl.
  iIntros "[#Ht #Hmin]"; iSplit => //.
  iIntros "!>" (lvl) "Ht'"; case: lvl => //.
  by iDestruct ("Hmin" with "Ht'") as "[]".
Qed.

Lemma keyT_agree lvl_enc lvl_enc' lvl_dec lvl_dec' k :
  keyT lvl_enc lvl_dec k -∗
  keyT lvl_enc' lvl_dec' k -∗
  ⌜lvl_enc = lvl_enc'⌝ ∗
  ⌜lvl_dec = lvl_dec'⌝.
Proof.
iIntros "[Hk|Hk] [Hk'|Hk']".
- iDestruct "Hk" as "(enc & dec & _ & _)".
  iDestruct "Hk'" as "(enc' & dec' & _ & _ )".
  iDestruct (atomicT_agree with "enc enc'") as "->".
  by iDestruct (atomicT_agree with "dec dec'") as "->".
- iDestruct "Hk" as "(enc & dec & _ & sec & #npub)".
  iDestruct "Hk'" as "(pub & _)".
  by iDestruct ("npub" with "pub") as "[]".
- iDestruct "Hk" as "(pub & _)".
  iDestruct "Hk'" as "(_ & _ & _ & _ & npub)".
  by iDestruct ("npub" with "pub") as "[]".
- iDestruct "Hk" as "(_ & -> & ->)".
  by iDestruct "Hk'" as "(_ & -> & ->)".
Qed.

Lemma keyT_eq lvl_enc lvl_dec k :
  keyT lvl_enc lvl_dec k ⊣⊢
  stermT lvl_enc (TKey Enc k) ∗
  stermT lvl_dec (TKey Dec k).
Proof.
apply (anti_symm _).
- iIntros "#Hk"; do 2!iSplit.
  + rewrite termT_eq; eauto.
  + iIntros "!>" (lvl).
    rewrite termT_eq.
    iDestruct 1 as (lvl_enc' lvl_dec') "[Hk' %leq]".
    by iDestruct (keyT_agree with "Hk' Hk") as "[-> ->]".
  + rewrite termT_eq; eauto.
  + iIntros "!>" (lvl).
    rewrite termT_eq.
    iDestruct 1 as (lvl_enc' lvl_dec') "[Hk' %leq]".
    by iDestruct (keyT_agree with "Hk' Hk") as "[-> ->]".
- iDestruct 1 as "# [[enc #min_enc] [dec #min_dec]]".
  rewrite !termT_eq /=.
  iDestruct "enc" as (lvl_enc' lvl_dec') "[enc %leq]".
  iDestruct "dec" as (lvl_enc'' lvl_dec'') "[dec %leq']".
  iDestruct (keyT_agree with "dec enc") as "[-> ->]".
  iAssert (⌜lvl_enc ⊑ lvl_enc'⌝)%I as "%".
    iApply "min_enc"; rewrite termT_eq; eauto.
  iAssert (⌜lvl_dec ⊑ lvl_dec'⌝)%I as "%".
    iApply "min_dec"; rewrite termT_eq; eauto.
  by destruct lvl_enc, lvl_enc', lvl_dec, lvl_dec'.
Qed.

Lemma stermT_TKey_eq lvl kt k :
  stermT lvl (TKey kt k) ⊣⊢
  ∃ lvl_enc lvl_dec,
    keyT lvl_enc lvl_dec k ∗
    ⌜lvl = if kt is Enc then lvl_enc else lvl_dec⌝.
Proof.
apply (anti_symm _).
- iIntros "# [Hk #min]"; rewrite termT_eq.
  iDestruct "Hk" as (lvl_enc lvl_dec) "[Hk %lb]".
  iExists lvl_enc, lvl_dec; iSplit => //.
  case: kt lb => lb.
  + iPoseProof ("min" $! lvl_enc with "[]") as "%lb'".
      rewrite termT_eq; iExists lvl_enc, lvl_dec; eauto.
    by case: lvl_enc lvl lb lb' => [] [].
  + iPoseProof ("min" $! lvl_dec with "[]") as "%lb'".
      rewrite termT_eq; iExists lvl_enc, lvl_dec; eauto.
    by case: lvl_dec lvl lb lb' => [] [].
- iDestruct 1 as (lvl_enc lvl_dec) "# [Hk ->]".
  iSplit.
  + by rewrite termT_eq; iExists lvl_enc, lvl_dec; eauto.
  + iIntros "!>" (lvl); rewrite termT_eq.
    iDestruct 1 as (lvl_enc' lvl_dec') "# [Hk' %lb]".
    by iDestruct (keyT_agree with "Hk' Hk") as %[-> ->].
Qed.

Lemma sub_termT lvl lvl' t :
  lvl ⊑ lvl' →
  termT lvl t -∗
  termT lvl' t.
Proof.
elim: t lvl lvl' => [n|t1 IH1 t2 IH2|l|kt k _|k _ t IH|t IH] lvl lvl' sub.
- by rewrite !termT_eq.
- rewrite ![termT _ (TPair t1 t2)]termT_eq /=.
  by iIntros "[#Ht1 #Ht2]"; rewrite IH1 // IH2 //; iSplit.
- rewrite !termT_eq /=.
  iDestruct 1 as (lvl0) "(#Hnonce & #Hmeta & %sub0)".
  iExists lvl0; repeat iSplit=> //; iPureIntro; by etransitivity.
- rewrite ![termT _ (TKey _ k)]termT_eq.
  iDestruct 1 as (lvl_enc lvl_dec) "(#Hkey & %sub0)".
  iExists lvl_enc, lvl_dec; iSplit=> //; iPureIntro; by etransitivity.
- rewrite ![termT _ (TEnc _ t)]termT_eq.
  iDestruct 1 as (lvl_enc lvl_dec) "# (Hk & Ht)".
  iExists lvl_enc, lvl_dec; iSplit => //.
  iDestruct "Ht" as "[Ht|Ht]"; eauto.
  iDestruct "Ht" as "(tP & Ht)".
  iRight; iSplit => //.
  iApply (IH with "Ht").
  by case: lvl lvl' lvl_dec sub=> [] [] [].
- by rewrite ![termT _ (THash _)]termT_eq.
Qed.

Lemma termT_int lvl n : ⊢ termT lvl (TInt n).
Proof. by rewrite termT_eq. Qed.

Lemma stermT_int n : ⊢ stermT Pub (TInt n).
Proof. by rewrite /stermT termT_eq /=; iSplit; eauto. Qed.
Hint Resolve stermT_int : typing.

Lemma termT_aenc_pub_pub k t :
  termT Pub (TKey Enc k) -∗
  termT Pub t -∗
  termT Pub (TEnc k t).
Proof.
rewrite [termT _ (TKey _ _)]termT_eq [termT _ (TEnc _ _)]termT_eq.
iDestruct 1 as (lvl_enc lvl_dec) "[Hk %leq]".
iIntros "Ht".
iExists lvl_enc, lvl_dec; iSplit => //; iLeft; iSplit => //.
by case: lvl_enc leq.
Qed.

Lemma termT_tag lvl n t :
  termT lvl (Spec.tag n t) ⊣⊢ termT lvl t.
Proof.
by rewrite Spec.tag_eq termT_eq /= termT_eq bi.True_sep.
Qed.

Lemma termT_aenc_sec_pub N Φ lvl_k k t :
  termT lvl_k (TKey Enc k) -∗
  crypto_inv_meta N Φ -∗
  termT Pub t -∗
  □ Φ k t -∗
  termT Pub (TEnc k (Spec.tag N t)).
Proof.
iIntros "#k_lo #pred #t_lo #inv".
rewrite [termT _ (TEnc _ _)]termT_eq.
rewrite [termT _ (TKey Enc _)]termT_eq.
iDestruct "k_lo" as (lvl_enc lvl_dec) "[k_lo %leq]".
iExists lvl_enc, lvl_dec; iSplit => //.
iRight; iSplit => //; last first.
  rewrite termT_tag.
  iApply (sub_termT with "t_lo"); by case: (lvl_dec).
by iExists N, t, Φ; eauto.
Qed.

Lemma stermTP lvl lvl' t :
  stermT lvl t -∗ termT lvl' t -∗ ⌜lvl ⊑ lvl'⌝.
Proof. by iIntros "[_ #min]". Qed.

Lemma stermT_agree lvl lvl' t :
  stermT lvl t -∗ stermT lvl' t -∗ ⌜lvl = lvl'⌝.
Proof.
iIntros "[#Ht #min] [#Ht' #min']".
iPoseProof ("min" with "Ht'") as "%l1".
iPoseProof ("min'" with "Ht") as "%l2".
by case: lvl lvl' l1 l2 => [] // [] //.
Qed.

Lemma termT_to_list t ts lvl :
  Spec.to_list t = Some ts →
  termT lvl t -∗
  [∗ list] t' ∈ ts, termT lvl t'.
Proof.
elim: t ts => //=.
  by case=> // ts [<-] /=; iIntros "?".
move=> t _ tl IH ts.
case e: (Spec.to_list tl) => [ts'|] // [<-] /=.
rewrite {1}termT_eq /=; iIntros "[??]"; iFrame.
by iApply IH.
Qed.

Lemma termT_of_list lvl ts :
  termT lvl (Spec.of_list ts) ⊣⊢
  [∗ list] t ∈ ts, termT lvl t.
Proof.
rewrite Spec.of_list_eq.
elim: ts => [|t ts IH]; first by rewrite termT_eq.
by rewrite termT_eq /= IH.
Qed.

Lemma stermT_pair lvl1 t1 lvl2 t2 :
  stermT lvl1 t1 -∗
  stermT lvl2 t2 -∗
  stermT (lvl1 ⊔ lvl2) (TPair t1 t2).
Proof.
iIntros "[#type1 #min1] [#type2 #min2]"; iSplit.
- rewrite (termT_eq (lvl1 ⊔ lvl2)).
  iSplit; iApply sub_termT; try by [iApply "type1"|iApply "type2"];
  by case: lvl1 lvl2=> [] [].
- iIntros "!>" (lvl').
  rewrite (termT_eq _ (TPair t1 t2)).
  iIntros "[#type1' #type2']".
  iPoseProof ("min1" with "type1'") as "%".
  iPoseProof ("min2" with "type2'") as "%".
  by iPureIntro; rewrite level_joinP; split.
Qed.

Lemma stermTS lvl t :
  termT Pub t -∗
  stermT lvl t -∗
  ⌜lvl = Pub⌝.
Proof.
iIntros "Ht1 [Ht2 #Hmin]".
iSpecialize ("Hmin" with "Ht1").
by case: lvl.
Qed.

Lemma termT_lvlP lvl t : termT lvl t -∗ ∃ lvl', stermT lvl' t.
Proof.
elim: t lvl=> [n|t1 IH1 t2 IH2|n|kt k IHk|k IHk t IHt|t IH] lvl /=;
rewrite termT_eq /=.
- iIntros "_"; iExists Pub; iApply stermT_int.
- iIntros "[#type1 #type2]".
  iDestruct (IH1 with "type1") as (lvl1) "type1'".
  iDestruct (IH2 with "type2") as (lvl2) "type2'".
  by iExists (lvl1 ⊔ lvl2); iApply stermT_pair.
- iDestruct 1 as (lvl') "(#Hn & #Hmeta & %Hsub)".
  iExists lvl'.
  iSplit; first by rewrite termT_eq /=; eauto.
  iIntros "!>" (lvl''); rewrite termT_eq /=.
  iDestruct 1 as (lvl''') "# (Hn' & _ & %leq')".
  by iPoseProof (atomicT_agree with "Hn' Hn") as "->".
- iDestruct 1 as (lvl_enc lvl_dec) "[Hk _]".
  rewrite keyT_eq; iDestruct "Hk" as "[??]".
  by destruct kt; eauto.
- iDestruct 1 as (lvl_enc lvl_dec) "# (Hk & Ht)".
  iDestruct "Ht" as "[[-> Ht]|Ht]".
    iExists Pub; rewrite stermT_eq keyT_eq stermT_eq.
    iApply termT_aenc_pub_pub => //.
    by iDestruct "Hk" as "[??]".
  iDestruct "Ht" as "(#tP & Ht)".
  iDestruct (IHt with "Ht") as (lvl') "Ht'".
  case: lvl'.
    iExists Pub; rewrite !stermT_eq /=.
    rewrite [termT Pub (TEnc _ _)]termT_eq.
    iExists lvl_enc, lvl_dec; iSplit => //.
    case: lvl_enc; eauto.
    iRight; iSplit => //.
    by iApply (sub_termT with "Ht'").
  rewrite stermT_eq; iDestruct "Ht'" as "[sec #pub]".
  iExists (if lvl_dec is Sec then Pub else Sec).
  rewrite stermT_eq; case: lvl_dec; last first.
    rewrite (termT_eq _ (TEnc k t)).
    iExists lvl_enc, Sec; iSplit => //.
    by case: lvl_enc; eauto.
  iSplit.
    rewrite (termT_eq _ (TEnc k t)).
    iExists lvl_enc, Pub; iSplit => //.
    by iRight; eauto.
  iIntros "!>"; rewrite (termT_eq _ (TEnc k t)).
  iDestruct 1 as (lvl_enc' lvl_dec') "# (Hk' & Ht')".
  iDestruct (keyT_agree with "Hk' Hk") as "[-> ->]".
  iDestruct "Ht'" as "[[_ Ht']|Ht']".
    by iApply "pub".
  iDestruct "Ht'" as "(? & Ht')".
  by iApply "pub".
- iIntros "Ht"; iExists Pub; rewrite stermT_eq.
  by rewrite [termT _ (THash t)]termT_eq.
Qed.

Lemma termT_TKey_swap l kt k :
  termT l (TKey kt k) -∗
  ∃ l', stermT l' (TKey (if kt is Enc then Dec else Enc) k).
Proof.
iIntros "Hk".
iDestruct (termT_lvlP with "Hk") as (l') "Hk".
rewrite stermT_TKey_eq.
iDestruct "Hk" as (l_e l_d) "[Hk' ?]".
iExists (if kt is Enc then l_d else l_e).
rewrite stermT_TKey_eq.
iExists l_e, l_d; iSplit => //.
by case: (kt).
Qed.

Lemma termT_adec_pub N Φ k t :
  termT Pub (TEnc k (Spec.tag N t)) -∗
  crypto_inv_meta N Φ -∗
  termT Pub t ∨ □ ▷ Φ k t ∗ termT Sec t.
Proof.
rewrite termT_eq; iIntros "#Ht #HΦ".
iDestruct "Ht" as (lvl_enc lvl_dec) "# (Hk & Ht)".
rewrite !termT_tag.
iDestruct "Ht" as "[(?&?)|Ht]"; eauto.
iDestruct "Ht" as "(inv & Ht)".
iRight; iSplit; first by iApply enc_inv_elim.
iApply (sub_termT with "Ht"); by case: lvl_dec.
Qed.

Lemma termT_adec_pub_sec N Φ k t :
  termT Pub (TEnc k (Spec.tag N t)) -∗
  crypto_inv_meta N Φ -∗
  ∃ lvl, termT lvl t ∗ □ ▷ guarded (lvl = Sec) (Φ k t).
Proof.
iIntros "Ht Hpred".
iPoseProof (termT_adec_pub with "Ht Hpred") as "[Ht|Ht]".
- by iExists Pub; iSplit.
- by iExists Sec; iDestruct "Ht" as "[??]"; iSplit.
Qed.

Lemma termT_adec_sec N Φ k lvl t :
  stermT Sec (TKey Enc k) -∗
  crypto_inv_meta N Φ -∗
  termT lvl (TEnc k (Spec.tag N t)) -∗
  termT Sec t ∗ □ ▷ Φ k t.
Proof.
iIntros "#Hk #HΦ #Ht".
rewrite stermT_TKey_eq.
iDestruct "Hk" as (? lvl_dec) "[Hk <-]".
rewrite termT_eq.
iDestruct "Ht" as (lvl_enc' lvl_dec') "(Hk' & Ht)".
iDestruct (keyT_agree with "Hk' Hk") as "[-> ->]".
iDestruct "Ht" as "[[% ?]|Ht]" => //.
iDestruct "Ht" as "(#inv & Ht)"; rewrite termT_tag.
iSplit.
  iApply (sub_termT with "Ht"); by case: (_ ⊔ _).
by iApply enc_inv_elim.
Qed.

Lemma termT_adec_sec_pub N Φ k t :
  stermT Sec (TKey Enc k) -∗
  crypto_inv_meta N Φ -∗
  termT Pub (TKey Dec k) -∗
  termT Pub (TEnc k (Spec.tag N t)) -∗
  termT Pub t ∗ □ ▷ Φ k t.
Proof.
iIntros "#enc #HΦ #dec #Ht".
iAssert (keyT Sec Pub k) as "{enc dec} Hk".
  by rewrite keyT_eq [stermT Pub _]stermT_eq; iSplit.
rewrite termT_eq.
iDestruct "Ht" as (lvl_enc lvl_dec) "[Hk' Ht]".
iDestruct (keyT_agree with "Hk' Hk") as "[-> ->]".
iDestruct "Ht" as "[[% ?]|Ht]" => //.
iDestruct "Ht" as "(#inv & Ht)".
iSplit => //; first by rewrite termT_tag.
by iApply enc_inv_elim.
Qed.

Lemma termT_adec_sec_pubG N Φ l k t :
  stermT l (TKey Enc k) -∗
  crypto_inv_meta N Φ -∗
  termT Pub (TKey Dec k) -∗
  termT Pub (TEnc k (Spec.tag N t)) -∗
  termT Pub t ∗ □ ▷ guarded (l = Sec) (Φ k t).
Proof.
rewrite /guarded; case: decide => [->|_].
  by iApply termT_adec_sec_pub.
iIntros "_ _ #Hk #Ht".
iAssert (stermT Pub (TKey Dec k)) as "{Hk} Hk".
  by rewrite stermT_eq.
rewrite stermT_TKey_eq.
iDestruct "Hk" as (lvl_enc ?) "[Hk <-]".
rewrite termT_eq.
iDestruct "Ht" as (lvl_enc' lvl_dec') "[Hk' Ht]".
iDestruct (keyT_agree with "Hk' Hk") as "[-> ->]".
rewrite !termT_tag.
iDestruct "Ht" as "[[??]|Ht]"; eauto.
by iDestruct "Ht" as "(?&?)"; eauto.
Qed.

Lemma termT_aenc_pub_sec l N Φ k t :
  termT  l (TKey Enc k) -∗
  stermT Sec (TKey Dec k) -∗
  crypto_inv_meta N Φ -∗
  □ Φ k t -∗
  termT Sec t -∗
  termT Pub (TEnc k (Spec.tag N t)).
Proof.
iIntros "#Henc #Hdec #HΦ #HΦt #Ht".
iDestruct (termT_lvlP with "Henc") as (lvl') "{Henc} Henc".
rewrite [termT _ (TEnc _ _)]termT_eq.
iExists lvl', Sec; rewrite keyT_eq !termT_tag; iSplit; eauto.
iRight; iSplit => //; iExists N, t, Φ; eauto.
Qed.

Lemma termT_aenc_pub_secG k N Φ l t :
  termT Pub (TKey Enc k) -∗
  termT l t -∗
  guarded (l = Sec) (stermT Sec (TKey Dec k)) -∗
  crypto_inv_meta N Φ -∗
  □ guarded (l = Sec) (Φ k t) -∗
  termT Pub (TEnc k (Spec.tag N t)).
Proof.
iIntros "#Henc #Ht #Hdec #Hpred #HG"; case: l => /=.
- by iApply termT_aenc_pub_pub; rewrite // termT_tag.
- by iApply termT_aenc_pub_sec; rewrite // termT_tag.
Qed.

Lemma stermT_termT lvl t : stermT lvl t -∗ termT lvl t.
Proof. by iDestruct 1 as "[??]". Qed.

Lemma sub_termT_pub lvl t : termT Pub t -∗ termT lvl t.
Proof. by iApply sub_termT. Qed.

Definition term_inv t d : iProp :=
  let '(lvl, _, _) := d in
  ⌜atomic t⌝ ∗ stermT lvl t ∗
  if lvl is Pub then published t ⊤ else emp.

Global Instance term_inv_persistent t d : Persistent (term_inv t d).
Proof.
by case: t => *; case: d => [] [] [] * /=; apply _.
Qed.

Definition term_data_inv (td : term_data) : iProp :=
  ([∗ map] t ↦ d ∈ td, term_inv t d)%I.

Global Instance term_data_inv_persistent td : Persistent (term_data_inv td).
Proof. by apply _. Qed.

Definition crypto_inv :=
  auth_inv crypto_name to_term_data' term_data_inv.

Definition crypto_ctx :=
  auth_ctx crypto_name cryptoN to_term_data' term_data_inv.

Global Instance term_data'_cmra_total : CmraTotal term_data'UR.
Proof. apply _. Qed.

Global Instance term_data'_core_id (a : term_data'UR) : CoreId a.
Proof.
case: a => [] [] ???.
apply _.
Qed.

(* MOVE *)
Lemma auth_inv_acc' E (a : term_data'UR) :
  ▷ auth_inv crypto_name to_term_data' term_data_inv ∗
  crypto_own a ={E}=∗ ∃ t,
    ⌜a ≼ to_term_data' t⌝ ∗ ▷ term_data_inv t ∗ ∀ u b,
    ⌜(to_term_data' t, a) ~l~> (to_term_data' u, b)⌝ ∗
    (crypto_own b -∗ ▷ term_data_inv u) ={E}=∗
    ▷ auth_inv crypto_name to_term_data' term_data_inv ∗
    crypto_own b.
Proof using Type*.
  iIntros "[Hinv Hγf]". rewrite /crypto_own /auth_inv /auth_own.
  iDestruct "Hinv" as (t) "[>Hγa Hφ]".
  iModIntro. iExists t.
  iDestruct (own_valid_2 with "Hγa Hγf") as % [? ?]%auth_both_valid.
  iSplit; first done. iFrame. iIntros (u b) "[% Hφ]".
  iMod (own_update_2 with "Hγa Hγf") as "[Hγa Hγf]".
  { eapply auth_update; eassumption. }
  iPoseProof "Hγf" as "#Hγf".
  iModIntro. iSplit => //. iExists u. iFrame. by iApply "Hφ".
Qed.

Lemma auth_acc' E (a : term_data'UR) :
  ↑cryptoN ⊆ E →
  crypto_ctx ∗ crypto_own a ={E,E ∖ ↑cryptoN}=∗
  ∃ t, ⌜a ≼ to_term_data' t⌝ ∗
       ▷ term_data_inv t ∗
       (∀ u b,
           ⌜(to_term_data' t, a) ~l~> (to_term_data' u, b)⌝ ∗
           (crypto_own b -∗ ▷ term_data_inv u)
           ={E ∖ ↑cryptoN,E}=∗ crypto_own b).
Proof.
  iIntros (?) "[#ctx Hγf]". rewrite /crypto_ctx /crypto_own /crypto_ctx /auth_ctx.
  iInv "ctx" as "Hinv" "Hclose".
  iMod (auth_inv_acc' with "[$Hinv $Hγf]") as (t) "(?&?&HclAuth)".
  iModIntro. iExists t. iFrame. iIntros (u b) "H".
  iMod ("HclAuth" $! u b with "H") as "(Hinv & ?)". by iMod ("Hclose" with "Hinv").
Qed.
(* /MOVE *)

Lemma term_data_local_update td frag t lvl γ_pub γ_meta :
  td !! t = None →
  (to_term_data' td, frag) ~l~>
  (to_term_data' (<[t := (lvl, γ_pub, γ_meta)]>td),
   to_term_data' {[t := (lvl, γ_pub, γ_meta)]} ⋅ frag).
Proof.
move=> td_t.
apply prod_local_update; last first.
  rewrite /to_term_data' /= fmap_insert map_fmap_singleton.
  rewrite insert_singleton_op ?lookup_fmap ?td_t //.
  apply op_local_update_discrete => valid t'.
  rewrite lookup_op.
  destruct (decide (t' = t)) as [->|ne].
    by rewrite lookup_singleton lookup_fmap td_t.
  rewrite lookup_singleton_ne //.
  by move: (valid t'); rewrite lookup_fmap left_id.
apply prod_local_update; last first.
  rewrite /to_term_data' /= fmap_insert map_fmap_singleton.
  rewrite insert_singleton_op ?lookup_fmap ?td_t //.
  apply op_local_update_discrete => valid t'.
  rewrite lookup_op.
  destruct (decide (t' = t)) as [->|ne].
    by rewrite lookup_singleton lookup_fmap td_t.
  rewrite lookup_singleton_ne //.
  by move: (valid t'); rewrite lookup_fmap left_id.
rewrite /to_term_data' /= fmap_insert map_fmap_singleton.
rewrite insert_singleton_op ?lookup_fmap ?td_t //.
apply op_local_update_discrete => valid t'.
rewrite lookup_op.
destruct (decide (t' = t)) as [->|ne].
  by rewrite lookup_singleton lookup_fmap td_t.
rewrite lookup_singleton_ne //.
by move: (valid t'); rewrite lookup_fmap left_id.
Qed.

Lemma publish E lvl t Ts :
  ↑cryptoN ⊆ E →
  atomic t →
  crypto_ctx -∗
  stermT lvl t -∗
  guarded (lvl = Sec) (unpublished t Ts) ={E}=∗
  published t Ts.
Proof.
case: lvl => /=.
- iIntros (? atomic_t) "#ctx #Ht _".
  iMod (auth_empty crypto_name) as "#own0".
  iMod (auth_acc' with "[ctx own0]") as (td) "{own0} (_ & #tdP & close)"; eauto.
  destruct (td !! t) as [d|] eqn:td_t.
  + case: d td_t => [] [] lvl' γ_pub γ_meta td_t.
    iAssert (▷ term_inv t (lvl', γ_pub, γ_meta))%I as "#Ht'".
    { iModIntro; rewrite /term_data_inv big_sepM_forall.
      by iApply "tdP". }
    iDestruct "Ht'" as "(_ & Ht' & publ)".
    iAssert (▷ ⌜lvl' = Pub⌝)%I as ">->".
    { iModIntro; iApply (stermT_agree with "Ht' Ht"). }
    iDestruct "publ" as ">publ".
    iMod ("close" $! td ε with "[]") as "_".
      by iSplit => //; iIntros "_ !>".
    iModIntro.
    rewrite (union_difference_L Ts ⊤) // published_op.
    by iDestruct "publ" as "[??]".
  + iMod (own_alloc (coGset_pair_set ⊤)) as (γ_pub) "#publ" => //.
    iMod (own_alloc (namespace_map_token ⊤)) as (γ_meta) "meta" => //.
      apply namespace_map_token_valid.
    pose (td' := <[t := (Pub, γ_pub, γ_meta)]>td).
    pose (d'  := to_term_data' {[t := (Pub, γ_pub, γ_meta)]} ⋅ ε).
    iMod ("close" $! td' d' with "[]") as "#own"; first iSplit.
    * iPureIntro; by apply term_data_local_update.
    * iIntros "#own !>".
      rewrite /d' /crypto_own right_id auth_own_prod_3 /term_data_inv.
      rewrite big_sepM_insert //; iSplit => //=.
      do 2![iSplit => //].
      iDestruct "own" as "(_ & ? & _)".
      by iExists γ_pub; rewrite map_fmap_singleton; eauto.
    rewrite /d' /crypto_own right_id auth_own_prod_3 !map_fmap_singleton.
    iDestruct "own" as "(_ & ? & _)".
    iAssert (published t ⊤) as "{publ} publ".
      by iExists γ_pub; eauto.
    rewrite (union_difference_L Ts ⊤) // published_op.
    by iModIntro; iDestruct "publ" as "[??]".
- iIntros (_ atomic_t) "#ctx #Ht unpubl".
  iDestruct "unpubl" as (γ_pub) "[#own unpubl]".
  iMod (own_update _ _ (coGset_pair_set Ts) with "unpubl") as "#publ".
    apply: coGset_pair_alloc_update.
  by iIntros "!>"; iExists γ_pub; iSplit.
Qed.

Lemma declare_nonce E1 E2 lvl a :
  ↑cryptoN ⊆ E1 →
  ↑cryptoN.@"nonce" ⊆ E2 →
  crypto_ctx -∗
  meta_token a E2 ={E1}=∗
  stermT lvl (TNonce a) ∗
  guarded (lvl = Sec) (unpublished (TNonce a) ⊤) ∗
  crypto_meta_token (TNonce a) ⊤.
Proof.
iIntros (sub1 sub2) "#ctx Hmeta".
iMod (auth_empty crypto_name) as "#own0".
iMod (auth_acc' with "[ctx own0]")
  as (td) "(_ & #tdP & close)"; eauto.
pose (t := TNonce a); iAssert (▷ ⌜td !! t = None⌝)%I as "#>%undef".
  case e: (td !! t) => [[] [] lvl' γ_pub_t γ_meta_t|] //=.
  rewrite /term_data_inv big_sepM_forall.
  iSpecialize ("tdP" $! _ _ e) => /=.
  iDestruct "tdP" as "(_ & (tdP & _) & _)".
  rewrite termT_eq /=.
  iDestruct "tdP" as (?) "(_ & tdP & _)".
  iModIntro.
  by iDestruct (meta_meta_token with "Hmeta tdP") as "[]".
pose (publ := if lvl is Pub then coGset_pair_set ⊤
              else coGset_pair_unset ⊤).
iMod (own_alloc publ) as (γ_pub) "publ" => //.
  rewrite /publ; case: (lvl) => //.
iMod (own_alloc (namespace_map_token ⊤)) as (γ_meta) "token" => //.
  exact: namespace_map_token_valid.
iMod (meta_set ⊤ a () (cryptoN.@"nonce") with "Hmeta") as "#l_nonce"; eauto.
pose (d   := (lvl, γ_pub, γ_meta)).
pose (td' := <[t := d]>td).
iAssert (□ (⌜lvl = Pub⌝ -∗ own γ_pub (coGset_pair_set ⊤)))%I
  with "[publ]" as "#publ'".
  rewrite /publ; case: (lvl).
  - by iDestruct "publ" as "#publ"; iIntros "!> _".
  - by iIntros "!> %".
iMod ("close" $! td' (to_term_data' {[t := d]} ⋅ ε) with "[]")
  as "own"; first iSplit.
- by iPureIntro; apply: term_data_local_update.
- iIntros "#own !> {own0}".
  rewrite /crypto_own right_id /term_data_inv big_sepM_insert //.
  iSplit => //.
  iSplit => //.
  rewrite /to_term_data' !map_fmap_singleton /= /crypto_own.
  rewrite auth_own_prod_3.
  iDestruct "own" as "(own_lvl & own_pub & own_meta)".
  iSplit; first iSplit.
  + rewrite termT_eq /=.
    iExists lvl; do 2![iSplit => //].
  + iIntros "!>" (lvl').
    rewrite termT_eq /=.
    iDestruct 1 as (lvl'') "(own_lvl' & _ & %sub)".
    by iDestruct (atomicT_agree with "own_lvl own_lvl'") as "<-".
  + case: (lvl) => //.
    iExists γ_pub; iSplit => //.
    by iApply "publ'".
rewrite /to_term_data' !map_fmap_singleton /= /crypto_own.
rewrite right_id.
iClear "own0"; rewrite auth_own_prod_3.
iDestruct "own" as "# (Hlvl & Hpub & Hmeta)".
iModIntro; iSplit.
  iSplit; first by rewrite termT_eq; iExists lvl; eauto.
  iIntros "!>" (lvl').
  rewrite termT_eq.
  iDestruct 1 as (lvl'') "(Ha & _ & %sub')".
  by iDestruct (atomicT_agree with "Ha Hlvl") as "->".
iSplitL "publ" => //.
  rewrite /publ; case: (lvl) => //=.
  by iExists γ_pub; iSplit.
by iExists γ_meta; eauto.
Qed.

Lemma termT_atoms lvl t t' :
  t' ∈ atoms t →
  termT lvl t -∗ termT Sec t'.
Proof.
elim: t lvl => //=.
- move=> t1 IH1 t2 IH2 lvl t'_atom.
  rewrite termT_eq; iIntros "[#Ht1 #Ht2]".
  case/elem_of_union: t'_atom => t'_atom.
  + by iApply IH1.
  + by iApply IH2.
- move=> a lvl /elem_of_singleton ->.
  by apply sub_termT; case: lvl.
- move=> kt k IH lvl /elem_of_singleton ->.
  by apply sub_termT; case: lvl.
- move=> k IHk t IHt lvl t'_atom.
  iIntros "Ht".
  rewrite termT_eq.
  iDestruct "Ht" as (lvl_enc lvl_dec) "(_ & Ht)".
  iDestruct "Ht" as "[(_ & Ht)|Ht]"; first by iApply IHt.
  iDestruct "Ht" as "(_ & Ht)"; by iApply IHt.
Qed.

Definition secret_terms (T T' : gset term) : iProp :=
  □ (∀ t, ⌜t ∈ T'⌝ ∗-∗ ⌜t ∈ T⌝ ∧ stermT Sec t).

Lemma secret_terms_sub T T' : secret_terms T T' -∗ ⌜T' ⊆ T⌝.
Proof.
rewrite elem_of_subseteq.
iIntros "#secret" (t t_in).
iDestruct ("secret" $! t) as "{secret} [secret _]".
by iDestruct ("secret" with "[]") as "[??]" => //.
Qed.

Lemma secret_termsP T :
  ([∗ set] t ∈ T, termT Sec t) -∗
  ∃ T', secret_terms T T'.
Proof.
induction T as [|t T t_T IH] using set_ind_L.
- iIntros "_"; iExists ∅.
  iIntros "!>" (t); iSplit.
  + iIntros (?); set_solver.
  + iIntros "[%Ht _]"; case: H; set_solver.
- rewrite big_sepS_insert //.
  iIntros "[#Ht #HT]".
  iDestruct (IH with "HT") as (T') "#HT'".
  iDestruct (termT_lvlP with "Ht") as (lvl) "{Ht} Ht".
  pose (T'' := if lvl is Sec then {[t]} : gset _ else ∅).
  iExists (T'' ∪ T'); iIntros "!>" (t'); iSplit.
  + iIntros "%t'_T'".
    case/elem_of_union: t'_T' => t'_T'.
      move: t'_T'; rewrite {}/T''; case: lvl; first set_solver.
      move/elem_of_singleton=> ->.
      iSplit => //.
      iPureIntro; set_solver.
    iDestruct ("HT'" $! t') as "{HT'} [HT' _]".
    iDestruct ("HT'" $! t'_T') as "[%t'_T #Ht']".
    iSplit => //.
    iPureIntro; set_solver.
  + iIntros "[%t'_T #Ht']".
    case/elem_of_union: t'_T => [/elem_of_singleton ->|t'_T].
      iDestruct (stermT_agree with "Ht Ht'") as "->".
      by iPureIntro; set_solver.
    iDestruct ("HT'" $! t') as "{HT'} [_ HT']".
    rewrite elem_of_union; iRight.
    iApply "HT'"; eauto.
Qed.

(* TODO Rename *)
Lemma unpublished_secret T T' (P : term → iProp) :
  secret_terms T T' -∗
  ([∗ set] t ∈ T, □ (stermT Sec t -∗ P t)) -∗
  [∗ set] t ∈ T', P t.
Proof.
move: T'.
induction T as [|t T t_T IH] using set_ind_L.
  iIntros (T') "secret _".
  iPoseProof (secret_terms_sub with "secret") as "%sub".
  assert (e : T' = ∅); first set_solver.
  by rewrite e big_sepS_empty.
iIntros (T') "secret unpub".
destruct (decide (t ∈ T')) as [t_in|t_nin]; last first.
  rewrite big_sepS_union; last set_solver.
  iDestruct "unpub" as "[_ unpub]".
  iApply (IH with "[secret]"); eauto.
  iPoseProof "secret" as "#secret".
  iIntros "!>" (t'); iDestruct ("secret" $! t') as "[s1 s2]".
  iSplit.
  - iIntros "%t'_T'".
    iDestruct ("s1" with "[//]") as "[%t'_T ?]".
    iSplit => //.
    case/elem_of_union: t'_T => // /elem_of_singleton e.
    congruence.
  - iIntros "[%t'_T Ht']"; iApply "s2".
    iSplit => //.
    iPureIntro; set_solver.
rewrite big_sepS_insert // (big_sepS_delete _ T' t) //.
iPoseProof "secret" as "#secret".
iDestruct "unpub" as "[u1 u2]".
iSplitL "u1".
  iApply "u1".
  iDestruct ("secret" $! t) as "[s1 _]".
  by iDestruct ("s1" with "[//]") as "[??]".
iApply IH => //.
iIntros "!>" (t'); iDestruct ("secret" $! t') as "[s1 s2]".
iSplit.
  iIntros ([t'_T' ne]%elem_of_difference).
  iDestruct ("s1" with "[//]") as "{s1} [%s11 s12]".
  iSplit => //.
  iPureIntro; set_solver.
iIntros "[%t'_T #?]".
iDestruct ("s2" with "[]") as "%".
  iSplit => //.
  iPureIntro; set_solver.
by iPureIntro; set_solver.
Qed.

Lemma stermT_atomicT t :
  atomic t →
  stermT Sec t -∗
  atomicT Sec t.
Proof.
rewrite stermT_eq.
case: t => //=.
- move => a _.
  rewrite !termT_eq.
  iDestruct 1 as "[#sec #pub]".
  iDestruct "sec" as (lvl) "(sec & ? & %leq)".
  case: lvl leq => // _.
  iDestruct ("pub" with "[]") as "[]".
  by iExists Pub; do 2![iSplit => //].
- move=> kt k _.
  rewrite !termT_eq.
  iDestruct 1 as "[#sec #pub]".
  iDestruct "sec" as (lvl_enc lvl_dec) "[sec %leq]".
  iDestruct "sec" as "[sec|(contra & -> & ->)]"; last first.
    iDestruct ("pub" with "[]") as "[]".
    iExists Pub, Pub; iSplit; last by case: (kt).
    by iRight; repeat iSplit.
  iDestruct "sec" as "(sec_enc & sec_dec & sec_k & #Hk)".
  case: (kt) {leq}.
  + case: lvl_enc => //.
    iDestruct ("pub" with "[]") as "[]".
    iExists Pub, lvl_dec; iSplit => //.
    by iLeft; eauto.
  + case: lvl_dec => //.
    iDestruct ("pub" with "[]") as "[]".
    iExists lvl_enc, Pub; iSplit => //.
    by iLeft; eauto.
Qed.

Lemma big_sepS_exists `{Countable A, !EqDecision B} :
  ∀ (Φ : A → B → iProp) (X : gset A),
    ([∗ set] x ∈ X, ∃ y : B, Φ x y) -∗
    ∃ m : gmap A B, ⌜dom _ m = X⌝ ∧ [∗ map] x↦y ∈ m, Φ x y.
Proof.
move=> Φ X.
induction X as [|x X x_X IH] using set_ind_L.
  by iIntros "_"; iExists ∅; iSplit; rewrite ?big_sepM_empty ?dom_empty_L.
rewrite big_sepS_insert //.
iIntros "[Hx HX]"; iDestruct "Hx" as (y) "Hx".
iDestruct (IH with "HX") as (m) "[%dom_m Hm]".
iExists (<[x := y]>m).
rewrite dom_insert_L dom_m; iSplit => //.
rewrite big_sepM_insert // -?(@not_elem_of_dom _ _ (gset A)) ?dom_m //.
iFrame; iApply (big_sepS_mono with "Hf").
Qed.

Lemma big_opS_auth_own' `{!authG Σ A, !EqDecision B, !Countable B}
  γ (g : B → A) (X : gset B) :
  ([∗ set] x ∈ X, auth_own γ (g x)) ==∗
  auth_own γ ([^op set] x ∈ X, g x).
Proof.
destruct (decide (X = ∅)) as [->|ne].
  rewrite big_sepS_empty big_opS_empty; iIntros "_".
  by iApply auth_empty.
rewrite big_opS_auth_own //.
by iIntros "? !>".
Qed.

Lemma big_opM_auth_own' `{!authG Σ A, !EqDecision B, !Countable B} {C}
  γ (g : B → C → A) (m : gmap B C) :
  ([∗ map] x↦y ∈ m, auth_own γ (g x y)) ==∗
  auth_own γ ([^op map] x↦y ∈ m, g x y).
Proof.
destruct (decide (m = ∅)) as [->|ne].
  rewrite big_sepM_empty big_opM_empty; iIntros "_".
  by iApply auth_empty.
rewrite big_opM_auth_own //.
by iIntros "? !>".
Qed.

Lemma big_opS_pair {A1 : ucmraT} {A2 : ucmraT} `{!EqDecision B, !Countable B}
  (g : B → prodUR A1 A2) (X : gset B) :
  ([^op set] x ∈ X, g x) ≡
  (([^op set] x ∈ X, (g x).1),
   ([^op set] x ∈ X, (g x).2)).
Proof.
induction X as [|x X x_X IH] using set_ind_L.
- by rewrite !big_opS_empty.
- rewrite !big_opS_insert //.
  by rewrite [X in X ≡ _]surjective_pairing /= IH.
Qed.

Lemma big_opM_pair {A1 : ucmraT} {A2 : ucmraT} `{!EqDecision B, !Countable B} {C}
  (g : B → C → prodUR A1 A2) (m : gmap B C) :
  ([^op map] x↦y ∈ m, g x y) ≡
  (([^op map] x↦y ∈ m, (g x y).1),
   ([^op map] x↦y ∈ m, (g x y).2)).
Proof.
induction m as [|x y m x_m IH] using map_ind.
- by rewrite !big_opM_empty.
- rewrite !big_opM_insert //.
  by rewrite [X in X ≡ _]surjective_pairing /= IH.
Qed.

Lemma big_opM_fmap' `{!EqDecision A, !Countable A} {B} {C : cmraT}
  (m : gmap A B) (f : B → C) :
  ([^(@op (gmapUR _ _) _) map] x↦y ∈ m, {[x := f y]}) ≡ f <$> m.
Proof.
induction m as [|x y m x_m IH] using map_ind.
- by rewrite !big_opM_empty fmap_empty.
- rewrite big_opM_insert // IH.
  move=> x'; rewrite lookup_op !lookup_fmap.
  destruct (decide (x' = x)) as [->|ne].
    by rewrite lookup_singleton x_m lookup_insert.
  by rewrite lookup_singleton_ne // lookup_insert_ne // left_id.
Qed.

Lemma keyT_published lvl_enc lvl_dec k t :
  t ∈ atoms k →
  stermT Sec k -∗
  keyT lvl_enc lvl_dec k -∗
  published t {[TKey Enc k; TKey Dec k]}.
Proof.
iIntros (t_atom) "#Hk1 #[Hk2|Hk2]"; last first.
  rewrite stermT_eq /=; iDestruct "Hk1" as "[_ #Hk1]".
  iDestruct "Hk2" as "(Hk2 & _ & _)".
  by iDestruct ("Hk1" with "Hk2") as "[]".
iDestruct "Hk2" as "(_ & _ & Hpub & _ & _)".
by rewrite big_sepS_delete //; iDestruct "Hpub" as "[??]".
Qed.

Lemma declare_sec_key E k t lvl_enc lvl_dec :
  ↑cryptoN ⊆ E →
  t ∈ atoms k →
  crypto_ctx -∗
  stermT Sec k -∗
  stermT Sec t -∗
  unpublished t {[TKey Enc k; TKey Dec k]} -∗
  ([∗ set] t' ∈ atoms k ∖ {[t]}, published t' {[TKey Enc k; TKey Dec k]}) ={E}=∗
  stermT lvl_enc (TKey Enc k) ∗
  stermT lvl_dec (TKey Dec k) ∗
  guarded (lvl_enc = Sec) (unpublished (TKey Enc k) ⊤) ∗
  guarded (lvl_dec = Sec) (unpublished (TKey Dec k) ⊤) ∗
  crypto_meta_token (TKey Enc k) ⊤ ∗
  crypto_meta_token (TKey Dec k) ⊤.
Proof.
iIntros (sub t_atom) "#ctx #Hk #Ht unpubl #publ".
iPoseProof (stermT_atomicT with "Ht") as "t_atomic" => //.
  by apply: atomic_atom.
iDestruct (big_sepS_exists with "publ") as (mγ) "[%dom_mγ publ']".
rewrite big_sepM_sep.
iDestruct "publ'" as "[own publ']".
iMod (big_opM_auth_own' with "own") as "{own} own".
rewrite !big_opM_pair /= !big_opM_unit big_opM_fmap'.
iDestruct "unpubl" as (γ_pub_t) "[#t_pub unpubl]".
rewrite {1}/atomicT /crypto_own.
iCombine "t_atomic t_pub" as "{t_atomic} own_t".
rewrite -auth_own_op -!pair_op !left_id right_id.
iCombine "own own_t" as "{own_t} own".
rewrite -auth_own_op -!pair_op !left_id.
iMod (auth_acc' with "[ctx own]") as (td) "(%lb & #tdP & close)".
- eauto.
- iClear "t_pub"; eauto.
move: lb; rewrite !pair_included; case=> [] [] Hlvl Hγ_pub _.
move: Hlvl; rewrite lookup_included => /(_ t).
rewrite /= lookup_fmap lookup_singleton => Ht.
assert (is_Some (td !! t)) as [d td_t].
  apply/fmap_is_Some.
  by apply: is_Some_included (Ht) _; eauto.
case: d td_t => [] [] lvl_t γ_pub_t' γ_meta_t td_t.
move: Ht; rewrite td_t /= Some_included_total to_agree_included => e.
apply leibniz_equiv in e; subst lvl_t.
pose proof (Hγ_pub_t := transitivity (cmra_included_r _ _) Hγ_pub).
pose proof (Hγ_pub_mγ := transitivity (cmra_included_l _ _) Hγ_pub).
move: {Hγ_pub} Hγ_pub_t; rewrite lookup_included => /(_ t).
rewrite /= lookup_fmap lookup_singleton td_t /=.
rewrite Some_included_total to_agree_included => Hγ_pub_t.
apply leibniz_equiv in Hγ_pub_t; subst γ_pub_t'.
destruct (td !! TKey Enc k) as [d|] eqn:td_key_e.
  iAssert (▷ False)%I with "[unpubl]" as ">[]"; iModIntro.
  iAssert (unpublished t {[TKey Enc k; TKey Dec k]}) with "[unpubl]" as "unpubl".
    by iExists γ_pub_t; iSplit.
  rewrite /term_data_inv (big_sepM_forall _ td).
  iPoseProof ("tdP" $! (TKey Enc k) with "[//]") as "decl".
  case: d td_key_e => [] [] lvl_e γ_pub_e γ_meta_e td_key_e.
  iDestruct "decl" as "(_ & #He & _)".
  rewrite stermT_TKey_eq.
  iDestruct "He" as (lvl_enc' lvl_dec') "[He <-]".
  iPoseProof (keyT_published with "Hk He") as "{publ} publ"; eauto.
  iPoseProof (own_publish_valid_2 with "publ unpubl") as "%valid".
  rewrite coGset_pair_valid_eq /= left_id_L in valid.
  set_solver.
destruct (td !! TKey Dec k) as [d|] eqn:td_key_d.
  iAssert (▷ False)%I with "[unpubl]" as ">[]"; iModIntro.
  iAssert (unpublished t {[TKey Enc k; TKey Dec k]}) with "[unpubl]" as "unpubl".
    by iExists γ_pub_t; iSplit.
  rewrite /term_data_inv (big_sepM_forall _ td).
  iPoseProof ("tdP" $! (TKey Dec k) with "[//]") as "decl".
  case: d td_key_d => [] [] lvl_d γ_pub_d γ_meta_d td_key_d.
  iDestruct "decl" as "(_ & #Hd & _)".
  rewrite stermT_TKey_eq.
  iDestruct "Hd" as (lvl_enc' lvl_dec') "[Hd <-]".
  iPoseProof (keyT_published with "Hk Hd") as "{publ} publ"; eauto.
  iPoseProof (own_publish_valid_2 with "publ unpubl") as "%valid".
  rewrite coGset_pair_valid_eq /= left_id_L in valid.
  set_solver.
iMod (own_update _ _ (coGset_pair_set {[TKey Enc k; TKey Dec k]})
        with "unpubl") as "#publ_t".
  exact: coGset_pair_alloc_update.
iAssert (published t {[TKey Enc k; TKey Dec k]}) as "{publ_t} publ_t".
  by iExists γ_pub_t; eauto.
pose (Ts_e := if lvl_enc is Pub then coGset_pair_set ⊤ else coGset_pair_unset ⊤).
pose (Ts_d := if lvl_dec is Pub then coGset_pair_set ⊤ else coGset_pair_unset ⊤).
iMod (own_alloc Ts_e) as (γ_pub_e) "pub_e" => //.
  by rewrite /Ts_e; case: (lvl_enc).
iMod (own_alloc Ts_d) as (γ_pub_d) "pub_d" => //.
  by rewrite /Ts_d; case: (lvl_dec).
iMod (own_alloc (namespace_map_token ⊤)) as (γ_meta_e) "meta_e" => //.
  exact: namespace_map_token_valid.
iMod (own_alloc (namespace_map_token ⊤)) as (γ_meta_d) "meta_d" => //.
  exact: namespace_map_token_valid.
pose (d_e := (lvl_enc, γ_pub_e, γ_meta_e)).
pose (frag_e := {[TKey Enc k := d_e]} : gmap _ _).
pose (d_d := (lvl_dec, γ_pub_d, γ_meta_d)).
pose (frag_d := {[TKey Dec k := d_d]} : gmap _ _).
pose (td' := <[TKey Enc k:=d_e]>(<[TKey Dec k:=d_d]>td)).
set  frag := (singletonM _ _, op _ _, _).
pose (frag' := to_term_data' {[TKey Enc k := d_e]} ⋅
               (to_term_data' {[TKey Dec k := d_d]} ⋅ frag)).
iAssert (crypto_own frag' -∗ stermT lvl_enc (TKey Enc k) ∗
                             stermT lvl_dec (TKey Dec k))%I as "post".
  rewrite /crypto_own 2!auth_own_op.
  iIntros "#(own_e & own_d & _) {t_pub}".
  rewrite /to_term_data' /= !map_fmap_singleton /=.
  rewrite auth_own_prod_3.
  iDestruct "own_e" as "(?&?&?)".
  rewrite [auth_own crypto_name (singletonM _ _, singletonM _ _, _)]auth_own_prod_3.
  iDestruct "own_d" as "(?&?&?)".
  rewrite -keyT_eq.
  iLeft.
  do 3![iSplit => //].
    rewrite (big_sepS_delete _ (atoms k)) //; iSplit => //.
  by rewrite stermT_eq; iDestruct "Hk" as "[??]"; eauto.
iAssert (⌜lvl_enc = Pub⌝ -∗ □ (crypto_own frag' -∗ published (TKey Enc k) ⊤))%I
    with "[pub_e]" as "#pub_e'".
  iIntros "->".
  iPoseProof "pub_e" as "#pub_e".
  rewrite /crypto_own 2!auth_own_op.
  iIntros "!> (#own_e & _ & _) {post t_pub}".
  rewrite /to_term_data' !map_fmap_singleton /= auth_own_prod_3.
  iDestruct "own_e" as "(?&own_e&?)".
  by iExists γ_pub_e; iSplit.
iAssert (⌜lvl_dec = Pub⌝ -∗ □ (crypto_own frag' -∗ published (TKey Dec k) ⊤))%I
    with "[pub_d]" as "#pub_d'".
  iIntros "-> {post pub_e'}".
  iPoseProof "pub_d" as "#pub_d".
  rewrite /crypto_own 2!auth_own_op.
  iIntros "!> (_ & #own_d & _) {t_pub}".
  rewrite /to_term_data' !map_fmap_singleton /= auth_own_prod_3.
  iDestruct "own_d" as "(?&own_d&?)".
  by iExists γ_pub_d; iSplit.
iMod ("close" $! td' frag' with "[]") as "#key_info"; first iSplit.
- iPureIntro.
  eapply transitivity; last first.
    apply: term_data_local_update => //.
    by rewrite lookup_insert_ne // td_key_e.
  by apply: term_data_local_update => //.
- iIntros "#own !> {t_pub}".
  iDestruct ("post" with "own") as "{post} [??]".
  rewrite /term_data_inv big_sepM_insert ?lookup_insert_ne //.
  iSplit => //.
    rewrite /=; do 2![iSplit => //].
    case: (lvl_enc) => //.
    by iDestruct ("pub_e'" with "[//] own") as "?".
  rewrite big_sepM_insert ?lookup_insert_ne //.
  iSplit => //.
  rewrite /=; do 2![iSplit => //].
  case: (lvl_dec) => //.
  by iDestruct ("pub_d'" with "[//] own") as "?".
iIntros "!> {pub_e' pub_d'}".
iDestruct ("post" with "key_info") as "[??] {post t_pub}".
rewrite /crypto_own !auth_own_op.
iDestruct "key_info" as "(own_e & own_d & _)".
rewrite /to_term_data' /= !map_fmap_singleton.
rewrite auth_own_prod_3 /=; iDestruct "own_e" as "(?&?&?)".
rewrite [auth_own _ (singletonM _ _, singletonM _ _, _)]auth_own_prod_3 /=.
iDestruct "own_d" as "(?&?&?)".
do 2![iSplit => //].
iSplitL "pub_e" => //.
  case: (lvl_enc) @Ts_e => //=.
  by iExists γ_pub_e; iSplit.
iSplitL "pub_d" => //.
  case: (lvl_dec) @Ts_d => //=.
  by iExists γ_pub_d; iSplit.
by iSplitL "meta_e"; [iExists γ_meta_e|iExists γ_meta_d]; eauto.
Qed.

Lemma declare_pub_key k :
  stermT Pub k -∗
  stermT Pub (TKey Enc k) ∗
  stermT Pub (TKey Dec k).
Proof.
iIntros "#Hk"; rewrite -keyT_eq.
iRight.
iSplit; first by iDestruct "Hk" as "[??]".
by eauto.
Qed.

Lemma declare_key E k t lvl lvl_enc lvl_dec :
  ↑cryptoN ⊆ E →
  t ∈ atoms k →
  lvl_enc ⊔ lvl_dec ⊑ lvl→
  crypto_ctx -∗
  stermT lvl k -∗
  stermT lvl t -∗
  guarded (lvl = Sec) (unpublished t {[TKey Enc k; TKey Dec k]}) -∗
  guarded (lvl = Sec) (
    [∗ set] t' ∈ atoms k ∖ {[t]}, published t' {[TKey Enc k; TKey Dec k]}) ={E}=∗
  stermT lvl_enc (TKey Enc k) ∗
  stermT lvl_dec (TKey Dec k) ∗
  guarded (lvl_enc = Sec) (unpublished (TKey Enc k) ⊤) ∗
  guarded (lvl_dec = Sec) (unpublished (TKey Dec k) ⊤) ∗
  guarded (lvl = Sec) (crypto_meta_token (TKey Enc k) ⊤) ∗
  guarded (lvl = Sec) (crypto_meta_token (TKey Dec k) ⊤).
Proof.
case: lvl => /=.
  case: lvl_enc lvl_dec => [] // [] //= _ _ _.
  iIntros "_ Hk _ _ _".
  iDestruct (declare_pub_key with "Hk") as "[??]".
  by iModIntro; iFrame.
by iIntros (? ? ?); iApply declare_sec_key.
Qed.

Lemma atomic_atoms t : atomic t → atoms t = {[t]}.
Proof. by case: t. Qed.

Lemma crypto_own_valid_2 (td1 td2 : term_data') :
  crypto_own td1 -∗
  crypto_own td2 -∗
  ✓ (td1 ⋅ td2).
Proof.
iIntros "#own1 #own2".
iAssert (crypto_own (td1 ⋅ td2)) as "own".
  by rewrite /crypto_own auth_own_op; iSplit.
iApply (auth_own_valid with "own").
Qed.

Lemma unpublished_op t Ts1 Ts2 :
  Ts1 ## Ts2 →
  unpublished t (Ts1 ⋅ Ts2) ⊣⊢ unpublished t Ts1 ∗ unpublished t Ts2.
Proof.
move=> disj; apply (anti_symm _).
- iDestruct 1 as (γ) "[#H1 H2]".
  rewrite coGset_pair_unset_union //.
  by iDestruct "H2" as "[H21 H22]"; iSplitL "H21"; iExists γ; iSplit.
- iIntros "[H1 H2]".
  iDestruct "H1" as (γ1) "[#H11 H12]".
  iDestruct "H2" as (γ2) "[#H21 H22]".
  iPoseProof (crypto_own_valid_2 with "H11 H21") as "%valid".
  case: valid => [] /= [] _ /= valid _.
  rewrite singleton_op singleton_valid in valid *.
  move=> /agree_op_invL' ->.
  iExists γ2; iSplit => //.
  by rewrite coGset_pair_unset_union // own_op; iFrame.
Qed.

Lemma unpublished_difference t Ts1 Ts2 :
  Ts1 ⊆ Ts2 →
  unpublished t Ts2 ⊣⊢ unpublished t Ts1 ∗ unpublished t (Ts2 ∖ Ts1).
Proof.
move=> sub.
rewrite {1}(_ : Ts2 = Ts1 ∪ (Ts2 ∖ Ts1)) ?unpublished_op //; first set_solver.
rewrite [_ ∪ _]comm_L difference_union_L. set_solver.
Qed.

Lemma termT_hash l t : termT l (THash t) ⊣⊢ termT Sec t.
Proof. by rewrite termT_eq. Qed.

End Resources.

Arguments crypto_name {Σ _}.
Arguments crypto_inv {Σ _ _}.
Arguments crypto_ctx {Σ _ _}.
