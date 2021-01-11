From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list namespace_map.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib term coGset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cryptoN := nroot.@"crypto".

(* TODO: Move to Iris *)
Inductive readers :=
| RPub
| RPriv of gset loc.

Canonical readersO := leibnizO readers.

Instance inhabited_readers : Inhabited readers :=
  populate RPub.

Instance readers_elem_of : ElemOf loc readers := λ l rs,
  match rs with
  | RPub => True
  | RPriv rs => l ∈ rs
  end.
Instance readers_subseteq : SubsetEq readers := _.
Instance readers_singleton : Singleton loc readers := λ l,
  RPriv {[l]}.
Instance readers_union : Union readers := λ rs1 rs2,
  match rs1, rs2 with
  | RPriv rs1, RPriv rs2 => RPriv (rs1 ∪ rs2)
  | _, _ => RPub
  end.
Instance readers_empty : Empty readers := RPriv ∅.
Instance readers_semiset : SemiSet loc readers.
Proof.
split.
- by move=> x; rewrite /elem_of /=; apply/elem_of_empty; case.
- by move=> x y; rewrite /elem_of /= elem_of_singleton.
- move=> [|X] [|Y] l; rewrite /union /elem_of /=; try by intuition eauto.
  by rewrite elem_of_union.
Qed.

Instance readers_valid : Valid readers := λ _, True.
Instance readers_validN : ValidN readers := λ _ _, True.
Instance readers_pcore : PCore readers := λ x, Some x.
Instance readers_op : Op readers := union.

Lemma readers_subseteq_equiv (rs1 rs2 : readers) :
  rs1 ⊆ rs2 ↔
  match rs1, rs2 with
  | _, RPub => True
  | RPub, _ => False
  | RPriv rs1, RPriv rs2 => rs1 ⊆ rs2
  end.
Proof.
case: rs1 rs2=> [|rs1] [|rs2] //=.
split=> // /(_ (fresh rs2) I).
rewrite /elem_of /=; exact: is_fresh.
Qed.

Lemma readers_cmra_mixin : CmraMixin readers.
Proof.
apply cmra_total_mixin; eauto.
- by move=> x ? y1 y2 ->.
- by move=> n x y ->.
- by move=> ??? ->.
- by move=> x; split.
- case=> [|rs1] [|rs2] [|rs3] //; congr RPriv; exact: assoc.
- case=> [|rs1] [|rs2] //; congr RPriv; exact: comm.
- case=> // rs1; congr RPriv; set_solver+.
Qed.
Canonical readersR := CmraT readers readers_cmra_mixin.

Instance readers_cmra_discrete : CmraDiscrete readersR.
Proof. by split; first apply _. Qed.

Instance readers_unit : Unit readers := RPriv ∅.
Lemma readers_ucmra_mixin : UcmraMixin readersR.
Proof. split=> //; case=> // rs; congr RPriv; set_solver+. Qed.

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
Notation key_pred := (prodO termO termO -n> iPropO).
Implicit Types Φ : key_pred.
Implicit Types l : loc.
Implicit Types lvl : level.
Implicit Types γ : gname.

Implicit Types P Q : iProp.

Definition guarded lvl P : iProp :=
  if lvl is Sec then P else emp.

Lemma guarded_leq lvl1 lvl2 P :
  lvl2 ⊑ lvl1 →
  guarded lvl1 P -∗ guarded lvl2 P.
Proof. by case: lvl1 lvl2 => [] [] //= _; iIntros. Qed.

Global Instance guarded_persistent lvl P :
  Persistent P →
  Persistent (guarded lvl P).
Proof. case: lvl; apply _. Qed.

Lemma guarded_sep lvl P Q :
  guarded lvl (P ∗ Q) ⊣⊢ guarded lvl P ∗ guarded lvl Q.
Proof.
case: lvl => /=; eauto.
by rewrite -bi.intuitionistically_emp -bi.intuitionistically_sep_dup.
Qed.

Global Instance guarded_from_sep lvl P Q R :
  FromSep P Q R →
  FromSep (guarded lvl P) (guarded lvl Q) (guarded lvl R).
Proof.
rewrite {2}/FromSep; iIntros (FS) "H".
rewrite -guarded_sep; case: lvl => //=.
by iApply from_sep.
Qed.

Global Instance guarded_into_sep lvl P Q R :
  IntoSep P Q R →
  IntoSep (guarded lvl P) (guarded lvl Q) (guarded lvl R).
Proof.
rewrite {2}/IntoSep; iIntros (FS) "H".
rewrite -guarded_sep; case: lvl => //=.
by iApply into_sep.
Qed.

Global Instance guarded_into_and b lvl (P Q R : iProp) :
  IntoAnd b P Q R →
  IntoAnd b (guarded lvl P) (guarded lvl Q) (guarded lvl R).
Proof.
by case: b lvl=> [] //= [] //= _; rewrite /IntoAnd /=; eauto.
Qed.

Lemma guarded_fupd `{!invG Σ} lvl E P :
  guarded lvl (|={E}=> P) ⊣⊢ |={E}=> guarded lvl P.
Proof.
by case: lvl => //=; apply (anti_symm _); iIntros => //.
Qed.

Lemma guarded_later lvl P :
  guarded lvl (▷ P) ⊣⊢ ▷ guarded lvl P.
Proof. by case: lvl => //=; rewrite bi.later_emp. Qed.

Lemma guarded_mono lvl P Q :
  guarded lvl P -∗
  □ (P -∗ Q) -∗
  guarded lvl Q.
Proof.
iIntros "HP #PQ"; by case: lvl => //; iApply "PQ".
Qed.

Lemma guarded_exist T lvl (φ : T -> iProp) :
  Inhabited T →
  guarded lvl (∃ x : T, φ x) ⊣⊢ ∃ x : T, guarded lvl (φ x).
Proof.
move=> ?; case: lvl=> //=.
apply (anti_symm _); last by eauto.
by iIntros "_"; iExists inhabitant.
Qed.

Global Instance guarded_from_exist T lvl (φ : T -> iProp) :
  Inhabited T →
  FromExist (guarded lvl (∃ x, φ x)) (λ x, guarded lvl (φ x)).
Proof.
by move => ?; rewrite /FromExist guarded_exist.
Qed.

Global Instance guarded_into_exist T lvl (φ : T -> iProp) :
  Inhabited T →
  IntoExist (guarded lvl (∃ x, φ x)) (λ x, guarded lvl (φ x)).
Proof.
by move => ?; rewrite /IntoExist guarded_exist.
Qed.

Lemma guarded_box lvl (P : iProp) : □ guarded lvl P ⊣⊢ guarded lvl (□ P).
Proof.
case: lvl => //=; by rewrite bi.intuitionistically_emp.
Qed.

Global Instance guarded_box_into_persistent p lvl (P Q : iProp) :
  IntoPersistent p P Q →
  IntoPersistent p (guarded lvl P) (guarded lvl Q).
Proof.
case: lvl => //= _.
by rewrite /IntoPersistent; rewrite -bi.persistently_emp_intro; eauto.
Qed.

Definition atomic t : bool :=
  match t with
  | TInt _ => false
  | TPair _ _ => false
  | TNonce _ => true
  | TKey _ _ => true
  | TEnc _ _ => false
  end.

Fixpoint atoms t : gset term :=
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => atoms t1 ∪ atoms t2
  | TNonce _ => {[t]}
  | TKey _ _ => {[t]}
  | TEnc _ t => atoms t
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

Notation nonce := loc (only parsing).
Implicit Types (a : nonce).

Context `{!heapG Σ}.

Definition term_data : Type :=
  gmap term (level * gname * coGset term * coGset term).

Global Instance term_data_inhabited : Inhabited term_data.
Proof. apply _. Qed.

Definition term_data' : Type :=
  gmap term (agree level) *
  gmap term (agree gname) *
  gmap term (coGset_pair term).

Canonical term_data'UR :=
  (fun (sT : ucmraT) (f : term_data' -> sT) => sT) _ (fun x => x).

Definition to_term_data' (td : term_data) : term_data'UR :=
  (fmap (fun '(lvl, _, _ , _) => to_agree lvl) td,
   fmap (fun '(_  , γ, _ , _) => to_agree γ)   td,
   fmap (fun '(_  , _, Ts, Ds) =>
           coGset_pair_unset Ts ⋅ coGset_pair_set Ds) td).

Class cryptoG := CryptoG {
  crypto_inG :> inG Σ (authUR term_data'UR);
  crypto_meta_inG :> inG Σ (namespace_mapR (agreeR positiveO));
  crypto_key_inG :> inG Σ (agreeR key_pred);
  crypto_name : gname;
}.

Context `{!cryptoG}.

Global Instance cryptoG_authG : authG Σ term_data'UR := @AuthG _ _ _ _.

Implicit Types d : level * gname * coGset term * coGset term.
Implicit Types td : term_data.

Definition wf_key_data k d td : Prop :=
  let '(lvl, _, _, _) := d in
  atoms k ⊆ dom _ td ∧
  ((∀ t' lvl' γ' Ts' Ds', t' ∈ atoms k →
      td !! t' = Some (lvl', γ', Ts', Ds') →
      lvl' = Pub) →
      lvl = Pub) ∧
   ∀ t' γ' Ts' Ds', t' ∈ atoms k →
     td !! t' = Some (Sec, γ', Ts', Ds') →
     k ∈ Ds'.

Definition declared t d td : iProp :=
  match t with
  | TNonce a =>
    meta a (cryptoN.@"nonce") ()
  | TKey _ k => ⌜wf_key_data k d td⌝
  | _ => False
  end.

Global Instance declared_persistent t d td : Persistent (declared t d td).
Proof. by case: t=> *; apply _. Qed.

Global Instance declared_timeless t d td : Timeless (declared t d td).
Proof. by case: t=> *; apply _. Qed.

Definition term_data_inv (td : term_data) : iProp :=
  ([∗ map] t ↦ d ∈ td, declared t d td)%I.

Global Instance term_data_inv_persistent td : Persistent (term_data_inv td).
Proof. by apply _. Qed.

Global Instance term_data_inv_timeless td : Timeless (term_data_inv td).
Proof. by apply _. Qed.

Definition crypto_inv :=
  auth_inv crypto_name to_term_data' term_data_inv.

Definition crypto_ctx :=
  auth_ctx crypto_name cryptoN to_term_data' term_data_inv.

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
  crypto_own (∅, {[t := to_agree γm]}, ∅).

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
iDestruct "valid" as "((_ & #valid) & _)".
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

Definition key_predT Φ t : iProp :=
  ∃ γ, crypto_meta t (cryptoN.@"key") γ ∗
       own γ (to_agree Φ).

Global Instance key_predT_persistent Φ t : Persistent (key_predT Φ t).
Proof. by apply _. Qed.

Lemma key_predT_agree Φ1 Φ2 t :
  key_predT Φ1 t -∗
  key_predT Φ2 t -∗
  Φ1 ≡ Φ2.
Proof.
iDestruct 1 as (γ1) "[#meta1 #own1]".
iDestruct 1 as (γ2) "[#meta2 #own2]".
iPoseProof (crypto_meta_agree with "meta2 meta1") as "->".
iPoseProof (own_valid_2 with "own1 own2") as "#valid".
by rewrite agree_validI agree_equivI.
Qed.

(** [termT lvl t] holds when the term [t] can be declared public after
encrypting it.  If [lvl = Pub], [t] is considered public and does not have to be
encrypted.  *)

Fixpoint termT_def lvl t : iProp :=
  let keyT lvl_enc lvl_dec k :=
    (atomicT lvl_enc (TKey Enc k) ∗
     atomicT lvl_dec (TKey Dec k) ∗
     termT_def Sec k ∗
     □ (termT_def Pub k → False) ∨
     termT_def Pub k ∗
     ⌜lvl_enc = Pub⌝ ∗
     ⌜lvl_dec = Pub⌝)%I in
  match t with
  | TInt _ => True
  | TPair t1 t2 => termT_def lvl t1 ∗ termT_def lvl t2
  | TNonce _  =>
    ∃ lvl', atomicT lvl' t ∗ ⌜lvl' ⊑ lvl⌝
  | TKey kt k =>
    ∃ lvl_enc lvl_dec,
      keyT lvl_enc lvl_dec k ∗
      ⌜(if kt is Enc then lvl_enc else lvl_dec) ⊑ lvl⌝
  | TEnc k t =>
    ∃ lvl_enc lvl_dec,
      keyT lvl_enc lvl_dec k ∗
      (⌜lvl_enc = Pub⌝ ∗ termT_def Pub t ∨
       ∃ Φ, key_predT Φ k ∗ □ Φ (k, t) ∗ termT_def (lvl ⊔ lvl_dec) t)
  end.

Definition termT_aux : seal termT_def. by eexists. Qed.
Definition termT := unseal termT_aux.
Definition keyT lvl_enc lvl_dec k : iProp :=
  atomicT lvl_enc (TKey Enc k) ∗
  atomicT lvl_dec (TKey Dec k) ∗
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
  | TNonce _  =>
    ∃ lvl', atomicT lvl' t ∗ ⌜lvl' ⊑ lvl⌝
  | TKey kt k =>
    ∃ lvl_enc lvl_dec,
      keyT lvl_enc lvl_dec k ∗
      ⌜(if kt is Enc then lvl_enc else lvl_dec) ⊑ lvl⌝
  | TEnc k t =>
    ∃ lvl_enc lvl_dec,
      keyT lvl_enc lvl_dec k ∗
      (⌜lvl_enc = Pub⌝ ∗ termT Pub t ∨
       ∃ Φ, key_predT Φ k ∗ □ Φ (k, t) ∗ termT (lvl ⊔ lvl_dec) t)
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
- iDestruct "Hk" as "(enc & dec & _)".
  iDestruct "Hk'" as "(enc' & dec' & _)".
  iDestruct (atomicT_agree with "enc enc'") as "->".
  by iDestruct (atomicT_agree with "dec dec'") as "->".
- iDestruct "Hk" as "(enc & dec & sec & #npub)".
  iDestruct "Hk'" as "(pub & _)".
  by iDestruct ("npub" with "pub") as "[]".
- iDestruct "Hk" as "(pub & _)".
  iDestruct "Hk'" as "(_ & _ & _ & npub)".
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

Lemma sub_termT lvl lvl' t :
  lvl ⊑ lvl' →
  termT lvl t -∗
  termT lvl' t.
Proof.
elim: t lvl lvl' => [n|t1 IH1 t2 IH2|l|kt k _|k _ t IH] lvl lvl' sub.
- by rewrite !termT_eq.
- rewrite ![termT _ (TPair t1 t2)]termT_eq /=.
  by iIntros "[#Ht1 #Ht2]"; rewrite IH1 // IH2 //; iSplit.
- rewrite !termT_eq /=.
  iDestruct 1 as (lvl0) "[#Hnonce %sub0]".
  iExists lvl0; iSplit=> //; iPureIntro; by etransitivity.
- rewrite ![termT _ (TKey _ k)]termT_eq.
  iDestruct 1 as (lvl_enc lvl_dec) "(#Hkey & %sub0)".
  iExists lvl_enc, lvl_dec; iSplit=> //; iPureIntro; by etransitivity.
- rewrite ![termT _ (TEnc _ t)]termT_eq.
  iDestruct 1 as (lvl_enc lvl_dec) "# (Hk & Ht)".
  iExists lvl_enc, lvl_dec; iSplit => //.
  iDestruct "Ht" as "[Ht|Ht]"; eauto.
  iDestruct "Ht" as (Φ) "(HΦ & tP & Ht)".
  iRight; iExists Φ; do 2![iSplit => //].
  iApply (IH with "Ht").
  by case: lvl lvl' lvl_dec sub=> [] [] [].
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

(*
Lemma stermT_atomic lvl t : atomicT lvl t -∗ stermT lvl t.
Proof.
move=> atomic_t; iIntros "#atomic"; iSplit; first by iApply termT_atomic.
iIntros "!>" (lvl') "#Ht".
rewrite termT_eq; case: t atomic_t => //= [l|kt k] _.
- iDestruct "Ht" as (lvl'') "[atomic' %leq]" => //.
by iPoseProof (atomicT_agree with "atomic atomic'") as "->".


case: t =
iDestruct (termT_atomicE with "Ht") as (lvl'') "[atomic' %leq]" => //.
by iPoseProof (atomicT_agree with "atomic atomic'") as "->".
Qed.
*)

(*
Lemma stermT_TKeyE kt k : stermT Sec (TKey kt k) -∗ atomicT Sec (TKey kt k).
Proof.
iIntros "# (Hk & #min)"; rewrite termT_eq /= -termT_eq.
iDestruct "Hk" as "[Hk|Hk]"; last first.
  iAssert (⌜Sec ⊑ Pub⌝)%I as "%" => //.
  iApply "min"; eauto.
iDestruct "Hk" as (lvl) "(Hk & ? & _)".
iAssert (⌜Sec ⊑ lvl⌝)%I as "%leq".
  by iApply "min"; iLeft; eauto.
by case: lvl leq.
Qed.
*)

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

(*
Lemma termT_TEncE lvl k t :
  termT lvl (TEnc k t) ⊣⊢
  termT Pub (TKey Enc k) ∗ termT Pub t ∨
  ∃ lvl_enc lvl_dec Φ,
    termT lvl_enc (TKey Enc k) ∗
    stermT lvl_dec (TKey Dec k) ∗
    termT (lvl ⊔ lvl_dec) t ∗
    key_predT Φ k ∗
    □ Φ (k, t).
Proof.
rewrite termT_eq /= -termT_eq; apply: (anti_symm _).
- iDestruct 1 as "# [[Hk Ht]|[[Hk Ht]|Ht]]".
  + by iLeft; iSplit => //; eauto.
  + by iLeft; eauto.
  + iDestruct "Ht" as (lvl_enc lvl_dec Φ) "(enc & dec & pred & #inv & Ht)".
    iRight; iExists lvl_enc, lvl_dec, Φ.
    iSplit; eauto.
    by iSplit; eauto.
- iDestruct 1 as "# [[Hk Ht]|Ht]".
  + iDestruct "Hk" as "[Hk|Hk]"; eauto.
    iDestruct "Hk" as (lvl') "[Hk %leq]".
    case: lvl' leq => // _; eauto.
  + iDestruct "Ht" as
        (lvl_enc lvl_dec Φ) "(enc & dec & Ht & pred & #inv)".
*)


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

Lemma termT_tag lvl n t :
  termT lvl (Spec.tag n t) ⊣⊢ termT lvl t.
Proof.
by rewrite Spec.tag_eq termT_eq /= termT_eq bi.True_sep.
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
elim: t lvl=> [n|t1 IH1 t2 IH2|n|kt k IHk|k IHk t IHt] lvl /=;
rewrite termT_eq /=.
- iIntros "_"; iExists Pub; iApply stermT_int.
- iIntros "[#type1 #type2]".
  iDestruct (IH1 with "type1") as (lvl1) "type1'".
  iDestruct (IH2 with "type2") as (lvl2) "type2'".
  by iExists (lvl1 ⊔ lvl2); iApply stermT_pair.
- iDestruct 1 as (lvl') "[#Hn %Hsub]".
  iExists lvl'.
  iSplit; first by rewrite termT_eq /=; eauto.
  iIntros "!>" (lvl''); rewrite termT_eq /=.
  iDestruct 1 as (lvl''') "# [Hn' %leq']".
  by iPoseProof (atomicT_agree with "Hn' Hn") as "->".
- iDestruct 1 as (lvl_enc lvl_dec) "[Hk _]".
  rewrite keyT_eq; iDestruct "Hk" as "[??]".
  by destruct kt; eauto.
- iDestruct 1 as (lvl_enc lvl_dec) "# (Hk & Ht)".
  iDestruct "Ht" as "[[-> Ht]|Ht]".
    iExists Pub; rewrite stermT_eq keyT_eq stermT_eq.
    iApply termT_aenc_pub_pub => //.
    by iDestruct "Hk" as "[??]".
  iDestruct "Ht" as (Φ) "(HΦ & #tP & Ht)".
  iDestruct (IHt with "Ht") as (lvl') "Ht'".
  case: lvl'.
    iExists Pub; rewrite !stermT_eq /=.
    rewrite [termT Pub (TEnc _ _)]termT_eq.
    iExists lvl_enc, lvl_dec; iSplit => //.
    case: lvl_enc; eauto.
    iRight; iExists Φ; do 2![iSplit => //].
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
  iDestruct "Ht'" as (?) "(? & ? & Ht')".
  by iApply "pub".
Qed.

Lemma termT_adec_pub Φ k t :
  termT Pub (TEnc k t) -∗
  key_predT Φ k -∗
  termT Pub t ∨ □ Φ (k, t) ∗ termT Sec t.
Proof.
rewrite termT_eq; iIntros "#Ht #HΦ".
iDestruct "Ht" as (lvl_enc lvl_dec) "# (Hk & Ht)".
iDestruct "Ht" as "[(?&?)|Ht]"; eauto.
iDestruct "Ht" as (Φ') "(HΦ' & #inv & Ht)".
iPoseProof (key_predT_agree with "HΦ' HΦ") as "e".
rewrite ofe_morO_equivI; iRewrite ("e" $! (k, t)) in "inv"; iClear "e".
iRight; iSplit => //; iApply (sub_termT with "Ht"); by case: lvl_dec.
Qed.

Lemma termT_adec_pub_sec Φ k t :
  termT Pub (TEnc k t) -∗
  key_predT Φ k -∗
  ∃ lvl, termT lvl t ∗ guarded lvl (□ Φ (k, t)).
Proof.
iIntros "Ht Hpred".
iPoseProof (termT_adec_pub with "Ht Hpred") as "[Ht|Ht]".
- by iExists Pub; iSplit.
- by iExists Sec; iDestruct "Ht" as "[??]"; iSplit.
Qed.

Lemma termT_aenc_pub_sec lvl Φ k t :
  termT  lvl (TKey Enc k) -∗
  stermT Sec (TKey Dec k) -∗
  key_predT Φ k -∗
  □ Φ (k, t) -∗
  termT Sec t -∗
  termT Pub (TEnc k t).
Proof.
iIntros "#Henc #Hdec #HΦ #HΦt #Ht".
iDestruct (termT_lvlP with "Henc") as (lvl') "{Henc} Henc".
rewrite [termT _ (TEnc _ _)]termT_eq.
by iExists lvl', Sec; rewrite keyT_eq; iSplit; eauto.
Qed.

Lemma termT_aenc_pub_secG k Φ lvl t :
  termT Pub (TKey Enc k) -∗
  termT lvl t -∗
  guarded lvl (stermT Sec (TKey Dec k)) -∗
  guarded lvl (key_predT Φ k) -∗
  guarded lvl (□ Φ (k, t)) -∗
  termT Pub (TEnc k t).
Proof.
iIntros "#Henc #Ht #Hdec #Hpred #HG"; case: lvl => /=.
- by iApply termT_aenc_pub_pub.
- by iApply termT_aenc_pub_sec.
Qed.

Lemma auth_own_4
  (a : gmap term (agree level))
  (b : gmap term (agree gname))
  (c : gmap term (coGset_pair term)) :
  auth_own crypto_name (a, b, c) ⊣⊢
  auth_own crypto_name (a, ε, ε) ∗
  auth_own crypto_name (ε, b, ε) ∗
  auth_own crypto_name (ε, ε, c).
Proof.
rewrite -auth_own_op -auth_own_op.
rewrite -!pair_op /=.
by rewrite !(ucmra_unit_left_id, ucmra_unit_right_id).
Qed.

Definition unpublished t Ts : iProp :=
  stermT Sec t -∗ crypto_own (∅, ∅, {[t := coGset_pair_unset Ts]}).

Definition published t Ts : iProp :=
  □ (stermT Sec t -∗ crypto_own (∅, ∅, {[t := coGset_pair_set Ts]})).

Global Instance published_persistent t Ts : Persistent (published t Ts).
Proof. apply _. Qed.

(* MOVE *)
Lemma Some_included_ucmra {A : ucmraT} (a b : A) : Some a ≼ Some b ↔ a ≼ b.
Proof.
split; last exact: Some_included_2.
case=> [mc]; rewrite option_equivE.
case: mc => [c|] //= e; [by exists c|exists ε].
by rewrite ucmra_unit_right_id.
Qed.
(* /MOVE *)


Lemma term_data_inv_insert td t lvl γm Ts1 Ts2 Ds :
  Ts1 ⊆ Ts2 →
  td !! t = Some (lvl, γm, Ts2, Ds) →
  term_data_inv td -∗
  term_data_inv (<[t := (lvl, γm, Ts2 ∖ Ts1, Ds ∪ Ts1)]>td).
Proof.
iIntros (sub td_t) "#inv".
rewrite /term_data_inv !big_sepM_forall.
iIntros (t' d'); destruct (decide (t' = t)) as [->|ne].
- rewrite lookup_insert; iIntros "%e"; case: e=> ?; subst d'.
  iSpecialize ("inv" $! t with "[]"); eauto.
  case: t td_t => //= kt k td_t.
  iDestruct "inv" as % (sub_dom & all_pub & publ).
  iPureIntro; repeat split.
  + set_solver.
  + move=> pub; apply: all_pub => t' lvl' γm' Ts' Ds' t'_atom td_t'.
    apply: pub (t'_atom) _.
    rewrite lookup_insert_ne // => ?; subst t'.
    move/atoms_term_height: t'_atom => /=; lia.
  + move=> t' γm' Ts' Ds' t'_atom.
    destruct (decide (t' = TKey kt k)) as [->|ne].
      rewrite lookup_insert; case => ????; subst lvl γm' Ts' Ds'.
      move/atoms_term_height: t'_atom => /=; lia.
    rewrite lookup_insert_ne //. exact: publ.
- rewrite lookup_insert_ne //.
  iIntros (td_t').
  iSpecialize ("inv" $! t' d' with "[//]").
  case: d' td_t' => [] [] [] lvl' γm' Ts' Ds' td_t'.
  case: t' td_t' ne => //= kt k td_t' ne.
  iDestruct "inv" as % (sub_dom & all_pub & publ).
  iPureIntro; repeat split.
  + set_solver.
  + move=> pub; apply: all_pub => t'' lvl'' γm'' Ts'' Ds'' t''_atom td_t''.
    destruct (decide (t'' = t)) as [->|ne''].
      apply: pub (t''_atom) _.
      rewrite lookup_insert //; eauto.
      move: td_t''; rewrite td_t; case => <- _ _ _.
      by eauto.
    apply: pub (t''_atom) _.
    by rewrite lookup_insert_ne //.
  + move=> t'' γm'' Ts'' Ds'' t''_atom.
    destruct (decide (t'' = t)) as [->|ne''].
      rewrite lookup_insert; case => ????; subst lvl γm'' Ts'' Ds''.
      move/(_ _ _ _ _ t''_atom td_t) in publ; set_solver.
    rewrite lookup_insert_ne //. exact: publ.
Qed.

Lemma publish E lvl t Ts :
  ↑cryptoN ⊆ E →
  crypto_ctx -∗
  termT lvl t -∗
  unpublished t Ts ={E}=∗
  published t Ts.
Proof.
iIntros (sub) "#ctx #Ht unpubl".
iDestruct (termT_lvlP with "Ht") as (lvl') "{Ht} Ht".
case: lvl' {lvl}.
  iIntros "!> !> #contra".
  by iDestruct (stermT_agree with "Ht contra") as "%".
iSpecialize ("unpubl" with "Ht").
iMod (auth_acc to_term_data' term_data_inv with "[ctx unpubl]")
  as (td) "(%lb & >#tdP & close)"; eauto.
move: lb; rewrite !prod_included; case=> [] [] [] /= _ _ _ lb.
move: lb; rewrite singleton_included_l; case=> [] Ts' [].
rewrite lookup_fmap option_equivE.
case td_t: (td !! t) Ts' => [[] [] [] lvl' γm' Ts' Ds'|] //= _ <-.
rewrite Some_included_ucmra coGset_pair_included /=.
rewrite ucmra_unit_right_id coGset_disj_included /=.
case=> _ incl.
pose (d' := (lvl', γm', Ts' ∖ Ts, Ds' ∪ Ts)).
pose (td' := <[t := d']>td).
iMod ("close" $! td' (∅, ∅, {[t := coGset_pair_set Ts]}) with "[]")
  as "#own"; first iSplit.
- iPureIntro.
  apply prod_local_update => //=.
    by rewrite !fmap_insert /= !insert_id ?lookup_fmap ?td_t.
  rewrite !fmap_insert /=.
  apply: singleton_local_update.
    by rewrite lookup_fmap td_t.
  exact: coGset_pair_local_update.
- iModIntro; by iApply term_data_inv_insert.
by iIntros "!> !> _".
Qed.

Lemma declare_nonce E1 E2 lvl a :
  ↑cryptoN ⊆ E1 →
  ↑cryptoN.@"nonce" ⊆ E2 →
  crypto_ctx -∗
  meta_token a E2 ={E1}=∗
  stermT lvl (TNonce a) ∗
  unpublished (TNonce a) ⊤ ∗
  crypto_meta_token (TNonce a) ⊤.
Proof.
iIntros (sub1 sub2) "#ctx Hmeta".
iMod (auth_empty crypto_name) as "#own0".
iMod (auth_acc to_term_data' with "[ctx own0]") as (td) "(_ & tdP & close)"; eauto.
iDestruct "tdP" as "> # tdP".
pose (t := TNonce a); iAssert (⌜td !! t = None⌝)%I as "%undef".
  case e: (td !! t) => [m|] //=.
  rewrite /term_data_inv big_sepM_forall.
  iSpecialize ("tdP" $! _ _ e).
  iDestruct "tdP" as "[tdP _]".
  rewrite /=.
  by iDestruct (meta_meta_token with "tdP Hmeta") as "[]".
iMod (own_alloc (namespace_map_token ⊤)) as (γm) "token" => //.
  exact: namespace_map_token_valid.
iMod (meta_set ⊤ a () (cryptoN.@"nonce") with "Hmeta") as "#l_nonce"; eauto.
pose (d  := (lvl, ⊤ : coGset term, ∅ : coGset term, γm)).
pose (td'   := <[t := d]>td).
iMod ("close" $! td' (to_term_data' {[t := d]}) with "[]") as "own"; first iSplit.
- iPureIntro; apply: prod_local_update => /=; last first.
    rewrite /td' fmap_insert map_fmap_singleton /=.
    apply alloc_singleton_local_update => //.
    by rewrite lookup_fmap undef.
  apply: prod_local_update; last first.
    rewrite /= /td' fmap_insert map_fmap_singleton /=.
    apply alloc_singleton_local_update => //.
    by rewrite lookup_fmap undef.
  apply: prod_local_update; last first.
    rewrite /= /td' fmap_insert map_fmap_singleton /=.
    apply alloc_singleton_local_update => //.
    by rewrite lookup_fmap undef.
  rewrite /= /td' fmap_insert map_fmap_singleton /=.
  apply alloc_singleton_local_update => //.
  by rewrite lookup_fmap undef.
- iModIntro; rewrite /term_data_inv !big_sepM_forall.
  iIntros (t'); destruct (decide (t' = t)) as [->|ne].
    rewrite lookup_insert; iIntros (?) "%Hlookup"; case: Hlookup => <-.
    by iSplit => //.
  iIntros (d'); rewrite lookup_insert_ne //; iIntros (td_t').
  iDestruct ("tdP" $! _ _ td_t') as "[decl %owned]".
  iSplit => //.
  case: t' ne {td_t'} => //= kt k ne.
  case: d' {owned} => [] [] [] lvl' Ts' Ds' γm' /=.
  iDestruct "decl" as % (k_td & pub & sec); iPureIntro.
  split.
    rewrite dom_insert; set_solver.
  split.
    move=> all_pub; apply: pub.
    move=> t'' lvl'' Ts'' Ds'' γm'' t''_atom td_t''.
    destruct (decide (t'' = t)) as [->|ne'']; first by congruence.
    apply: all_pub; eauto.
    by rewrite lookup_insert_ne //.
  move=> t'' Ts'' Ds'' γm'' t''_atom td'_t''.
  destruct (decide (t'' = t)) as [->|ne''].
    case/(_ _ t''_atom)/elem_of_dom: k_td => ? k_td.
    by rewrite undef in k_td.
  rewrite lookup_insert_ne // in td'_t''.
  exact: sec.
rewrite /to_term_data' !map_fmap_singleton /=.
iClear "own0"; rewrite auth_own_4.
iDestruct "own" as "(#Hlvl & Hown & _ & #Hγm)".
iModIntro; iSplit.
  iSplit; first by rewrite termT_eq; iExists lvl; eauto.
  iIntros "!>" (lvl').
  rewrite termT_eq.
  iDestruct 1 as (lvl'') "[Ha %sub']".
  by iDestruct (atomicT_agree with "Ha Hlvl") as "->".
iSplitL "Hown" => //.
  by iIntros "_".
by iExists γm; eauto.
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
  iDestruct "Ht" as (?) "(_ & _ & Ht)"; by iApply IHt.
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
  iDestruct "sec" as (lvl) "[sec %leq]".
  case: lvl leq => // _.
  iDestruct ("pub" with "[]") as "[]".
  by iExists Pub; iSplit.
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

Lemma declare_sec_key E kt k t lvl :
  ↑cryptoN ⊆ E →
  t ∈ atoms k →
  crypto_ctx -∗
  stermT Sec k -∗
  stermT Sec t -∗
  unpublished t {[TKey kt k]} -∗
  ([∗ set] t' ∈ atoms k ∖ {[t]}, published t' {[TKey kt k]}) ={E}=∗
  atomicT lvl (TKey kt k) ∗
  unpublished (TKey kt k) ⊤ ∗
  crypto_meta_token (TKey kt k) ⊤.
Proof.
iIntros (sub t_atom) "#ctx #Hk #Ht unpubl #publ".
iAssert (∃ T, secret_terms (atoms k ∖ {[t]}) T)%I as "secret".
  iApply secret_termsP.
  rewrite !big_sepS_forall.
  iIntros (t' t'_atom).
  case/elem_of_difference: t'_atom => t'_atom _.
  iApply (termT_atoms _ t'_atom).
  by iDestruct "Hk" as "[??]".
iDestruct "secret" as (T) "secret".
iAssert ([∗ set] t' ∈ T, crypto_own (∅, ∅, {[t' := {[TKey kt k]}]}, ∅))%I
  as "own".
  by iApply unpublished_secret.
iMod (big_opS_auth_own' with "own") as "{own} own".
rewrite !big_opS_pair /= !big_opS_unit /=.
iSpecialize ("unpubl" with "Ht").
rewrite /crypto_own.
iCombine "own unpubl" as "own".
rewrite -auth_own_op -!pair_op !ucmra_unit_right_id ucmra_unit_left_id.
iMod (auth_acc to_term_data' with "[ctx own]") as (td) "(%lb & tdP & close)"; eauto.
iDestruct "tdP" as "> # tdP".
move: lb; rewrite !pair_included; case=> [] [] [] _ Ht HT _.
move: Ht; rewrite lookup_included => /(_ t).
rewrite lookup_fmap lookup_singleton => Ht.
assert (is_Some (td !! t)) as [d td_t].
  apply/fmap_is_Some.
  by apply: is_Some_included (Ht) _; eauto.
case: d td_t => [] [] [] lvl_t Ts_t Ds_t γm_t td_t.
move: Ht; rewrite td_t /= => /Some_included Ht.
have {}Ht : TKey kt k ∈ Ts_t.
  case: Ht => [[<-]|]; first set_solver.
  rewrite coGset_disj_included; set_solver.
move: HT; rewrite lookup_included => HT.
rewrite {1}/term_data_inv big_sepM_forall.
pose (d_t := (lvl_t, Ts_t ∖ {[TKey kt k]}, {[TKey kt k]} ∪ Ds_t, γm_t)).
destruct (td !! TKey kt k) as [d_k|] eqn:td_k.
  iDestruct ("tdP" $! _ _ td_k) as "[%decl_k _]".
  case: d_k decl_k td_k => [] [] [] lvl_k Ts_k Ds_k γm_k decl_k td_k.
  case: decl_k.
Admitted.

End Resources.

Arguments crypto_name {Σ _}.
Arguments crypto_inv {Σ _ _}.
Arguments crypto_ctx {Σ _ _}.

Section Tagging.

Context (Σ : gFunctors).
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation key_inv := (prodO termO termO -n> iPropO).
Implicit Types Φ : key_inv.
Implicit Types l : loc.
Implicit Types lvl : level.
Implicit Types γ : gname.
Implicit Types c : string.
Implicit Types k t : term.

Class tagG := TagG {
  tag_inG :> inG Σ (authR (gmapUR string (agreeR key_inv)));
}.

Context `{!heapG Σ, !cryptoG Σ, !tagG}.

Definition key_tag k c Φ : iProp :=
  ∃ γ, crypto_meta k (cryptoN.@"tag_key") γ ∗
       own γ (◯ {[c := to_agree Φ]}).

Lemma key_tag_persistent k c Φ : Persistent (key_tag k c Φ).
Proof. apply _. Qed.

Lemma key_tag_agree k c Φ1 Φ2 :
  key_tag k c Φ1 -∗
  key_tag k c Φ2 -∗
  Φ1 ≡ Φ2.
Proof.
iDestruct 1 as (γ1) "[#meta1 #own1]".
iDestruct 1 as (γ2) "[#meta2 #own2]".
iPoseProof (crypto_meta_agree with "meta2 meta1") as "->".
iPoseProof (own_valid_2 with "own1 own2") as "#valid".
rewrite auth_validI /= singleton_op gmap_validI; iSpecialize ("valid" $! c).
by rewrite lookup_singleton uPred.option_validI agree_validI agree_equivI.
Qed.

Lemma key_tag_proper n : Proper (eq ==> eq ==> dist n ==> dist n) key_tag.
Proof. solve_contractive. Qed.

Definition tagged_inv_def (p : term * term) : iProp :=
  match p.2 with
  | TPair (TInt (Zpos n)) t =>
    ∃ c Φ, ⌜n = encode c⌝ ∗ key_tag p.1 c Φ ∗ □ (Φ : key_inv) (p.1, t)
  | _ => False
  end.
Definition tagged_inv_aux : seal tagged_inv_def. by eexists. Qed.
Definition tagged_inv := unseal tagged_inv_aux.
Lemma tagged_inv_eq : tagged_inv = tagged_inv_def. Proof. exact: seal_eq. Qed.

Global Instance tagged_inv_proper : NonExpansive tagged_inv.
Proof.
rewrite tagged_inv_eq /tagged_inv_def.
move=> n [l1 t1] [l2 t2] [/= e1 e2].
by rewrite /tagged_inv /= (leibniz_equiv _ _ e1) (leibniz_equiv _ _ e2).
Qed.

Global Instance tagged_inv_persistent p :
  Persistent (tagged_inv p).
Proof.
rewrite tagged_inv_eq /tagged_inv_def.
case: p=> [] k []; try by apply _.
by do 2![case; try by apply _].
Qed.

Definition tkey_predT c Φ k : iProp :=
  key_predT (OfeMor tagged_inv) k ∗
  key_tag k c Φ.

Lemma tagged_inv_intro k c Φ t :
  key_tag k c Φ -∗
  □ Φ (k, t) -∗
  tagged_inv (k, Spec.tag c t).
Proof.
rewrite tagged_inv_eq /tagged_inv_def Spec.tag_eq /=.
by iIntros "own Ht"; eauto.
Qed.

Lemma tagged_inv_elim k t :
  tagged_inv (k, t) -∗
  ∃ c t' Φ, ⌜t = Spec.tag c t'⌝ ∗
            key_tag k c Φ ∗
            □ Φ (k, t').
Proof.
rewrite tagged_inv_eq /tagged_inv_def /=.
iIntros "H".
case: t => [] // [] // [] // n t.
iDestruct "H" as (c Φ) "(-> & own & Ht)".
iExists _, t, Φ.
by rewrite Spec.tag_eq /Spec.tag_def //; eauto.
Qed.

Lemma tagged_inv_elim' Φ k c t :
  key_tag k c Φ -∗
  tagged_inv (k, Spec.tag c t) -∗
  □ Φ (k, t).
Proof.
iIntros "#own #H".
iDestruct (tagged_inv_elim with "H") as (c' t' Φ') "{H} (%e & #own' & #Ht)".
case: (Spec.tag_inj _ _ _ _ e) => ??; subst c' t'.
iPoseProof (key_tag_agree with "own own'") as "#e".
rewrite ofe_morO_equivI.
by iRewrite -("e" $! (k, t)) in "Ht".
Qed.

Lemma termT_tag_aenc_pub_secG k lvl c Φ t :
  termT Pub (TKey Enc k) -∗
  termT lvl t -∗
  guarded lvl (stermT Sec (TKey Dec k)) -∗
  guarded lvl (tkey_predT c Φ k) -∗
  guarded lvl (□ Φ (k, t)) -∗
  termT Pub (TEnc k (Spec.tag c t)).
Proof.
rewrite /tkey_predT; iIntros "#k_lo #t_lo #k_hi [#pred #k_c] #t_hi".
iApply termT_aenc_pub_secG; eauto.
  iApply termT_tag; eauto.
case: lvl => //=; iModIntro.
by iApply tagged_inv_intro.
Qed.

Lemma termT_tag_adec_pub_sec k c Φ t :
  termT Pub (TEnc k (Spec.tag c t)) -∗
  tkey_predT c Φ k -∗
  ∃ lvl, termT lvl t ∗ guarded lvl (□ Φ (k, t)).
Proof.
iIntros "#Ht [#Hk #Hown]".
iDestruct (termT_adec_pub_sec with "Ht Hk") as (lvl) "{Ht} [#Ht #guard]".
rewrite termT_tag.
iExists lvl; iSplit => //; case: lvl => //=; iModIntro.
by iApply (tagged_inv_elim' with "Hown guard").
Qed.

End Tagging.

Arguments tagged_inv_def {_} /.
Arguments tagged_inv {_ _}.
