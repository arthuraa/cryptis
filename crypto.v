From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import term coGset_disj.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: Move to Iris? *)
Instance dom_ne {T : ofeT} :
  NonExpansive (dom (gset loc) : gmap loc T -> gset loc).
Proof. by move=> ??? e ?; rewrite !elem_of_dom e. Qed.

(* I've made an MR for this. *)
Lemma gmap_equivI `{!EqDecision K, !Countable K, A : ofeT, M : ucmraT}
  (m1 m2 : gmap K A) :
  m1 ≡ m2 ⊣⊢@{uPredI M} (∀ i : K, m1 !! i ≡ m2 !! i).
Proof. by uPred.unseal. Qed.

Lemma dom_singleton_eq `{EqDecision K, Countable K} {T} (m : gmap K T) x :
  dom (gset K) m = {[x]} →
  ∃ y, m = {[x := y]}.
Proof.
move=> e.
have {}e: ∀ x' : K, x' ∈ dom (gset K) m ↔ x' ∈ ({[x]} : gset K) by rewrite e.
have: x ∈ ({[x]} : gset K) by rewrite elem_of_singleton.
rewrite -e elem_of_dom; case=> y m_x; exists y.
apply: map_eq=> x'; case: (decide (x' = x))=> [ {x'}->|ne].
  by rewrite lookup_singleton.
rewrite lookup_singleton_ne // -(@not_elem_of_dom _ _ (gset K)).
by rewrite e elem_of_singleton.
Qed.

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
  | TEnc _ _ => ∅
  end.

Definition owners t : gset term :=
  match t with
  | TKey _ t => atoms t
  | _ => ∅
  end.

Notation nonce := loc (only parsing).
Implicit Types (a : nonce).

Context `{!heapG Σ}.

Inductive key_data :=
| KeyData of level & level & prodO termO termO -n> iPropO.

Implicit Types kd : key_data.

Global Instance key_data_equiv : Equiv key_data := λ kd1 kd2,
  match kd1, kd2 with
  | KeyData lvl11 lvl12 P1, KeyData lvl21 lvl22 P2 =>
    lvl11 = lvl21 ∧ lvl12 = lvl22 ∧ P1 ≡ P2
  end.

Global Instance key_data_dist : Dist key_data := λ n kd1 kd2,
  match kd1, kd2 with
  | KeyData lvl11 lvl12 P1, KeyData lvl21 lvl22 P2 =>
    lvl11 = lvl21 ∧ lvl12 = lvl22 ∧ P1 ≡{n}≡ P2
  end.

Lemma key_data_ofe_mixin : OfeMixin key_data.
Proof.
split.
- move=> kd1 kd2; case: kd1=> *; case: kd2=> *;
  rewrite /equiv /dist /= ?forall_and_distr ?equiv_dist;
  intuition eauto using 0.
- rewrite /dist; move=> n; split.
  + case=> * //=; by apply equiv_dist.
  + case=> [lvl11 lvl12 P1] [lvl21 lvl22 P2] //=;
    intuition eauto.
  + case=> [???] [???] //= [???] //=;
    intuition (try congruence); etransitivity; eauto.
- rewrite /dist => n [???] [???] //=;
  intuition eauto using dist_S.
Qed.
Canonical key_dataO := OfeT key_data key_data_ofe_mixin.

Lemma key_data_equivI (kd1 kd2 : key_data) :
  kd1 ≡ kd2 ⊣⊢@{iPropI}
  match kd1, kd2 with
  | KeyData lvl_enc1 lvl_dec1 Φ1, KeyData lvl_enc2 lvl_dec2 Φ2 =>
    ⌜lvl_enc1 = lvl_enc2⌝ ∧ ⌜lvl_dec1 = lvl_dec2⌝ ∧ Φ1 ≡ Φ2
  end.
Proof. case: kd1=> *; case: kd2=> * /=; by uPred.unseal. Qed.

Global Instance KeyData_proper n :
  Proper ((=) ==> (=) ==> dist n ==> dist n) KeyData.
Proof.
move=> ?? -> ?? -> Φ1 Φ2 e /=.
rewrite /dist /=; eauto.
Qed.

Definition term_data : Type :=
  gmap term level *
  gmap term (coGset term) *
  gmap term key_pred.

Definition term_data' : Type :=
  gmap term (agree level) *
  gmap term (coGset_disj term) *
  gmap term (agree key_pred).

Definition term_data'UR :=
  Eval hnf in (fun (sT : ucmraT) (f : term_data' -> sT) => sT) _ (fun x => x).

Definition to_term_data' (td : term_data) : term_data' :=
  let '(lvls, Ts, kps) := td in
  (fmap to_agree lvls, fmap CoGset Ts, fmap to_agree kps).

Class cryptoG := CryptoG {
  crypto_inG :> authG Σ term_data'UR;
  crypto_name : gname;
}.

Context `{!cryptoG}.

Definition declared_nonces (ts : gset term) : iProp :=
  ∀ a, ⌜TNonce a ∈ ts⌝ → meta a (cryptoN.@"nonce") ().

Definition term_data_inv (td : term_data) : iProp :=
  let '(lvls, Ts, kps) := td in
  declared_nonces (dom _ lvls) ∗
  ⌜∀ t, t ∈ dom (gset term) lvls → atomic t⌝ ∗
  ⌜∀ t, lvls !! t = Some Sec ↔ is_Some (Ts !! t)⌝ ∗
  ⌜∀ t, t ∈ dom (gset term) lvls →
   ∀ t' T, t' ∈ owners t → lvls !! t' = Some Sec → Ts !! t' = Some T →
   t ∉ T⌝ ∗
  ⌜∀ t T t', Ts !! t = Some T → t' ∉ T →
   t ∈ owners t' ∧ t' ∈ dom (gset term) lvls⌝.

Definition crypto_inv :=
  auth_inv crypto_name to_term_data' term_data_inv.

Definition crypto_ctx :=
  auth_ctx crypto_name cryptoN to_term_data' term_data_inv.

Definition crypto_own td :=
  auth_own crypto_name (to_term_data' td).

Definition atomicT lvl t :=
  crypto_own ({[t := lvl]}, ∅, ∅).

Global Instance atomicT_persistent lvl t : Persistent (atomicT lvl t).
Proof.
rewrite /atomicT /crypto_own /to_term_data' !fmap_empty.
by apply _.
Qed.

Lemma atomicT_agree lvl1 lvl2 t :
  atomicT lvl1 t -∗
  atomicT lvl2 t -∗
  ⌜lvl1 = lvl2⌝.
Proof.
iIntros "own1 own2".
iPoseProof (own_valid_2 with "own1 own2") as "#valid".
rewrite auth_validI /= -!pair_op !uPred.prod_validI /=.
iDestruct "valid" as "([#valid _] & _)".
rewrite !map_fmap_singleton singleton_op gmap_validI.
iSpecialize ("valid" $! t); rewrite lookup_singleton.
rewrite uPred.option_validI agree_validI agree_equivI.
by iPoseProof "valid" as "->".
Qed.

Definition freshT t T :=
  crypto_own (∅, {[t := T]}, ∅).

Definition key_predT Φ t :=
  crypto_own (∅, ∅, {[t := Φ]}).

Global Instance key_predT_persistent Φ t : Persistent (key_predT Φ t).
Proof.
rewrite /key_predT /crypto_own /to_term_data' !fmap_empty.
by apply _.
Qed.

Lemma key_predT_agree Φ1 Φ2 t :
  key_predT Φ1 t -∗
  key_predT Φ2 t -∗
  Φ1 ≡ Φ2.
Proof.
iIntros "own1 own2".
iPoseProof (own_valid_2 with "own1 own2") as "#valid".
rewrite auth_validI /= -!pair_op !uPred.prod_validI /=.
iDestruct "valid" as "([_ _] & #valid)".
rewrite !map_fmap_singleton singleton_op gmap_validI.
iSpecialize ("valid" $! t); rewrite lookup_singleton.
by rewrite uPred.option_validI agree_validI agree_equivI.
Qed.

(** [termT lvl t] holds when the term [t] can be declared public after
encrypting it.  If [lvl = Pub], [t] is considered public and does not have to be
encrypted.  *)

Fixpoint termT_def lvl t : iProp :=
  match t with
  | TInt _ => True
  | TPair t1 t2 => termT_def lvl t1 ∗ termT_def lvl t2
  | TNonce _  => ∃ lvl', atomicT lvl' t ∗ ⌜lvl' ⊑ lvl⌝
  | TKey _ _ => ∃ lvl', atomicT lvl' t ∗ ⌜lvl' ⊑ lvl⌝
  | TEnc k t =>
    ∃ lvl_enc,
      atomicT lvl_enc (TKey Enc k) ∗ (
      ⌜lvl_enc = Pub⌝ ∗ termT_def Pub t ∨
      ∃ lvl_dec Φ,
        atomicT lvl_dec (TKey Dec k) ∗
        key_predT Φ k ∗
        □ Φ (k, t) ∗
        termT_def (lvl ⊔ lvl_dec) t)
  end.

Definition termT_aux : seal termT_def. by eexists. Qed.
Definition termT := unseal termT_aux.
Definition termT_eq : termT = termT_def := seal_eq termT_aux.

Global Instance persistent_termT lvl t :
  Persistent (termT lvl t).
Proof.
by rewrite termT_eq; elim: t lvl => /= *; apply _.
Qed.

(** A stricter version of [termT] that does not allow subtyping *)
Definition stermT lvl t : iProp :=
  termT lvl t ∗ □ ∀ lvl', termT lvl' t -∗ ⌜lvl ⊑ lvl'⌝.

Global Instance stermT_persistent lvl t : Persistent (stermT lvl t).
Proof. apply _. Qed.

Lemma sub_termT lvl lvl' t :
  lvl ⊑ lvl' →
  termT lvl t -∗
  termT lvl' t.
Proof.
elim: t lvl lvl' => [n|t1 IH1 t2 IH2|l|kt k _|k _ t IH] lvl lvl' sub;
rewrite termT_eq /= -?termT_eq //.
- by iIntros "[#Ht1 #Ht2]"; rewrite IH1 // IH2 //; iSplit.
- iDestruct 1 as (lvl0) "[#Hnonce %sub0]".
  iExists lvl0; iSplit=> //; iPureIntro; by etransitivity.
- iDestruct 1 as (lvl0) "[#Hkey %sub0]".
  iExists lvl0; iSplit=> //; iPureIntro; by etransitivity.
- iDestruct 1 as (lvl_enc) "[#enc #Ht]".
  iExists lvl_enc; iSplit => //.
  iDestruct "Ht" as "[Ht|Ht]"; first by iLeft.
  iDestruct "Ht" as (lvl_dec Φ) "(dec & HΦ & tP & Ht)".
  iRight; iExists lvl_dec, Φ; do 3![iSplit => //].
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
rewrite {1 3}termT_eq /= -termT_eq.
iDestruct 1 as (lvl') "[Hk %leq]".
case: lvl' leq => [] // _.
by iIntros "Ht"; iExists Pub; eauto.
Qed.

Lemma termT_atomic lvl t : atomic t → atomicT lvl t -∗ termT lvl t.
Proof.
iIntros (Ht) "H"; rewrite termT_eq; case: t Ht => //= *; eauto.
Qed.

Lemma termT_atomicE lvl t :
  atomic t →
  termT lvl t -∗
  ∃ lvl', atomicT lvl' t ∗ ⌜lvl' ⊑ lvl⌝.
Proof.
by case: t => // [a|kt k] _; rewrite termT_eq.
Qed.

Lemma stermT_atomic lvl t :
  atomic t →
  atomicT lvl t -∗
  stermT lvl t.
Proof.
move=> atomic_t; iIntros "#atomic"; iSplit; first by iApply termT_atomic.
iIntros "!>" (lvl') "#Ht".
iDestruct (termT_atomicE with "Ht") as (lvl'') "[atomic' %leq]" => //.
by iPoseProof (atomicT_agree with "atomic atomic'") as "->".
Qed.

Lemma stermT_atomicE lvl t :
  atomic t →
  stermT lvl t -∗
  atomicT lvl t.
Proof.
iIntros (atomic_t) "[#Ht #Hmin]".
iDestruct (termT_atomicE with "Ht") as (lvl') "[atomic %leq]" => //.
iPoseProof (termT_atomic with "atomic") as "Ht'" => //.
iPoseProof ("Hmin" with "Ht'") as "%leq'".
by case: lvl lvl' leq leq' => [] // [].
Qed.

Lemma stermT_TKeyE lvl kt k : stermT lvl (TKey kt k) -∗ atomicT lvl (TKey kt k).
Proof. by apply: stermT_atomicE. Qed.

Lemma termT_aenc_pub_sec lvl Φ k t :
  termT  lvl (TKey Enc k) -∗
  stermT Sec (TKey Dec k) -∗
  key_predT Φ k -∗
  □ Φ (k, t) -∗
  termT Sec t -∗
  termT Pub (TEnc k t).
Proof.
iIntros "#Henc #Hdec #HΦ #HΦt #Ht".
iDestruct (termT_atomicE with "Henc") as (lvl') "[Henc' %leq]" => //.
iPoseProof (stermT_TKeyE with "Hdec") as "Hdec'".
rewrite {3}termT_eq /=.
iExists lvl'; iSplit => //; iRight.
by iExists Sec, Φ; rewrite -termT_eq; eauto.
Qed.

Lemma termT_adec_pub lvl Φ k t :
  termT Pub (TEnc k t) -∗
  termT Pub (TKey Enc k) -∗
  termT lvl (TKey Dec k) -∗
  key_predT Φ k -∗
  termT Pub t ∨ □ Φ (k, t) ∗ termT lvl t.
Proof.
rewrite {1}termT_eq /= -termT_eq.
iDestruct 1 as (lvl_enc) "[#atomic_enc [[-> ?]|#Ht]]"; eauto.
iIntros "#enc #dec #HΦ".
iDestruct "Ht" as (lvl_dec Φ') "(atomic_dec & HΦ' & tP & Ht)".
iPoseProof (key_predT_agree with "HΦ' HΦ") as "e".
rewrite ofe_morO_equivI; iRewrite ("e" $! (k, t)) in "tP"; iClear "e".
iDestruct (termT_atomicE with "dec") as (lvl_dec') "[atomic_dec' %leq]" => //.
iPoseProof (atomicT_agree with "atomic_dec' atomic_dec") as "->".
iRight; iSplit => //.
iApply (sub_termT with "Ht"); by case: lvl_dec leq.
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
rewrite {1}termT_eq /= -termT_eq; iIntros "[??]"; iFrame.
by iApply IH.
Qed.

Lemma termT_tag lvl n t :
  termT lvl t -∗
  termT lvl (Spec.tag n t).
Proof.
by iIntros "#?"; rewrite termT_eq Spec.tag_eq /=; iSplit.
Qed.

Lemma termT_untag lvl n t :
  termT lvl (Spec.tag n t) -∗
  termT lvl t.
Proof.
by rewrite Spec.tag_eq /= termT_eq /=; iDestruct 1 as "[??]".
Qed.

Lemma termT_of_list lvl ts :
  ([∗ list] t ∈ ts, termT lvl t) -∗
  termT lvl (Spec.of_list ts).
Proof.
rewrite Spec.of_list_eq.
elim: ts => [|t ts IH]; first by rewrite termT_eq.
rewrite {2}termT_eq /= -termT_eq.
iDestruct 1 as "[??]".
by iFrame; iApply IH.
Qed.

Lemma termT_of_listE lvl ts :
  termT lvl (Spec.of_list ts) -∗
  [∗ list] t ∈ ts, termT lvl t.
Proof.
rewrite Spec.of_list_eq.
elim: ts => [|t ts IH] //=; iIntros "Hts" => //.
rewrite termT_eq /= -termT_eq; iDestruct "Hts" as "[??]".
by iFrame; iApply IH.
Qed.

Lemma proj_termT t n lvl t' :
  Spec.proj t n = Some t' →
  termT lvl t -∗
  termT lvl t'.
Proof.
rewrite termT_eq.
elim: t n=> // t1 IH1 t2 IH2 [|n] /=.
  by move=> [<-]; iIntros "[??]".
move=> {}/IH2 IH2; iIntros "[??]".
by iApply IH2.
Qed.

Lemma stermT_pair lvl1 t1 lvl2 t2 :
  stermT lvl1 t1 -∗
  stermT lvl2 t2 -∗
  stermT (lvl1 ⊔ lvl2) (TPair t1 t2).
Proof.
iIntros "[#type1 #min1] [#type2 #min2]"; iSplit.
- rewrite termT_eq /= -?termT_eq.
  iSplit; iApply sub_termT; try by [iApply "type1"|iApply "type2"];
  by case: lvl1 lvl2=> [] [].
- rewrite termT_eq /= -?termT_eq.
  iIntros "!>" (lvl') "[#type1' #type2']".
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
rewrite termT_eq /= -?termT_eq.
- iIntros "_"; iExists Pub; iApply stermT_int.
- iIntros "[#type1 #type2]".
  iDestruct (IH1 with "type1") as (lvl1) "type1'".
  iDestruct (IH2 with "type2") as (lvl2) "type2'".
  by iExists (lvl1 ⊔ lvl2); iApply stermT_pair.
- iDestruct 1 as (lvl') "[#Hn %Hsub]".
  by iExists lvl'; iApply stermT_atomic.
- iDestruct 1 as (lvl') "[#Hk %Hsub]".
  by iExists lvl'; iApply stermT_atomic.
- case: lvl.
    iIntros "#Ht"; iExists Pub; iSplit=> //.
      by rewrite termT_eq /= -termT_eq.
    by iIntros "!>" (lvl) "_".
  iDestruct 1 as (lvl_enc) "[#Hk #Ht]".
  rewrite /stermT {3 4}termT_eq /= -termT_eq.
  iDestruct "Ht" as "[[-> type]|Ht]".
    iExists Pub; iSplit; first by iExists _; iSplit; eauto.
    by iIntros "!>" (lvl) "_".
  iDestruct "Ht" as (lvl_dec Φ) "(Hdec & HΦ & tP & type)".
  iDestruct (IHt with "type") as (lvl) "[type' #min']".
  case: lvl.
    iExists Pub; iSplit=> /=.
      iExists _; iSplit => //.
      by iRight; iExists lvl_dec, Φ; do 3![iSplit => //]; case: lvl_dec.
    by iIntros "!>" (lvl) "_".
  case: lvl_dec.
    iExists Sec; iSplit=> /=.
      iExists _; iSplit => //.
      by iRight; iExists _, _; do 3![iSplit=> //]; case: lvl_dec.
    iIntros "!>" (lvl).
    iDestruct 1 as (lvl_enc') "[#Hk' #Ht]".
    iPoseProof (atomicT_agree with "Hk' Hk") as "->".
    iDestruct "Ht" as "[[_ Ht]|Ht]".
      case: lvl=> //; by iApply ("min'" with "Ht").
    iDestruct "Ht" as (lvl_dec' Φ') "(Hdec' & _ & _ & type'')".
    iPoseProof (atomicT_agree with "Hdec' Hdec") as "->".
    case: lvl => //.
    by iPoseProof ("min'" with "type''") as "?".
  iExists Pub; iSplit=> /=.
    iExists _; iSplit => //.
    by iRight; iExists _, _; do 3![iSplit => //]; eauto.
  by iIntros "!>" (lvl) "_".
Qed.

Lemma termT_adec_pub_sec Φ k t :
  termT Pub (TEnc k t) -∗
  termT Pub (TKey Enc k) -∗
  termT Sec (TKey Dec k) -∗
  key_predT Φ k -∗
  ∃ lvl, termT lvl t ∗ guarded lvl (□ Φ (k, t)).
Proof.
iIntros "Ht Henc Hdec Hpred".
iPoseProof (termT_adec_pub with "Ht Henc Hdec Hpred") as "[Ht|Ht]".
- by iExists Pub; iSplit.
- by iExists Sec; iDestruct "Ht" as "[??]"; iSplit.
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

End Resources.

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
  tag_inG :> inG Σ (gmapR string (agreeR key_inv));
}.

Context `{!heapG Σ, !cryptoG Σ, !tagG}.

Definition own_tag k c Φ : iProp :=
  ∃ γ, meta
  own tag_name {[(k, c) := to_agree Φ]}.

Lemma own_tag_persistent k c Φ : Persistent (own_tag k c Φ).
Proof. apply _. Qed.

Lemma own_tag_agree k c Φ1 Φ2 :
  own_tag k c Φ1 -∗
  own_tag k c Φ2 -∗
  Φ1 ≡ Φ2.
Proof.
iIntros "own1 own2".
iPoseProof (own_valid_2 with "own1 own2") as "#valid".
rewrite singleton_op gmap_validI; iSpecialize ("valid" $! (k, c)).
by rewrite lookup_singleton uPred.option_validI agree_validI agree_equivI.
Qed.

Lemma own_tag_proper n : Proper (eq ==> eq ==> dist n ==> dist n) own_tag.
Proof. solve_contractive. Qed.

Definition tagged_inv_def (p : term * term) : iProp :=
  match p.2 with
  | TPair (TInt (Zpos n)) t =>
    ∃ c Φ, ⌜n = encode c⌝ ∗ own_tag p.1 c Φ ∗ □ (Φ : key_inv) (p.1, t)
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
  own_tag k c Φ.


Lemma tag_akeyT_persistent lvl c Φ k : Persistent (tag_akeyT lvl c Φ k).
Proof. apply _. Qed.

Lemma tag_akeyT_agree lvl c Φ1 Φ2 k :
  tag_akeyT lvl c Φ1 k -∗
  tag_akeyT lvl c Φ2 k -∗
  Φ1 ≡ Φ2.
Proof.
iIntros "[_ #H1] [_ #H2]"; by iApply own_tag_agree.
Qed.

Lemma tagged_inv_intro k c Φ t :
  own_tag k c Φ -∗
  □ Φ (k, t) -∗
  tagged_inv (k, Spec.tag c t).
Proof.
rewrite tagged_inv_eq /tagged_inv_def Spec.tag_eq /=.
by iIntros "own Ht"; eauto.
Qed.

Lemma tagged_inv_elim k t :
  tagged_inv (k, t) -∗
  ∃ c t' Φ, ⌜t = Spec.tag c t'⌝ ∗
            own_tag k c Φ ∗
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
  own_tag k c Φ -∗
  tagged_inv (k, Spec.tag c t) -∗
  □ Φ (k, t).
Proof.
iIntros "#own #H".
iDestruct (tagged_inv_elim with "H") as (c' t' Φ') "{H} (%e & #own' & #Ht)".
case: (Spec.tag_inj _ _ _ _ e) => ??; subst c' t'.
iPoseProof (own_tag_agree with "own own'") as "#e".
rewrite ofe_morO_equivI.
by iRewrite -("e" $! (k, t)) in "Ht".
Qed.

Lemma termT_tag_aenc_pub_secG k lvl c Φ t :
  pub_enc_key k -∗
  termT lvl t -∗
  guarded lvl (tag_akeyT Pub c Φ k) -∗
  guarded lvl (□ Φ (k, t)) -∗
  termT Pub (TEnc (TNonce k) (Spec.tag c t)).
Proof.
iIntros "#k_lo #t_lo [#k_hi #own] #t_hi".
iApply termT_aenc_pub_secG; eauto.
  iApply termT_tag; eauto.
case: lvl => //=; iModIntro.
by iApply tagged_inv_intro.
Qed.

Lemma termT_tag_adec_pub_sec k c Φ t :
  termT Pub (TEnc (TNonce k) (Spec.tag c t)) -∗
  tag_akeyT Pub c Φ k -∗
  ∃ lvl, termT lvl t ∗ guarded lvl (□ Φ (k, t)).
Proof.
iIntros "#Ht [#Hk #Hown]".
iDestruct (termT_adec_pub_sec with "Ht Hk") as (lvl) "{Ht} [#Ht #guard]".
iDestruct (termT_untag with "Ht") as "{Ht} #Ht".
iExists lvl; iSplit => //; case: lvl => //=; iModIntro.
by iApply (tagged_inv_elim' with "Hown guard").
Qed.

End Tagging.

Arguments tagged_inv_def {_} /.
Arguments tagged_inv {_ _}.
