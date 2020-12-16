From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import term.

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
by rewrite lookup_singleton_ne // -not_elem_of_dom e elem_of_singleton.
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
Notation key_inv := (prodO locO termO -n> iPropO Σ).
Implicit Types Φ : key_inv.
Implicit Types l : loc.
Implicit Types lvl : level.
Implicit Types γ : gname.

Implicit Types P Q : iProp Σ.

Definition guarded lvl P : iProp Σ :=
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


Lemma guarded_exist T lvl (φ : T -> iProp Σ) :
  Inhabited T →
  guarded lvl (∃ x : T, φ x) ⊣⊢ ∃ x : T, guarded lvl (φ x).
Proof.
move=> ?; case: lvl=> //=.
apply (anti_symm _); last by eauto.
by iIntros "_"; iExists inhabitant.
Qed.

Global Instance guarded_from_exist T lvl (φ : T -> iProp Σ) :
  Inhabited T →
  FromExist (guarded lvl (∃ x, φ x)) (λ x, guarded lvl (φ x)).
Proof.
by move => ?; rewrite /FromExist guarded_exist.
Qed.

Global Instance guarded_into_exist T lvl (φ : T -> iProp Σ) :
  Inhabited T →
  IntoExist (guarded lvl (∃ x, φ x)) (λ x, guarded lvl (φ x)).
Proof.
by move => ?; rewrite /IntoExist guarded_exist.
Qed.

Lemma guarded_box lvl (P : iProp Σ) : □ guarded lvl P ⊣⊢ guarded lvl (□ P).
Proof.
case: lvl => //=; by rewrite bi.intuitionistically_emp.
Qed.

Global Instance guarded_box_into_persistent p lvl (P Q : iProp Σ) :
  IntoPersistent p P Q →
  IntoPersistent p (guarded lvl P) (guarded lvl Q).
Proof.
case: lvl => //= _.
by rewrite /IntoPersistent; rewrite -bi.persistently_emp_intro; eauto.
Qed.

Inductive res :=
| RNonce of level
| RAKey of level & level & prodO locO termO -n> iPropO Σ
| RSKey of level & prodO locO termO -n> iPropO Σ.

Global Instance res_equiv : Equiv res := λ r1 r2,
  match r1, r2 with
  | RNonce lvl1, RNonce lvl2 => lvl1 = lvl2
  | RAKey lvl11 lvl12 P1, RAKey lvl21 lvl22 P2 =>
    lvl11 = lvl21 ∧ lvl12 = lvl22 ∧ P1 ≡ P2
  | RSKey lvl1 P1, RSKey lvl2 P2 => lvl1 = lvl2 ∧ P1 ≡ P2
  | _, _ => False
  end.

Implicit Types r : res.

Global Instance res_dist : Dist res := λ n r1 r2,
  match r1, r2 with
  | RNonce lvl1, RNonce lvl2 => lvl1 = lvl2
  | RAKey lvl11 lvl12 P1, RAKey lvl21 lvl22 P2 =>
    lvl11 = lvl21 ∧ lvl12 = lvl22 ∧ P1 ≡{n}≡ P2
  | RSKey lvl1 P1, RSKey lvl2 P2 => lvl1 = lvl2 ∧ P1 ≡{n}≡ P2
  | _, _ => False
  end.

Lemma res_ofe_mixin : OfeMixin res.
Proof.
split.
- move=> r1 r2; case: r1=> *; case: r2=> *;
  rewrite /equiv /dist /= ?forall_and_distr ?equiv_dist;
  intuition eauto using 0.
- rewrite /dist; move=> n; split.
  + case=> * //=; by apply equiv_dist.
  + case=> [lvl1|lvl11 lvl12 P1|lvl1 P1] [lvl2|lvl21 lvl22 P2|lvl2 P2] //=;
    intuition eauto.
  + case=> [?|???|??] [?|???|??] //= [?|???|??] //=;
    intuition (try congruence); etransitivity; eauto.
- rewrite /dist => n [?|???|??] [?|???|??] //=;
  intuition eauto using dist_S.
Qed.
Canonical resO := OfeT res res_ofe_mixin.

Lemma res_equivI (r1 r2 : res) :
  r1 ≡ r2 ⊣⊢@{iPropI Σ}
  match r1, r2 with
  | RNonce lvl1, RNonce lvl2 => ⌜lvl1 = lvl2⌝
  | RAKey lvl_enc1 lvl_dec1 Φ1, RAKey lvl_enc2 lvl_dec2 Φ2 =>
    ⌜lvl_enc1 = lvl_enc2⌝ ∧ ⌜lvl_dec1 = lvl_dec2⌝ ∧ Φ1 ≡ Φ2
  | RSKey lvl1 Φ1, RSKey lvl2 Φ2 =>
    ⌜lvl1 = lvl2⌝ ∧ Φ1 ≡ Φ2
  | _, _ => False
  end.
Proof. case: r1=> *; case: r2=> * /=; by uPred.unseal. Qed.

Global Instance discrete_RNonce lvl : Discrete (RNonce lvl).
Proof. by case. Qed.

Global Instance RAKey_proper n :
  Proper ((=) ==> (=) ==> dist n ==> dist n) RAKey.
Proof.
move=> ?? -> ?? -> Φ1 Φ2 e /=.
rewrite /dist /=; eauto.
Qed.

Class resG := {
  res_inG :> inG Σ (agreeR resO);
}.

Context `{!resG, !heapG Σ}.

Definition is_res γ r : iProp Σ := own γ (to_agree r).

Global Instance is_res_proper n : Proper ((=) ==> dist n ==> dist n) is_res.
Proof. solve_proper. Qed.

Lemma is_res_agree γ r1 r2 :
  is_res γ r1 -∗ is_res γ r2 -∗ r1 ≡ r2.
Proof.
iIntros "#own1 #own2".
iPoseProof (own_valid_2 with "own1 own2") as "e".
by rewrite agree_validI agree_equivI.
Qed.

Definition resT γ l : iProp Σ :=
  meta l (cryptoN.@"res") γ.

Lemma resT_persistent γ l : Persistent (resT γ l).
Proof. apply _. Qed.

Lemma resT_agree γ1 γ2 l :
  resT γ1 l -∗ resT γ2 l -∗ ⌜γ1 = γ2⌝.
Proof. iApply meta_agree. Qed.

Definition resT' r l : iProp Σ := ∃ γ, resT γ l ∗ is_res γ r.

Lemma resT'_persistent r l : Persistent (resT' r l).
Proof. apply _. Qed.

Lemma resT'_agree r1 r2 l :
  resT' r1 l -∗ resT' r2 l -∗ r1 ≡ r2.
Proof.
iDestruct 1 as (γ1) "[meta1 own1]".
iDestruct 1 as (γ2) "[meta2 own2]".
iPoseProof (meta_agree with "meta1 meta2") as "->".
iPoseProof (own_valid_2 with "own1 own2") as "#valid".
by rewrite agree_validI agree_equivI.
Qed.

Definition nonceT lvl l : iProp Σ := resT' (RNonce lvl) l.

Lemma nonceT_agree lvl1 lvl2 l :
  nonceT lvl1 l -∗ nonceT lvl2 l -∗ ⌜lvl1 = lvl2⌝.
Proof.
iIntros "Hown1 Hown2".
by iPoseProof (resT'_agree with "Hown1 Hown2") as "%Hvalid".
Qed.

Global Instance persistent_nonceT lvl l : Persistent (nonceT lvl l).
Proof. apply _. Qed.

Global Instance timeless_nonceT lvl l : Timeless (nonceT lvl l).
Proof. apply _. Qed.

Definition akeyT lvl_enc lvl_dec Φ l : iProp Σ :=
  resT' (RAKey lvl_enc lvl_dec Φ) l.

Global Instance persistent_akeyT lvl_enc lvl_dec Φ l :
  Persistent (akeyT lvl_enc lvl_dec Φ l).
Proof. apply _. Qed.

Global Instance akeyT_proper n :
  Proper ((=) ==> (=) ==> dist n ==> (=) ==> dist n) akeyT.
Proof. rewrite /akeyT /resT'; solve_proper. Qed.

Lemma akeyT_agree lvl_enc1 lvl_enc2 lvl_dec1 lvl_dec2 Φ1 Φ2 l :
  akeyT lvl_enc1 lvl_dec1 Φ1 l -∗
  akeyT lvl_enc2 lvl_dec2 Φ2 l -∗
  ⌜lvl_enc1 = lvl_enc2⌝ ∗
  ⌜lvl_dec1 = lvl_dec2⌝ ∗
  Φ1 ≡ Φ2.
Proof.
iIntros "Hres1 Hres2".
iPoseProof (resT'_agree with "Hres1 Hres2") as "#Hres".
by rewrite res_equivI; iDestruct "Hres" as "(? & ? & ?)"; eauto.
Qed.

Definition skeyT lvl Φ l : iProp Σ :=
  resT' (RSKey lvl Φ) l.

Global Instance persistent_skeyT lvl Φ l :
  Persistent (skeyT lvl Φ l).
Proof. apply _. Qed.

Lemma skeyT_agree lvl1 lvl2 Φ1 Φ2 l :
  skeyT lvl1 Φ1 l -∗
  skeyT lvl2 Φ2 l -∗
  ⌜lvl1 = lvl2⌝ ∗
  Φ1 ≡ Φ2.
Proof.
iIntros "Hres1 Hres2".
iPoseProof (resT'_agree with "Hres1 Hres2") as "#Hres".
by rewrite res_equivI; iDestruct "Hres" as "[??]"; eauto.
Qed.

Definition keyT kt rs Φ l : iProp Σ :=
  match kt with
  | KSym => skeyT rs Φ l
  | KAEnc => ∃ rs_dec, akeyT rs rs_dec Φ l
  | KADec => ∃ rs_enc, akeyT rs_enc rs Φ l
  end.

Lemma keyT_agree kt rs1 rs2 Φ1 Φ2 l :
  keyT kt rs1 Φ1 l -∗
  keyT kt rs2 Φ2 l -∗
  ⌜rs1 = rs2⌝ ∗ Φ1 ≡ Φ2.
Proof.
case: kt=> /=.
- by iApply skeyT_agree.
- iDestruct 1 as (rs1') "Hres1".
  iDestruct 1 as (rs2') "Hres2".
  by iPoseProof (akeyT_agree with "Hres1 Hres2") as "(<-&<-&?)";
  eauto.
- iDestruct 1 as (rs1') "Hres1".
  iDestruct 1 as (rs2') "Hres2".
  by iPoseProof (akeyT_agree with "Hres1 Hres2") as "(<-&<-&?)";
  eauto.
Qed.

Global Instance persistent_keyT kt rs Φ l : Persistent (keyT kt rs Φ l).
Proof. by case: kt; apply _. Qed.

Definition key_info (asym : bool) lvl_enc lvl_dec Φ l : iProp Σ :=
  if asym then akeyT lvl_enc lvl_dec Φ l
  else (⌜lvl_enc = lvl_dec⌝ ∗ skeyT lvl_enc Φ l)%I.

Lemma key_info_agree asym1 asym2 lvl_enc1 lvl_dec1 lvl_enc2 lvl_dec2 Φ1 Φ2 l :
  key_info asym1 lvl_enc1 lvl_dec1 Φ1 l -∗
  key_info asym2 lvl_enc2 lvl_dec2 Φ2 l -∗
  ⌜asym1 = asym2⌝ ∗ ⌜lvl_enc1 = lvl_enc2⌝ ∗ ⌜lvl_dec1 = lvl_dec2⌝ ∗
  Φ1 ≡ Φ2.
Proof.
case: asym1 asym2=> [] [] /=.
- iIntros "Hown1 Hown2".
  iPoseProof (akeyT_agree with "Hown1 Hown2") as "(<-&<-&?)".
  by eauto.
- iIntros "Hown1 [_ Hown2]".
  iPoseProof (resT'_agree with "Hown1 Hown2") as "#Hvalid".
  by rewrite res_equivI.
- iIntros "[_ Hown1] Hown2".
  iPoseProof (resT'_agree with "Hown1 Hown2") as "#Hvalid".
  by rewrite res_equivI.
- iIntros "[<- Hown1] [<- Hown2]".
  iPoseProof (skeyT_agree with "Hown1 Hown2") as "(<-&#Hvalid)".
  by eauto.
Qed.

Global Instance persistent_key_info asym lvl_enc lvl_dec Φ l :
  Persistent (key_info asym lvl_enc lvl_dec Φ l).
Proof. by case: asym; apply _. Qed.

(** [termT lvl t] holds when the term [t] can be declared public after
encrypting it with any of the readers lvl.  If [lvl = Pub], [t] is considered
public and does not have to be encrypted. *)

Fixpoint termT_def lvl t : iProp Σ :=
  match t with
  | TInt _ => True
  | TPair t1 t2 => termT_def lvl t1 ∗ termT_def lvl t2
  | TNonce l  => ∃ lvl', nonceT lvl' l ∗ ⌜lvl' ⊑ lvl⌝
  | TKey kt l => ∃ lvl' Φ, keyT kt lvl' Φ l ∗ ⌜lvl' ⊑ lvl⌝
  | TEnc asym l t =>
    ∃ lvl_enc lvl_dec Φ,
      key_info asym lvl_enc lvl_dec Φ l
      ∗ (□ Φ (l, t) ∗ termT_def (lvl ⊔ lvl_dec) t ∨
         ⌜lvl_enc = Pub⌝ ∗ termT_def Pub t)
  end.

Definition termT_aux : seal termT_def. by eexists. Qed.
Definition termT := unseal termT_aux.
Definition termT_eq : termT = termT_def := seal_eq termT_aux.

Global Instance persistent_termT lvl t :
  Persistent (termT lvl t).
Proof. rewrite termT_eq; elim: t lvl=> *; apply _. Qed.

Lemma termT_int lvl n : ⊢ termT lvl (TInt n).
Proof. by rewrite termT_eq. Qed.

Lemma termT_nonce lvl l :
  nonceT lvl l -∗
  termT lvl (TNonce l).
Proof.
by iIntros "#Hl"; rewrite termT_eq; iExists lvl; eauto.
Qed.

Lemma termT_aenc_pub_pub lvl Φ k t :
  akeyT Pub lvl Φ k -∗
  termT Pub t -∗
  termT Pub (TEnc true k t).
Proof.
rewrite {2}termT_eq /= -termT_eq.
iIntros "#Hk #Ht"; by iExists Pub, lvl, Φ; eauto.
Qed.

Lemma termT_aenc_pub_sec Φ k t :
  akeyT Pub Sec Φ k -∗
  □ Φ (k, t) -∗
  termT Sec t -∗
  termT Pub (TEnc true k t).
Proof.
rewrite {2}termT_eq /= -termT_eq.
iIntros "#Hk #Φt #Ht".
by iExists Pub, Sec, Φ; eauto.
Qed.

Lemma termT_adec_pub lvl Φ k t :
  termT Pub (TEnc true k t) -∗
  akeyT Pub lvl Φ k -∗
  termT Pub t ∨ □ Φ (k, t) ∗ termT lvl t.
Proof.
rewrite {1}termT_eq /= -termT_eq.
iDestruct 1 as (lvl_enc lvl_dec Φ') "[Hk' Ht]".
iIntros "Hk".
iPoseProof (akeyT_agree with "Hk' Hk") as "(-> & -> & e)".
rewrite ofe_morO_equivI; iRewrite -("e" $! (k, t)).
iDestruct "Ht" as "[[Ht1 Ht2]|[_ Ht]]"; eauto.
iRight; iFrame; by case: lvl.
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

Lemma termT_kenc lvl_enc lvl_dec Φ k :
  akeyT lvl_enc lvl_dec Φ k -∗
  termT lvl_enc (TKey KAEnc k).
Proof.
iIntros "kP"; rewrite termT_eq /=.
iExists lvl_enc, Φ; iSplit => //.
by eauto.
Qed.

Lemma termT_kdec lvl_enc lvl_dec Φ k :
  akeyT lvl_enc lvl_dec Φ k -∗
  termT lvl_dec (TKey KADec k).
Proof.
iIntros "kP"; rewrite termT_eq /=.
iExists lvl_dec, Φ; iSplit => //.
by eauto.
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

Lemma sub_termT lvl lvl' t :
  lvl ⊑ lvl' →
  termT lvl t -∗
  termT lvl' t.
Proof.
elim: t lvl lvl' => [n|t1 IH1 t2 IH2|l|kt l|b l t IH] lvl lvl' sub;
rewrite termT_eq /= -?termT_eq //.
- by iIntros "[#Ht1 #Ht2]"; rewrite IH1 // IH2 //; iSplit.
- iDestruct 1 as (lvl0) "[#Hnonce %sub0]".
  iExists lvl0; iSplit=> //; iPureIntro; by etransitivity.
- iDestruct 1 as (lvl0 Φ) "[#Hkey %sub0]".
  iExists lvl0, Φ; iSplit=> //; iPureIntro; by etransitivity.
- iDestruct 1 as (lvl_enc lvl_dec Φ) "[#Hkey #Ht]".
  iExists lvl_enc, lvl_dec, Φ; iSplit=> //.
  iDestruct "Ht" as "[[? Ht]|Ht]"; last by iRight.
  iLeft; iSplit=> //; iApply (IH with "Ht").
  by case: lvl lvl' lvl_dec sub=> [] [] [].
Qed.

(** A stricter version of [termT] that does not allow subtyping *)
Definition stermT lvl t : iProp Σ :=
  termT lvl t ∗ □ ∀ lvl', termT lvl' t -∗ ⌜lvl ⊑ lvl'⌝.

Global Instance stermT_persistent lvl t : Persistent (stermT lvl t).
Proof. apply _. Qed.

Lemma stermT_int n : ⊢ stermT Pub (TInt n).
Proof. by rewrite /stermT termT_eq /=; iSplit. Qed.
Hint Resolve stermT_int : typing.

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

Lemma stermT_nonce lvl l :
  nonceT lvl l -∗
  stermT lvl (TNonce l).
Proof.
iIntros "#Hn"; iSplit; first by iApply termT_nonce.
rewrite termT_eq /=; iIntros "!>" (lvl').
iDestruct 1 as (lvl'') "[#Hn' %Hsub']".
iPoseProof (resT'_agree with "Hn Hn'") as "e".
by rewrite res_equivI; iPoseProof "e" as "->".
Qed.

Lemma stermT_key lvl kt Φ l :
  keyT kt lvl Φ l -∗
  stermT lvl (TKey kt l).
Proof.
iIntros "#Hk"; rewrite /stermT termT_eq /=.
iSplit; first by iExists lvl, Φ; iSplit.
iIntros "/= !>" (lvl'); iDestruct 1 as (lvl'' Φ') "[#Hk' %Hsub']".
by iPoseProof (keyT_agree with "Hk Hk'") as "(<-&_)".
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
elim: t lvl=> [n|t1 IH1 t2 IH2|n|kt k|b k t IH] lvl /=;
rewrite termT_eq /= -?termT_eq.
- iIntros "_"; iExists Pub; iApply stermT_int.
- iIntros "[#type1 #type2]".
  iDestruct (IH1 with "type1") as (lvl1) "type1'".
  iDestruct (IH2 with "type2") as (lvl2) "type2'".
  by iExists (lvl1 ⊔ lvl2); iApply stermT_pair.
- iDestruct 1 as (lvl') "[#Hn %Hsub]".
  by iExists lvl'; iApply stermT_nonce.
- iDestruct 1 as (lvl' Φ) "[#Hk %Hsub]".
  by iExists lvl'; iApply stermT_key.
- case: lvl.
    iIntros "#Ht"; iExists Pub; iSplit=> //.
      by rewrite termT_eq /= -termT_eq.
    by iIntros "!>" (lvl) "_".
  iDestruct 1 as (lvl_enc lvl_dec Φ) "[#Hk #Ht]".
  rewrite /stermT {3 4}termT_eq /= -termT_eq.
  iDestruct "Ht" as "[[#Ht type]|[-> type]]"; last first.
    iExists Pub; iSplit=> /=; first by iExists _, _, _; iSplit; eauto.
    by iIntros "!>" (lvl) "_".
  iDestruct (IH with "type") as (lvl) "[type' #min']".
  case: lvl.
    iExists Pub; iSplit=> /=.
      iExists _, _, _; iSplit=> //.
      by iLeft; iSplit=> //; case: lvl_dec.
    by iIntros "!>" (lvl) "_".
  case: lvl_dec.
    iExists Sec; iSplit=> /=.
      iExists _, _, _; iSplit=> //.
      by iLeft; iSplit=> //; case: lvl_dec.
    iIntros "!>" (lvl).
    iDestruct 1 as (lvl_enc' lvl_dec' Φ') "[#Hk' #type'']".
    iDestruct (key_info_agree with "Hk Hk'") as "(_&<-&<-&_)".
    iDestruct "type''" as "[[_ type'']|[_ type'']]";
    iPoseProof ("min'" with "type''") as "?"=> //.
    by case: lvl.
  iExists Pub; iSplit=> /=.
    iExists _, _, _; iSplit=> //.
    by iLeft; iSplit.
  by iIntros "!>" (lvl) "_".
Qed.

Lemma termT_adec_pub_sec Φ k t :
  termT Pub (TEnc true k t) -∗
  akeyT Pub Sec Φ k -∗
  ∃ lvl, termT lvl t ∗ guarded lvl (□ Φ (k, t)).
Proof.
iIntros "Ht Hk".
iPoseProof (termT_adec_pub with "Ht Hk") as "[Ht|Ht]".
- by iExists Pub; iSplit.
- by iExists Sec; iDestruct "Ht" as "[??]"; iSplit.
Qed.

Definition pub_enc_key k : iProp Σ :=
  ∃ lvl_dec Φ, akeyT Pub lvl_dec Φ k.

Global Instance pub_enc_key_persistent k : Persistent (pub_enc_key k).
Proof. apply _. Qed.

Lemma termT_TAEncE k :
  termT Pub (TKey KAEnc k) -∗ pub_enc_key k.
Proof.
rewrite termT_eq /=.
iDestruct 1 as (lvl Φ) "[Hk %Hlvl]".
case: lvl Hlvl => // _.
iDestruct "Hk" as (lvl_dec) "Hk".
by rewrite /pub_enc_key; eauto.
Qed.

Lemma termT_TAEnc lvl_enc lvl_dec Φ k :
  akeyT lvl_enc lvl_dec Φ k -∗
  termT lvl_enc (TKey KAEnc k).
Proof.
iIntros; rewrite termT_eq /=.
by iExists lvl_enc, Φ; iSplit; eauto.
Qed.

Lemma termT_aenc_pub_secG k Φ lvl t :
  pub_enc_key k -∗
  termT lvl t -∗
  guarded lvl (akeyT Pub Sec Φ k) -∗
  guarded lvl (□ Φ (k, t)) -∗
  termT Pub (TEnc true k t).
Proof.
iIntros "#Hk #Ht #Hk' #HG"; case: lvl => /=.
- iDestruct "Hk" as (??) "Hk".
  by iApply termT_aenc_pub_pub.
- by iApply termT_aenc_pub_sec.
Qed.

Lemma res_alloc γ E r l :
  ↑cryptoN.@"res" ⊆ E →
  is_res γ r -∗
  meta_token l E ==∗
  resT' r l.
Proof.
iIntros (Hsub) "Hown Hmeta".
iMod (meta_set E l γ with "Hmeta") as "Hmeta"=> //.
by rewrite /resT'; eauto.
Qed.

End Resources.

Arguments RNonce {_} _.
Arguments nonceT {_ _ _} _ _.
Arguments skeyT {_ _ _} _ _ _.
Arguments akeyT {_ _ _} _ _ _ _.
Arguments is_res {Σ _} _ _.
Arguments RAKey {Σ} _ _ _.

Section Tagging.

Context (Σ : gFunctors).
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation key_inv := (prodO locO termO -n> iPropO).
Implicit Types Φ : key_inv.
Implicit Types l k : loc.
Implicit Types lvl : level.
Implicit Types γ : gname.
Implicit Types c : string.

Class tagG := TagG {
  tag_inG :> inG Σ (gmapR (loc * string) (agreeR key_inv));
  tag_name : gname;
}.

Context `{!heapG Σ, !resG Σ, !tagG}.

Definition own_tag k c Φ : iProp :=
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

Definition tagged_inv_def (p : loc * term) : iProp :=
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

Definition tag_akeyT lvl c Φ k : iProp :=
  akeyT lvl Sec (OfeMor tagged_inv) k ∗
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
  termT Pub (TEnc true k (Spec.tag c t)).
Proof.
iIntros "#k_lo #t_lo [#k_hi #own] #t_hi".
iApply termT_aenc_pub_secG; eauto.
  iApply termT_tag; eauto.
case: lvl => //=; iModIntro.
by iApply tagged_inv_intro.
Qed.

Lemma termT_tag_adec_pub_sec k c Φ t :
  termT Pub (TEnc true k (Spec.tag c t)) -∗
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
