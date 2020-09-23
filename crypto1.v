From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
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
Implicit Types Φ : termO -n> iPropO Σ.
Implicit Types l : loc.
Implicit Types lvl : level.
Implicit Types γ : gname.

Inductive res :=
| RNonce of level
| RAKey of level & level & termO -n> iPropO Σ
| RSKey of level & termO -n> iPropO Σ.

Global Instance res_equiv : Equiv res := λ r1 r2,
  match r1, r2 with
  | RNonce lvl1, RNonce lvl2 => lvl1 = lvl2
  | RAKey lvl11 lvl12 P1, RAKey lvl21 lvl22 P2 =>
    lvl11 = lvl21 ∧ lvl12 = lvl22 ∧ P1 ≡ P2
  | RSKey lvl1 P1, RSKey lvl2 P2 => lvl1 = lvl2 ∧ P1 ≡ P2
  | _, _ => False
  end.

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

Class resG := {
  res_inG :> inG Σ (agreeR resO);
}.

Context `{!resG, !heapG Σ}.

Definition resT r l : iProp Σ :=
  ∃ γ, meta l (cryptoN.@"res") γ ∗ own γ (to_agree r).

Lemma resT_persistent r l : Persistent (resT r l).
Proof. apply _. Qed.

Lemma resT_agree r1 r2 l : resT r1 l -∗ resT r2 l -∗ r1 ≡ r2.
Proof.
iDestruct 1 as (γ) "[#Hl #Hγ]".
iDestruct 1 as (γ') "[#Hl' #Hγ']".
iPoseProof (meta_agree with "Hl Hl'") as "<-".
iPoseProof (own_valid_2 with "Hγ Hγ'") as "Hvalid".
by rewrite agree_validI agree_equivI.
Qed.

Lemma later_resT r l :
  ▷ resT r l -∗ ◇ ∃ r', resT r' l ∗ ▷ (r ≡ r').
Proof.
iDestruct 1 as (γ) "[> #Hmeta Hown]".
iMod (later_own with "Hown") as (ag) "[#Hown #Hr]".
iPoseProof (own_valid with "Hown") as "#Hvalid".
iDestruct (to_agree_uninjI with "Hvalid") as (r') "Hr'".
iRewrite -"Hr'" in "Hr"; iRewrite -"Hr'" in "Hown"; rewrite agree_equivI.
iModIntro; iExists r'; iSplit=> //.
by iExists γ; iSplit.
Qed.

Definition nonceT lvl l : iProp Σ := resT (RNonce lvl) l.

Lemma nonceT_agree lvl1 lvl2 l : nonceT lvl1 l -∗ nonceT lvl2 l -∗ ⌜lvl1 = lvl2⌝.
Proof.
iIntros "Hown1 Hown2".
iPoseProof (resT_agree with "Hown1 Hown2") as "#Hvalid".
by rewrite res_equivI.
Qed.

Global Instance persistent_nonceT lvl l : Persistent (nonceT lvl l).
Proof. apply _. Qed.

Global Instance timeless_nonceT lvl l : Timeless (nonceT lvl l).
Proof. apply _. Qed.

Definition akeyT lvl_enc lvl_dec Φ l : iProp Σ :=
  resT (RAKey lvl_enc lvl_dec Φ) l.

Global Instance persistent_akeyT lvl_enc lvl_dec Φ l :
  Persistent (akeyT lvl_enc lvl_dec Φ l).
Proof. apply _. Qed.

Definition skeyT lvl Φ l : iProp Σ := resT (RSKey lvl Φ) l.

Global Instance persistent_skeyT lvl Φ l :
  Persistent (skeyT lvl Φ l).
Proof. apply _. Qed.

Definition keyT kt rs Φ l : iProp Σ :=
  match kt with
  | KSym => skeyT rs Φ l
  | KAEnc => ∃ rs_dec, akeyT rs rs_dec Φ l
  | KADec => ∃ rs_enc, akeyT rs_enc rs Φ l
  end.

Lemma keyT_agree kt rs1 rs2 Φ1 Φ2 l :
  keyT kt rs1 Φ1 l -∗ keyT kt rs2 Φ2 l -∗ ⌜rs1 = rs2⌝ ∗ Φ1 ≡ Φ2.
Proof.
case: kt=> /=.
- iIntros "Hown1 Hown2".
  iPoseProof (resT_agree with "Hown1 Hown2") as "#Hvalid".
  by rewrite res_equivI /=; iDestruct "Hvalid" as "(?&?)"; iSplit.
- iDestruct 1 as (rs1') "Hown1".
  iDestruct 1 as (rs2') "Hown2".
  iPoseProof (resT_agree with "Hown1 Hown2") as "#Hvalid".
  rewrite res_equivI.
  by iDestruct "Hvalid" as "(?&?&?)"; iSplit.
- iDestruct 1 as (rs1') "Hown1".
  iDestruct 1 as (rs2') "Hown2".
  iPoseProof (resT_agree with "Hown1 Hown2") as "#Hvalid".
  rewrite res_equivI.
  by iDestruct "Hvalid" as "(?&?&?)"; iSplit.
Qed.

Global Instance persistent_keyT kt rs Φ l : Persistent (keyT kt rs Φ l).
Proof. by case: kt; apply _. Qed.

Definition key_info (asym : bool) lvl_enc lvl_dec Φ l : iProp Σ :=
  if asym then akeyT lvl_enc lvl_dec Φ l
  else (⌜lvl_enc = lvl_dec⌝ ∗ skeyT lvl_enc Φ l)%I.

Lemma key_info_agree asym1 asym2 lvl_enc1 lvl_dec1 lvl_enc2 lvl_dec2  Φ1 Φ2 l :
  key_info asym1 lvl_enc1 lvl_dec1 Φ1 l -∗
  key_info asym2 lvl_enc2 lvl_dec2 Φ2 l -∗
  ⌜asym1 = asym2⌝ ∗ ⌜lvl_enc1 = lvl_enc2⌝ ∗ ⌜lvl_dec1 = lvl_dec2⌝ ∗ Φ1 ≡ Φ2.
Proof.
case: asym1 asym2=> [] [] /=.
- iIntros "Hown1 Hown2".
  iPoseProof (resT_agree with "Hown1 Hown2") as "#Hvalid".
  by rewrite res_equivI /=; iDestruct "Hvalid" as "(?&?&?)"; repeat iSplit.
- iIntros "Hown1 [_ Hown2]".
  iPoseProof (resT_agree with "Hown1 Hown2") as "#Hvalid".
  by rewrite res_equivI.
- iIntros "[_ Hown1] Hown2".
  iPoseProof (resT_agree with "Hown1 Hown2") as "#Hvalid".
  by rewrite res_equivI.
- iIntros "[<- Hown1] [<- Hown2]".
  iPoseProof (resT_agree with "Hown1 Hown2") as "#Hvalid".
  by rewrite res_equivI /=; iDestruct "Hvalid" as "(?&?)"; repeat iSplit.
Qed.

Global Instance persistent_key_info asym lvl_enc lvl_dec Φ l :
  Persistent (key_info asym lvl_enc lvl_dec Φ l).
Proof. by case: asym; apply _. Qed.

(** [termT lvl t] holds when the term [t] can be declared public after
encrypting it with any of the readers lvl.  If [lvl = Pub], [t] is considered
public and does not have to be encrypted. *)

Fixpoint termT lvl t : iProp Σ :=
  match t with
  | TInt _ => True
  | TPair t1 t2 => termT lvl t1 ∗ termT lvl t2
  | TNonce l  => ∃ lvl', nonceT lvl' l ∗ ⌜lvl' ⊑ lvl⌝
  | TKey kt l => ∃ lvl' Φ, keyT kt lvl' Φ l ∗ ⌜lvl' ⊑ lvl⌝
  | TEnc asym l t =>
    ∃ lvl_enc lvl_dec Φ,
      key_info asym lvl_enc lvl_dec Φ l
      ∗ (□ Φ t ∗ termT (lvl ⊔ lvl_dec) t ∨
         ⌜lvl_enc = Pub⌝ ∗ termT Pub t)
  end.

Global Instance persistent_termT lvl t :
  Persistent (termT lvl t).
Proof. elim: t lvl=> *; apply _. Qed.

Lemma proj_termT t n lvl t' :
  Spec.proj t n = Some t' →
  termT lvl t -∗
  termT lvl t'.
Proof.
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
elim: t lvl lvl'=> [n|t1 IH1 t2 IH2|l|kt l|b l t IH] lvl lvl' sub //=.
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
  termT lvl t ∗ □ (∀ lvl', termT lvl' t -∗ ⌜lvl ⊑ lvl'⌝).

Global Instance stermT_persistent lvl t : Persistent (stermT lvl t).
Proof. apply _. Qed.

Lemma res_alloc E r l :
  ↑cryptoN.@"res" ⊆ E →
  meta_token l E ==∗
  resT r l.
Proof.
iIntros (Hsub) "Hmeta".
iMod (own_alloc (to_agree r)) as (γ) "#Hown" => //.
iMod (meta_set E l γ with "Hmeta") as "Hmeta"=> //.
by iModIntro; iExists γ; iSplit.
Qed.

End Resources.

Arguments RNonce {_} _.
Arguments nonceT {_ _ _} _ _.
Arguments skeyT {_ _ _} _ _ _.
Arguments akeyT {_ _ _} _ _ _ _.
