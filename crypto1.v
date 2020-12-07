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
Implicit Types Φ : prodO locO termO -n> iPropO Σ.
Implicit Types l : loc.
Implicit Types lvl : level.
Implicit Types γ : gname.

Inductive res :=
| RNonce of level
| RAKey of level & level & gname (* was: Predicate *)
| RSKey of level & gname.

Canonical resO := leibnizO res.

Implicit Types r : res.

Definition sum_of_res r :=
  match r with
  | RNonce lvl => inl lvl
  | RAKey lvl_enc lvl_dec γ => inr (inl (lvl_enc, lvl_dec, γ))
  | RSKey lvl γ => inr (inr (lvl, γ))
  end.

Definition res_of_sum x :=
  match x with
  | inl lvl => RNonce lvl
  | inr (inl (lvl_enc, lvl_dec, γ)) => RAKey lvl_enc lvl_dec γ
  | inr (inr (lvl, γ)) => RSKey lvl γ
  end.

Lemma sum_of_resK : Cancel (=) res_of_sum sum_of_res.
Proof. by case. Qed.

Global Instance res_eq_dec : EqDecision res.
Proof.
refine (λ r1 r2,
         match r1, r2 with
         | RNonce lvl1, RNonce lvl2 =>
           cast_if (decide (lvl1 = lvl2))
         | RAKey lvl_enc1 lvl_dec1 γ1, RAKey lvl_enc2 lvl_dec2 γ2 =>
           cast_if_and3 (decide (lvl_enc1 = lvl_enc2))
                        (decide (lvl_dec1 = lvl_dec2))
                        (decide (γ1 = γ2))
         | RSKey lvl1 γ1, RSKey lvl2 γ2 =>
           cast_if_and (decide (lvl1 = lvl2)) (decide (γ1 = γ2))
         | _, _ => right _
         end); abstract intuition congruence.
Defined.

Global Instance res_countable : Countable res.
Proof.
eapply (inj_countable' _ _ sum_of_resK).
Qed.

Class resG := {
  res_inG :> inG Σ (optionUR (agreeR (prodO locO termO -n> iPropO Σ)));
}.

Context `{!resG, !heapG Σ}.

Definition resT r l : iProp Σ :=
  meta l (cryptoN.@"res") r.

Lemma resT_persistent r l : Persistent (resT r l).
Proof. apply _. Qed.

Lemma resT_agree r1 r2 l : resT r1 l -∗ resT r2 l -∗ ⌜r1 = r2⌝.
Proof. exact: meta_agree. Qed.

Lemma resT_timeless r l : Timeless (resT r l).
Proof. apply _. Qed.

Definition nonceT lvl l : iProp Σ := resT (RNonce lvl) l.

Lemma nonceT_agree lvl1 lvl2 l : nonceT lvl1 l -∗ nonceT lvl2 l -∗ ⌜lvl1 = lvl2⌝.
Proof.
iIntros "Hown1 Hown2".
iPoseProof (resT_agree with "Hown1 Hown2") as "%Hvalid".
by case: Hvalid.
Qed.

Global Instance persistent_nonceT lvl l : Persistent (nonceT lvl l).
Proof. apply _. Qed.

Global Instance timeless_nonceT lvl l : Timeless (nonceT lvl l).
Proof. apply _. Qed.

Definition akeyT lvl_enc lvl_dec γ Φ l : iProp Σ :=
  resT (RAKey lvl_enc lvl_dec γ) l ∗
  own γ (Some (to_agree Φ)).

Global Instance persistent_akeyT lvl_enc lvl_dec γ Φ l :
  Persistent (akeyT lvl_enc lvl_dec γ Φ l).
Proof. apply _. Qed.

Lemma akeyT_agree lvl_enc1 lvl_enc2 lvl_dec1 lvl_dec2 γ1 γ2 Φ1 Φ2 l :
  akeyT lvl_enc1 lvl_dec1 γ1 Φ1 l -∗
  akeyT lvl_enc2 lvl_dec2 γ2 Φ2 l -∗
  ⌜lvl_enc1 = lvl_enc2⌝ ∗
  ⌜lvl_dec1 = lvl_dec2⌝ ∗
  ⌜γ1 = γ2⌝ ∗
  Φ1 ≡ Φ2.
Proof.
iIntros "[Hres1 Hown1] [Hres2 Hown2]".
iPoseProof (resT_agree with "Hres1 Hres2") as "%Hres".
case: Hres=> <- <- <-.
iPoseProof (own_valid_2 with "Hown1 Hown2") as "#Hvalid".
rewrite -Some_op uPred.option_validI agree_validI agree_equivI.
by eauto.
Qed.

Definition skeyT lvl γ Φ l : iProp Σ :=
  resT (RSKey lvl γ) l ∗
  own γ (Some (to_agree Φ)).

Global Instance persistent_skeyT lvl γ Φ l :
  Persistent (skeyT lvl γ Φ l).
Proof. apply _. Qed.

Lemma skeyT_agree lvl1 lvl2 γ1 γ2 Φ1 Φ2 l :
  skeyT lvl1 γ1 Φ1 l -∗
  skeyT lvl2 γ2 Φ2 l -∗
  ⌜lvl1 = lvl2⌝ ∗
  ⌜γ1 = γ2⌝ ∗
  Φ1 ≡ Φ2.
Proof.
iIntros "[Hres1 Hown1] [Hres2 Hown2]".
iPoseProof (resT_agree with "Hres1 Hres2") as "%Hres".
case: Hres=> <- <-.
iPoseProof (own_valid_2 with "Hown1 Hown2") as "#Hvalid".
rewrite -Some_op uPred.option_validI agree_validI agree_equivI.
by eauto.
Qed.

Definition keyT kt rs γ Φ l : iProp Σ :=
  match kt with
  | KSym => skeyT rs γ Φ l
  | KAEnc => ∃ rs_dec, akeyT rs rs_dec γ Φ l
  | KADec => ∃ rs_enc, akeyT rs_enc rs γ Φ l
  end.

Lemma keyT_agree kt rs1 rs2 γ1 γ2 Φ1 Φ2 l :
  keyT kt rs1 γ1 Φ1 l -∗ keyT kt rs2 γ2 Φ2 l -∗
  ⌜rs1 = rs2⌝ ∗ ⌜γ1 = γ2⌝ ∗ Φ1 ≡ Φ2.
Proof.
case: kt=> /=.
- by iApply skeyT_agree.
- iDestruct 1 as (rs1') "Hres1".
  iDestruct 1 as (rs2') "Hres2".
  by iPoseProof (akeyT_agree with "Hres1 Hres2") as "(<-&_&<-&?)";
  eauto.
- iDestruct 1 as (rs1') "Hres1".
  iDestruct 1 as (rs2') "Hres2".
  by iPoseProof (akeyT_agree with "Hres1 Hres2") as "(<-&<-&<-&?)";
  eauto.
Qed.

Global Instance persistent_keyT kt rs γ Φ l : Persistent (keyT kt rs γ Φ l).
Proof. by case: kt; apply _. Qed.

Definition key_info (asym : bool) lvl_enc lvl_dec γ Φ l : iProp Σ :=
  if asym then akeyT lvl_enc lvl_dec γ Φ l
  else (⌜lvl_enc = lvl_dec⌝ ∗ skeyT lvl_enc γ Φ l)%I.

Lemma key_info_agree asym1 asym2 lvl_enc1 lvl_dec1 lvl_enc2 lvl_dec2 γ1 γ2 Φ1 Φ2 l :
  key_info asym1 lvl_enc1 lvl_dec1 γ1 Φ1 l -∗
  key_info asym2 lvl_enc2 lvl_dec2 γ2 Φ2 l -∗
  ⌜asym1 = asym2⌝ ∗ ⌜lvl_enc1 = lvl_enc2⌝ ∗ ⌜lvl_dec1 = lvl_dec2⌝ ∗
  ⌜γ1 = γ2⌝ ∗ Φ1 ≡ Φ2.
Proof.
case: asym1 asym2=> [] [] /=.
- iIntros "Hown1 Hown2".
  iPoseProof (akeyT_agree with "Hown1 Hown2") as "(<-&<-&<-&?)".
  by eauto.
- iIntros "[Hown1 _] [_ [Hown2 _]]".
  by iPoseProof (resT_agree with "Hown1 Hown2") as "%Hvalid".
- iIntros "[_ [Hown1 _]] [Hown2 _]".
  by iPoseProof (resT_agree with "Hown1 Hown2") as "%Hvalid".
- iIntros "[<- Hown1] [<- Hown2]".
  iPoseProof (skeyT_agree with "Hown1 Hown2") as "(<-&<-&#Hvalid)".
  by eauto.
Qed.

Global Instance persistent_key_info asym lvl_enc lvl_dec γ Φ l :
  Persistent (key_info asym lvl_enc lvl_dec γ Φ l).
Proof. by case: asym; apply _. Qed.

(** [termT lvl t] holds when the term [t] can be declared public after
encrypting it with any of the readers lvl.  If [lvl = Pub], [t] is considered
public and does not have to be encrypted. *)

Fixpoint termT lvl t : iProp Σ :=
  match t with
  | TInt _ => True
  | TPair t1 t2 => termT lvl t1 ∗ termT lvl t2
  | TNonce l  => ∃ lvl', nonceT lvl' l ∗ ⌜lvl' ⊑ lvl⌝
  | TKey kt l => ∃ lvl' γ Φ, keyT kt lvl' γ Φ l ∗ ⌜lvl' ⊑ lvl⌝
  | TEnc asym l t =>
    ∃ lvl_enc lvl_dec γ Φ,
      key_info asym lvl_enc lvl_dec γ Φ l
      ∗ (□ Φ (l, t) ∗ termT (lvl ⊔ lvl_dec) t ∨
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
- iDestruct 1 as (lvl0 γ Φ) "[#Hkey %sub0]".
  iExists lvl0, γ, Φ; iSplit=> //; iPureIntro; by etransitivity.
- iDestruct 1 as (lvl_enc lvl_dec γ Φ) "[#Hkey #Ht]".
  iExists lvl_enc, lvl_dec, γ, Φ; iSplit=> //.
  iDestruct "Ht" as "[[? Ht]|Ht]"; last by iRight.
  iLeft; iSplit=> //; iApply (IH with "Ht").
  by case: lvl lvl' lvl_dec sub=> [] [] [].
Qed.

(** A stricter version of [termT] that does not allow subtyping *)
Definition stermT lvl t : iProp Σ :=
  termT lvl t ∗ □ ∀ lvl', termT lvl' t -∗ ⌜lvl ⊑ lvl'⌝.

Global Instance stermT_persistent lvl t : Persistent (stermT lvl t).
Proof. apply _. Qed.

Lemma stermT_pair lvl1 t1 lvl2 t2 :
  stermT lvl1 t1 -∗
  stermT lvl2 t2 -∗
  stermT (lvl1 ⊔ lvl2) (TPair t1 t2).
Proof.
iIntros "[#type1 #min1] [#type2 #min2]"; iSplit.
- rewrite /=; iSplit; iApply sub_termT; try by [iApply "type1"|iApply "type2"];
  by case: lvl1 lvl2=> [] [].
- rewrite /=; iIntros "!>" (lvl') "[#type1' #type2']".
  iPoseProof ("min1" with "type1'") as "%".
  iPoseProof ("min2" with "type2'") as "%".
  by iPureIntro; rewrite level_joinP; split.
Qed.

Lemma termT_lvlP lvl t : termT lvl t -∗ ∃ lvl', stermT lvl' t.
Proof.
elim: t lvl=> [n|t1 IH1 t2 IH2|n|kt k|b k t IH] lvl /=.
- iIntros "_"; iExists Pub; iSplit=> //.
- iIntros "[#type1 #type2]".
  iDestruct (IH1 with "type1") as (lvl1) "type1'".
  iDestruct (IH2 with "type2") as (lvl2) "type2'".
  by iExists (lvl1 ⊔ lvl2); iApply stermT_pair.
- iDestruct 1 as (lvl') "[#Hn %Hsub]".
  iExists lvl'; iSplit; first by iExists lvl'; eauto.
  iIntros "!> /=" (lvl''); iDestruct 1 as (lvl''') "[#Hn' %Hsub']".
  by iPoseProof (resT_agree with "Hn Hn'") as "%e"; case: e=> ->.
- iDestruct 1 as (lvl' γ Φ) "[#Hk %Hsub]".
  iExists lvl'; iSplit; first by iExists lvl', γ, Φ; iSplit.
  iIntros "/= !>" (lvl''); iDestruct 1 as (lvl''' γ' Φ') "[#Hk' %Hsub']".
  by iPoseProof (keyT_agree with "Hk Hk'") as "(<-&<-&_)".
- case: lvl.
    iIntros "#Ht"; iExists Pub; iSplit=> //.
    by iIntros "!>" (lvl) "_".
  iDestruct 1 as (lvl_enc lvl_dec γ Φ) "[#Hk #Ht]".
  iDestruct "Ht" as "[[#Ht type]|[-> type]]"; last first.
    iExists Pub; iSplit=> /=; first by iExists _, _, _, _; iSplit; eauto.
    by iIntros "!>" (lvl) "_".
  iDestruct (IH with "type") as (lvl) "[type' #min']".
  case: lvl.
    iExists Pub; iSplit=> /=.
      iExists _, _, _, _; iSplit=> //.
      by iLeft; iSplit=> //; case: lvl_dec.
    by iIntros "!>" (lvl) "_".
  case: lvl_dec.
    iExists Sec; iSplit=> /=.
      iExists _, _, _, _; iSplit=> //.
      by iLeft; iSplit=> //; case: lvl_dec.
    iIntros "!>" (lvl).
    iDestruct 1 as (lvl_enc' lvl_dec' γ' Φ') "[#Hk' #type'']".
    iDestruct (key_info_agree with "Hk Hk'") as "(_&<-&<-&<-&_)".
    iDestruct "type''" as "[[_ type'']|[_ type'']]";
    iPoseProof ("min'" with "type''") as "?"=> //.
    by case: lvl.
  iExists Pub; iSplit=> /=.
    iExists _, _, _, _; iSplit=> //.
    by iLeft; iSplit.
  by iIntros "!>" (lvl) "_".
Qed.

Lemma res_alloc E r l :
  ↑cryptoN.@"res" ⊆ E →
  meta_token l E ==∗
  resT r l.
Proof.
iIntros (Hsub) "Hmeta".
iMod (meta_set E l r with "Hmeta") as "Hmeta"=> //.
Qed.

End Resources.

Arguments nonceT {_ _} _ _.
Arguments skeyT {_ _ _} _ _ _ _.
Arguments akeyT {_ _ _} _ _ _ _ _.
