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

Section Resources.

Context (Σ : gFunctors).
Implicit Types Φ : termO -n> iPropO Σ.
Implicit Types l : loc.

Inductive res :=
| RNonce of readers
| RAKey of readers & readers & termO -n> iPropO Σ
| RSKey of readers & termO -n> iPropO Σ.

Global Instance res_equiv : Equiv res := λ r1 r2,
  match r1, r2 with
  | RNonce rs1, RNonce rs2 => rs1 = rs2
  | RAKey rs11 rs12 P1, RAKey rs21 rs22 P2 =>
    rs11 = rs21 ∧ rs12 = rs22 ∧ P1 ≡ P2
  | RSKey rs1 P1, RSKey rs2 P2 => rs1 = rs2 ∧ P1 ≡ P2
  | _, _ => False
  end.

Global Instance res_dist : Dist res := λ n r1 r2,
  match r1, r2 with
  | RNonce rs1, RNonce rs2 => rs1 = rs2
  | RAKey rs11 rs12 P1, RAKey rs21 rs22 P2 =>
    rs11 = rs21 ∧ rs12 = rs22 ∧ P1 ≡{n}≡ P2
  | RSKey rs1 P1, RSKey rs2 P2 => rs1 = rs2 ∧ P1 ≡{n}≡ P2
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
  + case=> [rs1|rs11 rs12 P1|rs1 P1] [rs2|rs21 rs22 P2|rs2 P2] //=;
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
  | RNonce rs1, RNonce rs2 => ⌜rs1 = rs2⌝
  | RAKey rs_enc1 rs_dec1 Φ1, RAKey rs_enc2 rs_dec2 Φ2 =>
    ⌜rs_enc1 = rs_enc2⌝ ∧ ⌜rs_dec1 = rs_dec2⌝ ∧ Φ1 ≡ Φ2
  | RSKey rs1 Φ1, RSKey rs2 Φ2 =>
    ⌜rs1 = rs2⌝ ∧ Φ1 ≡ Φ2
  | _, _ => False
  end.
Proof. case: r1=> *; case: r2=> * /=; by uPred.unseal. Qed.

Global Instance discrete_RNonce rs : Discrete (RNonce rs).
Proof. by case. Qed.

Definition resM := gmap loc res.
Definition resR := gmapUR loc (agreeR resO).
Implicit Types (RM : resM) (RR : resR).

Definition to_resR : resM → resR :=
  fmap to_agree.

Lemma to_resR_uninjI RR : ✓ RR ⊢@{iPropI Σ} ∃ RM, to_resR RM ≡ RR.
Proof.
move: RR; apply: map_ind.
  by iIntros "_"; iExists ∅; rewrite /to_resR fmap_empty.
move=> l ag RR RR_l IH; iIntros "#valid"; rewrite gmap_validI.
iAssert (✓ ag)%I as "valid_ag".
  by iSpecialize ("valid" $! l); rewrite lookup_insert uPred.option_validI.
iAssert (✓ RR)%I as "valid_RR".
  rewrite gmap_validI; iIntros (l').
  iSpecialize ("valid" $! l').
  destruct (decide (l' = l)) as [->|ne ].
  - by rewrite RR_l !uPred.option_validI.
  - by rewrite lookup_insert_ne //.
iDestruct (to_agree_uninjI with "valid_ag") as (r) "Hr".
iDestruct (IH with "valid_RR") as (RM) "IH".
iExists (<[l := r]>RM).
rewrite /to_resR fmap_insert.
iRewrite -"Hr".
by iRewrite -"IH".
Qed.

Lemma to_resR_equivI RM1 RM2 :
  to_resR RM1 ≡ to_resR RM2 ⊣⊢@{iPropI Σ} RM1 ≡ RM2.
Proof.
rewrite /to_resR !gmap_equivI; iSplit.
- iIntros "e" (l).
  iSpecialize ("e" $! l).
  rewrite !lookup_fmap !option_equivI.
  case: (RM1 !! l) (RM2 !! l)=> [v1|] [v2|] //=.
  by rewrite agree_equivI.
- iIntros "e" (l).
  iSpecialize ("e" $! l).
  rewrite !lookup_fmap !option_equivI.
  case: (RM1 !! l) (RM2 !! l) => [v1|] [v2|] //=.
  by rewrite agree_equivI.
Qed.

Class resG := {
  res_inG :> inG Σ (authR resR);
  res_name : gname
}.

Context `{!resG, !heapG Σ}.

Definition nonceT rs l : iProp Σ :=
  own res_name (◯ {[l := to_agree (RNonce rs)]}).

Global Instance persistent_nonceT rs l :
  Persistent (nonceT rs l).
Proof. apply _. Qed.

Global Instance timeless_nonceT rs l :
  Timeless (nonceT rs l).
Proof. apply _. Qed.

Definition akeyT rs_enc rs_dec Φ l : iProp Σ :=
  own res_name (◯ {[l := to_agree (RAKey rs_enc rs_dec Φ)]}).

Global Instance persistent_akeyT rs_enc rs_dec Φ l :
  Persistent (akeyT rs_enc rs_dec Φ l).
Proof. apply _. Qed.

Definition skeyT rs Φ l : iProp Σ :=
  own res_name (◯ {[l := to_agree (RSKey rs Φ)]}).

Global Instance persistent_skeyT rs Φ l :
  Persistent (skeyT rs Φ l).
Proof. apply _. Qed.

Definition keyT kt rs Φ l : iProp Σ :=
  match kt with
  | KSym => skeyT rs Φ l
  | KAEnc => ∃ rs_dec, akeyT rs rs_dec Φ l
  | KADec => ∃ rs_enc, akeyT rs_enc rs Φ l
  end.

Global Instance persistent_keyT kt rs Φ l : Persistent (keyT kt rs Φ l).
Proof. by case: kt; apply _. Qed.

Definition priv_keyT rs l : iProp Σ :=
    (∃ rs_enc Φ, akeyT rs_enc (RPriv rs) Φ l)
  ∨ (∃ Φ, skeyT (RPriv rs) Φ l).

Global Instance priv_keyT_proper : Proper (equiv ==> equiv ==> equiv) priv_keyT.
Proof.
by move=> rs1 rs2 /(leibniz_equiv rs1 rs2) -> l1 l2 /(leibniz_equiv l1 l2) ->.
Qed.

Global Instance priv_keyT_ne : NonExpansive2 priv_keyT.
Proof.
move=> n.
by move=> rs1 rs2 /(leibniz_equiv rs1 rs2) -> l1 l2 /(leibniz_equiv l1 l2) ->.
Qed.

Global Instance persistent_priv_keyT rs l :
  Persistent (priv_keyT rs l).
Proof. apply _. Qed.

Global Instance timeless_priv_keyT rs l :
  Timeless (priv_keyT rs l).
Proof.
rewrite /Timeless; iDestruct 1 as "[H|H]".
- iDestruct "H" as (rs_enc Φ) "H"; iLeft.
  iExists rs_enc; iMod (later_own with "H") as (rm) "[Hown #He]".
  case: rm=> ? rm.
  rewrite auth_equivI /=; iDestruct "He" as "(> <- & Hfrag)".
  rewrite -[Auth None rm]/(◯ rm).
  iAssert (▷ (dom (gset loc) rm ≡ {[l]}))%I as "> %Hdom".
    by iModIntro; iRewrite -"Hfrag"; rewrite dom_singleton.
  apply leibniz_equiv in Hdom.
  have {Hdom rm} [ag ->] := dom_singleton_eq Hdom.
  iPoseProof (own_valid with "Hown") as "#Hvalid".
  iAssert (✓ {[l := ag]})%I as "#Hvalid'".
    by rewrite auth_validI /=.
  rewrite gmap_validI; iSpecialize ("Hvalid'" $! l); rewrite lookup_singleton.
  rewrite uPred.option_validI.
  iDestruct (to_agree_uninjI with "Hvalid'") as (r) "Hr".
  iRewrite -"Hr" in "Hown".
  iAssert (▷ (r ≡ RAKey rs_enc (RPriv rs) Φ))%I as "H".
    iModIntro; rewrite -[(r ≡ _)%I]agree_equivI; iRewrite "Hr".
    rewrite gmap_equivI; iSpecialize ("Hfrag" $! l); rewrite !lookup_singleton.
    by rewrite option_equivI; iRewrite -"Hfrag".
  destruct r as [rs'|rs_enc' rs_dec' Φ'|rs' Φ'] eqn:er.
  + iAssert (▷ False)%I as "> []"; iModIntro; by rewrite res_equivI.
  + rewrite res_equivI; iDestruct "H" as "(>% & >% & H)".
    by subst r rs_enc' rs_dec'; iExists Φ'; iModIntro.
  + iAssert (▷ False)%I as "> []"; iModIntro; by rewrite res_equivI.
- iDestruct "H" as (Φ) "H"; iRight.
  iMod (later_own with "H") as (rm) "[Hown #He]".
  case: rm=> ? rm.
  rewrite auth_equivI /=; iDestruct "He" as "(> <- & Hfrag)".
  rewrite -[Auth None rm]/(◯ rm).
  iAssert (▷ (dom (gset loc) rm ≡ {[l]}))%I as "> %Hdom".
    by iModIntro; iRewrite -"Hfrag"; rewrite dom_singleton.
  apply leibniz_equiv in Hdom.
  have {Hdom rm} [ag ->] := dom_singleton_eq Hdom.
  iPoseProof (own_valid with "Hown") as "#Hvalid".
  iAssert (✓ {[l := ag]})%I as "#Hvalid'".
    by rewrite auth_validI /=.
  rewrite gmap_validI; iSpecialize ("Hvalid'" $! l); rewrite lookup_singleton.
  rewrite uPred.option_validI.
  iDestruct (to_agree_uninjI with "Hvalid'") as (r) "Hr".
  iRewrite -"Hr" in "Hown".
  iAssert (▷ (r ≡ RSKey (RPriv rs) Φ))%I as "H".
    iModIntro; rewrite -[(r ≡ _)%I]agree_equivI; iRewrite "Hr".
    rewrite gmap_equivI; iSpecialize ("Hfrag" $! l); rewrite !lookup_singleton.
    by rewrite option_equivI; iRewrite -"Hfrag".
  destruct r as [rs'|rs_enc' rs_dec' Φ'|rs' Φ'] eqn:er.
  + iAssert (▷ False)%I as "> []"; iModIntro; by rewrite res_equivI.
  + iAssert (▷ False)%I as "> []"; iModIntro; by rewrite res_equivI.
  + rewrite res_equivI; iDestruct "H" as "(>% & H)".
    by subst r rs'; iExists Φ'; iModIntro.
Qed.

Definition wf_readers rs : iProp Σ :=
  match rs with
  | RPub     => True
  | RPriv rs => ∀l, ⌜l ∈ rs⌝ → ∃ rs', priv_keyT rs' l
  end.

Global Instance wf_readers_proper : Proper (equiv ==> equiv) wf_readers.
Proof. by move=> rs1 rs2 ->. Qed.

Global Instance wf_readers_ne : NonExpansive wf_readers.
Proof. by move=> n rs1 rs2 ->. Qed.

Global Instance persistent_wf_readers rs :
  Persistent (wf_readers rs).
Proof. case: rs=> *; apply _. Qed.

Global Instance timeless_wf_readers rs :
  Timeless (wf_readers rs).
Proof. case: rs=> *; apply _. Qed.

Definition wf_res r : iProp Σ :=
  match r with
  | RNonce rs => wf_readers rs
  | RAKey rs1 rs2 _ => wf_readers rs1 ∗ wf_readers rs2
  | RSKey rs _ => wf_readers rs
  end.

Global Instance persistent_wf_res r : Persistent (wf_res r).
Proof. case: r=> *; apply _. Qed.

Global Instance timeless_wf_res r : Timeless (wf_res r).
Proof. case: r=> *; apply _. Qed.

Global Instance wf_res_proper : Proper (equiv ==> equiv) wf_res.
Proof.
move=> r1 r2.
case: r1=> [rs1|rs1_enc rs1_dec Φ1|rs1 Φ1];
case: r2=> [rs2|rs2_enc rs2_dec Φ2|rs2 Φ2] //=.
- by solve_proper.
- by intros (-> & -> & _).
- by intros (-> & _).
Qed.

Global Instance wf_res_ne : NonExpansive wf_res.
Proof.
move=> n r1 r2.
case: r1=> [rs1|rs1_enc rs1_dec Φ1|rs1 Φ1];
case: r2=> [rs2|rs2_enc rs2_dec Φ2|rs2 Φ2] //=.
- by solve_proper.
- by intros (-> & -> & _).
- by intros (-> & _).
Qed.

Definition res_inv : iProp Σ :=
  ∃ RM, own res_name (● (to_resR RM))
        ∗ [∗ map] l ↦ r ∈ RM, l ↦ #() ∗ wf_res r.

(** [termT rs t] holds when the term [t] can be declared public after encrypting
it with any of the readers rs.  If [rs = RPub], [t] is considered public and
does not have to be encrypted. *)

Fixpoint termT rs t : iProp Σ :=
  match t with
  | TInt _ => True
  | TPair t1 t2 => termT rs t1 ∗ termT rs t2
  | TNonce l  => ∃ rs', nonceT rs' l ∗ ⌜rs ⊆ rs'⌝
  | TKey kt l => ∃ rs' Φ, keyT kt rs' Φ l ∗ ⌜rs ⊆ rs'⌝
  | TEnc asym l t =>
    let kt := if asym then KAEnc else KSym in
    ∃ rs' Φ, keyT kt rs' Φ l
             ∗ (□ Φ t ∗ termT {[l]} t ∨ ⌜rs' = RPub⌝ ∗ termT RPub t)
  end.

Global Instance persistent_termT rs t :
  Persistent (termT rs t).
Proof. elim: t rs=> *; apply _. Qed.

Lemma sub_termT rs rs' t :
  rs' ⊆ rs →
  termT rs t -∗
  termT rs' t.
Proof.
elim: t rs=> [n|t1 IH1 t2 IH2|l|kt l|b l t IH] rs sub //=.
- by iIntros "[#Ht1 #Ht2]"; rewrite IH1 // IH2 //; iSplit.
- iDestruct 1 as (rs0) "[#Hnonce %sub0]".
  iExists rs0; iSplit=> //; iPureIntro; by etransitivity.
- iDestruct 1 as (rs0 Φ) "[#Hkey %sub0]".
  iExists rs0, Φ; iSplit=> //; iPureIntro; by etransitivity.
Qed.

Lemma nonce_alloc rs l :
  res_inv -∗
  l ↦ #() -∗
  wf_readers rs -∗
  |==> res_inv ∗ nonceT rs l.
Proof.
iDestruct 1 as (RM) "[Hown Hreaders]".
iIntros "Hl Hrs".
destruct (RM !! l) as [rs'|] eqn:e.
  rewrite big_sepM_delete //.
  iDestruct "Hreaders" as "[[Hl' _] _]".
  by iPoseProof (mapsto_valid_2 with "Hl Hl'") as "%".
pose (RM' := <[l := RNonce rs]>RM).
iAssert ([∗ map] l' ↦ rs' ∈ RM', l' ↦ #() ∗ wf_res rs')%I
    with "[Hreaders Hl Hrs]" as "Hreaders".
  by rewrite /RM' big_sepM_insert //; iFrame.
iMod (own_update _ _ (_ ⋅ ◯ {[l := to_agree (RNonce rs)]}) with "Hown")
    as "[Hown #Hfrag]".
  apply auth_update_alloc, alloc_singleton_local_update=> //.
  by rewrite lookup_fmap e.
iModIntro; iSplitL=> //.
iExists RM'; iFrame; by rewrite /RM' /to_resR fmap_insert.
Qed.

Lemma akey_alloc rs_enc rs_dec Φ l :
  res_inv -∗
  l ↦ #() -∗
  wf_readers rs_enc -∗
  wf_readers rs_dec -∗
  |==> res_inv ∗ akeyT rs_enc rs_dec Φ l.
Proof.
iDestruct 1 as (RM) "[Hown Hreaders]".
iIntros "Hl Henc Hdec".
destruct (RM !! l) as [rs'|] eqn:e.
  rewrite big_sepM_delete //.
  iDestruct "Hreaders" as "[[Hl' _] _]".
  by iPoseProof (mapsto_valid_2 with "Hl Hl'") as "%".
pose (RM' := <[l := RAKey rs_enc rs_dec Φ]>RM).
iAssert ([∗ map] l' ↦ rs' ∈ RM', l' ↦ #() ∗ wf_res rs')%I
    with "[Hreaders Hl Henc Hdec]" as "Hreaders".
  by rewrite /RM' big_sepM_insert //; iFrame.
iMod (own_update _ _ (_ ⋅ ◯ {[l := to_agree (RAKey rs_enc rs_dec Φ)]})
       with "Hown") as "[Hown #Hfrag]".
  apply auth_update_alloc, alloc_singleton_local_update=> //.
  by rewrite lookup_fmap e.
iModIntro; iSplitL=> //.
iExists RM'; iFrame; by rewrite /RM' /to_resR fmap_insert.
Qed.

Lemma skey_alloc rs Φ l :
  res_inv -∗
  l ↦ #() -∗
  wf_readers rs -∗
  |==> res_inv ∗ skeyT rs Φ l.
Proof.
iDestruct 1 as (RM) "[Hown Hreaders]".
iIntros "Hl Hrs".
destruct (RM !! l) as [rs'|] eqn:e.
  rewrite big_sepM_delete //.
  iDestruct "Hreaders" as "[[Hl' _] _]".
  by iPoseProof (mapsto_valid_2 with "Hl Hl'") as "%".
pose (RM' := <[l := RSKey rs Φ]>RM).
iAssert ([∗ map] l' ↦ rs' ∈ RM', l' ↦ #() ∗ wf_res rs')%I
    with "[Hreaders Hl Hrs]" as "Hreaders".
  by rewrite /RM' big_sepM_insert //; iFrame.
iMod (own_update _ _ (_ ⋅ ◯ {[l := to_agree (RSKey rs Φ)]}) with "Hown")
    as "[Hown #Hfrag]".
  apply auth_update_alloc, alloc_singleton_local_update=> //.
  by rewrite lookup_fmap e.
iModIntro; iSplitL=> //.
iExists RM'; iFrame; by rewrite /RM' /to_resR fmap_insert.
Qed.

Lemma res_alloc E r l :
  ▷ res_inv -∗
  l ↦ #() -∗
  wf_res r ={E}=∗
  ▷ res_inv ∗ own res_name (◯ {[l := to_agree r]}).
Proof.
iDestruct 1 as (RM1) "[Hown >wf_RM1]"; iIntros "Hl #wf_r".
iMod (later_own with "Hown") as (a) "[Hown Ha]".
case: a=> [aa af]; rewrite auth_equivI /=.
iDestruct "Ha" as "[Ha >Haf]"; iRewrite -"Haf" in "Hown".
rewrite option_equivI; case: aa=> [[q a]|]; last by iMod "Ha" as "[]".
rewrite prod_equivI /=; iDestruct "Ha" as "[> <- #Ha]".
iPoseProof (own_valid with "Hown") as "#Hvalid".
rewrite auth_validI /=.
iDestruct "Hvalid" as "(_&Hvalid)".
iDestruct "Hvalid" as (RR) "(e & _ & Hvalid)".
iRewrite "e" in "Hown"; iRewrite "e" in "Ha"; iClear "e"; clear a af.
rewrite -[Auth _ _]/(● RR) agree_equivI.
iDestruct (to_resR_uninjI with "Hvalid") as (RM2) "e".
iRewrite -"e" in "Hown"; iRewrite -"e" in "Ha".
rewrite to_resR_equivI.
iAssert (▷ (dom (gset loc) RM1 ≡ dom (gset loc) RM2))%I as "> %e".
  by iModIntro; iRewrite "Ha".
iAssert (⌜l ∉ dom (gset loc) RM2⌝)%I as "%Hfresh".
  rewrite -e elem_of_dom; iIntros "%contra".
  case: contra=> v RM_l; rewrite big_sepM_delete //.
  iDestruct "wf_RM1" as "[[Hl' _] _]".
  by iPoseProof (mapsto_valid_2 with "Hl Hl'") as "%".
iMod (own_update _ _ (_ ⋅ ◯ {[l := to_agree r]}) with "Hown")
    as "[Hown ?]".
  apply auth_update_alloc, alloc_singleton_local_update; last done.
  by rewrite -not_elem_of_dom dom_fmap.
iAssert (▷ res_inv)%I with "[Hl wf_RM1 Hown]" as "Hinv".
  iModIntro. iRewrite -"Ha" in "Hown".
  iExists (<[l:=r]> RM1).
  rewrite -fmap_insert; iFrame.
  rewrite big_sepM_insert /=; first by iFrame.
  by apply/not_elem_of_dom; rewrite e.
by iModIntro; iFrame.
Qed.

End Resources.

Arguments res_name {_ _}.
Arguments RNonce {_} _.
Arguments to_resR {_} _.
Arguments nonceT {_ _} _ _.
Arguments skeyT {_ _} _ _ _.
Arguments akeyT {_ _} _ _ _ _.
Arguments priv_keyT {_ _} _ _.
Arguments wf_readers {_ _} _.
Arguments wf_res {_ _} _.
Arguments res_inv {_ _ _}.
