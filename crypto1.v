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

Section Resources.

Context (Σ : gFunctors).
Implicit Types Φ : termO -n> iPropO Σ.
Implicit Types l : loc.
Implicit Types γ : gname.

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

Definition priv_dec_key (rs : gset loc) r : Prop :=
  match r with
  | RAKey _ (RPriv rs') _ | RSKey (RPriv rs') _ => rs' ⊆ rs
  | _ => False
  end.

Lemma priv_dec_key_sub rs rs' r :
  rs ⊆ rs' → priv_dec_key rs r → priv_dec_key rs' r.
Proof.
case: r=> [?|?[|?]?|[|?]?] //=; set_solver.
Qed.

Definition pub_dec_key r : Prop :=
  match r with
  | RAKey _ RPub _ | RSKey RPub _ => True
  | _ => False
  end.

Class resG := {
  res_inG :> inG Σ (agreeR resO);
}.

Context `{!resG, !heapG Σ}.

Definition pre_resT r l : iProp Σ :=
  ∃ γ, meta l (cryptoN.@"res") γ ∗ own γ (to_agree r).

Lemma pre_resT_persistent r l : Persistent (pre_resT r l).
Proof. apply _. Qed.

Lemma pre_resT_agree r1 r2 l : pre_resT r1 l -∗ pre_resT r2 l -∗ r1 ≡ r2.
Proof.
iDestruct 1 as (γ) "[#Hl #Hγ]".
iDestruct 1 as (γ') "[#Hl' #Hγ']".
iPoseProof (meta_agree with "Hl Hl'") as "<-".
iPoseProof (own_valid_2 with "Hγ Hγ'") as "Hvalid".
by rewrite agree_validI agree_equivI.
Qed.

Lemma later_pre_resT r l :
  ▷ pre_resT r l -∗ ◇ ∃ r', pre_resT r' l ∗ ▷ (r ≡ r').
Proof.
iDestruct 1 as (γ) "[> #Hmeta Hown]".
iMod (later_own with "Hown") as (ag) "[#Hown #Hr]".
iPoseProof (own_valid with "Hown") as "#Hvalid".
iDestruct (to_agree_uninjI with "Hvalid") as (r') "Hr'".
iRewrite -"Hr'" in "Hr"; iRewrite -"Hr'" in "Hown"; rewrite agree_equivI.
iModIntro; iExists r'; iSplit=> //.
by iExists γ; iSplit.
Qed.

Definition pre_wf_readers rs_priv rs :=
  match rs with
  | RPub     => True
  | RPriv rs => rs ⊆ rs_priv
  end.

Lemma pre_wf_readers_sub rs_priv rs_priv' rs :
  rs_priv ⊆ rs_priv' → pre_wf_readers rs_priv rs → pre_wf_readers rs_priv' rs.
Proof. case: rs=> //= rs *; set_solver. Qed.

Definition pre_wf_res rs_priv r :=
  match r with
  | RNonce rs => pre_wf_readers rs_priv rs
  | RAKey rs1 rs2 _ => pre_wf_readers rs_priv rs1 ∧ pre_wf_readers rs_priv rs2
  | RSKey rs _ => pre_wf_readers rs_priv rs
  end.

Definition priv_keyT rs_priv l : iProp Σ :=
  ∃ r, pre_resT r l ∗ ⌜priv_dec_key rs_priv r⌝.

Global Instance priv_keyT_proper :
  Proper (equiv ==> equiv ==> equiv) priv_keyT.
Proof.
by move=> rs1 rs2 /(leibniz_equiv rs1 rs2) -> l1 l2 /(leibniz_equiv l1 l2) ->.
Qed.

Global Instance priv_keyT_ne : NonExpansive2 priv_keyT.
Proof.
move=> n.
by move=> rs1 rs2 /(leibniz_equiv rs1 rs2) -> l1 l2 /(leibniz_equiv l1 l2) ->.
Qed.

Global Instance priv_keyT_persistent rs_priv l :
  Persistent (priv_keyT rs_priv l).
Proof. apply _. Qed.

Global Instance priv_keyT_timeless rs_priv l :
  Timeless (priv_keyT rs_priv l).
Proof.
rewrite /Timeless /priv_keyT bi.later_exist_except_0.
iMod 1 as (r) "[#Hown >%Hpriv]".
iMod (later_pre_resT with "Hown") as (r') "[Hown' He]".
iExists r'; iSplit; eauto; rewrite res_equivI.
case: r Hpriv => [rs|rs_enc [|rs_dec] Φ|[|rs_dec] Φ] //= Hpriv;
case: r'=> [?|???|??]; try by iDestruct "He" as "> []".
- by iDestruct "He" as "(><-&><-&?)".
- by iDestruct "He" as "(><-&?)".
Qed.

Lemma priv_keyT_sub rs_priv rs_priv' l :
  rs_priv ⊆ rs_priv' → priv_keyT rs_priv l -∗ priv_keyT rs_priv' l.
Proof.
move=> sub; iDestruct 1 as (r) "[Hr %Hpriv]".
iExists r; iFrame; iPureIntro.
by eapply priv_dec_key_sub.
Qed.

Definition priv_keysT rs_priv : iProp Σ :=
  ∀ l, ⌜l ∈ rs_priv⌝ -∗ priv_keyT rs_priv l.

Definition pub_keyT l : iProp Σ :=
  ∃ r, pre_resT r l ∗ ⌜pub_dec_key r⌝.

Global Instance pub_keyT_persistent l : Persistent (pub_keyT l).
Proof. apply _. Qed.

Global Instance pub_keyT_timeless l : Timeless (pub_keyT l).
Proof.
rewrite /Timeless /pub_keyT bi.later_exist_except_0.
iMod 1 as (r) "[#Hown >%Hpriv]".
iMod (later_pre_resT with "Hown") as (r') "[Hown' He]".
iExists r'; iSplit; eauto; rewrite res_equivI.
case: r Hpriv => [rs|rs_enc [|rs_dec] Φ|[|rs_dec] Φ] //= Hpriv;
case: r'=> [?|???|??]; try by iDestruct "He" as "> []".
- by iDestruct "He" as "(><-&><-&?)".
- by iDestruct "He" as "(><-&?)".
Qed.

Definition pub_keysT (rs_pub : gset loc) : iProp Σ :=
  ∀ l, ⌜l ∈ rs_pub⌝ -∗ pub_keyT l.

Global Instance pub_keysT_persistent rs_pub : Persistent (pub_keysT rs_pub).
Proof. apply _. Qed.

Global Instance pub_keysT_timeless rs_pub : Timeless (pub_keysT rs_pub).
Proof. apply _. Qed.

Definition wf_readers_priv rs : iProp Σ :=
  ∃ rs_priv, priv_keysT rs_priv ∗ ⌜pre_wf_readers rs_priv rs⌝.

Global Instance wf_readers_priv_persistent rs : Persistent (wf_readers_priv rs).
Proof. apply _. Qed.

Global Instance wf_readers_priv_timeless rs : Timeless (wf_readers_priv rs).
Proof. apply _. Qed.

Definition wf_readers rs : iProp Σ :=
  match rs with
  | RPub => True
  | RPriv rs =>
    ∃ rs1 rs2, ⌜rs = rs1 ∪ rs2⌝ ∗ wf_readers_priv (RPriv rs1) ∗ pub_keysT rs2
  end.

Global Instance wf_readers_persistent rs : Persistent (wf_readers rs).
Proof. case: rs=> *; apply _. Qed.

Global Instance wf_readers_timeless rs : Timeless (wf_readers rs).
Proof. case: rs=> *; apply _. Qed.

Definition wf_res_priv r : iProp Σ :=
  ∃ rs_priv, priv_keysT rs_priv ∗ ⌜pre_wf_res rs_priv r⌝.

Global Instance wf_res_priv_persistent r : Persistent (wf_res_priv r).
Proof. apply _. Qed.

Global Instance wf_res_priv_timeless r : Timeless (wf_res_priv r).
Proof. apply _. Qed.

Lemma wf_res_privE r :
  wf_res_priv r ⊣⊢@{iPropI Σ}
  match r with
  | RNonce rs => wf_readers_priv rs
  | RAKey rs_enc rs_dec _ => wf_readers_priv rs_enc ∧ wf_readers_priv rs_dec
  | RSKey rs _ => wf_readers_priv rs
  end.
Proof.
case: r; try by move=> *; iSplit; eauto.
move=> rs_enc rs_dec Φ /=; iSplit.
- iDestruct 1 as (rs_priv) "(wf_rs_priv & %wf_rs_enc & %wf_rs_dec)".
  by iSplit; iExists rs_priv; iSplit.
- iIntros "[Henc Hdec]".
  iDestruct "Henc" as (rs_priv_enc) "[Hpriv_enc %Hwf_enc]".
  iDestruct "Hdec" as (rs_priv_dec) "[Hpriv_dec %Hwf_dec]".
  iExists (rs_priv_enc ∪ rs_priv_dec); iSplit; last first.
    iPureIntro; split; eapply pre_wf_readers_sub; try eassumption;
    set_solver.
  iIntros (l) "%Hl"; case/elem_of_union: Hl=> Hl.
  + iSpecialize ("Hpriv_enc" $! _ Hl).
    iApply (priv_keyT_sub with "Hpriv_enc"); set_solver.
  + iSpecialize ("Hpriv_dec" $! _ Hl).
    iApply (priv_keyT_sub with "Hpriv_dec"); set_solver.
Qed.

Definition res_privT r l : iProp Σ :=
  pre_resT r l ∗ wf_res_priv r.

Lemma res_privT_agree r1 r2 l : res_privT r1 l -∗ res_privT r2 l -∗ r1 ≡ r2.
Proof.
iIntros "[Hr1 _] [Hr2 _]". iApply (pre_resT_agree with "Hr1 Hr2").
Qed.

Global Instance res_privT_persistent r l : Persistent (res_privT r l).
Proof. apply _. Qed.

Definition wf_res r : iProp Σ :=
  match r with
  | RNonce rs => wf_readers rs
  | RAKey rs_enc rs_dec _ => wf_readers rs_enc ∧ wf_readers rs_dec
  | RSKey rs _ => wf_readers rs
  end.

Global Instance wf_resT_persistent r : Persistent (wf_res r).
Proof. case: r=> *; apply _. Qed.

Global Instance wf_resT_timeless r : Timeless (wf_res r).
Proof. case: r=> *; apply _. Qed.

Definition resT r l : iProp Σ :=
  pre_resT r l ∗ wf_res r.

Lemma resT_agree r1 r2 l : resT r1 l -∗ resT r2 l -∗ r1 ≡ r2.
Proof.
iIntros "[Hr1 _] [Hr2 _]". iApply (pre_resT_agree with "Hr1 Hr2").
Qed.

Global Instance resT_persistent r l : Persistent (resT r l).
Proof. case: r=> *; apply _. Qed.

Definition nonceT rs l : iProp Σ := resT (RNonce rs) l.

Lemma nonceT_agree rs1 rs2 l : nonceT rs1 l -∗ nonceT rs2 l -∗ ⌜rs1 = rs2⌝.
Proof.
iIntros "Hown1 Hown2".
iPoseProof (resT_agree with "Hown1 Hown2") as "#Hvalid".
by rewrite res_equivI.
Qed.

Global Instance persistent_nonceT rs l :
  Persistent (nonceT rs l).
Proof. apply _. Qed.

Global Instance timeless_nonceT rs l :
  Timeless (nonceT rs l).
Proof. apply _. Qed.

Definition akeyT rs_enc rs_dec Φ l : iProp Σ :=
  resT (RAKey rs_enc rs_dec Φ) l.

Global Instance persistent_akeyT rs_enc rs_dec Φ l :
  Persistent (akeyT rs_enc rs_dec Φ l).
Proof. apply _. Qed.

Definition skeyT rs Φ l : iProp Σ := resT (RSKey rs Φ) l.

Global Instance persistent_skeyT rs Φ l :
  Persistent (skeyT rs Φ l).
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

Lemma term_proj_termT t n rs t' :
  term_proj t n = Some t' →
  termT rs t -∗
  termT rs t'.
Proof.
elim: t n=> // t1 IH1 t2 IH2 [|n] /=.
  by move=> [<-]; iIntros "[??]".
move=> {}/IH2 IH2; iIntros "[??]".
by iApply IH2.
Qed.

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

(** A stricter version of [termT] that does not allow subtyping *)
Definition stermT rs t : iProp Σ :=
  termT rs t ∗ □ (∀ rs', termT rs' t -∗ ⌜rs' ⊆ rs⌝).

Global Instance stermT_persistent rs t : Persistent (stermT rs t).
Proof. apply _. Qed.

Definition termT' rs t : iProp Σ :=
  termT rs t ∨ ∃ l, ⌜l ∈ rs⌝ ∗ pub_keyT l ∗ termT RPub t.

Definition stermT' rs t : iProp Σ :=
  stermT rs t ∨ ∃ l, ⌜l ∈ rs⌝ ∗ pub_keyT l ∗ termT RPub t.

(** Because of [sub_termT], the definition of [termT] does not allow us to track
the owners of a term exactly.  To remedy that, we introduce the [secretT rs t]
predicate below, which says that [t] is private exactly to the readers in
[rs].  *)

Fixpoint secretT_def (rs : gset loc) t : iProp Σ :=
  match t with
  | TInt _ => False
  | TPair t1 t2 => secretT_def rs t1 ∨ secretT_def rs t2
  | TNonce l => nonceT (RPriv rs) l
  | TKey kt l => ∃ Φ, keyT kt (RPriv rs) Φ l
  | TEnc _ _ _ => False
  end.

Global Instance secretT_def_persistent (rs : gset loc) t :
  Persistent (secretT_def rs t).
Proof. by elim: t=> *; apply _. Qed.

Definition secretT (rs : gset loc) t : iProp Σ :=
  termT (RPriv rs) t ∗ secretT_def rs t.

Global Instance secretT_persistent (rs : gset loc) t :
  Persistent (secretT rs t).
Proof. by apply _. Qed.

Lemma res_alloc E r l :
  ↑cryptoN.@"res" ⊆ E →
  meta_token l E -∗
  wf_res r ==∗
  resT r l.
Proof.
iIntros (Hsub) "Hmeta #Hr".
iMod (own_alloc (to_agree r)) as (γ) "#Hown" => //.
iMod (meta_set E l γ with "Hmeta") as "Hmeta"=> //.
by iModIntro; iSplit=> //; iExists γ; iSplit.
Qed.

End Resources.

Arguments RNonce {_} _.
Arguments nonceT {_ _ _} _ _.
Arguments skeyT {_ _ _} _ _ _.
Arguments akeyT {_ _ _} _ _ _ _.
Arguments wf_readers_priv {_ _ _} _.
Arguments wf_readers {_ _ _} _.
Arguments wf_res_priv {_ _ _} _.
Arguments wf_res {_ _ _} _.
