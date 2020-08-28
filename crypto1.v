From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gmap.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import term.

Inductive readers :=
| RPub
| RPriv of gset loc.

Canonical readersO := leibnizO readers.

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

Inductive res :=
| RNonce of readers
| RKey of readers & termO -n> iPropO Σ.

Definition readers_of_res r :=
  match r with
  | RNonce rs => rs
  | RKey rs _ => rs
  end.

Global Instance res_equiv : Equiv res := λ r1 r2,
  match r1, r2 with
  | RNonce rs1, RNonce rs2 => rs1 = rs2
  | RKey rs1 P1, RKey rs2 P2 => rs1 = rs2 ∧ P1 ≡ P2
  | _, _ => False
  end.

Global Instance res_dist : Dist res := λ n r1 r2,
  match r1, r2 with
  | RNonce rs1, RNonce rs2 => rs1 = rs2
  | RKey rs1 P1, RKey rs2 P2 => rs1 = rs2 ∧ P1 ≡{n}≡ P2
  | _, _ => False
  end.

Lemma res_ofe_mixin : OfeMixin res.
Proof.
split.
- move=> r1 r2; case: r1=> *; case: r2=> *;
  rewrite /equiv /dist /= ?forall_and_distr ?equiv_dist;
  intuition eauto using 0.
- move=> n; split.
  + case=> * //=; by apply equiv_dist.
  + case=> [rs1|rs1 P1] [rs2|rs2 P2] // [-> e2].
    by rewrite /dist /=.
  + case=> [?|??] [?|??] // [?|??] //.
      by move=> ->.
    by rewrite /dist /=; case=> -> ->.
- rewrite /dist => n [?|??] [?|??] //=.
  by case=> -> /dist_S ->.
Qed.
Canonical resO := OfeT res res_ofe_mixin.

Definition resM := gmap loc res.
Definition resR := gmapUR loc (agreeR resO).
Implicit Types RM : resM.

Definition to_resR : resM → resR :=
  fmap to_agree.

Class resG := {
  res_inG :> inG Σ (authR resR);
  res_name : gname
}.

Context `{!resG, !heapG Σ}.

Definition nonceT l rs : iProp Σ :=
  own res_name (◯ {[l := to_agree (RNonce rs)]}).

Global Instance persistent_nonceT l rs :
  Persistent (nonceT l rs).
Proof. apply _. Qed.

Definition keyT l rs Φ : iProp Σ :=
  own res_name (◯ {[l := to_agree (RKey rs Φ)]}).

Global Instance persistent_keyT l rs Φ :
  Persistent (keyT l rs Φ).
Proof. apply _. Qed.

Definition wf_readers rs : iProp Σ :=
  match rs with
  | RPub     => True
  | RPriv rs => ∀l, ⌜l ∈ rs⌝ → ∃ rs' Φ, keyT l (RPriv rs') Φ
  end.

Global Instance persistent_wf_readers rs :
  Persistent (wf_readers rs).
Proof. case: rs=> *; apply _. Qed.

Definition res_inv : iProp Σ :=
  ∃ RM, own res_name (● (to_resR RM))
        ∗ [∗ map] l ↦ r ∈ RM, l ↦ #() ∗ wf_readers (readers_of_res r).

(** [termT t rs] holds when the term [t] can be declared public after encrypting
it with any of the readers rs.  If [rs = RPub], [t] is considered public and
does not have to be encrypted. *)

Fixpoint termT t rs : iProp Σ :=
  match t with
  | TInt _ => True
  | TPair t1 t2 => termT t1 rs ∗ termT t2 rs
  | TNonce l => ∃ rs', nonceT l rs' ∗ ⌜rs ⊆ rs'⌝
  | TKey l   => ∃ rs' Φ, keyT l rs' Φ ∗ ⌜rs ⊆ rs'⌝
  | TEnc l t => ∃ rs' Φ, keyT l rs' Φ
                ∗ (□ Φ t ∗ termT t {[l]} ∨ ⌜rs' = RPub⌝ ∗ termT t RPub)
  end.

Global Instance persistent_termT t rs :
  Persistent (termT t rs).
Proof. elim: t rs=> *; apply _. Qed.

Lemma nonce_alloc l rs :
  res_inv -∗
  l ↦ #() -∗
  wf_readers rs -∗
  |==> res_inv ∗ nonceT l rs.
Proof.
iDestruct 1 as (RM) "[Hown Hreaders]".
iIntros "Hl Hrs".
destruct (RM !! l) as [rs'|] eqn:e.
  rewrite big_sepM_delete //.
  iDestruct "Hreaders" as "[[Hl' _] _]".
  by iPoseProof (mapsto_valid_2 with "Hl Hl'") as "%".
pose (RM' := <[l := RNonce rs]>RM).
iAssert ([∗ map] l' ↦ rs' ∈ RM', l' ↦ #() ∗ wf_readers (readers_of_res rs'))%I
    with "[Hreaders Hl Hrs]" as "Hreaders".
  by rewrite /RM' big_sepM_insert //; iFrame.
iMod (own_update _ _ (_ ⋅ ◯ {[l := to_agree (RNonce rs)]}) with "Hown")
    as "[Hown #Hfrag]".
  apply auth_update_alloc, alloc_singleton_local_update=> //.
  by rewrite lookup_fmap e.
iModIntro; iSplitL=> //.
iExists RM'; iFrame; by rewrite /RM' /to_resR fmap_insert.
Qed.

Lemma key_alloc l rs Φ :
  res_inv -∗
  l ↦ #() -∗
  wf_readers rs -∗
  |==> res_inv ∗ keyT l rs Φ.
Proof.
iDestruct 1 as (RM) "[Hown Hreaders]".
iIntros "Hl Hrs".
destruct (RM !! l) as [rs'|] eqn:e.
  rewrite big_sepM_delete //.
  iDestruct "Hreaders" as "[[Hl' _] _]".
  by iPoseProof (mapsto_valid_2 with "Hl Hl'") as "%".
pose (RM' := <[l := RKey rs Φ]>RM).
iAssert ([∗ map] l' ↦ rs' ∈ RM', l' ↦ #() ∗ wf_readers (readers_of_res rs'))%I
    with "[Hreaders Hl Hrs]" as "Hreaders".
  by rewrite /RM' big_sepM_insert //; iFrame.
iMod (own_update _ _ (_ ⋅ ◯ {[l := to_agree (RKey rs Φ)]}) with "Hown")
    as "[Hown #Hfrag]".
  apply auth_update_alloc, alloc_singleton_local_update=> //.
  by rewrite lookup_fmap e.
iModIntro; iSplitL=> //.
iExists RM'; iFrame; by rewrite /RM' /to_resR fmap_insert.
Qed.

End Resources.
