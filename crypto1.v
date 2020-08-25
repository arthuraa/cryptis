From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import term.

Inductive readers :=
| RPub
| RPriv of gset loc.

Canonical readersO := leibnizO readers.

Instance readers_valid : Valid readers := λ _, True.
Instance readers_validN : ValidN readers := λ _ _, True.
Instance readers_pcore : PCore readers := λ x, Some x.
Instance readers_op : Op readers := λ rs1 rs2,
  match rs1, rs2 with
  | RPriv rs1, RPriv rs2 => RPriv (rs1 ∪ rs2)
  | _, _ => RPub
  end.

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
Implicit Types P : agree (termO -n> iPropO Σ).

Inductive res :=
| RNonce of readers
| RKey of agree (termO -n> iPropO Σ)
| RBot.

Global Instance res_equiv : Equiv res := λ r1 r2,
  match r1, r2 with
  | RNonce rs1, RNonce rs2 => rs1 = rs2
  | RKey P1, RKey P2 => P1 ≡ P2
  | RBot, RBot => True
  | _, _ => False
  end.

Global Instance res_dist : Dist res := λ n r1 r2,
  match r1, r2 with
  | RNonce rs1, RNonce rs2 => rs1 = rs2
  | RKey P1, RKey P2 => P1 ≡{n}≡ P2
  | RBot, RBot => True
  | _, _ => False
  end.

Lemma res_ofe_mixin : OfeMixin res.
Proof.
split.
- move=> r1 r2; case: r1=> *; case: r2=> *;
  split=> //; by move/(_ 0).
- move=> n; split.
  + case=> * //=; by apply equiv_dist.
  + case=> [?|?|] [?|?|] // e.
    by rewrite /dist /=.
  + case=> [?|?|] [?|?|] // [?|?|] //.
      by move=> ->.
    by rewrite /dist /= => ->.
- rewrite /dist => n [?|?|] [?|?|] //=.
  exact: dist_S.
Qed.
Canonical resO := OfeT res res_ofe_mixin.

(* NB: [res] is probably not complete because [agree _] is not complete in
general. *)

Global Instance res_valid : Valid res := λ r,
  match r with
  | RNonce _ => True
  | RKey P => ✓ P
  | RBot => False
  end.
Global Instance res_validN : ValidN res := λ n r,
  match r with
  | RNonce _ => True
  | RKey P => ✓{n} P
  | RBot => False
  end.
Global Instance res_pcore : PCore res := Some.
Global Instance res_op : Op res := λ r1 r2,
  match r1, r2 with
  | RNonce rs1, RNonce rs2 => RNonce (rs1 ⋅ rs2)
  | RKey P1, RKey P2 => RKey (P1 ⋅ P2)
  | _, _ => RBot
  end.

Lemma res_cmra_mixin : CmraMixin res.
Proof.
split.
- case=> [rs1|P1|] n [?|?|] [?|?|] //;
  by rewrite /dist /=; move=> ->.
- move=> n x y _ exy [<-]; by exists y.
- move=> n [?|?|] [?|?|] //.
  by rewrite /dist /= /validN /= => ->.
- case=> *; rewrite /valid /validN /=; try by intuition eauto.
  split=> //; apply; exact: 0.
- move=> n [?|?|] //; rewrite /validN //=; apply cmra_validN_S.
- by case=> [?|?|] [?|?|] [?|?|] //; rewrite /= /op /equiv /= assoc.
- by case=> [?|?|] [?|?|]; rewrite // /op /equiv /= cmra_comm.
- move=> r _ [<-]; case: r=> [rs|P|]; rewrite // /op /=.
  + by apply: (cmra_pcore_l rs rs).
  + by apply: (cmra_pcore_l P P).
- by move=> ? _ [<-].
- by move=> r1 r2 _ r12 [<-]; exists r2; split.
- by move=> n [rs1|P1|] [rs2|P2|] // /cmra_validN_op_l.
- move=> n [rs1|P1|] // [rs21|P21|] [rs22|P22|] //.
  + by move=> _ e; exists (RNonce rs21), (RNonce rs22); intuition.
  + move=> P1val e; rewrite /validN /dist /= in P1val e.
    destruct (cmra_extend _ _ _ _ P1val e) as (P21' & P22' & ? & ? & ?).
    by exists (RKey P21'), (RKey P22'); intuition eauto.
Qed.
Canonical resR := CmraT res res_cmra_mixin.

End Resources.
