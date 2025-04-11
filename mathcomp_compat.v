(** We define these instances in their own file to avoid conflicts between
mathcomp and stdpp definitions. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From deriving Require Import deriving.
From stdpp Require base countable.
From Stdlib Require Import ZArith.ZArith Lia Permutation.
From iris.heap_lang Require locations.

(* FIXME: This should exist in deriving *)
Definition positive_isOrder := [derive isOrder for positive].
HB.instance Definition _ := positive_isOrder.

Lemma Z_leb_anti : antisymmetric Z.leb.
Proof.
move=> ?? /andP [] /Z.leb_spec0 ? /Z.leb_spec0 ?; lia.
Qed.

Lemma Z_leb_trans : transitive Z.leb.
Proof.
move=> ??? /Z.leb_spec0 ? /Z.leb_spec0 ?.
apply/Z.leb_spec0; lia.
Qed.

Lemma Z_leb_total : total Z.leb.
Proof.
move=> ??; apply/orP.
rewrite /is_true !Z.leb_le; lia.
Qed.

Definition Z_isOrder :=
  @Order.isOrder.Build Order.default_display Z Z.leb _ _ _
    (fun _ _ => erefl) (fun _ _ => erefl) (fun _ _ => erefl)
    Z_leb_anti Z_leb_trans Z_leb_total.
HB.instance Definition _ := Z_isOrder.

HB.instance Definition _ := [isNew for locations.loc_car].
HB.instance Definition _ := [Equality of locations.loc by <:].
HB.instance Definition _ := [Choice of locations.loc by <:].
HB.instance Definition _ := [Countable of locations.loc by <:].
HB.instance Definition _ := [Order of locations.loc by <:].

Definition def_eq_decision (T : eqType) : base.RelDecision (@eq T) :=
  fun x y =>
    match x == y as b return (x == y) = b -> {x = y} + {x <> y} with
    | true  => fun H => left  (elimT (x =P y) H)
    | false => fun H => right (elimF (x =P y) H)
    end erefl.

Definition def_countable (T : countType) (H : base.RelDecision (@eq T)) : countable.Countable T.
Proof.
apply:
  (@countable.inj_countable _ _ countable.nat_countable T H pickle unpickle).
exact: pickleK.
Qed.

Lemma perm_Perm {T : eqType} {s1 s2 : seq T} :
  reflect (Permutation s1 s2) (perm_eq s1 s2).
Proof.
apply/(iffP idP).
  rewrite perm_sym; elim: s1 s2 => [_ /perm_nilP -> //|x s1 IH] s2 ps1s2.
  have x_s2 : x \in s2 by rewrite (perm_mem ps1s2) inE eqxx.
  case/path.splitP: x_s2 ps1s2 => s21 s22 ps1s2.
  have {}ps1s2: perm_eq (s21 ++ s22) s1.
    by move: ps1s2; rewrite -cats1 perm_catAC perm_catC /= perm_cons.
  rewrite -cats1 -catA /=.
  by apply: Permutation_cons_app; apply: IH.
elim: s1 s2 / => //.
- by move=> x s1 s2 _ IH; rewrite perm_cons.
- move=> x1 x2 s.
  rewrite (perm_cat2r s [:: x2; x1] [:: x1; x2]) /=.
  by rewrite -cat1s -[[:: x1; x2]]cat1s perm_catC.
- by move=> ? ? ? _ ? _; apply: seq.perm_trans.
Qed.

Lemma perm_sort_leP d (T : orderType d) (s1 s2 : seq T) :
  reflect (sort <=%O s1 = sort <=%O s2) (perm_eq s1 s2).
Proof.
apply/perm_sortP.
- exact: Order.TotalTheory.le_total.
- exact: Order.POrderTheory.le_trans.
- exact: Order.POrderTheory.le_anti.
Qed.

Lemma is_trueP (b : bool) : is_true b <-> Stdlib.Bool.Bool.Is_true b.
Proof. by case: b => /=; split. Qed.

Lemma foldr_in (T : eqType) (S : T -> Type) xs :
  foldr (fun x R => S x * R)%type unit xs -> forall x, x \in xs -> S x.
Proof.
elim: xs => [//|x xs IH] /= [] Sx Sxs x'; rewrite inE.
case: eqP => [-> _|_] //=; exact: IH.
Qed.
