From stdpp Require Import coGset.
From stdpp Require Export sets coGset.
From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
Set Default Proof Using "Type".
(* Adapted from coPset_disj *)

(* The disjoiny union CMRA *)
Inductive coGset_disj A `{Countable A} :=
  | CoGset : coGset A → coGset_disj A
  | CoGsetBot : coGset_disj A.
Arguments coGset_disj _ {_ _} : assert.
Arguments CoGset {_ _ _} _.
Arguments CoGsetBot {_ _ _}.

Section coGset_disj.
  Context `{Countable A, Infinite A}.

  Arguments op _ _ !_ !_ /.
  Canonical Structure coGset_disjO := leibnizO (coGset_disj A).

  Instance coGset_disj_valid : Valid (coGset_disj A) := λ X,
    match X with CoGset _ => True | CoGsetBot => False end.
  Instance coGset_disj_unit : Unit (coGset_disj A) := CoGset ∅.
  Instance coGset_disj_op : Op (coGset_disj A) := λ X Y,
    match X, Y with
    | CoGset X, CoGset Y => if decide (X ## Y) then CoGset (X ∪ Y) else CoGsetBot
    | _, _ => CoGsetBot
    end.
  Instance coGset_disj_pcore : PCore (coGset_disj A) := λ _, Some ε.

  Ltac coGset_disj_solve :=
    repeat (simpl || case_decide);
    first [apply (f_equal CoGset)|done|exfalso]; set_solver by eauto.

  Lemma coGset_disj_included X Y : CoGset X ≼ CoGset Y ↔ X ⊆ Y.
  Proof.
    split.
    - move=> [[Z|]]; simpl; try case_decide; set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L.
      exists (CoGset Z). coGset_disj_solve.
  Qed.
  Lemma coGset_disj_valid_inv_l X Y :
    ✓ (CoGset X ⋅ Y) → ∃ Y', Y = CoGset Y' ∧ X ## Y'.
  Proof. destruct Y; repeat (simpl || case_decide); by eauto. Qed.
  Lemma coGset_disj_union X Y : X ## Y → CoGset X ⋅ CoGset Y = CoGset (X ∪ Y).
  Proof. intros. by rewrite /= decide_True. Qed.
  Lemma coGset_disj_valid_op X Y : ✓ (CoGset X ⋅ CoGset Y) ↔ X ## Y.
  Proof. simpl. case_decide; by split. Qed.

  Lemma coGset_disj_ra_mixin : RAMixin (coGset_disj A).
  Proof.
    apply ra_total_mixin; eauto.
    - intros [?|]; destruct 1; coGset_disj_solve.
    - by constructor.
    - by destruct 1.
    - intros [X1|] [X2|] [X3|]; coGset_disj_solve.
    - intros [X1|] [X2|]; coGset_disj_solve.
    - intros [X|]; coGset_disj_solve.
    - exists (CoGset ∅); coGset_disj_solve.
    - intros [X1|] [X2|]; coGset_disj_solve.
  Qed.
  Canonical Structure coGset_disjR := discreteR (coGset_disj A) coGset_disj_ra_mixin.

  Global Instance coGset_disj_cmra_discrete : CmraDiscrete coGset_disjR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma coGset_disj_ucmra_mixin : UcmraMixin (coGset_disj A).
  Proof. split; try apply _ || done. intros [X|]; coGset_disj_solve. Qed.
  Canonical Structure coGset_disjUR := UcmraT (coGset_disj A) coGset_disj_ucmra_mixin.
End coGset_disj.

Arguments coGset_disjUR A {_ _ _} : assert.
