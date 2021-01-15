From stdpp Require Import coGset.
From stdpp Require Export sets coGset.
From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates proofmode_classes.
Set Default Proof Using "Type".
(* Adapted from coPset *)

(* The union CMRA *)
Section coGset.
  Context `{Countable A}.

  Implicit Types X Y : coGset A.

  Canonical Structure coGsetO := discreteO (coGset A).

  Instance coGset_valid : Valid (coGset A) := λ _, True.
  Instance coGset_unit : Unit (coGset A) := (∅ : coGset A).
  Instance coGset_op : Op (coGset A) := union.
  Instance coGset_pcore : PCore (coGset A) := Some.

  Lemma coGset_op_union X Y : X ⋅ Y = X ∪ Y.
  Proof. done. Qed.
  Lemma coGset_core_self X : core X = X.
  Proof. done. Qed.
  Lemma coGset_included `{Infinite A} X Y : X ≼ Y ↔ X ⊆ Y.
  Proof.
    split.
    - intros [Z ->]. rewrite coGset_op_union. set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L. by exists Z.
  Qed.

  Lemma coGset_ra_mixin `{Infinite A} : RAMixin (coGset A).
  Proof.
    apply ra_total_mixin; eauto.
    - solve_proper.
    - solve_proper.
    - solve_proper.
    - intros X1 X2 X3. by rewrite !coGset_op_union assoc_L.
    - intros X1 X2. by rewrite !coGset_op_union comm_L.
    - intros X. by rewrite coGset_core_self idemp_L.
  Qed.
  Canonical Structure coGsetR `{Infinite A} := discreteR (coGset A) coGset_ra_mixin.

  Global Instance coGset_core_id `{Infinite A} X : CoreId X.
  Proof. by rewrite /CoreId. Qed.

  Global Instance coGset_cmra_discrete `{Infinite A} : CmraDiscrete coGsetR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma coGset_ucmra_mixin `{Infinite A} : UcmraMixin (coGset A).
  Proof. split. done. intros X. by rewrite coGset_op_union left_id_L. done. Qed.
  Canonical Structure coGsetUR `{Infinite A} := UcmraT (coGset A) coGset_ucmra_mixin.

  Lemma coGset_opM `{Infinite A} X mY : X ⋅? mY = X ∪ default ∅ mY.
  Proof. destruct mY; by rewrite /= ?right_id_L. Qed.

  Lemma coGset_update `{Infinite A} X Y : X ~~> Y.
  Proof. done. Qed.

  Lemma coGset_local_update `{Infinite A} X Y X' : X ⊆ X' → (X,Y) ~l~> (X',X').
  Proof.
    intros (Z&->&?)%subseteq_disjoint_union_L.
    rewrite local_update_unital_discrete=> Z' _ /leibniz_equiv_iff->.
    split. done. rewrite coGset_op_union. set_solver.
  Qed.
End coGset.

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

Record coGset_pair (A : Type) `{Countable A} := CoGsetPair {
  coGset_pair_set_proj : coGset A;
  coGset_pair_unset_proj : coGset_disj A
}.
Add Printing Constructor coGset_pair.
Arguments CoGsetPair {_ _ _} _ _.
Arguments coGset_pair_set_proj {_ _ _} _.
Arguments coGset_pair_unset_proj {_ _ _} _.
Instance: Params (@CoGsetPair) 1 := {}.
Instance: Params (@coGset_pair_set_proj) 1 := {}.
Instance: Params (@coGset_pair_unset_proj) 1 := {}.

Definition coGset_pair_set `{Countable A, Infinite A} (X : coGset A) : coGset_pair A :=
  CoGsetPair X ε.
Definition coGset_pair_unset `{Countable A, Infinite A} (X : coGset A) : coGset_pair A :=
  CoGsetPair ε (CoGset X).
Instance: Params (@coGset_pair_set) 2 := {}.

(* Ofe *)
Section ofe.
Context `{Countable A}.
Implicit Types x y : coGset_pair A.

Canonical coGset_pairO := leibnizO (coGset_pair A).

Global Instance CoGsetPair_discrete a b :
  Discrete (CoGsetPair a b).
Proof. by move. Qed.
Global Instance coGset_pair_ofe_discrete : OfeDiscrete coGset_pairO.
Proof. apply _. Qed.
End ofe.

Arguments coGset_pairO : clear implicits.

(* Camera *)
Section cmra.
Context `{Countable A}.
Implicit Types a b : A.
Implicit Types x y : coGset_pair A.

Instance coGset_pair_valid `{Infinite A} : Valid (coGset_pair A) := λ x,
  match coGset_pair_unset_proj x with
  | CoGset E => E ## coGset_pair_set_proj x
  | CoGsetBot => False
  end.
Global Arguments coGset_pair_valid !_ /.
Instance coGset_pair_validN : ValidN (coGset_pair A) := λ n x,
  match coGset_pair_unset_proj x with
  | CoGset E => E ## coGset_pair_set_proj x
  | CoGsetBot => False
  end.
Global Arguments coGset_pair_validN !_ /.
Instance coGset_pair_pcore `{Infinite A} : PCore (coGset_pair A) := λ x,
  Some (CoGsetPair (coGset_pair_set_proj x) ε).
Instance coGset_pair_op `{Infinite A} : Op (coGset_pair A) := λ x y,
  CoGsetPair (coGset_pair_set_proj x ⋅ coGset_pair_set_proj y)
               (coGset_pair_unset_proj x ⋅ coGset_pair_unset_proj y).

Definition coGset_pair_valid_eq :
  valid = λ x, match coGset_pair_unset_proj x with
               | CoGset E => E ## coGset_pair_set_proj x
               | CoGsetBot => False
               end := eq_refl _.
Definition coGset_pair_validN_eq :
  validN = λ n x, match coGset_pair_unset_proj x with
                  | CoGset E => E ## coGset_pair_set_proj x
                  | CoGsetBot => False
                  end := eq_refl _.

Lemma coGset_pair_included `{Infinite A} x y :
  x ≼ y ↔
    coGset_pair_set_proj x ≼ coGset_pair_set_proj y ∧
    coGset_pair_unset_proj x ≼ coGset_pair_unset_proj y.
Proof.
split.
- intros [[z1 z2] Hz].
  by split; [exists z1|exists z2]; rewrite (leibniz_equiv _ _ Hz).
- destruct x as [x1 x2], y as [y1 y2]. simpl in *.
  intros [[z1 Hz1] [z2 Hz2]]; exists (CoGsetPair z1 z2).
  by rewrite (leibniz_equiv _ _ Hz1) (leibniz_equiv _ _ Hz2).
Qed.

Lemma coGset_pair_set_proj_validN `{Infinite A} n x : ✓{n} coGset_pair_set_proj x.
Proof. by destruct x as [? [?|]]=> // -[??]. Qed.
Lemma coGset_pair_unset_proj_validN `{Infinite A} n x : ✓{n} x → ✓{n} coGset_pair_unset_proj x.
Proof. by destruct x as [? [?|]]=> // -[??]. Qed.

Lemma coGset_pair_cmra_mixin `{Infinite A} : CmraMixin (coGset_pair A).
Proof.
  apply cmra_total_mixin.
  - eauto.
  - by intros n x y1 y2 ->; split; simpl; rewrite ?Hy ?Hy'.
  - solve_proper.
  - move=> n [m1 [E1|]] [m2 [E2|]] [Hm ?] // ?.
    by simplify_eq.
  - intros [m [E|]]; rewrite coGset_pair_valid_eq coGset_pair_validN_eq /=
      ?cmra_valid_validN; naive_solver eauto using O.
  - intros n [m [E|]]; rewrite coGset_pair_validN_eq /=;
      naive_solver eauto using cmra_validN_S.
  - move=> ??? /=; congr CoGsetPair => /=; apply: assoc.
  - move=> ?? /=; congr CoGsetPair => /=; apply: comm.
  - case=> [x1 x2] /=; congr CoGsetPair => //=.
    + set_solver.
    + by rewrite ucmra_unit_left_id.
  - by [].
  - case=> [x1 x2] [y1 y2] [[z1 z2] [e1 e2]].
    exists (CoGsetPair z1 ε); congr CoGsetPair => //=.
    by rewrite ucmra_unit_left_id.
  - move=> n [x1 [x2|]] [y1 [y2|]] //=.
    rewrite coGset_pair_validN_eq /=.
    rewrite {1}/op /cmra_op /=.
    case: decide => //. set_solver.
  - move=> n [x1 x2] [y11 y12] [y21 y22] xP [e1 e2]; simpl in *.
    subst x1 x2.
    exists (CoGsetPair y11 y12), (CoGsetPair y21 y22).
    by split => //.
Qed.
Canonical Structure coGset_pairR `{Infinite A} :=
  CmraT (coGset_pair A) coGset_pair_cmra_mixin.

Global Instance coGset_pair_cmra_discrete `{Infinite A} :
  CmraDiscrete coGset_pairR.
Proof.
  split; first apply _.
  intros [m [E|]]; rewrite coGset_pair_validN_eq coGset_pair_valid_eq //=.
Qed.

Instance coGset_pair_empty `{Infinite A} : Unit (coGset_pair A) := CoGsetPair ε ε.
Lemma coGset_pair_ucmra_mixin `{Infinite A} : UcmraMixin (coGset_pair A).
Proof.
  split; simpl => //.
  move=> [x1 x2]; congr CoGsetPair => /=.
  + set_solver.
  + by rewrite ucmra_unit_left_id.
Qed.
Canonical Structure coGset_pairUR `{Infinite A} :=
  UcmraT (coGset_pair A) coGset_pair_ucmra_mixin.

Global Instance coGset_pair_set_core_id `{Infinite A} X :
  CoreId (coGset_pair_set X).
Proof. rewrite /CoreId; reflexivity. Qed.

Lemma coGset_pair_set_valid `{Infinite A} X : ✓ (coGset_pair_set X).
Proof. rewrite coGset_pair_valid_eq /=. set_solver. Qed.
Lemma coGset_pair_unset_valid `{Infinite A} E : ✓ (coGset_pair_unset E).
Proof. rewrite coGset_pair_valid_eq /=. set_solver. Qed.
Lemma coGset_pair_set_op `{Infinite A} X Y :
  coGset_pair_set (X ⋅ Y) = coGset_pair_set X ⋅ coGset_pair_set Y.
Proof.
by congr CoGsetPair; rewrite /= ucmra_unit_left_id.
Qed.
Lemma coGset_pair_set_included `{Infinite A} X Y :
  coGset_pair_set X ≼ coGset_pair_set Y ↔ X ⊆ Y.
Proof.
split.
- case => [[Z1 Z2] [-> _]]; set_solver.
- case/coGset_included=> Z e; exists (CoGsetPair Z ε).
  rewrite (leibniz_equiv _ _ e).
  congr CoGsetPair => //=.
  by rewrite ucmra_unit_left_id.
Qed.
Global Instance is_op_coGset_pair_set `{Infinite A} X Y1 Y2 :
  IsOp X Y1 Y2 →
  IsOp' (coGset_pair_set X) (coGset_pair_set Y1) (coGset_pair_set Y2).
Proof.
rewrite /IsOp' /IsOp => e.
rewrite (leibniz_equiv _ _ e).
by rewrite coGset_pair_set_op. Qed.

Lemma coGset_pair_unset_union `{Infinite A} E1 E2 :
  E1 ## E2 →
  coGset_pair_unset (E1 ∪ E2) = coGset_pair_unset E1 ⋅ coGset_pair_unset E2.
Proof.
  intros.
  congr CoGsetPair => /=; first set_solver.
  by rewrite coGset_disj_union.
Qed.
Lemma coGset_pair_unset_difference `{Infinite A} E1 E2 :
  E1 ⊆ E2 →
   coGset_pair_unset E2 = coGset_pair_unset E1 ⋅ coGset_pair_unset (E2 ∖ E1).
Proof.
  intros. rewrite -coGset_pair_unset_union; last set_solver.
  by rewrite -union_difference_L.
Qed.
Lemma coGset_pair_unset_valid_op `{Infinite A} E1 E2 :
  ✓ (coGset_pair_unset E1 ⋅ coGset_pair_unset E2) ↔ E1 ## E2.
Proof.
  rewrite coGset_pair_valid_eq /= {1}/op /cmra_op /=. case_decide; last done.
  split; [done|]; intros _. set_solver.
Qed.

Lemma coGset_pair_alloc_update `{Infinite A} X :
  coGset_pair_unset X ~~> coGset_pair_set X.
Proof.
move=> n [[Y1 [Y2|]]|] //=.
rewrite coGset_pair_validN_eq /=.
rewrite [ε ⋅ CoGset Y2]ucmra_unit_left_id.
rewrite {1}/op /cmra_op /=.
case: decide => //. set_solver.
Qed.

Lemma coGset_pair_local_update `{Infinite A} X Y Z :
  (coGset_pair_unset X ⋅ coGset_pair_set Y, coGset_pair_unset Z) ~l~>
  (coGset_pair_unset (X ∖ Z) ⋅ coGset_pair_set (Y ∪ Z), coGset_pair_set Z).
Proof.
move=> n [[W1 W2]|] /=.
- rewrite coGset_pair_validN_eq /= right_id left_id => disj.
  case; rewrite !left_id_L !right_id => <-.
  case: W2 => [W2|//] e.
  split; first set_solver.
  congr CoGsetPair => /=; first set_solver.
  assert (Z ## W2). by apply coGset_disj_valid_op; rewrite -e.
  move: e; rewrite coGset_disj_union //; case=> e; subst X.
  rewrite left_id right_id; congr CoGset.
  set_solver.
- rewrite coGset_pair_validN_eq /= right_id left_id => disj.
  case; rewrite !left_id_L !right_id => -> [<-].
  split; first set_solver.
  congr CoGsetPair => /=; first set_solver.
  by rewrite difference_diag_L right_id.
Qed.

End cmra.


Arguments coGset_pairR A {_ _ _}.
Arguments coGset_pairUR A {_ _ _}.
