(** Signed multisets over a type [T] ordered by a [Lexico] instance.

    [sms T] is the free abelian group on [T]: [∅] is its unit, [⊎] its
    operation, [inv] its inverse and [{[+ x +]}] its generators.  [count x s]
    is the signed multiplicity of [x] in [s], and equality is Leibniz
    ([count_inj]).  [make X Y] has the positive occurrences [X] and the negative
    ones [Y]; [bind] substitutes signed multisets for elements.

    [Internal] holds the representation: pairs of lists [A], with the positive
    occurrences in [A.1] and the negative ones in [A.2], so that

        count x A = count_mem x A.1 - count_mem x A.2   (in Z).

    Negating swaps the sides ([swap]), so no element needs an inverse and
    nothing is assumed of [T] beyond a total order [R].  A pair is well-formed
    ([wf]) when both sides are sorted and disjoint.  [to] cancels common
    occurrences and sorts both sides; it is the canonical form:

      (1) [wf (to A)];
      (2) [to A = to B <-> forall z, count z A = count z B].

    [sms T] sorts by [le], the reflexive closure of [lexico]. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import sorting list numbers proof_irrel.
From Stdlib Require Import ZArith Lia.
From cryptis.lib Require Import list_sort.

Module SMS.

Module Internal.

Section SignedMultiset.

Context {T : Type} `{EqDecision T}.
Context (R : relation T)
  `{!RelDecision R, !Transitive R, !Total R, !AntiSymm (=@{T}) R}.

Implicit Types (x y z : T) (X Y : list T) (A B : list T * list T).

(** ** Definitions *)

Definition count x A : Z :=
  (Z.of_nat (count_mem x A.1) - Z.of_nat (count_mem x A.2))%Z.

Definition wf A : bool :=
  bool_decide (StronglySorted R A.1) && bool_decide (StronglySorted R A.2)
  && bool_decide (A.1 ## A.2).

Definition swap A := (A.2, A.1).

Definition app A B := (A.1 ++ B.1, A.2 ++ B.2).

Definition elements A := A.1 ++ A.2.

Definition cancel_step x A :=
  if bool_decide (x ∈ A.2) then (A.1, rem x A.2) else (x :: A.1, A.2).

Definition cancel A := foldr cancel_step ([], A.2) A.1.

Arguments cancel : simpl never.

Definition to A := (merge_sort R (cancel A).1, merge_sort R (cancel A).2).

(** ** Signed counts *)

Lemma count_perm z A B : A.1 ≡ₚ B.1 → A.2 ≡ₚ B.2 → count z A = count z B.
Proof.
move=> e1 e2; rewrite /count.
by rewrite (count_mem_Permutation z _ _ e1) (count_mem_Permutation z _ _ e2).
Qed.

Lemma count_cons1 z x X Y :
  count z (x :: X, Y) = (count z (X, Y) + Z.b2z (bool_decide (z = x)))%Z.
Proof. rewrite /count /=; case_bool_decide; simpl; lia. Qed.

Lemma count_cons2 z x X Y :
  count z (X, x :: Y) = (count z (X, Y) - Z.b2z (bool_decide (z = x)))%Z.
Proof. rewrite /count /=; case_bool_decide; simpl; lia. Qed.

Lemma count_app z A B : count z (app A B) = (count z A + count z B)%Z.
Proof. rewrite /count /= !count_mem_app; lia. Qed.

Lemma count_swap z A : count z (swap A) = (- count z A)%Z.
Proof. rewrite /count /=; lia. Qed.

Lemma not_elem_of_count x A : x ∉ A.1 → x ∉ A.2 → count x A = 0%Z.
Proof. by rewrite !not_elem_of_count_mem /count => -> ->. Qed.

Lemma not_elem_of_count1 x A : x ∉ A.1 → (count x A ≤ 0)%Z.
Proof. rewrite not_elem_of_count_mem /count => ->; lia. Qed.

Lemma not_elem_of_count2 x A : x ∉ A.2 → (0 ≤ count x A)%Z.
Proof. rewrite not_elem_of_count_mem /count => ->; lia. Qed.

Lemma count_count_mem x A : x ∉ A.2 → count x A = Z.of_nat (count_mem x A.1).
Proof. rewrite not_elem_of_count_mem /count => ->; lia. Qed.

Lemma count_eq0_elem_of x A : count x A = 0%Z → x ∈ A.1 ↔ x ∈ A.2.
Proof.
rewrite /count => e0; have e : count_mem x A.1 = count_mem x A.2 by lia.
by rewrite !elem_of_count_mem e.
Qed.

Lemma count_mem_disjoint z A :
  A.1 ## A.2 →
  Z.of_nat (count_mem z A.1) = Z.max 0 (count z A) ∧
  Z.of_nat (count_mem z A.2) = Z.max 0 (- count z A).
Proof.
move=> dA; rewrite /count.
case: (decide (z ∈ A.1)) => zA.
- rewrite (proj1 (not_elem_of_count_mem z A.2) (dA z zA)); lia.
- rewrite (proj1 (not_elem_of_count_mem z A.1) zA); lia.
Qed.

(** ** Cancellation *)

Lemma cancel_nil Y : cancel ([], Y) = ([], Y).
Proof. reflexivity. Qed.

Lemma cancel_cons x X Y : cancel (x :: X, Y) = cancel_step x (cancel (X, Y)).
Proof. reflexivity. Qed.

Lemma count_cancel_step z x A :
  count z (cancel_step x A) = (count z A + Z.b2z (bool_decide (z = x)))%Z.
Proof.
case: A => X Y; rewrite /cancel_step /=.
case: (decide (x ∈ Y)) => xY.
- have Hx : count_mem x Y ≠ 0 by apply/elem_of_count_mem.
  rewrite (bool_decide_eq_true_2 _ xY) /count /= count_mem_rem.
  case_bool_decide as zx; [subst z|]; simpl; lia.
- by rewrite (bool_decide_eq_false_2 _ xY) count_cons1.
Qed.

Lemma count_cancel z A : count z (cancel A) = count z A.
Proof.
case: A => X Y; elim: X => [//|x X IH].
by rewrite cancel_cons count_cancel_step IH count_cons1.
Qed.

Lemma elem_of_cancel z A :
  (z ∈ (cancel A).1 → z ∈ A.1) ∧ (z ∈ (cancel A).2 → z ∈ A.2).
Proof.
case: A => X Y; elim: X => [|x X [IH1 IH2]]; first by rewrite cancel_nil.
rewrite cancel_cons /cancel_step.
case: (cancel (X, Y)) IH1 IH2 => C1 C2 /= IH1 IH2.
case_bool_decide as xC => /=; split.
- by move=> /IH1 ?; apply/elem_of_cons; right.
- by move=> /elem_of_rem /IH2.
- by rewrite elem_of_cons => -[->|/IH1 ?]; apply/elem_of_cons; [left|right].
- exact: IH2.
Qed.

Lemma cancel_disjoint A : (cancel A).1 ## (cancel A).2.
Proof.
case: A => X Y; elim: X => [|x X IH].
  by rewrite cancel_nil /= => ? /elem_of_nil.
rewrite cancel_cons /cancel_step.
case: (cancel (X, Y)) IH => C1 C2 /= IH.
case_bool_decide as xC => y /=.
- by move=> /IH yC /elem_of_rem.
- by rewrite elem_of_cons => -[->|/IH].
Qed.

Lemma cancel_id A : A.1 ## A.2 → cancel A = A.
Proof.
case: A => X Y /=; elim: X => [//|x X IH] dXY.
rewrite cancel_cons IH /cancel_step /=.
- by move=> y yX; apply: dXY; apply/elem_of_cons; right.
- by rewrite bool_decide_eq_false_2 //; apply: dXY; apply/elem_of_cons; left.
Qed.

(** ** Well-formedness *)

Lemma wf_sorted A : wf A → StronglySorted R A.1 ∧ StronglySorted R A.2.
Proof.
by case/andb_True=> /andb_True [/bool_decide_unpack ? /bool_decide_unpack ?] _.
Qed.

Lemma wf_disjoint A : wf A → A.1 ## A.2.
Proof. by case/andb_True=> _ /bool_decide_unpack. Qed.

Lemma wf_intro A :
  StronglySorted R A.1 → StronglySorted R A.2 → A.1 ## A.2 → wf A.
Proof.
move=> s1 s2 d; apply/andb_True; split; last exact: bool_decide_pack.
by apply/andb_True; split; exact: bool_decide_pack.
Qed.

Lemma wf_nil : wf ([], []).
Proof. apply: wf_intro; [constructor|constructor|by move=> ? /elem_of_nil]. Qed.

Lemma wf_singleton1 x : wf ([x], []).
Proof.
apply: wf_intro; [by repeat constructor|constructor|by move=> ? _ /elem_of_nil].
Qed.

Lemma wf_singleton2 x : wf ([], [x]).
Proof.
apply: wf_intro; [constructor|by repeat constructor|by move=> ? /elem_of_nil].
Qed.

Lemma wf_swap A : wf A → wf (swap A).
Proof.
move=> wfA; have [s1 s2] := wf_sorted A wfA.
apply: wf_intro => // x x2 x1; exact: wf_disjoint A wfA x x1 x2.
Qed.

Lemma wf_count_gt0 x A : wf A → (count x A > 0)%Z ↔ x ∈ A.1.
Proof.
move=> /wf_disjoint /(count_mem_disjoint x) [e1 _].
rewrite elem_of_count_mem; lia.
Qed.

Lemma wf_count_lt0 x A : wf A → (count x A < 0)%Z ↔ x ∈ A.2.
Proof.
move=> /wf_disjoint /(count_mem_disjoint x) [_ e2].
rewrite elem_of_count_mem; lia.
Qed.

(** ** Canonical forms *)

Lemma wf_count_inj A B :
  wf A → wf B → (∀ z, count z A = count z B) → A = B.
Proof.
move=> wfA wfB e.
have [sA1 sA2] := wf_sorted A wfA; have [sB1 sB2] := wf_sorted B wfB.
have dA := wf_disjoint A wfA; have dB := wf_disjoint B wfB.
have e1 : A.1 = B.1.
  apply: (StronglySorted_unique R) => //; apply: Permutation_count_mem => z.
  apply: Nat2Z.inj.
  by rewrite (proj1 (count_mem_disjoint z A dA))
             (proj1 (count_mem_disjoint z B dB)) e.
have e2 : A.2 = B.2.
  apply: (StronglySorted_unique R) => //; apply: Permutation_count_mem => z.
  apply: Nat2Z.inj.
  by rewrite (proj2 (count_mem_disjoint z A dA))
             (proj2 (count_mem_disjoint z B dB)) e.
by rewrite (surjective_pairing A) (surjective_pairing B) e1 e2.
Qed.

Lemma wf_to A : wf (to A).
Proof.
apply: wf_intro; rewrite /to /=; try exact: merge_sort_sorted.
move=> x; rewrite !elem_of_merge_sort; exact: cancel_disjoint.
Qed.

Lemma count_to z A : count z (to A) = count z A.
Proof.
rewrite -(count_cancel z A); apply: count_perm; exact: merge_sort_Permutation.
Qed.

Lemma to_id A : wf A → to A = A.
Proof.
move=> wfA; have [s1 s2] := wf_sorted A wfA.
rewrite /to (cancel_id A (wf_disjoint A wfA)) !merge_sort_id //.
by rewrite -surjective_pairing.
Qed.

Lemma to_eq A B : to A = to B ↔ ∀ z, count z A = count z B.
Proof.
split=> [e z|e]; first by rewrite -(count_to z A) -(count_to z B) e.
apply: wf_count_inj; [exact: wf_to|exact: wf_to|] => z.
by rewrite !count_to.
Qed.

Lemma count_to_eq A B :
  (∀ x, x ∈ A.1 ++ A.2 ++ B.1 ++ B.2 → count x A = count x B) →
  to A = to B.
Proof.
move=> e; apply/to_eq => z.
case: (decide (z ∈ A.1 ++ A.2 ++ B.1 ++ B.2)) => [/e //|].
rewrite !elem_of_app => zN.
rewrite !not_elem_of_count //; tauto.
Qed.

Lemma elem_of_to1 z A : z ∈ (to A).1 → z ∈ A.1.
Proof.
rewrite /to /= elem_of_merge_sort; exact: (proj1 (elem_of_cancel z A)).
Qed.

Lemma elem_of_to2 z A : z ∈ (to A).2 → z ∈ A.2.
Proof.
rewrite /to /= elem_of_merge_sort; exact: (proj2 (elem_of_cancel z A)).
Qed.

Lemma to_disjoint A :
  A.1 ## A.2 → to A = (merge_sort R A.1, merge_sort R A.2).
Proof. by move=> dA; rewrite /to cancel_id. Qed.

Lemma to_pos X : to (X, []) = (merge_sort R X, []).
Proof. by rewrite to_disjoint //= => ?? /elem_of_nil. Qed.

Lemma to_swap A : to (swap A) = swap (to A).
Proof.
apply: wf_count_inj; [exact: wf_to|apply: wf_swap; exact: wf_to|] => z.
by rewrite count_to !count_swap count_to.
Qed.

(** ** Elements *)

Lemma count_elements x A : x ∉ elements A → count x A = 0%Z.
Proof.
rewrite /elements elem_of_app => /Decidable.not_or [x1 x2].
exact: not_elem_of_count.
Qed.

Lemma wf_elem_of_elements x A : wf A → x ∈ elements A ↔ count x A ≠ 0%Z.
Proof.
move=> wfA; rewrite /elements elem_of_app -(wf_count_gt0 x A wfA).
rewrite -(wf_count_lt0 x A wfA); lia.
Qed.

Lemma wf_count_mem_elements x A :
  wf A → Z.of_nat (count_mem x (elements A)) = Z.abs (count x A).
Proof.
move=> /wf_disjoint /(count_mem_disjoint x) [e1 e2].
rewrite /elements count_mem_app Nat2Z.inj_add e1 e2; lia.
Qed.

Lemma elements_swap A : elements (swap A) ≡ₚ elements A.
Proof. exact: Permutation_app_comm. Qed.

Lemma elem_of_elements_to x A : x ∈ elements (to A) → x ∈ elements A.
Proof.
rewrite /elements !elem_of_app => -[/elem_of_to1 ?|/elem_of_to2 ?].
all: by [left|right].
Qed.

End SignedMultiset.

(** ** Mapping

    No injectivity is needed: cancelling [x] against [x] cancels [f x] against
    [f x]. *)

Definition smap {T U} (f : T → U) (A : list T * list T) :=
  (f <$> A.1, f <$> A.2).

Lemma elements_smap {T U} (f : T → U) A :
  elements (smap f A) = f <$> elements A.
Proof. by rewrite /elements /smap /= fmap_app. Qed.

Lemma smap_ext {T U} (f g : T → U) A :
  (∀ x, x ∈ elements A → f x = g x) → smap f A = smap g A.
Proof.
case: A => X Y; rewrite /elements /smap /= => H.
congr pair; apply/Forall_fmap_ext/list.Forall_forall => x x_in; apply: H;
  rewrite elem_of_app; by [left|right].
Qed.

Lemma smap_id {T} (f : T → T) (A : list T * list T) :
  (∀ x, x ∈ elements A → f x = x) → smap f A = A.
Proof.
case: A => X Y; rewrite /elements /smap /= => H.
congr pair; rewrite -[RHS]list_fmap_id; apply/Forall_fmap_ext/list.Forall_forall
  => x x_in; apply: H; rewrite elem_of_app; by [left|right].
Qed.

Lemma count_smap_cancel_step {T U} `{EqDecision T} `{EqDecision U}
    (f : T → U) z x A :
  count z (smap f (cancel_step x A)) =
  (count z (smap f A) + Z.b2z (bool_decide (z = f x)))%Z.
Proof.
case: A => X Y; rewrite /cancel_step /=.
case: (decide (x ∈ Y)) => xY.
- have e : f <$> Y ≡ₚ f x :: (f <$> rem x Y).
    by rewrite -fmap_cons; apply: fmap_Permutation; exact: rem_Permutation.
  rewrite (bool_decide_eq_true_2 _ xY) /smap /count /=.
  rewrite (count_mem_Permutation z _ _ e) /=.
  case_bool_decide; simpl; lia.
- rewrite (bool_decide_eq_false_2 _ xY) /smap; cbn [fst snd].
  by rewrite fmap_cons count_cons1.
Qed.

Lemma count_smap_cancel {T U} `{EqDecision T} `{EqDecision U}
    (f : T → U) z A :
  count z (smap f (cancel A)) = count z (smap f A).
Proof.
case: A => X Y; elim: X => [//|x X IH].
rewrite cancel_cons count_smap_cancel_step IH /smap; cbn [fst snd].
by rewrite fmap_cons count_cons1.
Qed.

Lemma count_smap_to {T U} `{EqDecision T} `{EqDecision U}
    (R : relation T) `{!RelDecision R} (f : T → U) z A :
  count z (smap f (to R A)) = count z (smap f A).
Proof.
rewrite -(count_smap_cancel f z A); apply: count_perm => /=;
  apply: fmap_Permutation; exact: merge_sort_Permutation.
Qed.

Lemma smap_smap {T U V} (f : T → U) (g : U → V) A :
  smap g (smap f A) = smap (λ x, g (f x)) A.
Proof. by rewrite /smap /= -!list_fmap_compose. Qed.

Lemma wf_smap {T U} `{EqDecision T, EqDecision U}
    (R : relation T) (S : relation U) `{!RelDecision R, !RelDecision S}
    (f : T → U) A :
  (∀ a b, f a = f b → a = b) → (∀ x y, R x y ↔ S (f x) (f y)) →
  wf S (smap f A) ↔ wf R A.
Proof.
move=> finj fRS.
have sorted (l : list T) : StronglySorted S (f <$> l) ↔ StronglySorted R l.
  elim: l => [|x l IH] /=; first by split=> _; constructor.
  split=> H; case: (StronglySorted_inv H) => H1 H2; constructor;
    try by apply/IH.
  - by move/Forall_fmap: H2; apply: Forall_impl => y /fRS.
  - by apply/Forall_fmap; apply: Forall_impl H2 => y /fRS.
have mem x (l : list T) : f x ∈ f <$> l ↔ x ∈ l.
  split; last exact: list_elem_of_fmap_2.
  by move=> /list_elem_of_fmap [y [/finj -> ?]].
split=> wfA.
- have [s1 s2] := wf_sorted S _ wfA.
  apply: wf_intro; [by apply/sorted|by apply/sorted|].
  move=> x x1 x2; apply: (wf_disjoint S _ wfA (f x)); rewrite /smap /= mem //.
- have [s1 s2] := wf_sorted R _ wfA.
  apply: wf_intro; [by apply/sorted|by apply/sorted|].
  move=> _ /list_elem_of_fmap [x [-> x1]] /mem x2.
  exact: (wf_disjoint R _ wfA x x1 x2).
Qed.

Lemma count_smap_inj {T U} `{EqDecision T} `{EqDecision U}
    (f : T → U) x A :
  (∀ a b, f a = f b → a = b) → count (f x) (smap f A) = count x A.
Proof. by move=> finj; rewrite /count /= !(count_mem_fmap f x _ finj). Qed.

(** ** Flattening

    [flat f A] multiplies out the elements of [A] through [f], swapping the
    sides of the image of a negative element. *)

Definition flat {T U} (f : T → list U * list U) (A : list T * list T) :=
  (mbind (λ t, (f t).1) A.1 ++ mbind (λ t, (f t).2) A.2,
   mbind (λ t, (f t).2) A.1 ++ mbind (λ t, (f t).1) A.2).

Lemma flat_ext {T U} (f g : T → list U * list U) A :
  (∀ x, x ∈ elements A → f x = g x) → flat f A = flat g A.
Proof.
case: A => X Y; rewrite /elements /flat /= => H.
have e l : (∀ x, x ∈ l → f x = g x) →
    mbind (λ t, (f t).1) l = mbind (λ t, (g t).1) l ∧
    mbind (λ t, (f t).2) l = mbind (λ t, (g t).2) l.
  elim: l => [//|x l IH] Hl.
  rewrite !bind_cons (Hl x); first exact: list_elem_of_here.
  by case: IH => [u u_l|-> ->] //; apply: Hl; apply: list_elem_of_further.
have [-> ->] : mbind (λ t, (f t).1) X = mbind (λ t, (g t).1) X ∧
               mbind (λ t, (f t).2) X = mbind (λ t, (g t).2) X.
  by apply: e => x x_X; apply: H; rewrite elem_of_app; left.
have [-> ->] : mbind (λ t, (f t).1) Y = mbind (λ t, (g t).1) Y ∧
               mbind (λ t, (f t).2) Y = mbind (λ t, (g t).2) Y.
  by apply: e => x x_Y; apply: H; rewrite elem_of_app; right.
done.
Qed.

Lemma flat_singletons {T U} (f : T → U) A :
  flat (λ x, ([f x], [])) A = smap f A.
Proof.
case: A => X Y; rewrite /flat /smap /=.
have e l : mbind (λ t, [f t]) l = f <$> l ∧ mbind (λ t : T, @nil U) l = [].
  by elim: l => [//|x l [IH1 IH2]]; rewrite !bind_cons IH1 IH2.
by case: (e X) => -> ->; case: (e Y) => -> ->; rewrite app_nil_r.
Qed.

Lemma flat_atoms {T} (f : T → list T * list T) A :
  (∀ t, t ∈ elements A → f t = ([t], [])) → flat f A = A.
Proof.
move=> H; rewrite (flat_ext _ (λ t, ([id t], []))) // flat_singletons.
by rewrite smap_id.
Qed.

Lemma elem_of_flat {T U} (f : T → list U * list U) A u :
  u ∈ elements (flat f A) → ∃ t, t ∈ elements A ∧ u ∈ elements (f t).
Proof.
case: A => ps ns; rewrite /elements /flat /= !elem_of_app.
by case=> [[]|[]] /list_elem_of_bind [t [u_t t_in]]; exists t;
  rewrite !elem_of_app; eauto.
Qed.

Lemma flat_smap {T U V} (f : U → list V * list V) (g : T → U) A :
  flat f (smap g A) = flat (λ t, f (g t)) A.
Proof. by rewrite /flat /smap /= !list_fmap_bind. Qed.

Lemma smap_flat {T U V} (g : U → V) (f : T → list U * list U) A :
  smap g (flat f A) = flat (λ t, smap g (f t)) A.
Proof. by rewrite /flat /smap /= !fmap_app !list_bind_fmap. Qed.

Section Flat.

Context {T U : Type} `{EqDecision U} (f : T → list U * list U).

Implicit Types (z : U) (x : T) (X Y : list T) (A B : list T * list T).

Lemma count_flat_nil z : count z (flat f ([], [])) = 0%Z.
Proof. by []. Qed.

Lemma count_flat_cons1 z x X Y :
  count z (flat f (x :: X, Y)) = (count z (f x) + count z (flat f (X, Y)))%Z.
Proof.
rewrite /count /flat; cbn [fst snd]; rewrite !bind_cons !count_mem_app; lia.
Qed.

Lemma count_flat_cons2 z x X Y :
  count z (flat f (X, x :: Y)) = (count z (flat f (X, Y)) - count z (f x))%Z.
Proof.
rewrite /count /flat; cbn [fst snd]; rewrite !bind_cons !count_mem_app; lia.
Qed.

Lemma count_flat_perm z A B :
  A.1 ≡ₚ B.1 → A.2 ≡ₚ B.2 → count z (flat f A) = count z (flat f B).
Proof. by move=> e1 e2; apply: count_perm; rewrite /flat /= e1 e2. Qed.

Lemma count_flat_app z A B :
  count z (flat f (app A B)) = (count z (flat f A) + count z (flat f B))%Z.
Proof. rewrite /count /flat /app /= !bind_app !count_mem_app; lia. Qed.

Lemma count_flat_swap z A :
  count z (flat f (swap A)) = (- count z (flat f A))%Z.
Proof. rewrite /count /flat /swap /= !count_mem_app; lia. Qed.

Lemma count_flat_cancel `{EqDecision T} z A :
  count z (flat f (cancel A)) = count z (flat f A).
Proof.
case: A => X Y; elim: X => [//|x X IH].
rewrite cancel_cons count_flat_cons1 -IH /cancel_step.
case: (cancel (X, Y)) => C1 C2 /=.
case: (decide (x ∈ C2)) => xC.
- rewrite (bool_decide_eq_true_2 _ xC).
  rewrite (count_flat_perm z (C1, C2) (C1, x :: rem x C2)) //=.
  + exact: rem_Permutation xC.
  + rewrite count_flat_cons2; lia.
- by rewrite (bool_decide_eq_false_2 _ xC) count_flat_cons1.
Qed.

Lemma count_flat_to `{EqDecision T} (R : relation T) `{!RelDecision R} z A :
  count z (flat f (to R A)) = count z (flat f A).
Proof.
rewrite -(count_flat_cancel z A); apply: count_flat_perm => /=;
  exact: merge_sort_Permutation.
Qed.

End Flat.

Lemma count_flat_ext_count {T U} `{EqDecision U}
    (f g : T → list U * list U) z A :
  (∀ x, count z (f x) = count z (g x)) →
  count z (flat f A) = count z (flat g A).
Proof.
move=> e; case: A => X Y; elim: X => [|x X IH].
  elim: Y => [|y Y IH]; first by rewrite !count_flat_nil.
  by rewrite !count_flat_cons2 IH e.
by rewrite !count_flat_cons1 IH e.
Qed.

(** ** The order of a [Lexico] type

    Sorting needs a total order: [le] is the reflexive closure of the strict
    [lexico]. *)

Section Order.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Definition le : relation T := λ x y, x = y ∨ lexico x y.

#[global] Instance le_dec : RelDecision le :=
  λ x y, decide (x = y ∨ lexico x y).

#[global] Instance le_trans : Transitive le.
Proof.
move=> x y z [->|xy] [<-|yz]; [by left|by right|by right|].
by right; trans y.
Qed.

#[global] Instance le_total : Total le.
Proof.
move=> x y; case: (trichotomy lexico x y) => [xy|[->|yx]].
- by left; right.
- by left; left.
- by right; right.
Qed.

#[global] Instance le_antisymm : AntiSymm (=) le.
Proof.
move=> x y [//|xy] [//|yx]; exfalso.
by apply: (irreflexivity lexico x); trans y.
Qed.

End Order.

End Internal.

(** ** Signed multisets

    Equality is Leibniz, and the group laws hold because [Internal.to] is
    canonical. *)

Section SignedMultiset.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Record sms :=
  mk { car : list T * list T; wf_car : Internal.wf Internal.le car }.

Implicit Types (x y z : T) (X Y : list T) (s : sms).

Definition make X Y :=
  mk (Internal.to Internal.le (X, Y)) (Internal.wf_to Internal.le (X, Y)).
Definition inv s :=
  mk (Internal.swap (car s)) (Internal.wf_swap Internal.le _ (wf_car s)).
Definition count x s := Internal.count x (car s).
Definition pos s := (car s).1.
Definition neg s := (car s).2.

#[global] Instance empty_instance : Empty sms := make [] [].
#[global] Instance singleton_instance : SingletonMS T sms := λ x, make [x] [].
#[global] Instance disj_union_instance : DisjUnion sms :=
  λ s1 s2, make (pos s1 ++ pos s2) (neg s1 ++ neg s2).
#[global] Instance elements_instance : Elements T sms := λ s, pos s ++ neg s.
#[global] Instance elem_of_instance : ElemOf T sms := λ x s, x ∈ elements s.
#[global] Instance elem_of_dec x s : Decision (x ∈ s) :=
  decide (x ∈ elements s).

Lemma car_inj s1 s2 : car s1 = car s2 → s1 = s2.
Proof.
case: s1 s2 => [A1 w1] [A2 w2] /= e; subst A2.
by rewrite (proof_irrel w1 w2).
Qed.

Lemma count_inj s1 s2 : (∀ z, count z s1 = count z s2) → s1 = s2.
Proof.
move=> e; apply: car_inj.
by apply: (Internal.wf_count_inj Internal.le); [exact: wf_car..|].
Qed.

Lemma car_make X Y : car (make X Y) = Internal.to Internal.le (X, Y).
Proof. done. Qed.

Lemma count_make z X Y : count z (make X Y) = Internal.count z (X, Y).
Proof. exact: Internal.count_to. Qed.

#[global] Instance make_proper : Proper ((≡ₚ) ==> (≡ₚ) ==> (=)) make.
Proof.
move=> X1 X2 eX Y1 Y2 eY; apply: count_inj => z.
by rewrite !count_make; apply: Internal.count_perm.
Qed.

Lemma make_pos_neg s : make (pos s) (neg s) = s.
Proof.
apply: car_inj; rewrite car_make /pos /neg -surjective_pairing.
exact: Internal.to_id _ _ (wf_car s).
Qed.

Lemma singleton_make x : {[+ x +]} = make [x] [].
Proof. done. Qed.

Lemma car_singleton x : car {[+ x +]} = ([x], []).
Proof. rewrite car_make Internal.to_id //; exact: Internal.wf_singleton1. Qed.

Lemma car_inv s : car (inv s) = Internal.swap (car s).
Proof. done. Qed.

Lemma pos_singleton x : pos {[+ x +]} = [x].
Proof. by rewrite /pos car_singleton. Qed.

Lemma neg_singleton x : neg {[+ x +]} = [].
Proof. by rewrite /neg car_singleton. Qed.

Lemma pos_inv s : pos (inv s) = neg s.
Proof. done. Qed.

Lemma neg_inv s : neg (inv s) = pos s.
Proof. done. Qed.

Lemma elements_car s : elements s = Internal.elements (car s).
Proof. done. Qed.

Lemma elements_pos_neg s : elements s = pos s ++ neg s.
Proof. done. Qed.

(** *** Counts *)

Lemma count_empty z : count z ∅ = 0%Z.
Proof. by rewrite count_make. Qed.

Lemma count_singleton z x : count z {[+ x +]} = Z.b2z (bool_decide (z = x)).
Proof. by rewrite count_make Internal.count_cons1. Qed.

Lemma count_disj_union z s1 s2 :
  count z (s1 ⊎ s2) = (count z s1 + count z s2)%Z.
Proof.
rewrite count_make /count /pos /neg /Internal.count /= !count_mem_app; lia.
Qed.

Lemma count_inv z s : count z (inv s) = (- count z s)%Z.
Proof. exact: Internal.count_swap. Qed.

Lemma disj_union_make X1 Y1 X2 Y2 :
  make X1 Y1 ⊎ make X2 Y2 = make (X1 ++ X2) (Y1 ++ Y2).
Proof.
apply: count_inj => z; rewrite count_disj_union !count_make /Internal.count /=.
rewrite !count_mem_app; lia.
Qed.

Lemma make_cons_l x X Y : make (x :: X) Y = {[+ x +]} ⊎ make X Y.
Proof. by rewrite singleton_make disj_union_make. Qed.

Lemma inv_make X Y : inv (make X Y) = make Y X.
Proof.
apply: count_inj => z; rewrite count_inv !count_make /Internal.count /=; lia.
Qed.

(** *** Group laws *)

#[global] Instance disj_union_comm : Comm (=@{sms}) (⊎).
Proof. move=> s1 s2; apply: count_inj => z; rewrite !count_disj_union; lia. Qed.

#[global] Instance disj_union_assoc : Assoc (=@{sms}) (⊎).
Proof.
move=> s1 s2 s3; apply: count_inj => z; rewrite !count_disj_union; lia.
Qed.

#[global] Instance disj_union_left_id : LeftId (=@{sms}) ∅ (⊎).
Proof.
move=> s; apply: count_inj => z; rewrite count_disj_union count_empty; lia.
Qed.

#[global] Instance disj_union_right_id : RightId (=@{sms}) ∅ (⊎).
Proof.
move=> s; apply: count_inj => z; rewrite count_disj_union count_empty; lia.
Qed.

Lemma disj_union_inv_r s : s ⊎ inv s = ∅.
Proof.
apply: count_inj => z; rewrite count_disj_union count_inv count_empty; lia.
Qed.

Lemma invK s : inv (inv s) = s.
Proof. apply: count_inj => z; rewrite !count_inv; lia. Qed.

(** *** Elements *)

Lemma elem_of_elements x s : x ∈ elements s ↔ x ∈ s.
Proof. done. Qed.

Lemma elem_of_count x s : x ∈ s ↔ count x s ≠ 0%Z.
Proof. exact: (Internal.wf_elem_of_elements _ x _ (wf_car s)). Qed.

Lemma not_elem_of_count x s : x ∉ s → count x s = 0%Z.
Proof. by rewrite elem_of_count; lia. Qed.

Lemma count_pos x s : (0 < count x s)%Z ↔ x ∈ pos s.
Proof.
by rewrite /pos /count -(Internal.wf_count_gt0 _ x _ (wf_car s)); split; lia.
Qed.

Lemma count_neg x s : (count x s < 0)%Z ↔ x ∈ neg s.
Proof. exact: (Internal.wf_count_lt0 _ x _ (wf_car s)). Qed.

Lemma elem_of_pos x s : x ∈ pos s → x ∈ s.
Proof. by rewrite -count_pos elem_of_count; lia. Qed.

Lemma elem_of_neg x s : x ∈ neg s → x ∈ s.
Proof. by rewrite -count_neg elem_of_count; lia. Qed.

Lemma count_mem_elements x s :
  Z.of_nat (count_mem x (elements s)) = Z.abs (count x s).
Proof. exact: (Internal.wf_count_mem_elements _ x _ (wf_car s)). Qed.

Lemma count_mem_pos x s :
  Z.of_nat (count_mem x (pos s)) = Z.max 0 (count x s).
Proof.
rewrite /pos /count /Internal.count.
case: (decide (x ∈ (car s).1)) => x_s.
- have /not_elem_of_count_mem -> := Internal.wf_disjoint _ _ (wf_car s) x x_s.
  lia.
- move/not_elem_of_count_mem: x_s => ->; lia.
Qed.

Lemma elements_empty : elements (∅ : sms) = [].
Proof. by rewrite elements_car car_make Internal.to_pos. Qed.

Lemma elements_singleton x : elements ({[+ x +]} : sms) = [x].
Proof. by rewrite elements_car car_singleton. Qed.

Lemma elements_inv s : elements (inv s) ≡ₚ elements s.
Proof. by rewrite !elements_car car_inv Internal.elements_swap. Qed.

Lemma elements_disj_union s1 s2 :
  pos s1 ## neg s2 → neg s1 ## pos s2 →
  elements (s1 ⊎ s2) ≡ₚ elements s1 ++ elements s2.
Proof.
move=> d12 d21; apply: Permutation_count_mem => z; apply: Nat2Z.inj.
rewrite count_mem_app Nat2Z.inj_add !count_mem_elements count_disj_union.
have ? : ¬ (0 < count z s1 ∧ count z s2 < 0)%Z.
  by case=> /count_pos ? /count_neg ?; exact: (d12 z).
have ? : ¬ (count z s1 < 0 ∧ 0 < count z s2)%Z.
  by case=> /count_neg ? /count_pos ?; exact: (d21 z).
lia.
Qed.

Lemma elem_of_disj_union {x s1 s2} : x ∈ s1 ⊎ s2 → x ∈ s1 ∨ x ∈ s2.
Proof.
rewrite !elem_of_count count_disj_union.
case: (decide (count x s1 = 0%Z)) => ?; [right|left]; lia.
Qed.

Lemma elem_of_singleton x y : x ∈ ({[+ y +]} : sms) ↔ x = y.
Proof.
by rewrite -elem_of_elements elements_singleton list_elem_of_singleton.
Qed.

Lemma pos_make_nil_r X : pos (make X []) ≡ₚ X.
Proof.
rewrite /pos car_make Internal.to_pos; exact: merge_sort_Permutation.
Qed.

Lemma neg_make_nil_r X : neg (make X []) = [].
Proof. by rewrite /neg car_make Internal.to_pos. Qed.

Lemma elements_make_nil_r X : elements (make X []) ≡ₚ X.
Proof.
by rewrite elements_pos_neg neg_make_nil_r app_nil_r pos_make_nil_r.
Qed.

Lemma elem_of_make_nil_r x X : x ∈ make X [] ↔ x ∈ X.
Proof. by rewrite -elem_of_elements elements_make_nil_r. Qed.

Lemma elem_of_make {x X Y} : x ∈ make X Y → x ∈ X ++ Y.
Proof.
rewrite -elem_of_elements elements_car car_make.
exact: (Internal.elem_of_elements_to _ x).
Qed.

End SignedMultiset.

Arguments sms T {_ _ _ _}.

(** ** Binding

    [bind f s] substitutes [f x] for each element [x] of [s]: [sms] is the free
    abelian group, and [bind] its monadic bind. *)

Section Bind.

Context {T U : Type}.
Context `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.
Context `{EqDecision U, Lexico U}
  `{!StrictOrder (@lexico U _), !TrichotomyT (@lexico U _)}.

Implicit Types (x : T) (X Y : list T) (s : sms T).

Definition bind (f : T → sms U) s : sms U :=
  make ((pos s ≫= λ x, pos (f x)) ++ (neg s ≫= λ x, neg (f x)))
       ((pos s ≫= λ x, neg (f x)) ++ (neg s ≫= λ x, pos (f x))).

Definition map (f : T → U) s : sms U := bind (λ x, {[+ f x +]}) s.

Lemma car_bind f s :
  car (bind f s) =
  Internal.to Internal.le (Internal.flat (λ x, car (f x)) (car s)).
Proof. reflexivity. Qed.

Lemma count_bind (z : U) f s :
  count z (bind f s) =
  Internal.count z (Internal.flat (λ x, car (f x)) (car s)).
Proof. by rewrite /count car_bind Internal.count_to. Qed.

Lemma bind_make f X Y :
  bind f (make X Y) =
  make ((X ≫= λ x, pos (f x)) ++ (Y ≫= λ x, neg (f x)))
       ((X ≫= λ x, neg (f x)) ++ (Y ≫= λ x, pos (f x))).
Proof.
apply: count_inj => z; rewrite count_bind car_make Internal.count_flat_to.
by rewrite count_make.
Qed.

Lemma bind_make_cons_l f x X Y :
  bind f (make (x :: X) Y) = f x ⊎ bind f (make X Y).
Proof.
apply: count_inj => z; rewrite [RHS]count_disj_union !count_bind !car_make.
by rewrite !Internal.count_flat_to Internal.count_flat_cons1.
Qed.

Lemma bind_make_cons_r f y X Y :
  bind f (make X (y :: Y)) = inv (f y) ⊎ bind f (make X Y).
Proof.
apply: count_inj => z; rewrite [RHS]count_disj_union count_inv !count_bind.
rewrite !car_make !Internal.count_flat_to Internal.count_flat_cons2 /count; lia.
Qed.

Lemma elem_of_bind {f s} {y : U} : y ∈ bind f s → ∃ x, x ∈ s ∧ y ∈ f x.
Proof.
rewrite -elem_of_elements elements_car car_bind.
move=> /(Internal.elem_of_elements_to _ y) /(Internal.elem_of_flat _ _ y).
by case=> x [x_s y_x]; exists x.
Qed.

Lemma bind_singleton f x : bind f {[+ x +]} = f x.
Proof.
apply: count_inj => z; rewrite count_bind car_singleton.
by rewrite Internal.count_flat_cons1 Internal.count_flat_nil Z.add_0_r.
Qed.

Lemma bind_empty f : bind f ∅ = ∅.
Proof. by rewrite bind_make. Qed.

Lemma bind_disj_union f s1 s2 : bind f (s1 ⊎ s2) = bind f s1 ⊎ bind f s2.
Proof.
apply: count_inj => z; rewrite [RHS]count_disj_union !count_bind car_make.
rewrite Internal.count_flat_to.
exact: (Internal.count_flat_app _ z (car s1) (car s2)).
Qed.

Lemma bind_inv f s : bind f (inv s) = inv (bind f s).
Proof.
apply: count_inj => z; rewrite [RHS]count_inv !count_bind car_inv.
exact: Internal.count_flat_swap.
Qed.

Lemma bind_ext f g s : (∀ x, x ∈ s → f x = g x) → bind f s = bind g s.
Proof.
move=> fg; apply: count_inj => z; rewrite !count_bind.
rewrite (Internal.flat_ext _ (λ x, car (g x))) //.
by move=> x /fg ->.
Qed.

Lemma car_map f s :
  car (map f s) = Internal.to Internal.le (Internal.smap f (car s)).
Proof.
rewrite -Internal.flat_singletons -(Internal.flat_ext (λ x, car {[+ f x +]})).
  by move=> x _; rewrite car_singleton.
reflexivity.
Qed.

Lemma count_map_inj f x s :
  (∀ a b, f a = f b → a = b) → count (f x) (map f s) = count x s.
Proof.
move=> finj.
by rewrite /count car_map Internal.count_to Internal.count_smap_inj.
Qed.

Lemma map_make f X Y : map f (make X Y) = make (f <$> X) (f <$> Y).
Proof.
apply: count_inj => z; rewrite [RHS]count_make /count car_map car_make.
by rewrite Internal.count_to Internal.count_smap_to.
Qed.

Lemma elem_of_map {f s} {y : U} : y ∈ map f s → ∃ x, y = f x ∧ x ∈ s.
Proof.
rewrite -elem_of_elements elements_car car_map.
move=> /(Internal.elem_of_elements_to _ y); rewrite Internal.elements_smap.
by move=> /list_elem_of_fmap [x [-> x_s]]; exists x.
Qed.

Lemma elements_map_inj f s :
  (∀ a b, f a = f b → a = b) → elements (map f s) ≡ₚ f <$> elements s.
Proof.
move=> finj; apply: Permutation_count_mem => y; apply: Nat2Z.inj.
rewrite count_mem_elements.
case: (decide (y ∈ map f s)) => [/elem_of_map [x [-> x_s]]|ny].
  by rewrite count_map_inj // count_mem_fmap // count_mem_elements.
rewrite (not_elem_of_count _ _ ny) (proj1 (not_elem_of_count_mem _ _)) //.
move=> /list_elem_of_fmap [x [ex x_s]]; apply: ny; rewrite ex.
by rewrite elem_of_count count_map_inj // -elem_of_count -elem_of_elements.
Qed.

Lemma map_pos_neg f s : map f s = make (f <$> pos s) (f <$> neg s).
Proof. by rewrite -{1}(make_pos_neg s) map_make. Qed.

Lemma map_singleton f x : map f {[+ x +]} = {[+ f x +]}.
Proof. exact: bind_singleton. Qed.

Lemma map_empty f : map f ∅ = ∅.
Proof. exact: bind_empty. Qed.

Lemma map_disj_union f s1 s2 : map f (s1 ⊎ s2) = map f s1 ⊎ map f s2.
Proof. exact: bind_disj_union. Qed.

Lemma map_ext f g s : (∀ x, x ∈ s → f x = g x) → map f s = map g s.
Proof. by move=> fg; apply: bind_ext => x /fg ->. Qed.

Lemma map_inv f s : map f (inv s) = inv (map f s).
Proof. exact: bind_inv. Qed.

End Bind.

Lemma map_map {T U V : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    `{EqDecision U, Lexico U, !StrictOrder (@lexico U _),
      !TrichotomyT (@lexico U _)}
    `{EqDecision V, Lexico V, !StrictOrder (@lexico V _),
      !TrichotomyT (@lexico V _)}
    (f : T → U) (g : U → V) (s : sms T) :
  map g (map f s) = map (λ x, g (f x)) s.
Proof.
apply: count_inj => z; rewrite /count !car_map !Internal.count_to.
by rewrite Internal.count_smap_to Internal.smap_smap.
Qed.

Lemma bind_map {T U V : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    `{EqDecision U, Lexico U, !StrictOrder (@lexico U _),
      !TrichotomyT (@lexico U _)}
    `{EqDecision V, Lexico V, !StrictOrder (@lexico V _),
      !TrichotomyT (@lexico V _)}
    (f : U → sms V) (g : T → U) (s : sms T) :
  bind f (map g s) = bind (λ x, f (g x)) s.
Proof.
apply: count_inj => z; rewrite !count_bind car_map Internal.count_flat_to.
by rewrite Internal.flat_smap.
Qed.

Lemma map_bind {T U V : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    `{EqDecision U, Lexico U, !StrictOrder (@lexico U _),
      !TrichotomyT (@lexico U _)}
    `{EqDecision V, Lexico V, !StrictOrder (@lexico V _),
      !TrichotomyT (@lexico V _)}
    (f : U → V) (g : T → sms U) (s : sms T) :
  map f (bind g s) = bind (λ x, map f (g x)) s.
Proof.
apply: count_inj => z; rewrite [RHS]count_bind /count car_map Internal.count_to.
rewrite car_bind Internal.count_smap_to Internal.smap_flat.
apply: Internal.count_flat_ext_count => x.
by rewrite car_map Internal.count_to.
Qed.

Lemma bind_unit {T : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    (s : sms T) :
  bind (λ x, {[+ x +]}) s = s.
Proof.
apply: count_inj => z; rewrite count_bind.
by rewrite (Internal.flat_ext _ (λ x, ([id x], []))) ?Internal.flat_singletons
  ?Internal.smap_id.
Qed.

Lemma map_id_ext {T : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    (f : T → T) (s : sms T) :
  (∀ x, x ∈ s → f x = x) → map f s = s.
Proof. by move=> fs; rewrite -[RHS]bind_unit; apply: bind_ext => x /fs ->. Qed.

End SMS.

#[global] Arguments SMS.Internal.cancel : simpl never.
#[global] Arguments SMS.Internal.to : simpl never.
#[global] Arguments SMS.Internal.wf : simpl never.
