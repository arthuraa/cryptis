(** Evaluation of polynomials in a commutative ring

    [eval rO rI radd rmul ropp φ p] evaluates the polynomial [p] in a
    commutative ring whose equality [req] is an arbitrary equivalence, sending
    each variable [x] to [φ x].  Evaluation is a ring morphism up to [req]
    ([eval_add], [eval_opp], [eval_mul], [eval_zero], [eval_one],
    [eval_var]).  Unlike [Frac.eval], the target can be syntax modulo an
    equational theory, given as an [IsRing] instance.

    Sums and products are folds of a commutative operation over lists
    ([fold_op]), which permutations leave unchanged ([fold_op_perm]); over
    multisets and signed multisets ([msum], [ssum]) they are taken over the
    elements.  The definitions take the operations explicitly and the lemmas
    infer them. *)

From mathcomp Require Import ssreflect.
From stdpp Require Import list numbers.
From Stdlib Require Import ZArith Lia Ring Setoid Morphisms.
From cryptis.lib Require Import mset sms poly.

Module PolyEval.

Class IsRing {R : Type} (req : relation R) (rO rI : R)
    (radd rmul : R → R → R) (ropp : R → R) : Prop :=
  is_ring : ring_theory rO rI radd rmul (λ x y, radd x (ropp y)) ropp req.

Definition fold_op {M} (mo : M) (mop : M → M → M) (l : list M) : M :=
  foldr mop mo l.

Definition msum {R} (rO : R) (radd : R → R → R) {A : Type}
    `{EqDecision A, Lexico A, !StrictOrder (@lexico A _),
      !TrichotomyT (@lexico A _)}
    (f : A → R) (X : MSet.mset A) : R :=
  fold_op rO radd (f <$> elements X).

Definition ssum {R} (rO : R) (radd : R → R → R) (ropp : R → R) {A : Type}
    `{EqDecision A, Lexico A, !StrictOrder (@lexico A _),
      !TrichotomyT (@lexico A _)}
    (f : A → R) (s : SMS.sms A) : R :=
  radd (msum rO radd f (SMS.pos s)) (ropp (msum rO radd f (SMS.neg s))).

Definition mono_eval {R} (rI : R) (rmul : R → R → R) {T : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    (φ : T → R) (m : MSet.mset T) : R :=
  fold_op rI rmul (φ <$> elements m).

Definition eval {R} (rO rI : R) (radd rmul : R → R → R) (ropp : R → R)
    {T : Type}
    `{EqDecision T, Lexico T, !StrictOrder (@lexico T _),
      !TrichotomyT (@lexico T _)}
    (φ : T → R) (p : Poly.poly T) : R :=
  ssum rO radd ropp (mono_eval rI rmul φ) (Poly.car p).

(** ** Folds of commutative operations *)

Section Fold.

Context {M : Type} {meq : relation M} `{!Equivalence meq}.
Context {mo : M} {mop : M → M → M}.
Context `{!Proper (meq ==> meq ==> meq) mop}.
Context `{!Assoc meq mop, !Comm meq mop, !LeftId meq mo mop}.

Local Infix "≈" := meq (at level 70).
Local Abbreviation fold := (fold_op mo mop).

Lemma fold_op_cons x l : fold (x :: l) = mop x (fold l).
Proof. by []. Qed.

Lemma fold_op_app l1 l2 : fold (l1 ++ l2) ≈ mop (fold l1) (fold l2).
Proof.
elim: l1 => [|x l1 IH] /=; first by rewrite (left_id mo mop).
by rewrite IH (assoc mop).
Qed.

Lemma fold_op_perm l1 l2 : l1 ≡ₚ l2 → fold l1 ≈ fold l2.
Proof.
elim=> {l1 l2} [|x l1 l2 _ IH|x y l|l1 l2 l3 _ IH1 _ IH2] /=.
- done.
- by rewrite IH.
- by rewrite !(assoc mop) (comm mop x y).
- by rewrite IH1 IH2.
Qed.

Lemma mop_interchange a b c d :
  mop (mop a b) (mop c d) ≈ mop (mop a c) (mop b d).
Proof.
rewrite -!(assoc mop) (assoc mop b c d) (comm mop b c).
by rewrite -(assoc mop c b d).
Qed.

Lemma fold_op_unit l : (∀ x, x ∈ l → x ≈ mo) → fold l ≈ mo.
Proof.
elim: l => [|x l IH] //= h.
have IH' : fold l ≈ mo.
  by apply: IH => y yl; apply: h; apply: list_elem_of_further.
by rewrite (h x (list_elem_of_here _ _)) IH' (left_id mo mop).
Qed.

Lemma fold_op_ext {A} (f g : A → M) (l : list A) :
  (∀ x, x ∈ l → f x ≈ g x) → fold (f <$> l) ≈ fold (g <$> l).
Proof.
elim: l => [|x l IH] //= h.
have IH' : fold (f <$> l) ≈ fold (g <$> l).
  by apply: IH => y yl; apply: h; apply: list_elem_of_further.
by rewrite (h x (list_elem_of_here _ _)) IH'.
Qed.

End Fold.

(** ** Sums over multisets and signed multisets *)

Section Sums.

Context {R : Type} {req : relation R} `{!Equivalence req}.
Context {rO rI : R} {radd rmul : R → R → R} {ropp : R → R}.
Context `{!Proper (req ==> req ==> req) radd}.
Context `{!Proper (req ==> req ==> req) rmul}.
Context `{!Proper (req ==> req) ropp}.
Context `{RI : !IsRing req rO rI radd rmul ropp}.

Local Infix "≈" := req (at level 70).
Local Abbreviation lsum := (fold_op rO radd).
Local Abbreviation msum := (msum rO radd).
Local Abbreviation ssum := (ssum rO radd ropp).
Local Abbreviation mono_eval := (mono_eval rI rmul).
Local Abbreviation eval := (eval rO rI radd rmul ropp).

Lemma rth : ring_theory rO rI radd rmul (λ x y, radd x (ropp y)) ropp req.
Proof. exact: RI. Qed.

Lemma req_setoid : Setoid_Theory R req.
Proof. exact: _. Qed.

Lemma ring_ext : ring_eq_ext radd rmul ropp req.
Proof. by split; apply _. Qed.

Add Ring R_ring : rth (setoid req_setoid ring_ext).

#[local] Instance radd_assoc : Assoc req radd.
Proof. by move=> ???; ring. Qed.
#[local] Instance radd_comm : Comm req radd.
Proof. by move=> ??; ring. Qed.
#[local] Instance radd_left_id : LeftId req rO radd.
Proof. by move=> ?; ring. Qed.
#[local] Instance rmul_assoc : Assoc req rmul.
Proof. by move=> ???; ring. Qed.
#[local] Instance rmul_comm : Comm req rmul.
Proof. by move=> ??; ring. Qed.
#[local] Instance rmul_left_id : LeftId req rI rmul.
Proof. by move=> ?; ring. Qed.

Lemma lsum_mul_l c (l : list R) : rmul c (lsum l) ≈ lsum (rmul c <$> l).
Proof.
elim: l => [|x l IH]; first by rewrite /=; ring.
by rewrite fmap_cons !fold_op_cons -IH; ring.
Qed.

Section MSum.

Context {A : Type} `{EqDecision A, Lexico A}
  `{!StrictOrder (@lexico A _), !TrichotomyT (@lexico A _)}.

Implicit Types (X Y : MSet.mset A) (s : SMS.sms A) (f g : A → R).

Lemma msum_empty f : msum f ∅ ≈ rO.
Proof. by rewrite /PolyEval.msum MSet.elements_empty. Qed.

Lemma msum_singleton f x : msum f {[+ x +]} ≈ f x.
Proof. by rewrite /PolyEval.msum MSet.elements_singleton /=; ring. Qed.

Lemma msum_disj_union f X Y : msum f (X ⊎ Y) ≈ radd (msum f X) (msum f Y).
Proof.
rewrite /PolyEval.msum -fold_op_app -fmap_app.
apply: fold_op_perm; apply: fmap_Permutation.
exact: MSet.elements_disj_union.
Qed.

Lemma msum_ext f g X : (∀ x, x ∈ X → f x ≈ g x) → msum f X ≈ msum g X.
Proof.
move=> h; rewrite /PolyEval.msum; apply: fold_op_ext.
by move=> x /MSet.elem_of_elements; exact: h.
Qed.

Lemma ssum_make f X Y :
  ssum f (SMS.make X Y) ≈ radd (msum f X) (ropp (msum f Y)).
Proof.
rewrite /PolyEval.ssum SMS.pos_make SMS.neg_make.
have EX : X = (X ∖ Y) ⊎ (X ∖ (X ∖ Y)).
  apply: MSet.count_inj => x.
  rewrite MSet.count_disj_union !MSet.count_difference; lia.
have EY : Y = (Y ∖ X) ⊎ (X ∖ (X ∖ Y)).
  apply: MSet.count_inj => x.
  rewrite MSet.count_disj_union !MSet.count_difference; lia.
have -> : msum f X = msum f ((X ∖ Y) ⊎ (X ∖ (X ∖ Y))) by rewrite -EX.
have -> : msum f Y = msum f ((Y ∖ X) ⊎ (X ∖ (X ∖ Y))) by rewrite -EY.
rewrite !msum_disj_union.
by move: (msum f (X ∖ Y)) (msum f (Y ∖ X)) (msum f (X ∖ (X ∖ Y))) => a b c;
  ring.
Qed.

Lemma ssum_empty f : ssum f ∅ ≈ rO.
Proof.
by rewrite /PolyEval.ssum SMS.pos_empty SMS.neg_empty !msum_empty; ring.
Qed.

Lemma ssum_singleton f x : ssum f {[+ x +]} ≈ f x.
Proof.
rewrite /PolyEval.ssum SMS.pos_singleton SMS.neg_singleton.
by rewrite msum_singleton msum_empty; ring.
Qed.

Lemma ssum_disj_union f s1 s2 :
  ssum f (s1 ⊎ s2) ≈ radd (ssum f s1) (ssum f s2).
Proof.
change (s1 ⊎ s2) with
  (SMS.make (SMS.pos s1 ⊎ SMS.pos s2) (SMS.neg s1 ⊎ SMS.neg s2)).
rewrite ssum_make !msum_disj_union /PolyEval.ssum.
move: (msum f (SMS.pos s1)) (msum f (SMS.pos s2)) => a b.
by move: (msum f (SMS.neg s1)) (msum f (SMS.neg s2)) => c d; ring.
Qed.

Lemma ssum_inv f s : ssum f (SMS.inv s) ≈ ropp (ssum f s).
Proof. by rewrite /PolyEval.ssum SMS.pos_inv SMS.neg_inv; ring. Qed.

Lemma ssum_ext f g s : (∀ x, x ∈ s → f x ≈ g x) → ssum f s ≈ ssum g s.
Proof.
move=> h; rewrite /PolyEval.ssum.
have hp : msum f (SMS.pos s) ≈ msum g (SMS.pos s).
  by apply: msum_ext => x xs; apply: h; left.
have hn : msum f (SMS.neg s) ≈ msum g (SMS.neg s).
  by apply: msum_ext => x xs; apply: h; right.
by rewrite hp hn.
Qed.

Lemma ssum_mul_l c f s : rmul c (ssum f s) ≈ ssum (λ x, rmul c (f x)) s.
Proof.
have E X : msum (λ x, rmul c (f x)) X ≈ rmul c (msum f X).
  by rewrite /PolyEval.msum lsum_mul_l -list_fmap_compose.
by rewrite /PolyEval.ssum !E; ring.
Qed.

End MSum.

Lemma ssum_bind {A B : Type}
    `{EqDecision A, Lexico A, !StrictOrder (@lexico A _),
      !TrichotomyT (@lexico A _)}
    `{EqDecision B, Lexico B, !StrictOrder (@lexico B _),
      !TrichotomyT (@lexico B _)}
    (g : B → R) (f : A → SMS.sms B) (s : SMS.sms A) :
  ssum g (SMS.bind f s) ≈ ssum (λ x, ssum g (f x)) s.
Proof.
elim/(SMS.sms_ind (T := A)): s => [|x s IH|x s IH].
- by rewrite SMS.bind_empty !ssum_empty.
- rewrite SMS.bind_disj_union SMS.bind_singleton !ssum_disj_union.
  by rewrite ssum_singleton IH.
- rewrite SMS.bind_disj_union SMS.bind_inv SMS.bind_singleton.
  by rewrite !ssum_disj_union !ssum_inv ssum_singleton IH.
Qed.

Lemma ssum_map {A B : Type}
    `{EqDecision A, Lexico A, !StrictOrder (@lexico A _),
      !TrichotomyT (@lexico A _)}
    `{EqDecision B, Lexico B, !StrictOrder (@lexico B _),
      !TrichotomyT (@lexico B _)}
    (g : B → R) (f : A → B) (s : SMS.sms A) :
  ssum g (SMS.map f s) ≈ ssum (λ x, g (f x)) s.
Proof.
rewrite [SMS.map]unlock ssum_bind.
by apply: ssum_ext => x _; apply: ssum_singleton.
Qed.

(** ** Polynomials *)

Section Eval.

Context {T : Type} `{EqDecision T, Lexico T}
  `{!StrictOrder (@lexico T _), !TrichotomyT (@lexico T _)}.

Implicit Types (x : T) (m n : MSet.mset T) (p q : Poly.poly T).
Implicit Types (φ ψ : T → R).

Lemma mono_eval_empty φ : mono_eval φ ∅ ≈ rI.
Proof. by rewrite /PolyEval.mono_eval MSet.elements_empty. Qed.

Lemma mono_eval_singleton φ x : mono_eval φ {[+ x +]} ≈ φ x.
Proof. by rewrite /PolyEval.mono_eval MSet.elements_singleton /=; ring. Qed.

Lemma mono_eval_disj_union φ m n :
  mono_eval φ (m ⊎ n) ≈ rmul (mono_eval φ m) (mono_eval φ n).
Proof.
rewrite /PolyEval.mono_eval -fold_op_app -fmap_app.
apply: fold_op_perm; apply: fmap_Permutation.
exact: MSet.elements_disj_union.
Qed.

Lemma mono_eval_ext φ ψ m :
  (∀ x, x ∈ m → φ x ≈ ψ x) → mono_eval φ m ≈ mono_eval ψ m.
Proof.
move=> h; rewrite /PolyEval.mono_eval; apply: fold_op_ext.
by move=> x /MSet.elem_of_elements; exact: h.
Qed.

Lemma eval_mono φ m : eval φ (Poly.mono m) ≈ mono_eval φ m.
Proof. by rewrite /PolyEval.eval Poly.car_mono ssum_singleton. Qed.

Lemma eval_zero φ : eval φ Poly.zero ≈ rO.
Proof. by rewrite /PolyEval.eval Poly.car_zero ssum_empty. Qed.

Lemma eval_one φ : eval φ Poly.one ≈ rI.
Proof. by rewrite Poly.oneE eval_mono mono_eval_empty. Qed.

Lemma eval_var φ x : eval φ (Poly.var x) ≈ φ x.
Proof. by rewrite Poly.varE eval_mono mono_eval_singleton. Qed.

Lemma eval_add φ p q : eval φ (Poly.add p q) ≈ radd (eval φ p) (eval φ q).
Proof. by rewrite /PolyEval.eval Poly.car_add ssum_disj_union. Qed.

Lemma eval_opp φ p : eval φ (Poly.opp p) ≈ ropp (eval φ p).
Proof. by rewrite /PolyEval.eval Poly.car_opp ssum_inv. Qed.

Lemma eval_mul φ p q : eval φ (Poly.mul p q) ≈ rmul (eval φ p) (eval φ q).
Proof.
rewrite /PolyEval.eval Poly.car_mul ssum_bind.
have E : ∀ m, m ∈ Poly.car p →
    ssum (mono_eval φ) (SMS.map (λ n, m ⊎ n) (Poly.car q)) ≈
    rmul (mono_eval φ m) (ssum (mono_eval φ) (Poly.car q)).
  move=> m _; rewrite ssum_map ssum_mul_l.
  by apply: ssum_ext => n _; apply: mono_eval_disj_union.
rewrite (ssum_ext _ _ _ E) (comm rmul) ssum_mul_l.
by apply: ssum_ext => m _; apply: (comm rmul).
Qed.

End Eval.

End Sums.

End PolyEval.
