(** An equational presentation of terms

    Pre-terms are a free syntax for terms: every operation is a constructor
    of [PreTerm.pre_term], up to the tag of its arity ([core/pre_term]).
    [fold_term] interprets them in [term], and [x ∼ y] is the least
    congruence satisfying the laws of a field for exponents, of an abelian
    group for the Diffie-Hellman product, and of exponentiation as a module
    action:

    - [(g ^ a) ^ b ∼ g ^ (a · b)]
    - [g ^ a ⋅ g ^ b ∼ g ^ (a + b)]
    - [g ^ 1 ∼ g]
    - [(u ⋅ v) ^ x ∼ u ^ x ⋅ v ^ x]

    The main result is [term_equiv_iff]: [x ∼ y ↔ fold_term x = fold_term y].
    Since [fold_term] is onto ([fold_term_surj]), [term] is [pre_term] modulo
    [∼].  The inverse law [x · x⁻¹ ∼ 1] is stated for the [x] whose normal
    form is not that of zero: exponents are rational functions in their
    atoms, and no equational axiom derives [(x + 1) · (x + 1)⁻¹ = 1], which
    fails in ℚ when [x = -1].

    Soundness compares the readings of normal forms ([normalize_sound]).
    Completeness shows that every pre-term is equivalent to its normal form
    ([term_equiv_normalize]): encodings of fractions and of Diffie-Hellman
    maps respect the operations up to [∼]. *)

From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith Lia Ring Field Setoid Morphisms.
From stdpp Require Import gmap sorting.
From cryptis.lib Require Import fmap mset sms poly poly_gcd frac poly_eval.
From cryptis.core Require Import term.

Import PreTerm.

Local Abbreviation frac := (Frac.frac pre_term).

Implicit Types (t u s : pre_term).

Abbreviation PZero := (PT0 O0Zero).
Abbreviation POne := (PT0 O0One).
Abbreviation PGOne := (PT0 O0GOne).
Abbreviation PAdd := (PT2 O2Add).
Abbreviation POpp := (PT1 O1Opp).
Abbreviation PMul := (PT2 O2Mul).
Abbreviation PInv := (PT1 O1Inv).
Abbreviation PGMul := (PT2 O2GMul).
Abbreviation PGInv := (PT1 O1GInv).
Abbreviation PExp := (PT2 O2Exp).

Reserved Notation "x ∼ y" (at level 70).

Inductive term_equiv : pre_term → pre_term → Prop :=
| E_refl x : x ∼ x
| E_sym x y : x ∼ y → y ∼ x
| E_trans x y z : x ∼ y → y ∼ z → x ∼ z
| E_PT1 o x1 x2 : x1 ∼ x2 → PT1 o x1 ∼ PT1 o x2
| E_PT2 o x1 x2 y1 y2 : x1 ∼ x2 → y1 ∼ y2 → PT2 o x1 y1 ∼ PT2 o x2 y2
| E_add_comm x y : PAdd x y ∼ PAdd y x
| E_add_assoc x y z : PAdd (PAdd x y) z ∼ PAdd x (PAdd y z)
| E_add_zero x : PAdd PZero x ∼ x
| E_add_opp x : PAdd x (POpp x) ∼ PZero
| E_mul_comm x y : PMul x y ∼ PMul y x
| E_mul_assoc x y z : PMul (PMul x y) z ∼ PMul x (PMul y z)
| E_mul_one x : PMul POne x ∼ x
| E_distr x y z : PMul (PAdd x y) z ∼ PAdd (PMul x z) (PMul y z)
| E_mul_inv x : normalize x ≠ normalize PZero → PMul x (PInv x) ∼ POne
| E_inv_zero : PInv PZero ∼ PZero
| E_gmul_comm u v : PGMul u v ∼ PGMul v u
| E_gmul_assoc u v w : PGMul (PGMul u v) w ∼ PGMul u (PGMul v w)
| E_gmul_one u : PGMul PGOne u ∼ u
| E_gmul_inv u : PGMul u (PGInv u) ∼ PGOne
| E_exp_exp g a b : PExp (PExp g a) b ∼ PExp g (PMul a b)
| E_exp_add g a b : PGMul (PExp g a) (PExp g b) ∼ PExp g (PAdd a b)
| E_exp_one g : PExp g POne ∼ g
| E_exp_gmul u v x : PExp (PGMul u v) x ∼ PGMul (PExp u x) (PExp v x)
where "x ∼ y" := (term_equiv x y).

(** ** Readings of normal forms *)

Definition fval t : frac := frac_of (normalize t).
Definition gval t : dhmap := dh_map (normalize t).

Definition atom_ok x := canon x ∧ is_mod x = false.
Definition base_ok k := canon k ∧ is_dh k = false.
Definition dh_ok (m : dhmap) : Prop :=
  (∀ k, m !!! k ≠ Frac.zero → base_ok k) ∧
  ∀ k, Frac.all_vars atom_ok (m !!! k).

Section Values.

Add Ring flat_frac_ring'' : (Frac.frac_ring_theory (T := pre_term)).
Add Field flat_frac_field : (Frac.frac_field_theory (T := pre_term)).

Implicit Types (r : frac) (m : dhmap).

Lemma normalize_props t : nf_props (normalize t).
Proof. exact: canon_props (canon_normalize t). Qed.

Lemma normalize_fvalE t : normalize t = mod_of_frac (fval t).
Proof. by have [_ [e _]] := normalize_props t; rewrite /fval e. Qed.

Lemma normalize_gvalE t : normalize t = dh_of (gval t).
Proof. by have [_ [_ [e _]]] := normalize_props t; rewrite /gval e. Qed.

Lemma fval_ok t : Frac.all_vars atom_ok (fval t).
Proof.
by have [_ [_ [_ [h _]]]] := normalize_props t; apply/Frac.all_vars_iff.
Qed.

Lemma gval_ok t : dh_ok (gval t).
Proof.
have [_ [_ [_ [_ [hk hv]]]]] := normalize_props t.
by split=> // k; apply/Frac.all_vars_iff; exact: hv k.
Qed.

Lemma parse_frac_encode_ok r :
  Frac.all_vars atom_ok r → frac_of (mod_of_frac r) = r.
Proof.
by move=> /Frac.all_vars_iff h; apply: frac_of_mod_of_frac_atoms => x /h [].
Qed.

Lemma parse_dh_encode_ok m : dh_ok m → dh_map (dh_of m) = m.
Proof.
move=> [hk hv]; apply: dh_map_dh_of_atoms; first by move=> k /hk [].
by move=> k x /(proj1 (Frac.all_vars_iff _ _) (hv k)) [].
Qed.

Lemma dh_ok_empty : dh_ok ∅.
Proof.
by split=> k; rewrite FMap.lookup_empty //; exact: Frac.all_vars_zero.
Qed.

Lemma dh_ok_add m1 m2 : dh_ok m1 → dh_ok m2 → dh_ok (dh_add m1 m2).
Proof.
move=> [k1 v1] [k2 v2]; split=> k; rewrite lookup_dh_add.
  case: (decide (m1 !!! k = Frac.zero)) => [z1|n1]; last by move=> _; apply: k1.
  by rewrite z1 => n2; apply: k2 => z2; apply: n2; rewrite z2; ring.
exact: Frac.all_vars_add.
Qed.

Lemma dh_ok_opp m : dh_ok m → dh_ok (dh_opp m).
Proof.
move=> [k1 v1]; split=> k; rewrite lookup_dh_opp; last exact: Frac.all_vars_opp.
by move=> nk; apply: k1 => e; apply: nk; rewrite e Frac.opp_zero.
Qed.

Lemma dh_ok_scale r m :
  Frac.all_vars atom_ok r → dh_ok m → dh_ok (dh_scale r m).
Proof.
move=> hr [k1 v1]; split=> k; rewrite lookup_dh_scale.
  by move=> nk; apply: k1 => z; apply: nk; rewrite z Frac.mul_zero_l.
exact: Frac.all_vars_mul.
Qed.

Lemma fval_zero : fval PZero = Frac.zero.
Proof.
rewrite /fval normalize_zero parse_frac_encode_ok //.
exact: Frac.all_vars_zero.
Qed.

Lemma fval_one : fval POne = Frac.one.
Proof.
rewrite /fval normalize_one parse_frac_encode_ok //.
exact: Frac.all_vars_one.
Qed.

Lemma fval_opp t : fval (POpp t) = Frac.opp (fval t).
Proof.
rewrite /fval normalize_opp parse_frac_encode_ok //.
by apply: Frac.all_vars_opp; apply: fval_ok.
Qed.

Lemma fval_inv t : fval (PInv t) = Frac.inv (fval t).
Proof.
rewrite /fval normalize_inv parse_frac_encode_ok //.
by apply: Frac.all_vars_inv; apply: fval_ok.
Qed.

Lemma fval_add t1 t2 : fval (PAdd t1 t2) = Frac.add (fval t1) (fval t2).
Proof.
rewrite /fval normalize_add parse_frac_encode_ok //.
by apply: Frac.all_vars_add; apply: fval_ok.
Qed.

Lemma fval_mul t1 t2 : fval (PMul t1 t2) = Frac.mul (fval t1) (fval t2).
Proof.
rewrite /fval normalize_mul parse_frac_encode_ok //.
by apply: Frac.all_vars_mul; apply: fval_ok.
Qed.

Lemma gval_gone : gval PGOne = ∅.
Proof.
rewrite /gval normalize_gone parse_dh_encode_ok //; exact: dh_ok_empty.
Qed.

Lemma gval_ginv t : gval (PGInv t) = dh_opp (gval t).
Proof.
rewrite /gval normalize_ginv parse_dh_encode_ok //.
by apply: dh_ok_opp; apply: gval_ok.
Qed.

Lemma gval_gmul t1 t2 : gval (PGMul t1 t2) = dh_add (gval t1) (gval t2).
Proof.
rewrite /gval normalize_gmul parse_dh_encode_ok //.
by apply: dh_ok_add; apply: gval_ok.
Qed.

Lemma gval_exp t1 t2 : gval (PExp t1 t2) = dh_scale (fval t2) (gval t1).
Proof.
rewrite /gval normalize_exp parse_dh_encode_ok //.
by apply: dh_ok_scale; [apply: fval_ok|apply: gval_ok].
Qed.

Lemma fval_sound x y : fval x = fval y → normalize x = normalize y.
Proof. by move=> e; rewrite normalize_fvalE [normalize y]normalize_fvalE e. Qed.

Lemma gval_sound x y : gval x = gval y → normalize x = normalize y.
Proof. by move=> e; rewrite normalize_gvalE [normalize y]normalize_gvalE e. Qed.

Lemma normalize_PT1 o x1 x2 :
  normalize x1 = normalize x2 → normalize (PT1 o x1) = normalize (PT1 o x2).
Proof. by move=> e; case: o => [kt| | | |] /=; rewrite e. Qed.

Lemma normalize_PT2 o x1 x2 y1 y2 :
  normalize x1 = normalize x2 → normalize y1 = normalize y2 →
  normalize (PT2 o x1 y1) = normalize (PT2 o x2 y2).
Proof. by move=> e1 e2; case: o => /=; rewrite e1 e2. Qed.

Lemma normalize_sound x y : x ∼ y → normalize x = normalize y.
Proof.
elim=> {x y}.
- by [].
- by move=> x y _ ->.
- by move=> x y z _ -> _ ->.
- by move=> o x1 x2 _; apply: normalize_PT1.
- by move=> o x1 x2 y1 y2 _ e1 _ e2; apply: normalize_PT2.
- by move=> x y; apply: fval_sound; rewrite !fval_add; ring.
- by move=> x y z; apply: fval_sound; rewrite !fval_add; ring.
- by move=> x; apply: fval_sound; rewrite fval_add fval_zero; ring.
- by move=> x; apply: fval_sound; rewrite fval_add fval_opp fval_zero; ring.
- by move=> x y; apply: fval_sound; rewrite !fval_mul; ring.
- by move=> x y z; apply: fval_sound; rewrite !fval_mul; ring.
- by move=> x; apply: fval_sound; rewrite fval_mul fval_one; ring.
- move=> x y z; apply: fval_sound.
  by rewrite !fval_mul !fval_add !fval_mul; ring.
- move=> x nx; apply: fval_sound; rewrite fval_mul fval_inv fval_one.
  have nz : fval x ≠ Frac.zero.
    by move=> e; apply: nx; rewrite (fval_sound _ PZero) // e fval_zero.
  by field.
- by apply: fval_sound; rewrite fval_inv fval_zero Frac.inv_zero.
- move=> u v; apply: gval_sound; apply/FMap.fmap_eq => k.
  rewrite !gval_gmul !lookup_dh_add.
  by move: (gval u !!! k) (gval v !!! k) => a b; ring.
- move=> u v w; apply: gval_sound; apply/FMap.fmap_eq => k.
  rewrite !gval_gmul !lookup_dh_add.
  by move: (gval u !!! k) (gval v !!! k) (gval w !!! k) => a b c; ring.
- move=> u; apply: gval_sound; apply/FMap.fmap_eq => k.
  rewrite gval_gmul gval_gone lookup_dh_add FMap.lookup_empty.
  by move: (gval u !!! k) => a; ring.
- move=> u; apply: gval_sound; apply/FMap.fmap_eq => k.
  rewrite gval_gmul gval_ginv gval_gone lookup_dh_add lookup_dh_opp.
  by rewrite FMap.lookup_empty; move: (gval u !!! k) => a; ring.
- move=> g a b; apply: gval_sound; apply/FMap.fmap_eq => k.
  rewrite !gval_exp fval_mul !lookup_dh_scale.
  by move: (gval g !!! k) (fval a) (fval b) => x y z; ring.
- move=> g a b; apply: gval_sound; apply/FMap.fmap_eq => k.
  rewrite gval_gmul !gval_exp fval_add lookup_dh_add !lookup_dh_scale.
  by move: (gval g !!! k) (fval a) (fval b) => x y z; ring.
- move=> g; apply: gval_sound; apply/FMap.fmap_eq => k.
  rewrite gval_exp fval_one lookup_dh_scale.
  by move: (gval g !!! k) => x; ring.
- move=> u v x; apply: gval_sound; apply/FMap.fmap_eq => k.
  rewrite gval_exp !gval_gmul !gval_exp lookup_dh_scale !lookup_dh_add.
  rewrite !lookup_dh_scale.
  by move: (gval u !!! k) (gval v !!! k) (fval x) => a b c; ring.
Qed.

End Values.

(** ** The setoid structure of [∼] *)

#[global] Instance term_equiv_equivalence : Equivalence term_equiv.
Proof. by split; [exact: E_refl|exact: E_sym|exact: E_trans]. Qed.

#[global] Instance PT1_proper o : Proper (term_equiv ==> term_equiv) (PT1 o).
Proof. by move=> ?? e; apply: E_PT1. Qed.

#[global] Instance PT2_proper o :
  Proper (term_equiv ==> term_equiv ==> term_equiv) (PT2 o).
Proof. by move=> ?? e1 ?? e2; apply: E_PT2. Qed.

#[global] Instance flat_is_ring :
  PolyEval.IsRing term_equiv PZero POne PAdd PMul POpp.
Proof.
split.
- exact: E_add_zero.
- exact: E_add_comm.
- by move=> x y z; symmetry; apply: E_add_assoc.
- exact: E_mul_one.
- exact: E_mul_comm.
- by move=> x y z; symmetry; apply: E_mul_assoc.
- exact: E_distr.
- by move=> x y; reflexivity.
- exact: E_add_opp.
Qed.

Lemma flat_rth :
  ring_theory PZero POne PAdd PMul (λ x y, PAdd x (POpp y)) POpp term_equiv.
Proof. exact: flat_is_ring. Qed.

Lemma term_equiv_setoid : Setoid_Theory pre_term term_equiv.
Proof. exact: term_equiv_equivalence. Qed.

Lemma flat_ring_ext : ring_eq_ext PAdd PMul POpp term_equiv.
Proof. by split; apply _. Qed.

Add Ring flat_equiv_ring : flat_rth (setoid term_equiv_setoid flat_ring_ext).

#[global] Instance PGMul_assoc : Assoc term_equiv PGMul.
Proof. by move=> u v w; symmetry; apply: E_gmul_assoc. Qed.
#[global] Instance PGMul_comm : Comm term_equiv PGMul.
Proof. exact: E_gmul_comm. Qed.
#[global] Instance PGMul_left_id : LeftId term_equiv PGOne PGMul.
Proof. exact: E_gmul_one. Qed.

(** ** Field closure: encodings respect the field operations up to [∼] *)

Section FieldClosure.

Implicit Types (x : pre_term) (p P Q : Poly.poly pre_term).
Implicit Types (r : frac) (a b c d w : pre_term).

Abbreviation peval := (PolyEval.eval PZero POne PAdd PMul POpp id).

Lemma fold_tree_foldr o u (l : list pre_term) :
  (∀ x, PT2 o x u ∼ x) → fold_tree (PT2 o) u l ∼ foldr (PT2 o) u l.
Proof.
move=> ru; case: l => [|t l] /=; first reflexivity.
elim: l t => [|t' l IH] t /=; first by symmetry; apply: ru.
by rewrite IH; reflexivity.
Qed.

Lemma foldr_equiv {A} o u (f g : A → pre_term) (l : list A) :
  (∀ y, y ∈ l → f y ∼ g y) →
  foldr (PT2 o) u (f <$> l) ∼ foldr (PT2 o) u (g <$> l).
Proof.
elim: l => [|y l IH] h /=; first reflexivity.
rewrite (h y (list_elem_of_here _ _)) IH; first reflexivity.
by move=> z zl; apply: h; apply: list_elem_of_further.
Qed.

Lemma encode_mono_eval M :
  encode_mono M ∼ PolyEval.mono_eval POne PMul id M.
Proof.
rewrite /encode_mono /PolyEval.mono_eval /PolyEval.fold_op list_fmap_id.
by apply: fold_tree_foldr => x; ring.
Qed.

Lemma encode_sum_eval Ms :
  encode_sum Ms ∼
  PolyEval.fold_op PZero PAdd (PolyEval.mono_eval POne PMul id <$> Ms).
Proof.
rewrite /encode_sum fold_tree_foldr; last by move=> x; ring.
by apply: foldr_equiv => M _; apply: encode_mono_eval.
Qed.

Lemma encode_sum_nil : encode_sum [] = PZero.
Proof. by []. Qed.

Lemma qp_eval p : encode_poly p ∼ peval p.
Proof.
rewrite /PolyEval.eval /PolyEval.ssum /PolyEval.msum -!encode_sum_eval.
rewrite /encode_poly /encode_signed.
case: (elements (SMS.neg _)) => [|n N]; first by rewrite encode_sum_nil; ring.
case: (elements (SMS.pos _)) => [|m M]; last reflexivity.
by rewrite encode_sum_nil; ring.
Qed.

Lemma qp_add p1 p2 : encode_poly (p1 + p2)%P ∼
  PAdd (encode_poly p1) (encode_poly p2).
Proof. rewrite !qp_eval; exact: PolyEval.eval_add. Qed.

Lemma qp_opp p : encode_poly (- p)%P ∼ POpp (encode_poly p).
Proof. rewrite !qp_eval; exact: PolyEval.eval_opp. Qed.

Lemma qp_mul p1 p2 : encode_poly (p1 * p2)%P ∼
  PMul (encode_poly p1) (encode_poly p2).
Proof. rewrite !qp_eval; exact: PolyEval.eval_mul. Qed.

Lemma qp_zero : encode_poly Poly.zero ∼ PZero.
Proof. rewrite qp_eval; exact: PolyEval.eval_zero. Qed.

Lemma qp_one : encode_poly Poly.one ∼ POne.
Proof. rewrite qp_eval; exact: PolyEval.eval_one. Qed.

Lemma qp_cross P1 Q1 P2 Q2 : (P1 * Q2 = P2 * Q1)%P →
  PMul (encode_poly P1) (encode_poly Q2) ∼
  PMul (encode_poly P2) (encode_poly Q1).
Proof. by move=> e; rewrite -!qp_mul e; reflexivity. Qed.

Definition cq r : pre_term :=
  PMul (encode_poly (Frac.num r)) (PInv (encode_poly (Frac.den r))).

Lemma fval_encode_poly p :
  (∀ x, x ∈ Poly.vars p → atom_ok x) → fval (encode_poly p) = Frac.of_poly p.
Proof.
move=> h.
have hf : ∀ x, x ∈ Poly.vars p → is_mod x = false by move=> x /h [].
rewrite /fval normalize_frac_of; first exact: frac_of_encode_poly.
apply: fall_encode_poly => x xp; split=> //; last exact: hf.
by split; [exact: (proj1 (canon_props _ (proj1 (h x xp))))|exact: hf].
Qed.

Lemma fval_neq0 t : fval t ≠ Frac.zero → normalize t ≠ normalize PZero.
Proof. by move=> nz e; apply: nz; rewrite /fval e -/(fval PZero) fval_zero. Qed.

Lemma qp_unit p :
  (∀ x, x ∈ Poly.vars p → atom_ok x) → p ≠ Poly.zero →
  PMul (encode_poly p) (PInv (encode_poly p)) ∼ POne.
Proof.
move=> h np; apply: E_mul_inv; apply: fval_neq0.
rewrite fval_encode_poly // => e; apply: np; apply: Frac.of_poly_inj.
by rewrite e Frac.zeroE.
Qed.

Lemma den_unit r : Frac.all_vars atom_ok r →
  PMul (encode_poly (Frac.den r)) (PInv (encode_poly (Frac.den r))) ∼ POne.
Proof.
move=> /Frac.all_vars_iff h; apply: qp_unit; last exact: Frac.den_neq0.
by move=> x xd; apply: h; apply: vars_den.
Qed.

Lemma num_unit r : Frac.all_vars atom_ok r → r ≠ Frac.zero →
  PMul (encode_poly (Frac.num r)) (PInv (encode_poly (Frac.num r))) ∼ POne.
Proof.
move=> /Frac.all_vars_iff h nr; apply: qp_unit; last exact: Frac.num_neq0.
by move=> x xn; apply: h; apply: vars_num.
Qed.

Lemma one_unit : PMul POne (PInv POne) ∼ POne.
Proof.
apply: E_mul_inv; apply: fval_neq0; rewrite fval_one.
exact: Frac.one_neq0.
Qed.

Lemma inv_one : PInv POne ∼ POne.
Proof.
transitivity (PMul POne (PInv POne)); first by symmetry; apply: E_mul_one.
exact: one_unit.
Qed.

Lemma encode_frac_cq r : mod_of_frac r ∼ cq r.
Proof.
rewrite /mod_of_frac /cq; case: bool_decide_reflect => [e|_]; last reflexivity.
by rewrite e qp_one inv_one; ring.
Qed.

Lemma frac_cross a b w c d :
  PMul b w ∼ POne → PMul d (PInv d) ∼ POne →
  PMul a d ∼ PMul c b → PMul a w ∼ PMul c (PInv d).
Proof.
move=> bw dd e.
transitivity (PMul (PMul a w) (PMul d (PInv d))); first by rewrite dd; ring.
transitivity (PMul (PMul a d) (PMul w (PInv d))); first ring.
rewrite e.
transitivity (PMul (PMul c (PInv d)) (PMul b w)); first ring.
by rewrite bw; ring.
Qed.

Lemma cq_make P Q a w :
  Frac.all_vars atom_ok (Frac.make P Q) → Q ≠ Poly.zero →
  a ∼ encode_poly P → PMul (encode_poly Q) w ∼ POne →
  PMul a w ∼ cq (Frac.make P Q).
Proof.
move=> h nQ aP Qw; rewrite aP /cq.
apply: frac_cross Qw (den_unit _ h) _.
by apply: qp_cross; symmetry; apply: Frac.make_spec.
Qed.

Lemma inv_unit2 b1 b2 :
  PMul b1 (PInv b1) ∼ POne → PMul b2 (PInv b2) ∼ POne →
  PMul (PMul b1 b2) (PMul (PInv b1) (PInv b2)) ∼ POne.
Proof.
move=> u1 u2.
transitivity (PMul (PMul b1 (PInv b1)) (PMul b2 (PInv b2))); first ring.
by rewrite u1 u2; ring.
Qed.

Lemma cq_add r1 r2 : Frac.all_vars atom_ok r1 → Frac.all_vars atom_ok r2 →
  PAdd (cq r1) (cq r2) ∼ cq (Frac.add r1 r2).
Proof.
move=> h1 h2; have := Frac.all_vars_add _ _ _ h1 h2; rewrite Frac.addE => h3.
have u1 := den_unit r1 h1; have u2 := den_unit r2 h2.
rewrite [cq r1]/cq [cq r2]/cq.
set b1 := encode_poly (Frac.den r1) in u1 *.
set b2 := encode_poly (Frac.den r2) in u2 *.
transitivity
  (PMul (PAdd (PMul (encode_poly (Frac.num r1)) b2)
              (PMul (encode_poly (Frac.num r2)) b1))
        (PMul (PInv b1) (PInv b2))).
  transitivity
    (PAdd (PMul (PMul (encode_poly (Frac.num r1)) (PInv b1))
                (PMul b2 (PInv b2)))
          (PMul (PMul (encode_poly (Frac.num r2)) (PInv b2))
                (PMul b1 (PInv b1)))).
    by rewrite u1 u2; ring.
  ring.
apply: cq_make => //.
- exact: PolyGcd.mul_neq0 (Frac.den_neq0 r1) (Frac.den_neq0 r2).
- by rewrite qp_add !qp_mul; reflexivity.
- by rewrite qp_mul; apply: inv_unit2.
Qed.

Lemma cq_mul r1 r2 : Frac.all_vars atom_ok r1 → Frac.all_vars atom_ok r2 →
  PMul (cq r1) (cq r2) ∼ cq (Frac.mul r1 r2).
Proof.
move=> h1 h2; have := Frac.all_vars_mul _ _ _ h1 h2; rewrite Frac.mulE => h3.
have u1 := den_unit r1 h1; have u2 := den_unit r2 h2.
rewrite [cq r1]/cq [cq r2]/cq.
transitivity
  (PMul (PMul (encode_poly (Frac.num r1)) (encode_poly (Frac.num r2)))
        (PMul (PInv (encode_poly (Frac.den r1)))
              (PInv (encode_poly (Frac.den r2))))).
  ring.
apply: cq_make => //.
- exact: PolyGcd.mul_neq0 (Frac.den_neq0 r1) (Frac.den_neq0 r2).
- by rewrite qp_mul; reflexivity.
- by rewrite qp_mul; apply: inv_unit2.
Qed.

Lemma cq_opp r : POpp (cq r) ∼ cq (Frac.opp r).
Proof. by rewrite /cq Frac.num_opp Frac.den_opp qp_opp; ring. Qed.

Lemma fval_cq r : Frac.all_vars atom_ok r → fval (cq r) = r.
Proof.
move=> /Frac.all_vars_iff h.
rewrite /cq fval_mul fval_inv !fval_encode_poly; first last.
- by move=> x xv; apply: h; apply: vars_num.
- by move=> x xv; apply: h; apply: vars_den.
by rewrite -Frac.divE -Frac.make_div Frac.make_num_den.
Qed.

Lemma cq_inv r : Frac.all_vars atom_ok r → PInv (cq r) ∼ cq (Frac.inv r).
Proof.
move=> h; case: (decide (r = Frac.zero)) => [->|nr].
  rewrite Frac.inv_zero /cq Frac.num_zero Frac.den_zero qp_zero qp_one inv_one.
  transitivity (PInv PZero); first by apply: E_PT1; ring.
  by rewrite E_inv_zero; ring.
have := Frac.all_vars_inv _ _ h; rewrite Frac.invE => h3.
have ua := num_unit r h nr; have ub := den_unit r h.
have uc : PMul (cq r) (PInv (cq r)) ∼ POne.
  by apply: E_mul_inv; apply: fval_neq0; rewrite fval_cq.
transitivity
  (PMul (encode_poly (Frac.den r)) (PInv (encode_poly (Frac.num r))));
  last first.
  by apply: cq_make; [exact: h3|exact: Frac.num_neq0|reflexivity|exact: ua].
transitivity
  (PMul (PInv (cq r))
        (PMul (PMul (encode_poly (Frac.num r))
                    (PInv (encode_poly (Frac.num r))))
              (PMul (encode_poly (Frac.den r))
                    (PInv (encode_poly (Frac.den r)))))).
  by rewrite ua ub; ring.
transitivity
  (PMul (PMul (cq r) (PInv (cq r)))
        (PMul (encode_poly (Frac.den r)) (PInv (encode_poly (Frac.num r))))).
  by rewrite [cq r]/cq; ring.
by rewrite uc; ring.
Qed.

Lemma ef_add r1 r2 : Frac.all_vars atom_ok r1 → Frac.all_vars atom_ok r2 →
  PAdd (mod_of_frac r1) (mod_of_frac r2) ∼ mod_of_frac (Frac.add r1 r2).
Proof. by move=> h1 h2; rewrite !encode_frac_cq; apply: cq_add. Qed.

Lemma ef_mul r1 r2 : Frac.all_vars atom_ok r1 → Frac.all_vars atom_ok r2 →
  PMul (mod_of_frac r1) (mod_of_frac r2) ∼ mod_of_frac (Frac.mul r1 r2).
Proof. by move=> h1 h2; rewrite !encode_frac_cq; apply: cq_mul. Qed.

Lemma ef_opp r : POpp (mod_of_frac r) ∼ mod_of_frac (Frac.opp r).
Proof. by rewrite !encode_frac_cq; apply: cq_opp. Qed.

Lemma ef_inv r : Frac.all_vars atom_ok r →
  PInv (mod_of_frac r) ∼ mod_of_frac (Frac.inv r).
Proof. by move=> h; rewrite !encode_frac_cq; apply: cq_inv. Qed.

End FieldClosure.

(** ** Group closure: encodings respect the group operations up to [∼] *)

Definition gprod_keys (K : list pre_term) (f : pre_term → frac) : pre_term :=
  PolyEval.fold_op PGOne PGMul ((λ k, PExp k (mod_of_frac (f k))) <$> K).

Definition supp (m : dhmap) : list pre_term := (FMap.to_list m).*1.

Section GroupClosure.

Implicit Types (x : pre_term) (m : dhmap) (K : list pre_term) (r : frac).
Implicit Types (f g h : pre_term → frac) (v b : pre_term).

Add Ring flat_frac_ring3 : (Frac.frac_ring_theory (T := pre_term)).

Lemma gmul_one_r u : PGMul u PGOne ∼ u.
Proof. by rewrite E_gmul_comm; apply: E_gmul_one. Qed.

Lemma ginv_unique u v : PGMul u v ∼ PGOne → v ∼ PGInv u.
Proof.
move=> uv; rewrite -(E_gmul_one v) -(E_gmul_inv u).
rewrite (E_gmul_comm u) E_gmul_assoc uv; exact: gmul_one_r.
Qed.

Lemma gmul_idem u : PGMul u u ∼ u → u ∼ PGOne.
Proof.
move=> uu; symmetry; transitivity (PGMul (PGMul u u) (PGInv u)).
  by rewrite uu; symmetry; apply: E_gmul_inv.
rewrite E_gmul_assoc E_gmul_inv; exact: gmul_one_r.
Qed.

Lemma ginv_one : PGInv PGOne ∼ PGOne.
Proof. by symmetry; apply: ginv_unique; apply: E_gmul_one. Qed.

Lemma ginv_mul u v : PGInv (PGMul u v) ∼ PGMul (PGInv u) (PGInv v).
Proof.
symmetry; apply: ginv_unique.
transitivity (PGMul (PGMul u (PGInv u)) (PGMul v (PGInv v))).
  exact: (PolyEval.mop_interchange (mop := PGMul)).
by rewrite !E_gmul_inv; apply: E_gmul_one.
Qed.

Lemma exp_zero b : PExp b PZero ∼ PGOne.
Proof. by apply: gmul_idem; rewrite E_exp_add E_add_zero; reflexivity. Qed.

Lemma exp_opp b a : PGInv (PExp b a) ∼ PExp b (POpp a).
Proof.
symmetry; apply: ginv_unique.
by rewrite E_exp_add E_add_opp; apply: exp_zero.
Qed.

Lemma gone_exp a : PExp PGOne a ∼ PGOne.
Proof. by apply: gmul_idem; rewrite -E_exp_gmul E_gmul_one; reflexivity. Qed.

Lemma gprod_keys_cons k K f :
  gprod_keys (k :: K) f = PGMul (PExp k (mod_of_frac (f k))) (gprod_keys K f).
Proof. by []. Qed.

Lemma gprod_keys_ext K f g :
  (∀ k, k ∈ K → f k = g k) → gprod_keys K f = gprod_keys K g.
Proof.
elim: K => [|k K IH] e //.
rewrite !gprod_keys_cons (e k (list_elem_of_here _ _)).
by rewrite (IH (λ k' kK, e k' (list_elem_of_further _ _ _ kK))).
Qed.

Lemma gprod_keys_mul K f g h :
  (∀ k, Frac.all_vars atom_ok (f k)) → (∀ k, Frac.all_vars atom_ok (g k)) →
  (∀ k, h k = Frac.add (f k) (g k)) →
  PGMul (gprod_keys K f) (gprod_keys K g) ∼ gprod_keys K h.
Proof.
move=> hf hg eh; elim: K => [|k K IH]; first exact: E_gmul_one.
rewrite !gprod_keys_cons -IH eh -(ef_add _ _ (hf k) (hg k)) -E_exp_add.
exact: (PolyEval.mop_interchange (mop := PGMul)).
Qed.

Lemma gprod_keys_inv K f h :
  (∀ k, h k = Frac.opp (f k)) → PGInv (gprod_keys K f) ∼ gprod_keys K h.
Proof.
move=> eh; elim: K => [|k K IH]; first exact: ginv_one.
rewrite !gprod_keys_cons ginv_mul IH eh -ef_opp exp_opp; reflexivity.
Qed.

Lemma gprod_keys_exp K f r h :
  (∀ k, Frac.all_vars atom_ok (f k)) → Frac.all_vars atom_ok r →
  (∀ k, h k = Frac.mul (f k) r) →
  PExp (gprod_keys K f) (mod_of_frac r) ∼ gprod_keys K h.
Proof.
move=> hf hr eh; elim: K => [|k K IH]; first exact: gone_exp.
rewrite !gprod_keys_cons E_exp_gmul IH E_exp_exp eh -(ef_mul _ _ (hf k) hr).
reflexivity.
Qed.

Lemma encode_dh_gprod m : dh_of m ∼ gprod_keys (supp m) (λ k, m !!! k).
Proof.
rewrite /dh_of /gprod_keys /supp fold_tree_foldr; last exact: gmul_one_r.
rewrite /PolyEval.fold_op -list_fmap_compose.
apply: foldr_equiv => [[k v]] /FMap.elem_of_to_list [kv nv].
rewrite /mk_exp /=; case: bool_decide_reflect => [e|_].
  by rewrite kv e mod_of_frac_one E_exp_one; reflexivity.
by rewrite kv; reflexivity.
Qed.

Lemma elem_of_supp m k : k ∈ supp m ↔ m !!! k ≠ Frac.zero.
Proof.
rewrite /supp list_elem_of_fmap; split.
- by move=> [[k' v] [/= -> /FMap.elem_of_to_list [-> ?]]].
- move=> nk; exists (k, m !!! k); split=> //.
  exact/FMap.elem_of_to_list.
Qed.

Lemma NoDup_supp m : NoDup (supp m).
Proof.
rewrite /supp; elim: (FMap.to_list_sorted m) => [|k l _ IH kl].
  exact: NoDup_nil_2.
apply: NoDup_cons_2 => // kl'.
exact: (FMap.lexico_neq _ _ (proj1 (list.Forall_forall _ _) kl k kl') eq_refl).
Qed.

Lemma encode_dh_sub m K f :
  NoDup K → (∀ k, m !!! k ≠ Frac.zero → k ∈ K) → (∀ k, f k = m !!! k) →
  dh_of m ∼ gprod_keys K f.
Proof.
move=> nK hK ef.
have [R eR] : ∃ R, K ≡ₚ supp m ++ R.
  apply: submseteq_Permutation; apply: NoDup_submseteq; first exact: NoDup_supp.
  by move=> k /elem_of_supp; apply: hK.
have hR : ∀ k, k ∈ R → f k = Frac.zero.
  move=> k kR; rewrite ef.
  case: (decide (m !!! k = Frac.zero)) => // nk.
  have : NoDup (supp m ++ R) by rewrite -eR.
  move=> /NoDup_app [_ [/(_ k) hk _]].
  by case: (hk (proj2 (elem_of_supp m k) nk) kR).
have E1 : gprod_keys K f ∼ PGMul (gprod_keys (supp m) f) (gprod_keys R f).
  rewrite /gprod_keys -PolyEval.fold_op_app -fmap_app.
  apply: PolyEval.fold_op_perm; exact: fmap_Permutation.
have E2 : gprod_keys R f ∼ PGOne.
  rewrite /gprod_keys; apply: PolyEval.fold_op_unit.
  move=> u /list_elem_of_fmap [k [-> kR]].
  by rewrite hR // mod_of_frac_zero; apply: exp_zero.
rewrite E1 E2 gmul_one_r encode_dh_gprod.
rewrite (gprod_keys_ext _ f (λ k, m !!! k) (λ k _, ef k)); reflexivity.
Qed.

Lemma encode_dh_zero m : (∀ k, m !!! k = Frac.zero) → PGOne ∼ dh_of m.
Proof.
move=> z; symmetry; apply: (encode_dh_sub m [] (λ k, m !!! k)) => //.
- exact: NoDup_nil_2.
- by move=> k; rewrite z.
Qed.

Lemma ed_mul m1 m2 m3 : dh_ok m1 → dh_ok m2 →
  (∀ k, m3 !!! k = Frac.add (m1 !!! k) (m2 !!! k)) →
  PGMul (dh_of m1) (dh_of m2) ∼ dh_of m3.
Proof.
move=> [_ h1] [_ h2] e3.
have [K [nK eK]] : ∃ K, NoDup K ∧ ∀ k, k ∈ K ↔ k ∈ supp m1 ++ supp m2.
  exists (remove_dups (supp m1 ++ supp m2)).
  by split; [apply: NoDup_remove_dups|move=> k; apply: elem_of_remove_dups].
have inK m : (∀ k, m !!! k ≠ Frac.zero →
               m1 !!! k ≠ Frac.zero ∨ m2 !!! k ≠ Frac.zero) →
    ∀ k, m !!! k ≠ Frac.zero → k ∈ K.
  move=> hm k nk; rewrite eK elem_of_app !elem_of_supp.
  exact: hm k nk.
transitivity
  (PGMul (gprod_keys K (λ k, m1 !!! k)) (gprod_keys K (λ k, m2 !!! k))).
  apply: E_PT2; apply: encode_dh_sub => //.
  - by apply: inK => k nk; left.
  - by apply: inK => k nk; right.
transitivity (gprod_keys K (λ k, m3 !!! k)); first exact: gprod_keys_mul.
symmetry; apply: encode_dh_sub => //.
apply: inK => k nk.
case: (decide (m1 !!! k = Frac.zero)) => [z1|n1]; last by left.
by right => z2; apply: nk; rewrite e3 z1 z2; ring.
Qed.

Lemma ed_inv m1 m3 : (∀ k, m3 !!! k = Frac.opp (m1 !!! k)) →
  PGInv (dh_of m1) ∼ dh_of m3.
Proof.
move=> e3.
have sub : ∀ k, m3 !!! k ≠ Frac.zero → k ∈ supp m1.
  move=> k nk; apply/elem_of_supp => z1; apply: nk.
  by rewrite e3 z1 Frac.opp_zero.
rewrite encode_dh_gprod (gprod_keys_inv _ _ (λ k, m3 !!! k) e3).
by symmetry; apply: encode_dh_sub => //; apply: NoDup_supp.
Qed.

Lemma ed_exp m1 r m3 : dh_ok m1 → Frac.all_vars atom_ok r →
  (∀ k, m3 !!! k = Frac.mul (m1 !!! k) r) →
  PExp (dh_of m1) (mod_of_frac r) ∼ dh_of m3.
Proof.
move=> [_ h1] hr e3.
have sub : ∀ k, m3 !!! k ≠ Frac.zero → k ∈ supp m1.
  move=> k nk; apply/elem_of_supp => z1; apply: nk.
  by rewrite e3 z1 Frac.mul_zero_l.
rewrite encode_dh_gprod (gprod_keys_exp _ _ _ (λ k, m3 !!! k) h1 hr e3).
by symmetry; apply: encode_dh_sub => //; apply: NoDup_supp.
Qed.

End GroupClosure.

(** ** Completeness *)

Lemma term_equiv_normalize x : x ∼ normalize x.
Proof.
elim: x => [o|o x IH|o x1 IH1 x2 IH2].
- case: o => [n|a| | |]; try reflexivity.
  + by rewrite normalize_zero mod_of_frac_zero; reflexivity.
  + by rewrite normalize_one mod_of_frac_one; reflexivity.
  + rewrite normalize_gone; apply: encode_dh_zero => k.
    exact: FMap.lookup_empty.
- transitivity (PT1 o (normalize x)); first exact: E_PT1.
  case: o => [kt| | | |]; try reflexivity.
  + by rewrite normalize_opp {1}normalize_fvalE; apply: ef_opp.
  + by rewrite normalize_inv {1}normalize_fvalE; apply: ef_inv; apply: fval_ok.
  + rewrite normalize_ginv {1}normalize_gvalE; apply: ed_inv => k.
    exact: lookup_dh_opp.
- transitivity (PT2 o (normalize x1) (normalize x2)); first exact: E_PT2.
  case: o => [| | | | |]; try reflexivity.
  + rewrite normalize_add {1}normalize_fvalE {1}normalize_fvalE.
    by apply: ef_add; apply: fval_ok.
  + rewrite normalize_mul {1}normalize_fvalE {1}normalize_fvalE.
    by apply: ef_mul; apply: fval_ok.
  + rewrite normalize_gmul {1}normalize_gvalE {1}normalize_gvalE.
    apply: ed_mul; [exact: gval_ok|exact: gval_ok|] => k.
    exact: lookup_dh_add.
  + rewrite normalize_exp {1}normalize_gvalE {1}normalize_fvalE.
    apply: ed_exp; [exact: gval_ok|exact: fval_ok|] => k.
    exact: lookup_dh_scale.
Qed.

Theorem normalize_equiv x y : x ∼ y ↔ normalize x = normalize y.
Proof.
split; first exact: normalize_sound.
move=> e; transitivity (normalize x); first exact: term_equiv_normalize.
by rewrite e; symmetry; apply: term_equiv_normalize.
Qed.


(** ** Terms *)

Theorem term_equiv_iff x y : x ∼ y ↔ fold_term x = fold_term y.
Proof.
rewrite normalize_equiv; split; first by move=> e; rewrite -fold_normalize e
  fold_normalize.
by move=> /(f_equal unfold_term); rewrite !unfold_fold.
Qed.

Corollary fold_term_surj (t : term) : ∃ x, fold_term x = t.
Proof. by exists (unfold_term t); exact: unfold_termK. Qed.
