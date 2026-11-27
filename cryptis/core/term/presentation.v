(** An equational presentation of terms

    [term'] is a free syntax for terms where every operation is a
    constructor: one neutral element, one product and one inverse for the
    Diffie-Hellman group, the field operations for exponents and
    exponentiation.  [i] interprets it in [term], and [x ∼ y] is the least
    congruence satisfying the laws of a field for exponents, of an abelian
    group for [⋅], and of exponentiation as a module action:

    - [(g ^ a) ^ b ∼ g ^ (a · b)]
    - [g ^ a ⋅ g ^ b ∼ g ^ (a + b)]
    - [g ^ 1 ∼ g]
    - [(u ⋅ v) ^ x ∼ u ^ x ⋅ v ^ x]

    The main result is [term_equiv_iff]: [x ∼ y ↔ i x = i y].  Since [i] is
    onto ([i_surj]), [term] is [term'] modulo [∼].  The inverse law
    [x · x⁻¹ ∼ 1] is stated for the [x] whose interpretation is nonzero:
    exponents are rational functions in their atoms, and no equational axiom
    derives [(x + 1) · (x + 1)⁻¹ = 1], which fails in ℚ when [x = -1].

    Completeness goes through a quotation [q] of normal forms
    ([i_q : i (q t) = t]): every [x] is equivalent to [q (i x)]
    ([term_equiv_q]), because quotations of fractions and of Diffie-Hellman
    maps respect the operations up to [∼]. *)

From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith Lia Ring Field Setoid Morphisms.
From stdpp Require Import gmap sorting.
From cryptis.lib Require Import fmap mset sms poly poly_gcd frac poly_eval.
From cryptis.core Require Import term.

Inductive term' :=
| TInt' of Z
| TPair' of term' & term'
| TNonce' of nonce
| TKey' of key_type & term'
| TSeal' of term' & term'
| THash' of term'
| TZero'
| TOne'
| TAdd' of term' & term'
| TOpp' of term'
| TMul' of term' & term'
| TInv' of term'
| TGOne'
| TGMul' of term' & term'
| TGInv' of term'
| TExp' of term' & term'.

Fixpoint i (x : term') : term :=
  match x with
  | TInt' n => TInt n
  | TPair' x y => TPair (i x) (i y)
  | TNonce' a => TNonce a
  | TKey' kt x => TKey kt (i x)
  | TSeal' x y => TSeal (i x) (i y)
  | THash' x => THash (i x)
  | TZero' => TSum ∅
  | TOne' => TMul ∅
  | TAdd' x y => TSum {[+ i x; i y +]}
  | TOpp' x => TSum (SMS.inv {[+ i x +]})
  | TMul' x y => TMul {[+ i x; i y +]}
  | TInv' x => TInv (i x)
  | TGOne' => TGMul ∅
  | TGMul' x y => TGMul {[+ i x; i y +]}
  | TGInv' x => TGInv (i x)
  | TExp' x y => TExp (i x) (i y)
  end.

Reserved Notation "x ∼ y" (at level 70).

Inductive term_equiv : term' → term' → Prop :=
| E_refl x : x ∼ x
| E_sym x y : x ∼ y → y ∼ x
| E_trans x y z : x ∼ y → y ∼ z → x ∼ z
| E_pair x1 x2 y1 y2 : x1 ∼ x2 → y1 ∼ y2 → TPair' x1 y1 ∼ TPair' x2 y2
| E_key kt x1 x2 : x1 ∼ x2 → TKey' kt x1 ∼ TKey' kt x2
| E_seal x1 x2 y1 y2 : x1 ∼ x2 → y1 ∼ y2 → TSeal' x1 y1 ∼ TSeal' x2 y2
| E_hash x1 x2 : x1 ∼ x2 → THash' x1 ∼ THash' x2
| E_add x1 x2 y1 y2 : x1 ∼ x2 → y1 ∼ y2 → TAdd' x1 y1 ∼ TAdd' x2 y2
| E_opp x1 x2 : x1 ∼ x2 → TOpp' x1 ∼ TOpp' x2
| E_mul x1 x2 y1 y2 : x1 ∼ x2 → y1 ∼ y2 → TMul' x1 y1 ∼ TMul' x2 y2
| E_inv x1 x2 : x1 ∼ x2 → TInv' x1 ∼ TInv' x2
| E_gmul x1 x2 y1 y2 : x1 ∼ x2 → y1 ∼ y2 → TGMul' x1 y1 ∼ TGMul' x2 y2
| E_ginv x1 x2 : x1 ∼ x2 → TGInv' x1 ∼ TGInv' x2
| E_exp x1 x2 y1 y2 : x1 ∼ x2 → y1 ∼ y2 → TExp' x1 y1 ∼ TExp' x2 y2
| E_add_comm x y : TAdd' x y ∼ TAdd' y x
| E_add_assoc x y z : TAdd' (TAdd' x y) z ∼ TAdd' x (TAdd' y z)
| E_add_zero x : TAdd' TZero' x ∼ x
| E_add_opp x : TAdd' x (TOpp' x) ∼ TZero'
| E_mul_comm x y : TMul' x y ∼ TMul' y x
| E_mul_assoc x y z : TMul' (TMul' x y) z ∼ TMul' x (TMul' y z)
| E_mul_one x : TMul' TOne' x ∼ x
| E_distr x y z : TMul' (TAdd' x y) z ∼ TAdd' (TMul' x z) (TMul' y z)
| E_mul_inv x : i x ≠ i TZero' → TMul' x (TInv' x) ∼ TOne'
| E_inv_zero : TInv' TZero' ∼ TZero'
| E_gmul_comm u v : TGMul' u v ∼ TGMul' v u
| E_gmul_assoc u v w : TGMul' (TGMul' u v) w ∼ TGMul' u (TGMul' v w)
| E_gmul_one u : TGMul' TGOne' u ∼ u
| E_gmul_inv u : TGMul' u (TGInv' u) ∼ TGOne'
| E_exp_exp g a b : TExp' (TExp' g a) b ∼ TExp' g (TMul' a b)
| E_exp_add g a b : TGMul' (TExp' g a) (TExp' g b) ∼ TExp' g (TAdd' a b)
| E_exp_one g : TExp' g TOne' ∼ g
| E_exp_gmul u v x : TExp' (TGMul' u v) x ∼ TGMul' (TExp' u x) (TExp' v x)
where "x ∼ y" := (term_equiv x y).

(** ** Soundness *)

Section Soundness.

Add Ring frac_ring : (Frac.frac_ring_theory (T := term)).
Add Field frac_field : (Frac.frac_field_theory (T := term)).
Add Ring pfrac_ring : (Frac.frac_ring_theory (T := PreTerm.pre_term)).

Lemma frac_of_TSum2 t1 t2 :
  frac_of (TSum {[+ t1; t2 +]}) = Frac.add (frac_of t1) (frac_of t2).
Proof. by rewrite frac_of_TSum Frac.ssum_disj_union !Frac.ssum_singleton. Qed.

Lemma frac_of_TSum_opp t :
  frac_of (TSum (SMS.inv {[+ t +]})) = Frac.opp (frac_of t).
Proof. by rewrite frac_of_TSum Frac.ssum_inv Frac.ssum_singleton. Qed.

Lemma dh_map_TGMul2 t1 t2 k :
  dh_map (TGMul {[+ t1; t2 +]}) !!! k =
  Frac.add (dh_map t1 !!! k) (dh_map t2 !!! k).
Proof.
by rewrite dh_map_TGMul Frac.ssum_disj_union !Frac.ssum_singleton.
Qed.

Lemma dh_map_TGInv t k : dh_map (TGInv t) !!! k = Frac.opp (dh_map t !!! k).
Proof. by rewrite dh_map_TGMul Frac.ssum_inv Frac.ssum_singleton. Qed.

Lemma i_sound x y : x ∼ y → i x = i y.
Proof.
elim=> {x y} /=.
- by [].
- by move=> x y _ ->.
- by move=> x y z _ -> _ ->.
- by move=> x1 x2 y1 y2 _ -> _ ->.
- by move=> kt x1 x2 _ ->.
- by move=> x1 x2 y1 y2 _ -> _ ->.
- by move=> x1 x2 _ ->.
- by move=> x1 x2 y1 y2 _ -> _ ->.
- by move=> x1 x2 _ ->.
- by move=> x1 x2 y1 y2 _ -> _ ->.
- by move=> x1 x2 _ ->.
- by move=> x1 x2 y1 y2 _ -> _ ->.
- by move=> x1 x2 _ ->.
- by move=> x1 x2 y1 y2 _ -> _ ->.
- by move=> x y; apply: frac_of_inj; rewrite !frac_of_TSum2; ring.
- by move=> x y z; apply: frac_of_inj; rewrite !frac_of_TSum2; ring.
- move=> x; apply: frac_of_inj.
  by rewrite frac_of_TSum2 frac_of_TSum_empty; ring.
- move=> x; apply: frac_of_inj.
  by rewrite frac_of_TSum2 frac_of_TSum_opp frac_of_TSum_empty; ring.
- by move=> x y; apply: frac_of_inj; rewrite !frac_of_TMul2; ring.
- by move=> x y z; apply: frac_of_inj; rewrite !frac_of_TMul2; ring.
- move=> x; apply: frac_of_inj.
  by rewrite frac_of_TMul2 frac_of_TMul_empty; ring.
- move=> x y z; apply: frac_of_inj.
  by rewrite !frac_of_TMul2 !frac_of_TSum2 !frac_of_TMul2; ring.
- move=> x nx; apply: frac_of_inj.
  rewrite frac_of_TMul2 frac_of_TInv frac_of_TMul_empty.
  have nf : frac_of (i x) ≠ Frac.zero by move=> /frac_of_eq0.
  by field.
- by apply: frac_of_inj; rewrite frac_of_TInv frac_of_TSum_empty Frac.inv_zero.
- move=> u v; apply: dh_map_inj; apply/FMap.fmap_eq => k.
  rewrite !dh_map_TGMul2.
  by move: (dh_map (i u) !!! k) (dh_map (i v) !!! k) => a b; ring.
- move=> u v w; apply: dh_map_inj; apply/FMap.fmap_eq => k.
  rewrite !dh_map_TGMul2.
  move: (dh_map (i u) !!! k) (dh_map (i v) !!! k) => a b.
  by move: (dh_map (i w) !!! k) => c; ring.
- move=> u; apply: dh_map_inj; apply/FMap.fmap_eq => k.
  rewrite dh_map_TGMul2 dh_map_TGMul_empty.
  by move: (dh_map (i u) !!! k) => a; ring.
- move=> u; apply: dh_map_inj; apply/FMap.fmap_eq => k.
  rewrite dh_map_TGMul2 dh_map_TGInv dh_map_TGMul_empty.
  by move: (dh_map (i u) !!! k) => a; ring.
- by move=> g a b; rewrite TExpA.
- by move=> g a b; rewrite TExp_TSum2.
- by move=> g; rewrite TExp_unit.
- by move=> u v x; rewrite TExp_TGMul SMS.map_disj_union !SMS.map_singleton.
Qed.

End Soundness.

(** ** The setoid structure of [∼] *)

#[global] Instance term_equiv_equivalence : Equivalence term_equiv.
Proof. by split; [exact: E_refl|exact: E_sym|exact: E_trans]. Qed.

#[global] Instance TPair'_proper :
  Proper (term_equiv ==> term_equiv ==> term_equiv) TPair'.
Proof. by move=> ?? e1 ?? e2; apply: E_pair. Qed.
#[global] Instance TKey'_proper kt :
  Proper (term_equiv ==> term_equiv) (TKey' kt).
Proof. by move=> ?? e; apply: E_key. Qed.
#[global] Instance TSeal'_proper :
  Proper (term_equiv ==> term_equiv ==> term_equiv) TSeal'.
Proof. by move=> ?? e1 ?? e2; apply: E_seal. Qed.
#[global] Instance THash'_proper : Proper (term_equiv ==> term_equiv) THash'.
Proof. by move=> ?? e; apply: E_hash. Qed.
#[global] Instance TAdd'_proper :
  Proper (term_equiv ==> term_equiv ==> term_equiv) TAdd'.
Proof. by move=> ?? e1 ?? e2; apply: E_add. Qed.
#[global] Instance TOpp'_proper : Proper (term_equiv ==> term_equiv) TOpp'.
Proof. by move=> ?? e; apply: E_opp. Qed.
#[global] Instance TMul'_proper :
  Proper (term_equiv ==> term_equiv ==> term_equiv) TMul'.
Proof. by move=> ?? e1 ?? e2; apply: E_mul. Qed.
#[global] Instance TInv'_proper : Proper (term_equiv ==> term_equiv) TInv'.
Proof. by move=> ?? e; apply: E_inv. Qed.
#[global] Instance TGMul'_proper :
  Proper (term_equiv ==> term_equiv ==> term_equiv) TGMul'.
Proof. by move=> ?? e1 ?? e2; apply: E_gmul. Qed.
#[global] Instance TGInv'_proper : Proper (term_equiv ==> term_equiv) TGInv'.
Proof. by move=> ?? e; apply: E_ginv. Qed.
#[global] Instance TExp'_proper :
  Proper (term_equiv ==> term_equiv ==> term_equiv) TExp'.
Proof. by move=> ?? e1 ?? e2; apply: E_exp. Qed.

#[global] Instance term'_is_ring :
  PolyEval.IsRing term_equiv TZero' TOne' TAdd' TMul' TOpp'.
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

Lemma term'_rth :
  ring_theory TZero' TOne' TAdd' TMul' (λ x y, TAdd' x (TOpp' y)) TOpp'
    term_equiv.
Proof. exact: term'_is_ring. Qed.

Lemma term_equiv_setoid : Setoid_Theory term' term_equiv.
Proof. exact: term_equiv_equivalence. Qed.

Lemma term'_ring_ext : ring_eq_ext TAdd' TMul' TOpp' term_equiv.
Proof. by split; apply _. Qed.

Add Ring term'_ring : term'_rth (setoid term_equiv_setoid term'_ring_ext).

#[global] Instance TGMul'_assoc : Assoc term_equiv TGMul'.
Proof. by move=> u v w; symmetry; apply: E_gmul_assoc. Qed.
#[global] Instance TGMul'_comm : Comm term_equiv TGMul'.
Proof. exact: E_gmul_comm. Qed.
#[global] Instance TGMul'_left_id : LeftId term_equiv TGOne' TGMul'.
Proof. exact: E_gmul_one. Qed.

(** ** Quotation of normal forms *)

Definition qmono (qa : PreTerm.pre_term → term') (m : list PreTerm.pre_term) :
    term' :=
  PolyEval.fold_op TOne' TMul' (map qa m).

Definition qsum (qa : PreTerm.pre_term → term') (ms : PreTerm.monos) : term' :=
  PolyEval.fold_op TZero' TAdd' (map (qmono qa) ms).

Definition qpoly (qa : PreTerm.pre_term → term') (A : PreTerm.poly_lists) :
    term' :=
  TAdd' (qsum qa A.1) (TOpp' (qsum qa A.2)).

Definition qfrac (qa : PreTerm.pre_term → term') (F : PreTerm.frac_lists) :
    term' :=
  TMul' (qpoly qa F.1) (TInv' (qpoly qa F.2)).

Definition gprod (l : list term') : term' := PolyEval.fold_op TGOne' TGMul' l.

Fixpoint qpt (pt : PreTerm.pre_term) : term' :=
  match pt with
  | PreTerm.PT0 (O0Int n) => TInt' n
  | PreTerm.PT0 (O0Nonce a) => TNonce' a
  | PreTerm.PT1 (O1Key kt) t => TKey' kt (qpt t)
  | PreTerm.PT1 O1Hash t => THash' (qpt t)
  | PreTerm.PT2 O2Pair t1 t2 => TPair' (qpt t1) (qpt t2)
  | PreTerm.PT2 O2Seal t1 t2 => TSeal' (qpt t1) (qpt t2)
  | PreTerm.PTMod F => qfrac qpt F
  | PreTerm.PTDH l => gprod (map (λ e, TExp' (qpt e.1) (qfrac qpt e.2)) l)
  end.

Definition q (t : term) : term' := qpt (unfold_term t).

Lemma i_TGMul' (u v : term') : i (TGMul' u v) = TGMul {[+ i u; i v +]}.
Proof. by []. Qed.

Lemma i_TExp' (u v : term') : i (TExp' u v) = TExp (i u) (i v).
Proof. by []. Qed.

Section Quotation.

Implicit Types (x : PreTerm.pre_term) (m : list PreTerm.pre_term).
Implicit Types (qa : PreTerm.pre_term → term').

Add Ring qpfrac_ring : (Frac.frac_ring_theory (T := PreTerm.pre_term)).

Definition pvar (x : PreTerm.pre_term) : Frac.frac PreTerm.pre_term :=
  Frac.of_poly (Poly.var x).

Lemma pre_frac_TMul_empty : pre_frac (TMul ∅) = Frac.one.
Proof. by rewrite -unfold_frac_of frac_of_TMul_empty Frac.map_one. Qed.

Lemma pre_frac_TSum_empty : pre_frac (TSum ∅) = Frac.zero.
Proof. by rewrite -unfold_frac_of frac_of_TSum_empty Frac.map_zero. Qed.

Lemma pre_frac_TSum_opp t :
  pre_frac (TSum (SMS.inv {[+ t +]})) = Frac.opp (pre_frac t).
Proof.
rewrite -!unfold_frac_of frac_of_TSum Frac.ssum_inv Frac.ssum_singleton.
exact: (Frac.map_opp _ unfold_term_inj).
Qed.

Lemma pre_frac_i_qmono qa m :
  (∀ x, x ∈ m → pre_frac (i (qa x)) = pvar x) →
  pre_frac (i (qmono qa m)) = Frac.fprod (pvar <$> m).
Proof.
rewrite /qmono; elim: m => [|x m IH] h /=.
  by rewrite pre_frac_TMul_empty Frac.fprod_nil.
rewrite pre_frac_TMul2 Frac.fprod_cons (h x (list_elem_of_here _ _)).
by rewrite (IH (λ y ym, h y (list_elem_of_further _ _ _ ym))).
Qed.

Lemma pre_frac_i_qsum qa (ms : PreTerm.monos) :
  (∀ m x, m ∈ ms → x ∈ m → pre_frac (i (qa x)) = pvar x) →
  pre_frac (i (qsum qa ms)) =
  Frac.fsum ((λ m, Frac.fprod (pvar <$> m)) <$> ms).
Proof.
rewrite /qsum; elim: ms => [|m ms IH] h /=.
  by rewrite pre_frac_TSum_empty Frac.fsum_nil.
rewrite pre_frac_TSum2 Frac.fsum_cons.
rewrite (pre_frac_i_qmono _ _ (λ x xm, h m x (list_elem_of_here _ _) xm)).
by rewrite (IH (λ m' x m'ms xm', h m' x (list_elem_of_further _ _ _ m'ms) xm')).
Qed.

Lemma fsum_poly_lists (X : MSet.mset (MSet.mset PreTerm.pre_term)) :
  Frac.fsum ((λ m, Frac.fprod (pvar <$> m)) <$> (MSet.car <$> elements X)) =
  Frac.msum pvar X.
Proof.
rewrite Frac.msumE; congr Frac.fsum.
elim: (elements X) => [|M L IH] //.
by rewrite !fmap_cons IH Frac.mono_valE.
Qed.

Lemma pre_frac_i_qpoly qa (p : Poly.poly PreTerm.pre_term) :
  (∀ x, x ∈ Poly.vars p → pre_frac (i (qa x)) = pvar x) →
  pre_frac (i (qpoly qa (PreTerm.poly_lists_of p))) = Frac.of_poly p.
Proof.
move=> h.
have hX : ∀ (X : MSet.mset (MSet.mset PreTerm.pre_term)),
    (∀ M, M ∈ X → M ∈ Poly.car p) →
    ∀ m x, m ∈ MSet.car <$> elements X → x ∈ m →
    pre_frac (i (qa x)) = pvar x.
  move=> X hX m x /list_elem_of_fmap [M [-> /MSet.elem_of_elements MX]] xM.
  by apply: h; apply/Poly.elem_of_vars; exists M; split=> //; apply: hX.
rewrite /qpoly /PreTerm.poly_lists_of /= pre_frac_TSum2 pre_frac_TSum_opp.
rewrite !pre_frac_i_qsum; first last.
- by apply: hX => M MX; left.
- by apply: hX => M MX; right.
rewrite !fsum_poly_lists -Frac.subE -Frac.evalE.
have -> : Frac.eval pvar p =
  Frac.eval (λ x, Frac.of_poly (Poly.var (id x))) p by [].
rewrite Frac.eval_var_map Poly.map_id_ext //.
Qed.

Lemma vars_num_sub (r : Frac.frac PreTerm.pre_term) x :
  x ∈ Poly.vars (Frac.num r) → x ∈ Frac.vars r.
Proof. by move=> h; rewrite /Frac.vars elem_of_app; left. Qed.

Lemma vars_den_sub (r : Frac.frac PreTerm.pre_term) x :
  x ∈ Poly.vars (Frac.den r) → x ∈ Frac.vars r.
Proof. by move=> h; rewrite /Frac.vars elem_of_app; right. Qed.

Lemma pre_frac_i_qfrac qa (r : Frac.frac PreTerm.pre_term) :
  (∀ x, x ∈ Frac.vars r → pre_frac (i (qa x)) = pvar x) →
  pre_frac (i (qfrac qa (PreTerm.frac_lists_of r))) = r.
Proof.
move=> h; rewrite /qfrac /PreTerm.frac_lists_of /= pre_frac_TMul2 pre_frac_TInv.
rewrite (pre_frac_i_qpoly _ _ (λ x xv, h x (vars_num_sub _ _ xv))).
rewrite (pre_frac_i_qpoly _ _ (λ x xv, h x (vars_den_sub _ _ xv))).
by rewrite -Frac.divE -Frac.make_div Frac.make_num_den.
Qed.

Lemma frac_of_lists_zero :
  PreTerm.frac_of_lists PreTerm.zero_lists = Frac.zero.
Proof. by rewrite -PreTerm.frac_lists_of_zero PreTerm.frac_of_listsK. Qed.

Lemma dh_map_i_entries (l : list PreTerm.entry) k :
  StronglySorted lexico (FMap.keys l) →
  (∀ e, e ∈ l →
     PreTerm.dh_map (unfold_term (i (qpt e.1))) = {[e.1 := Frac.one]} ∧
     pre_frac (i (qfrac qpt e.2)) = PreTerm.frac_of_lists e.2) →
  dh_map (i (gprod (map (λ e, TExp' (qpt e.1) (qfrac qpt e.2)) l))) !!! k =
  PreTerm.frac_of_lists (FMap.lookup_list PreTerm.zero_lists k l).
Proof.
elim: l => [|[b F] l IH] sl h.
  by rewrite /= dh_map_TGMul_empty frac_of_lists_zero.
have [sl' bl] : StronglySorted lexico (FMap.keys l) ∧
    Forall (lexico b) (FMap.keys l) := StronglySorted_inv sl.
have [hb hF] : PreTerm.dh_map (unfold_term (i (qpt b))) = {[b := Frac.one]} ∧
    pre_frac (i (qfrac qpt F)) = PreTerm.frac_of_lists F :=
  h (b, F) (list_elem_of_here _ _).
rewrite /gprod [map _ (_ :: _)]/= PolyEval.fold_op_cons -/(gprod _).
rewrite i_TGMul' i_TExp' dh_map_TGMul2.
rewrite (IH sl' (λ e el, h e (list_elem_of_further _ _ _ el))).
rewrite dh_map_TExp unfold_frac_of hF /dh_map hb FMap.lookup_singleton.
rewrite [FMap.lookup_list _ _ (_ :: _)]/=.
case: bool_decide_reflect => [->|_].
  rewrite FMap.lookup_list_lexico ?frac_of_lists_zero //.
  by move: (PreTerm.frac_of_lists F) => r; ring.
by move: (PreTerm.frac_of_lists _) (PreTerm.frac_of_lists F) => r s; ring.
Qed.

Lemma unfold_i_qpt pt : PreTerm.wf pt → unfold_term (i (qpt pt)) = pt.
Proof.
elim/PreTerm.pre_term_ind: pt =>
  [[n|a]|[kt|] t IH|[|] t1 IH1 t2 IH2|F IH|l IH] wpt.
- by [].
- by [].
- by rewrite /= IH.
- by rewrite /= IH.
- by move/andb_True: wpt => [w1 w2]; rewrite /= IH1 // IH2.
- by move/andb_True: wpt => [w1 w2]; rewrite /= IH1 // IH2.
- have /andb_True [/andb_True [aF cF] nl] := wpt.
  have hF : ∀ x, x ∈ Frac.vars (PreTerm.frac_of_lists F) →
      pre_frac (i (qpt x)) = pvar x.
    move=> x /PreTerm.vars_in_lists xF.
    have /andb_True [wx nx] := proj1 (PreTerm.all_atoms_in _ F) aF x xF.
    rewrite (PreTerm.frac_all_in _ _ IH x xF wx).
    exact: PreTerm.frac_of_Nmod.
  have E : pre_frac (i (qpt (PreTerm.PTMod F))) = PreTerm.frac_of_lists F.
    by have := pre_frac_i_qfrac qpt _ hF; rewrite PreTerm.frac_lists_ofK.
  rewrite -[LHS](PreTerm.mod_of_frac_frac_of _ (wf_unfold_term _)) E.
  rewrite /PreTerm.mod_of_frac PreTerm.frac_lists_ofK //.
  move: nl; rewrite /PreTerm.mod_of_lists /PreTerm.lone.
  by case: PreTerm.lone_atom.
- have /andb_True [/andb_True [hl wl] nt] := wpt.
  have sl : StronglySorted lexico (FMap.keys l).
    by move/bool_decide_unpack: wl => [].
  have Hl := PreTerm.entries_all_Forall IH.
  have he : ∀ e, e ∈ l →
      PreTerm.dh_map (unfold_term (i (qpt e.1))) = {[e.1 := Frac.one]} ∧
      pre_frac (i (qfrac qpt e.2)) = PreTerm.frac_of_lists e.2.
    move=> e el.
    have /andb_True [/andb_True [/andb_True [we1 ne1] ae] ce] :=
      proj1 (list.Forall_forall _ _) (proj1 (forallb_True _ _) hl) e el.
    have [IHe [IHF]] := proj1 (list.Forall_forall _ _) Hl e el.
    split; first by rewrite IHe //; exact: PreTerm.dh_map_Ngnf.
    have hF : ∀ x, x ∈ Frac.vars (PreTerm.frac_of_lists e.2) →
        pre_frac (i (qpt x)) = pvar x.
      move=> x /PreTerm.vars_in_lists xF.
      have /andb_True [wx nx] := proj1 (PreTerm.all_atoms_in _ e.2) ae x xF.
      rewrite (PreTerm.frac_all_in _ _ IHF x xF wx).
      exact: PreTerm.frac_of_Nmod.
    by have := pre_frac_i_qfrac qpt _ hF; rewrite PreTerm.frac_lists_ofK.
  set t := i _.
  have Ed : dh_map t = PreTerm.dh_map (PreTerm.PTDH l).
    apply/FMap.fmap_eq => k.
    by rewrite /t dh_map_i_entries //= PreTerm.lookup_of_entries.
  rewrite -[LHS](PreTerm.dh_of_dh_map _ (wf_unfold_term t)).
  by rewrite -/(dh_map t) Ed PreTerm.dh_of_dh_map.
Qed.

Lemma i_q t : i (q t) = t.
Proof.
by apply: unfold_term_inj; rewrite /q unfold_i_qpt // wf_unfold_term.
Qed.

End Quotation.

(** ** Field closure *)

Definition qp (p : Poly.poly PreTerm.pre_term) : term' :=
  qpoly qpt (PreTerm.poly_lists_of p).

Definition cq (r : Frac.frac PreTerm.pre_term) : term' :=
  qfrac qpt (PreTerm.frac_lists_of r).

Definition atom_ok (x : PreTerm.pre_term) : Prop :=
  pre_frac (i (qpt x)) = pvar x.

Section FieldClosure.

Implicit Types (x : PreTerm.pre_term) (p P Q : Poly.poly PreTerm.pre_term).
Implicit Types (r : Frac.frac PreTerm.pre_term) (a b c d w : term').

Lemma qp_eval p : qp p = PolyEval.eval TZero' TOne' TAdd' TMul' TOpp' qpt p.
Proof.
have E (L : list (MSet.mset PreTerm.pre_term)) :
    map (qmono qpt) (MSet.car <$> L) =
    PolyEval.mono_eval TOne' TMul' qpt <$> L.
  elim: L => [|M L IH] //=.
  by rewrite IH /qmono /PolyEval.mono_eval PreTerm.map_fmapE.
by rewrite /qp /qpoly /qsum /PolyEval.eval /PolyEval.ssum /PolyEval.msum !E.
Qed.

Lemma qp_add p1 p2 : qp (p1 + p2)%P ∼ TAdd' (qp p1) (qp p2).
Proof. rewrite !qp_eval; exact: PolyEval.eval_add. Qed.

Lemma qp_opp p : qp (- p)%P ∼ TOpp' (qp p).
Proof. rewrite !qp_eval; exact: PolyEval.eval_opp. Qed.

Lemma qp_mul p1 p2 : qp (p1 * p2)%P ∼ TMul' (qp p1) (qp p2).
Proof. rewrite !qp_eval; exact: PolyEval.eval_mul. Qed.

Lemma qp_zero : qp Poly.zero ∼ TZero'.
Proof. rewrite qp_eval; exact: PolyEval.eval_zero. Qed.

Lemma qp_one : qp Poly.one ∼ TOne'.
Proof. rewrite qp_eval; exact: PolyEval.eval_one. Qed.

Lemma qp_var x : qp (Poly.var x) ∼ qpt x.
Proof. rewrite qp_eval; exact: PolyEval.eval_var. Qed.

Lemma qp_cross P1 Q1 P2 Q2 : (P1 * Q2 = P2 * Q1)%P →
  TMul' (qp P1) (qp Q2) ∼ TMul' (qp P2) (qp Q1).
Proof. by move=> e; rewrite -!qp_mul e; reflexivity. Qed.

Lemma cqE r : cq r = TMul' (qp (Frac.num r)) (TInv' (qp (Frac.den r))).
Proof. by []. Qed.

Lemma atom_okP x : PreTerm.wf x → negb (PreTerm.is_mod x) → atom_ok x.
Proof.
move=> wx nx; rewrite /atom_ok unfold_i_qpt //.
exact: PreTerm.frac_of_Nmod.
Qed.

Lemma all_vars_frac_of_lists F :
  PreTerm.all_atoms (λ x, PreTerm.wf x && negb (PreTerm.is_mod x)) F →
  Frac.all_vars atom_ok (PreTerm.frac_of_lists F).
Proof.
move=> aF; apply/Frac.all_vars_iff => x /PreTerm.vars_in_lists xF.
have /andb_True [wx nx] := proj1 (PreTerm.all_atoms_in _ F) aF x xF.
exact: atom_okP.
Qed.

Lemma all_vars_pre_frac t : Frac.all_vars atom_ok (pre_frac t).
Proof.
move: (wf_unfold_term t).
case: (unfold_term t) => [o|o t'|o t1 t2|F|l] wt;
  try by apply: Frac.all_vars_var; apply: atom_okP.
have /andb_True [/andb_True [aF _] _] := wt.
exact: all_vars_frac_of_lists.
Qed.

Lemma i_qp_neq0 p :
  (∀ x, x ∈ Poly.vars p → atom_ok x) → p ≠ Poly.zero → i (qp p) ≠ i TZero'.
Proof.
move=> h np e; apply: np; apply: Frac.of_poly_inj.
rewrite -(pre_frac_i_qpoly qpt p h) -Frac.zeroE.
have -> : qpoly qpt (PreTerm.poly_lists_of p) = qp p by [].
by rewrite e pre_frac_TSum_empty.
Qed.

Lemma qp_unit p :
  (∀ x, x ∈ Poly.vars p → atom_ok x) → p ≠ Poly.zero →
  TMul' (qp p) (TInv' (qp p)) ∼ TOne'.
Proof. by move=> h np; apply: E_mul_inv; apply: i_qp_neq0. Qed.

Lemma den_unit r : Frac.all_vars atom_ok r →
  TMul' (qp (Frac.den r)) (TInv' (qp (Frac.den r))) ∼ TOne'.
Proof.
move=> /Frac.all_vars_iff h; apply: qp_unit; last exact: Frac.den_neq0.
by move=> x xd; apply: h; apply: vars_den_sub.
Qed.

Lemma num_unit r : Frac.all_vars atom_ok r → r ≠ Frac.zero →
  TMul' (qp (Frac.num r)) (TInv' (qp (Frac.num r))) ∼ TOne'.
Proof.
move=> /Frac.all_vars_iff h nr; apply: qp_unit; last exact: Frac.num_neq0.
by move=> x xn; apply: h; apply: vars_num_sub.
Qed.

Lemma frac_cross a b w c d :
  TMul' b w ∼ TOne' → TMul' d (TInv' d) ∼ TOne' →
  TMul' a d ∼ TMul' c b → TMul' a w ∼ TMul' c (TInv' d).
Proof.
move=> bw dd e.
transitivity (TMul' (TMul' a w) (TMul' d (TInv' d))); first by rewrite dd; ring.
transitivity (TMul' (TMul' a d) (TMul' w (TInv' d))); first ring.
rewrite e.
transitivity (TMul' (TMul' c (TInv' d)) (TMul' b w)); first ring.
by rewrite bw; ring.
Qed.

Lemma cq_make P Q a w :
  Frac.all_vars atom_ok (Frac.make P Q) → Q ≠ Poly.zero →
  a ∼ qp P → TMul' (qp Q) w ∼ TOne' → TMul' a w ∼ cq (Frac.make P Q).
Proof.
move=> h nQ aP Qw; rewrite aP cqE.
apply: frac_cross Qw (den_unit _ h) _.
by apply: qp_cross; symmetry; apply: Frac.make_spec.
Qed.

Lemma inv_unit2 b1 b2 :
  TMul' b1 (TInv' b1) ∼ TOne' → TMul' b2 (TInv' b2) ∼ TOne' →
  TMul' (TMul' b1 b2) (TMul' (TInv' b1) (TInv' b2)) ∼ TOne'.
Proof.
move=> u1 u2.
transitivity (TMul' (TMul' b1 (TInv' b1)) (TMul' b2 (TInv' b2))); first ring.
by rewrite u1 u2; ring.
Qed.

Lemma cq_add r1 r2 : Frac.all_vars atom_ok r1 → Frac.all_vars atom_ok r2 →
  TAdd' (cq r1) (cq r2) ∼ cq (Frac.add r1 r2).
Proof.
move=> h1 h2; have := Frac.all_vars_add _ _ _ h1 h2; rewrite Frac.addE => h3.
have u1 := den_unit r1 h1; have u2 := den_unit r2 h2.
rewrite [cq r1]cqE [cq r2]cqE.
set b1 := qp (Frac.den r1) in u1 *; set b2 := qp (Frac.den r2) in u2 *.
transitivity
  (TMul' (TAdd' (TMul' (qp (Frac.num r1)) b2) (TMul' (qp (Frac.num r2)) b1))
         (TMul' (TInv' b1) (TInv' b2))).
  transitivity
    (TAdd' (TMul' (TMul' (qp (Frac.num r1)) (TInv' b1)) (TMul' b2 (TInv' b2)))
           (TMul' (TMul' (qp (Frac.num r2)) (TInv' b2)) (TMul' b1 (TInv' b1)))).
    by rewrite u1 u2; ring.
  ring.
apply: cq_make => //.
- exact: PolyGcd.mul_neq0 (Frac.den_neq0 r1) (Frac.den_neq0 r2).
- by rewrite qp_add !qp_mul; reflexivity.
- by rewrite qp_mul; apply: inv_unit2.
Qed.

Lemma cq_mul r1 r2 : Frac.all_vars atom_ok r1 → Frac.all_vars atom_ok r2 →
  TMul' (cq r1) (cq r2) ∼ cq (Frac.mul r1 r2).
Proof.
move=> h1 h2; have := Frac.all_vars_mul _ _ _ h1 h2; rewrite Frac.mulE => h3.
have u1 := den_unit r1 h1; have u2 := den_unit r2 h2.
rewrite [cq r1]cqE [cq r2]cqE.
transitivity
  (TMul' (TMul' (qp (Frac.num r1)) (qp (Frac.num r2)))
         (TMul' (TInv' (qp (Frac.den r1))) (TInv' (qp (Frac.den r2))))).
  ring.
apply: cq_make => //.
- exact: PolyGcd.mul_neq0 (Frac.den_neq0 r1) (Frac.den_neq0 r2).
- by rewrite qp_mul; reflexivity.
- by rewrite qp_mul; apply: inv_unit2.
Qed.

Lemma cq_opp r : TOpp' (cq r) ∼ cq (Frac.opp r).
Proof. by rewrite !cqE Frac.num_opp Frac.den_opp qp_opp; ring. Qed.

Lemma one_neq_zero : i TOne' ≠ i TZero'.
Proof.
move=> e; apply: (Frac.one_neq0 (T := PreTerm.pre_term)).
have e' : TMul ∅ = TSum ∅ := e.
by rewrite -pre_frac_TMul_empty -pre_frac_TSum_empty e'.
Qed.

Lemma inv_one : TInv' TOne' ∼ TOne'.
Proof.
transitivity (TMul' TOne' (TInv' TOne')); first by symmetry; apply: E_mul_one.
exact: E_mul_inv one_neq_zero.
Qed.

Lemma cq_zero : TZero' ∼ cq Frac.zero.
Proof. by rewrite cqE Frac.num_zero Frac.den_zero qp_zero qp_one; ring. Qed.

Lemma cq_one : TOne' ∼ cq Frac.one.
Proof. by rewrite cqE Frac.num_one Frac.den_one qp_one inv_one; ring. Qed.

Lemma cq_var x : cq (Frac.of_poly (Poly.var x)) ∼ qpt x.
Proof.
by rewrite cqE Frac.num_of_poly Frac.den_of_poly qp_var qp_one inv_one; ring.
Qed.

Lemma cq_neq0 r : Frac.all_vars atom_ok r → r ≠ Frac.zero →
  i (cq r) ≠ i TZero'.
Proof.
move=> /Frac.all_vars_iff h nr e; apply: nr.
have := pre_frac_i_qfrac qpt r h.
rewrite -/(cq r) e => <-.
exact: pre_frac_TSum_empty.
Qed.

Lemma cq_inv r : Frac.all_vars atom_ok r → TInv' (cq r) ∼ cq (Frac.inv r).
Proof.
move=> h; case: (decide (r = Frac.zero)) => [->|nr].
  by rewrite Frac.inv_zero -cq_zero; exact: E_inv_zero.
have := Frac.all_vars_inv _ _ h; rewrite Frac.invE => h3.
have ua := num_unit r h nr; have ub := den_unit r h.
have uc := E_mul_inv _ (cq_neq0 r h nr).
transitivity (TMul' (qp (Frac.den r)) (TInv' (qp (Frac.num r)))); last first.
  apply: cq_make; [exact: h3|exact: Frac.num_neq0|reflexivity|exact: ua].
transitivity
  (TMul' (TInv' (cq r))
         (TMul' (TMul' (qp (Frac.num r)) (TInv' (qp (Frac.num r))))
                (TMul' (qp (Frac.den r)) (TInv' (qp (Frac.den r)))))).
  by rewrite ua ub; ring.
transitivity
  (TMul' (TMul' (cq r) (TInv' (cq r)))
         (TMul' (qp (Frac.den r)) (TInv' (qp (Frac.num r))))).
  by rewrite cqE; ring.
by rewrite uc; ring.
Qed.

Lemma q_cq t : q t ∼ cq (pre_frac t).
Proof.
rewrite /q; move: (wf_unfold_term t).
case: (unfold_term t) => [o|o t'|o t1 t2|F|l] wt;
  try by symmetry; apply: cq_var.
have /andb_True [/andb_True [_ cF] _] := wt.
by rewrite /cq [PreTerm.frac_of _]/= PreTerm.frac_lists_ofK //; reflexivity.
Qed.

Lemma q_TSum2 s t : TAdd' (q s) (q t) ∼ q (TSum {[+ s; t +]}).
Proof.
rewrite !q_cq pre_frac_TSum2.
exact: cq_add (all_vars_pre_frac s) (all_vars_pre_frac t).
Qed.

Lemma q_TSum_opp t : TOpp' (q t) ∼ q (TSum (SMS.inv {[+ t +]})).
Proof. by rewrite !q_cq pre_frac_TSum_opp; exact: cq_opp. Qed.

Lemma q_TMul2 s t : TMul' (q s) (q t) ∼ q (TMul {[+ s; t +]}).
Proof.
rewrite !q_cq pre_frac_TMul2.
exact: cq_mul (all_vars_pre_frac s) (all_vars_pre_frac t).
Qed.

Lemma q_TInv t : TInv' (q t) ∼ q (TInv t).
Proof. rewrite !q_cq pre_frac_TInv; exact: cq_inv (all_vars_pre_frac t). Qed.

Lemma q_TSum_empty : TZero' ∼ q (TSum ∅).
Proof. by rewrite q_cq pre_frac_TSum_empty; exact: cq_zero. Qed.

Lemma q_TMul_empty : TOne' ∼ q (TMul ∅).
Proof. by rewrite q_cq pre_frac_TMul_empty; exact: cq_one. Qed.

End FieldClosure.

(** ** Group closure *)

Definition gq (m : PreTerm.dhmap) : term' :=
  gprod (map (λ e, TExp' (qpt e.1) (qfrac qpt e.2)) (PreTerm.entries m)).

Definition gprod_keys (K : list PreTerm.pre_term)
    (f : PreTerm.pre_term → Frac.frac PreTerm.pre_term) : term' :=
  gprod ((λ k, TExp' (qpt k) (cq (f k))) <$> K).

Definition supp (m : PreTerm.dhmap) : list PreTerm.pre_term :=
  (FMap.to_list m).*1.

Definition logs_ok (m : PreTerm.dhmap) : Prop :=
  ∀ k, Frac.all_vars atom_ok (m !!! k).

Section GroupClosure.

Implicit Types (x : PreTerm.pre_term) (m : PreTerm.dhmap).
Implicit Types (K : list PreTerm.pre_term) (r : Frac.frac PreTerm.pre_term).
Implicit Types (f g h : PreTerm.pre_term → Frac.frac PreTerm.pre_term).
Implicit Types (u v b : term').

Add Ring gpfrac_ring : (Frac.frac_ring_theory (T := PreTerm.pre_term)).

Lemma gmul_one_r u : TGMul' u TGOne' ∼ u.
Proof. by rewrite E_gmul_comm; apply: E_gmul_one. Qed.

Lemma ginv_unique u v : TGMul' u v ∼ TGOne' → v ∼ TGInv' u.
Proof.
move=> uv; rewrite -(E_gmul_one v) -(E_gmul_inv u).
rewrite (E_gmul_comm u) E_gmul_assoc uv; exact: gmul_one_r.
Qed.

Lemma gmul_idem u : TGMul' u u ∼ u → u ∼ TGOne'.
Proof.
move=> uu; symmetry; transitivity (TGMul' (TGMul' u u) (TGInv' u)).
  by rewrite uu; symmetry; apply: E_gmul_inv.
rewrite E_gmul_assoc E_gmul_inv; exact: gmul_one_r.
Qed.

Lemma ginv_one : TGInv' TGOne' ∼ TGOne'.
Proof. by symmetry; apply: ginv_unique; apply: E_gmul_one. Qed.

Lemma ginv_mul u v : TGInv' (TGMul' u v) ∼ TGMul' (TGInv' u) (TGInv' v).
Proof.
symmetry; apply: ginv_unique.
transitivity (TGMul' (TGMul' u (TGInv' u)) (TGMul' v (TGInv' v))).
  exact: (PolyEval.mop_interchange (mop := TGMul')).
by rewrite !E_gmul_inv; apply: E_gmul_one.
Qed.

Lemma exp_zero b : TExp' b TZero' ∼ TGOne'.
Proof. by apply: gmul_idem; rewrite E_exp_add E_add_zero; reflexivity. Qed.

Lemma exp_opp b a : TGInv' (TExp' b a) ∼ TExp' b (TOpp' a).
Proof.
symmetry; apply: ginv_unique.
by rewrite E_exp_add E_add_opp; apply: exp_zero.
Qed.

Lemma gone_exp a : TExp' TGOne' a ∼ TGOne'.
Proof. by apply: gmul_idem; rewrite -E_exp_gmul E_gmul_one; reflexivity. Qed.

Lemma gprod_keys_cons k K f :
  gprod_keys (k :: K) f = TGMul' (TExp' (qpt k) (cq (f k))) (gprod_keys K f).
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
  TGMul' (gprod_keys K f) (gprod_keys K g) ∼ gprod_keys K h.
Proof.
move=> hf hg eh; elim: K => [|k K IH]; first exact: E_gmul_one.
rewrite !gprod_keys_cons -IH eh -(cq_add _ _ (hf k) (hg k)) -E_exp_add.
exact: (PolyEval.mop_interchange (mop := TGMul')).
Qed.

Lemma gprod_keys_inv K f h :
  (∀ k, h k = Frac.opp (f k)) → TGInv' (gprod_keys K f) ∼ gprod_keys K h.
Proof.
move=> eh; elim: K => [|k K IH]; first exact: ginv_one.
rewrite !gprod_keys_cons ginv_mul IH eh -cq_opp exp_opp; reflexivity.
Qed.

Lemma gprod_keys_exp K f r h :
  (∀ k, Frac.all_vars atom_ok (f k)) → Frac.all_vars atom_ok r →
  (∀ k, h k = Frac.mul (f k) r) →
  TExp' (gprod_keys K f) (cq r) ∼ gprod_keys K h.
Proof.
move=> hf hr eh; elim: K => [|k K IH]; first exact: gone_exp.
rewrite !gprod_keys_cons E_exp_gmul IH E_exp_exp eh -(cq_mul _ _ (hf k) hr).
reflexivity.
Qed.

Lemma gq_gprod_keys m : gq m = gprod_keys (supp m) (λ k, m !!! k).
Proof.
rewrite /gq /gprod_keys /supp /PreTerm.entries PreTerm.map_fmapE.
rewrite -!list_fmap_compose; congr gprod.
apply: list_fmap_ext => j [k v] H.
have /FMap.elem_of_to_list [kv _] := list_elem_of_lookup_2 _ _ _ H.
by rewrite /= kv.
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

Lemma gq_gprod_keys_sub m K f :
  NoDup K → (∀ k, m !!! k ≠ Frac.zero → k ∈ K) → (∀ k, f k = m !!! k) →
  gq m ∼ gprod_keys K f.
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
have E1 : gprod_keys K f ∼ TGMul' (gprod_keys (supp m) f) (gprod_keys R f).
  rewrite /gprod_keys /gprod -PolyEval.fold_op_app -fmap_app.
  apply: PolyEval.fold_op_perm; exact: fmap_Permutation.
have E2 : gprod_keys R f ∼ TGOne'.
  rewrite /gprod_keys /gprod; apply: PolyEval.fold_op_unit.
  move=> u /list_elem_of_fmap [k [-> kR]].
  by rewrite hR // -cq_zero; apply: exp_zero.
rewrite E1 E2 gmul_one_r gq_gprod_keys.
rewrite (gprod_keys_ext _ f (λ k, m !!! k) (λ k _, ef k)); reflexivity.
Qed.

Lemma gq_zero m : (∀ k, m !!! k = Frac.zero) → TGOne' ∼ gq m.
Proof.
move=> z; symmetry; apply: (gq_gprod_keys_sub m [] (λ k, m !!! k)) => //.
- exact: NoDup_nil_2.
- by move=> k; rewrite z.
Qed.

Lemma gq_mul m1 m2 m3 : logs_ok m1 → logs_ok m2 →
  (∀ k, m3 !!! k = Frac.add (m1 !!! k) (m2 !!! k)) →
  TGMul' (gq m1) (gq m2) ∼ gq m3.
Proof.
move=> h1 h2 e3.
have [K [nK eK]] : ∃ K, NoDup K ∧ ∀ k, k ∈ K ↔ k ∈ supp m1 ++ supp m2.
  exists (remove_dups (supp m1 ++ supp m2)).
  by split; [apply: NoDup_remove_dups|move=> k; apply: elem_of_remove_dups].
have inK m : (∀ k, m !!! k ≠ Frac.zero →
               m1 !!! k ≠ Frac.zero ∨ m2 !!! k ≠ Frac.zero) →
    ∀ k, m !!! k ≠ Frac.zero → k ∈ K.
  move=> hm k nk; rewrite eK elem_of_app !elem_of_supp.
  exact: hm k nk.
transitivity
  (TGMul' (gprod_keys K (λ k, m1 !!! k)) (gprod_keys K (λ k, m2 !!! k))).
  apply: E_gmul; apply: gq_gprod_keys_sub => //.
  - by apply: inK => k nk; left.
  - by apply: inK => k nk; right.
transitivity (gprod_keys K (λ k, m3 !!! k)); first exact: gprod_keys_mul.
symmetry; apply: gq_gprod_keys_sub => //.
apply: inK => k nk.
case: (decide (m1 !!! k = Frac.zero)) => [z1|n1]; last by left.
by right => z2; apply: nk; rewrite e3 z1 z2; ring.
Qed.

Lemma gq_inv m1 m3 : (∀ k, m3 !!! k = Frac.opp (m1 !!! k)) →
  TGInv' (gq m1) ∼ gq m3.
Proof.
move=> e3.
have sub : ∀ k, m3 !!! k ≠ Frac.zero → k ∈ supp m1.
  move=> k nk; apply/elem_of_supp => z1; apply: nk.
  by rewrite e3 z1 Frac.opp_zero.
rewrite gq_gprod_keys (gprod_keys_inv _ _ (λ k, m3 !!! k) e3).
by symmetry; apply: gq_gprod_keys_sub => //; apply: NoDup_supp.
Qed.

Lemma gq_exp m1 r m3 : logs_ok m1 → Frac.all_vars atom_ok r →
  (∀ k, m3 !!! k = Frac.mul (m1 !!! k) r) →
  TExp' (gq m1) (cq r) ∼ gq m3.
Proof.
move=> h1 hr e3.
have sub : ∀ k, m3 !!! k ≠ Frac.zero → k ∈ supp m1.
  move=> k nk; apply/elem_of_supp => z1; apply: nk.
  by rewrite e3 z1 Frac.mul_zero_l.
rewrite gq_gprod_keys (gprod_keys_exp _ _ _ (λ k, m3 !!! k) h1 hr e3).
by symmetry; apply: gq_gprod_keys_sub => //; apply: NoDup_supp.
Qed.

Lemma gq_singleton x : gq {[x := Frac.one]} ∼ qpt x.
Proof.
rewrite /gq /PreTerm.entries FMap.to_list_singleton; last exact: Frac.one_neq0.
change (TGMul' (TExp' (qpt x) (cq Frac.one)) TGOne' ∼ qpt x).
rewrite -cq_one E_exp_one; exact: gmul_one_r.
Qed.

Lemma q_gq t : q t ∼ gq (dh_map t).
Proof.
rewrite /q /dh_map; move: (wf_unfold_term t).
case: (unfold_term t) => [o|o t'|o t1 t2|F|l] wt;
  try by symmetry; apply: gq_singleton.
by rewrite /gq [PreTerm.dh_map _]/= PreTerm.entries_of_entries //; reflexivity.
Qed.

Lemma logs_ok_dh_map t : logs_ok (dh_map t).
Proof.
move=> k; rewrite /dh_map; move: (wf_unfold_term t).
case: (unfold_term t) => [o|o t'|o t1 t2|F|l] wt;
  try by rewrite [PreTerm.dh_map _]/= FMap.lookup_singleton; case: bool_decide;
    [exact: Frac.all_vars_one|exact: Frac.all_vars_zero].
rewrite [PreTerm.dh_map _]/= PreTerm.lookup_of_entries.
set F := FMap.lookup_list _ k l.
case: (decide (F = PreTerm.zero_lists)) => [->|ne].
  by rewrite frac_of_lists_zero; exact: Frac.all_vars_zero.
have kl := PreTerm.lookup_list_elem l k ne.
have /andb_True [/andb_True [hl _] _] := wt.
have /andb_True [/andb_True [_ aF] _] :=
  proj1 (list.Forall_forall _ _) (proj1 (forallb_True _ _) hl) _ kl.
exact: all_vars_frac_of_lists.
Qed.

Lemma q_TGMul2 s t : TGMul' (q s) (q t) ∼ q (TGMul {[+ s; t +]}).
Proof.
rewrite !q_gq; apply: gq_mul; [exact: logs_ok_dh_map|exact: logs_ok_dh_map|].
exact: dh_map_TGMul2.
Qed.

Lemma q_TGInv t : TGInv' (q t) ∼ q (TGInv t).
Proof. by rewrite !q_gq; apply: gq_inv => k; apply: dh_map_TGInv. Qed.

Lemma q_TGMul_empty : TGOne' ∼ q (TGMul ∅).
Proof. by rewrite q_gq; apply: gq_zero => k; apply: dh_map_TGMul_empty. Qed.

Lemma q_TExp s e : TExp' (q s) (q e) ∼ q (TExp s e).
Proof.
rewrite [q e]q_cq !q_gq.
apply: gq_exp; [exact: logs_ok_dh_map|exact: all_vars_pre_frac|].
by move=> k; rewrite dh_map_TExp unfold_frac_of.
Qed.

End GroupClosure.

(** ** Completeness *)

Lemma term_equiv_q x : x ∼ q (i x).
Proof.
elim: x => [n|x1 IH1 x2 IH2|a|kt x IH|x1 IH1 x2 IH2|x IH| | |x1 IH1 x2 IH2
  |x IH|x1 IH1 x2 IH2|x IH| |x1 IH1 x2 IH2|x IH|x1 IH1 x2 IH2].
- reflexivity.
- exact: E_pair IH1 IH2.
- reflexivity.
- exact: E_key IH.
- exact: E_seal IH1 IH2.
- exact: E_hash IH.
- exact: q_TSum_empty.
- exact: q_TMul_empty.
- by etransitivity; [exact: E_add IH1 IH2|exact: q_TSum2].
- by etransitivity; [exact: E_opp IH|exact: q_TSum_opp].
- by etransitivity; [exact: E_mul IH1 IH2|exact: q_TMul2].
- by etransitivity; [exact: E_inv IH|exact: q_TInv].
- exact: q_TGMul_empty.
- by etransitivity; [exact: E_gmul IH1 IH2|exact: q_TGMul2].
- by etransitivity; [exact: E_ginv IH|exact: q_TGInv].
- by etransitivity; [exact: E_exp IH1 IH2|exact: q_TExp].
Qed.

Theorem term_equiv_iff x y : x ∼ y ↔ i x = i y.
Proof.
split; first exact: i_sound.
move=> e; transitivity (q (i x)); first exact: term_equiv_q.
by rewrite e; symmetry; apply: term_equiv_q.
Qed.

Corollary i_surj t : ∃ x, i x = t.
Proof. by exists (q t); apply: i_q. Qed.
