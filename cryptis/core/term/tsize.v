From cryptis Require Import lib.
From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import sorting gmap.
From cryptis.lib Require Import list_sort mathcomp_compat fmap mset sms.
From cryptis.lib Require Import poly poly_gcd frac.
From iris.heap_lang Require locations.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core Require Export pre_term.
From cryptis.core.term Require Import base algebra.

Implicit Types (t k : term) (ts : list term).

(* The [tsize] measure and the well-founded induction principles it supports.
   [tsize] is [PreTerm.tsize] pulled back along [unfold_term]; the [tsize_*_lt]
   lemmas are the termination side conditions feeding [term_lt_rect] /
   [term_lt_ind].  It depends on core/term/algebra.v, which does not depend on
   it — no term-algebra lemma mentions [tsize]. *)

Definition tsize t := PreTerm.tsize (unfold_term t).

Lemma tsize_gt0 t : 0 < tsize t.
Proof. exact: PreTerm.tsize_pos. Qed.

Lemma tsize_eq t :
  tsize t =
  match t with
  | TInt _ => 1
  | TPair t1 t2 => S (tsize t1 + tsize t2)
  | TNonce _ => 1
  | TKey _ t => S (tsize t)
  | TSeal k t => S (tsize k + tsize t)
  | THash t => S (tsize t)
  | TNonFree pt _ _ => PreTerm.tsize pt
  end.
Proof.
by case: t => [n|t1 t2|a|kt t|k t|t|pt wpt npt] //;
  rewrite /tsize PreTerm.tsize_free.
Qed.

Definition tsizeE := tsize_eq.

Lemma tsize_gfactors_le t t' : t ∈ gfactors t' → tsize t ≤ tsize t'.
Proof.
move=> /elem_of_gfactors_unfold h; rewrite /tsize.
exact: (PreTerm.tsize_gfactors_le _ _ (wf_unfold_term _) h).
Qed.

Lemma tsize_gfactors_lt t' t : is_gmul t → t' ∈ gfactors t → tsize t' < tsize t.
Proof.
rewrite is_gmul_unfold => Mt /elem_of_gfactors_unfold h; rewrite /tsize.
exact: (PreTerm.tsize_gfactors_lt _ _ (wf_unfold_term _) Mt h).
Qed.

Lemma tsize_atoms_lt x t : is_mod t → x ∈ atoms t → tsize x < tsize t.
Proof.
rewrite is_mod_unfold => Mt /elem_of_atoms [y [-> yt]].
have [wy _] := PreTerm.atoms_wf _ _ (wf_unfold_term t) yt.
rewrite /tsize fold_termK //; exact: PreTerm.tsize_atoms_lt.
Qed.

Lemma tsize_factors_lt t' t :
  laurent t → is_mod t → t' ∈ factors t → tsize t' < tsize t.
Proof.
move=> L Mt t't; apply: (tsize_atoms_lt _ _ Mt).
exact: (factors_atoms t't (L _ t't)).
Qed.

Lemma tsize_exp_term t :
  is_exp t → tsize t = S (tsize (base t) + tsize (expo t)).
Proof.
rewrite is_exp_unfold => xt.
by rewrite /tsize unfold_base unfold_expo PreTerm.tsize_exp.
Qed.

Lemma tsize_base_lt t : is_exp t → tsize (base t) < tsize t.
Proof. by move=> xt; rewrite (tsize_exp_term _ xt); lia. Qed.

Lemma tsize_expo_lt t : is_exp t → tsize (expo t) < tsize t.
Proof. by move=> xt; rewrite (tsize_exp_term _ xt); lia. Qed.

Lemma term_lt_rect (T : term -> Type) :
  (forall t, (forall t', (tsize t' < tsize t) -> T t') -> T t) ->
  forall t, T t.
Proof.
move=> H t.
move: {-1}(tsize t) (Nat.le_refl (tsize t)) => n.
elim: n / (lt_wf n) t => n _ IH t t_n.
apply: H => t' t'_t.
apply: (IH (tsize t')); lia.
Qed.

Lemma term_lt_ind (T : term -> Prop) :
  (forall t, (forall t', (tsize t' < tsize t) -> T t') -> T t) ->
  forall t, T t.
Proof. exact: term_lt_rect. Qed.

(** The default induction principle.  Exponents are taken apart through their
    atoms, powers through their base and exponent, and group products through
    their factors. *)
Lemma term_rect (T : term -> Type)
  (H1 : forall n, T (TInt n))
  (H2 : forall t1, T t1 -> forall t2, T t2 -> T (TPair t1 t2))
  (H3 : forall a, T (TNonce a))
  (H4 : forall kt t, T t -> T (TKey kt t))
  (H5 : forall k, T k -> forall t, T t -> T (TSeal k t))
  (H6 : forall t, T t -> T (THash t))
  (H7 : forall t, is_exp t -> T (base t) -> T (expo t) -> T t)
  (H8 : forall t, is_mod t -> (forall x, x ∈ atoms t -> T x) -> T t)
  (H8g : forall s, (forall t, t ∈ s -> T t) ->
                   (forall t, t ∈ s -> negb (is_gmul t)) ->
                   (forall t, s ≠ {[+ t +]}) ->
        T (TGMul s)) :
  forall t, T t.
Proof.
apply: term_lt_rect => t IH.
case Ex: (is_exp t).
  have xt : is_exp t by rewrite Ex.
  by apply: H7 => //; apply: IH; [exact: tsize_base_lt|exact: tsize_expo_lt].
case Em: (is_mod t).
  have mt : is_mod t by rewrite Em.
  by apply: H8 => // x xt; apply: IH; exact: tsize_atoms_lt.
case Eg: (is_gmul t).
  have gt : is_gmul t by rewrite Eg.
  rewrite -(gfactorsK t); apply: H8g.
  - by move=> u ut; apply: IH; exact: tsize_gfactors_lt.
  - by move=> u /Ngmul_gfactors.
  - move=> u e; have Nu : negb (is_gmul u).
      by apply: (Ngmul_gfactors t); rewrite e SMS.elem_of_singleton.
    have : is_gmul t = is_gmul u.
      by rewrite -(gfactorsK t) e -(gfactors_Ngmul _ Nu) gfactorsK.
    by rewrite Eg; case: (is_gmul u) Nu.
case: t IH Ex Em Eg => [n|t1 t2|a|kt t1|k t1|t1|pt wpt npt] IH Ex Em Eg.
- exact: H1.
- by apply: H2; apply: IH; rewrite [tsize (TPair _ _)]tsize_eq; lia.
- exact: H3.
- by apply: H4; apply: IH; rewrite [tsize (TKey _ _)]tsize_eq; lia.
- by apply: H5; apply: IH; rewrite [tsize (TSeal _ _)]tsize_eq; lia.
- by apply: H6; apply: IH; rewrite [tsize (THash _)]tsize_eq; lia.
- exfalso; clear IH; move: Ex Em Eg => /= Ex Em Eg.
  by move: npt; rewrite /is_non_free Ex Em Eg.
Qed.

Register Scheme term_rect as rect_dep for term.

Definition term_ind (P : term -> Prop) := @term_rect P.

Register Scheme term_ind as ind_dep for term.

(** ** Stripping exponents

    The exponent of a power [t] is a fraction [M / D] with a monomial numerator
    [M] ([PreTerm.mono_num_expo]).  Its factors are the atoms of [M]
    (positively) and the atoms of the monomial content and the unit part of [D]
    (negatively); removing any of them from the exponent shrinks [t]
    ([tsize_satoms]). *)

Lemma tsize_TInv_le x :
  tsize (TInv x) ≤
  S (PreTerm.poly_size (PreTerm.poly_lists_of
       (Frac.num (Frac.inv (PreTerm.frac_of (unfold_term x))))) +
     PreTerm.poly_size (PreTerm.poly_lists_of
       (Frac.den (Frac.inv (PreTerm.frac_of (unfold_term x)))))).
Proof.
rewrite /tsize -(PreTerm.mod_of_frac_frac_of _ (wf_unfold_term (TInv x))).
rewrite pre_frac_TInv; apply: PreTerm.tsize_mod_of_frac_le.
apply: Frac.all_vars_inv; apply: PreTerm.all_vars_Nmod.
exact: PreTerm.frac_of_atoms.
Qed.

Lemma tsize_satoms f t :
  f ∈ satoms (exps t) → tsize f < tsize t ∧ tsize (TExp t (TInv f)) < tsize t.
Proof.
move=> ft; have xt := is_exp_of_satoms ft.
have Et := tsize_exp_term _ xt.
have gb := tsize_gt0 (base t).
have Nt' : negb (PreTerm.is_gmul (unfold_term t)).
  by rewrite -is_gmul_unfold; exact: is_exp_Ngmul.
have we := PreTerm.wf_expo _ (wf_unfold_term t).
set r := PreTerm.frac_of (PreTerm.expo (unfold_term t)).
have [M eM] : Frac.mono_num r := PreTerm.mono_num_expo _ (wf_unfold_term t) Nt'.
have nD : Frac.den r ≠ Poly.zero := Frac.den_neq0 r.
have A := PreTerm.frac_of_atoms _ we.
have cnt y : count y (expo t) =
    (Z.of_nat (MSet.count (unfold_term y) M) -
     Z.of_nat (MSet.count (unfold_term y)
                (PolyGcd.content (Frac.den r) ⊎ PreTerm.unit_factors
                  (Frac.den r))))%Z.
  rewrite count_unfold unfold_expo (PreTerm.factors_mono_num _ _ eM).
  exact: SMS.count_make.
have bound e' n' :
    Frac.num (Frac.mul r (PreTerm.frac_of (unfold_term e'))) = Poly.mono n' →
    tsize (TExp t e') ≤
    S (tsize (base t) +
       S (PreTerm.poly_size (PreTerm.poly_lists_of
            (Frac.num (Frac.mul r (PreTerm.frac_of (unfold_term e'))))) +
          PreTerm.poly_size (PreTerm.poly_lists_of
            (Frac.den (Frac.mul r (PreTerm.frac_of (unfold_term e'))))))).
  move=> en.
  have nz : Frac.mul r (PreTerm.frac_of (unfold_term e')) ≠ Frac.zero.
    by apply: Frac.mono_num_neq0; exists n'.
  have ar : Frac.all_vars (λ x, negb (PreTerm.is_mod x))
              (Frac.mul r (PreTerm.frac_of (unfold_term e'))).
    by apply: Frac.all_vars_mul; apply: PreTerm.all_vars_Nmod;
      apply: PreTerm.frac_of_atoms.
  rewrite /tsize unfold_TExp /PreTerm.exp.
  rewrite (PreTerm.exp_frac_Ngmul _ _ (wf_unfold_term t) Nt' nz) unfold_base.
  rewrite -/r.
  have := PreTerm.tsize_mk_exp_le (PreTerm.base (unfold_term t)) _ _ ar en.
  have := PreTerm.tsize_mod_of_frac_le _ ar.
  lia.
case Me: (is_mod (expo t)); last first.
  have Ne : negb (is_mod (expo t)) by rewrite Me.
  move: ft; rewrite /satoms /exps (factors_Nmod _ Ne) SMS.pos_singleton.
  rewrite SMS.neg_singleton MSet.elements_singleton MSet.elements_empty /=.
  move=> /list_elem_of_singleton ->.
  split; first by rewrite Et; lia.
  rewrite -[t in TExp t _]TExp_base_expo (TExpK _ (atom_frac_neq0 Ne)).
  exact: tsize_base_lt.
have Te : tsize (expo t) =
    S (PreTerm.poly_size (PreTerm.poly_lists_of (Frac.num r)) +
       PreTerm.poly_size (PreTerm.poly_lists_of (Frac.den r))).
  have Me' : PreTerm.is_mod (PreTerm.expo (unfold_term t)).
    by rewrite -unfold_expo -is_mod_unfold Me.
  by rewrite /tsize unfold_expo (PreTerm.tsize_mod _ Me').
have psM : PreTerm.poly_size (PreTerm.poly_lists_of (Frac.num r)) =
           PreTerm.mono_size (MSet.car M) by rewrite eM PreTerm.poly_size_monoE.
rewrite Et Te psM; move: ft; rewrite /satoms elem_of_app list_elem_of_fmap.
case=> [/MSet.elem_of_elements fp|[x [-> /MSet.elem_of_elements xn]]].
- have fM : unfold_term f ∈ M.
    move/count_gt0: fp; rewrite cnt => h; apply/MSet.elem_of_count; lia.
  have [wa na] : PreTerm.wf (unfold_term f) ∧
                 negb (PreTerm.is_mod (unfold_term f)).
    apply/andb_True; apply: (A M) fM; left.
    by rewrite eM Poly.car_mono; apply/SMS.elem_of_singleton.
  have ha : tsize f ≤ PreTerm.mono_size (MSet.car M).
    exact: (sum_list_with_in _ PreTerm.tsize _ fM).
  split; first lia.
  have ef : PreTerm.frac_of (unfold_term (TInv f)) =
            Frac.inv (Frac.var (unfold_term f)).
    by rewrite pre_frac_TInv PreTerm.frac_of_var.
  have [en ed] := Frac.mul_inv_var_canon r M (unfold_term f) eM fM.
  have en' : Frac.num (Frac.mul r (PreTerm.frac_of (unfold_term (TInv f)))) =
             Poly.mono (M ∖ {[+ unfold_term f +]}) by rewrite ef en.
  have EM : M = {[+ unfold_term f +]} ⊎ (M ∖ {[+ unfold_term f +]}).
    apply: MSet.count_inj => y.
    rewrite MSet.count_disj_union MSet.count_difference MSet.count_singleton.
    have := proj1 (MSet.elem_of_count _ _) fM.
    by case: bool_decide_reflect => [->|]; lia.
  have W : PreTerm.mono_size (MSet.car M) =
           tsize f + PreTerm.mono_size (MSet.car (M ∖ {[+ unfold_term f +]})).
    rewrite {1}EM PreTerm.mono_size_disj_union MSet.car_singleton /=.
    rewrite -/(tsize f); lia.
  have := bound (TInv f) _ en'; rewrite ef en ed PreTerm.poly_size_monoE.
  have := tsize_gt0 f; lia.
- have xY : unfold_term x ∈
            PolyGcd.content (Frac.den r) ⊎ PreTerm.unit_factors (Frac.den r).
    move/count_lt0: xn; rewrite cnt => h; apply/MSet.elem_of_count; lia.
  rewrite TInvK; case/MSet.elem_of_disj_union: xY => [xc|xu].
  + have [n [nD' xn']] := PolyGcd.elem_of_content _ _ xc.
    have [wc nc] : PreTerm.wf (unfold_term x) ∧
                   negb (PreTerm.is_mod (unfold_term x)).
      by apply/andb_True; apply: (A n) xn'; right.
    have hc : tsize x ≤ PreTerm.poly_size (PreTerm.poly_lists_of (Frac.den r)).
      have : tsize x ≤ PreTerm.mono_size (MSet.car n).
        exact: (sum_list_with_in _ PreTerm.tsize _ xn').
      have := PreTerm.poly_size_ge _ _ nD'; lia.
    have ef : PreTerm.frac_of (unfold_term x) = Frac.var (unfold_term x).
      exact: PreTerm.frac_of_var.
    split.
    * have := tsize_TInv_le x; rewrite ef.
      have [en ed] := Frac.inv_var_canon (unfold_term x).
      rewrite en ed PreTerm.poly_size_one Poly.varE PreTerm.poly_size_monoE
        MSet.car_singleton /=.
      rewrite -/(tsize x); lia.
    * have [en [ed eD]] := Frac.mul_var_content_canon r M (unfold_term x) eM xc.
      have en' : Frac.num (Frac.mul r (PreTerm.frac_of (unfold_term x))) =
                 Poly.mono M by rewrite ef en.
      set Dc := PolyGcd.div_mono {[+ unfold_term x +]} (Frac.den r) in ed eD.
      have nDc : Dc ≠ Poly.zero.
        move=> e; apply: nD; rewrite -eD e.
        exact: (right_absorb Poly.zero Poly.mul).
      have hD : PreTerm.poly_size (PreTerm.poly_lists_of (Frac.den r)) =
                PreTerm.poly_size (PreTerm.poly_lists_of Dc) +
                PreTerm.poly_length Dc * tsize x.
        rewrite -eD PreTerm.poly_size_mul_monoE MSet.car_singleton /=.
        rewrite -/(tsize x); lia.
      have := PreTerm.poly_length_pos _ nDc.
      have := tsize_gt0 x.
      have := bound x _ en'; rewrite ef en ed PreTerm.poly_size_monoE.
      nia.
  + have U1 : PolyGcd.unit_part (Frac.den r) ≠ Poly.one.
      move: xu; rewrite /PreTerm.unit_factors;
        case: bool_decide_reflect => // _.
      by move=> e; case: (MSet.not_elem_of_empty _ e).
    have hat : ∀ m y, m ∈ Poly.car (Frac.den r) → y ∈ m →
        negb (PreTerm.is_mod y).
      by move=> m y mD ym; have /andb_True [] := A m y (or_intror mD) ym.
    have ef : PreTerm.frac_of (unfold_term x) =
              Frac.of_poly (PolyGcd.unit_part (Frac.den r)).
      exact: PreTerm.frac_of_unit_factors hat xu.
    have fU := Frac.first_neg_unit_part r.
    have nU := PolyGcd.unit_part_neq0 _ nD.
    have hD := PreTerm.poly_size_mul_monoE (PolyGcd.content (Frac.den r))
                 (PolyGcd.unit_part (Frac.den r)).
    rewrite PolyGcd.content_unitK in hD.
    have pU := PreTerm.poly_size_pos_nonunit _ nU U1 fU.
    have := PreTerm.poly_length_pos _ nU.
    split.
    * have := tsize_TInv_le x; rewrite ef.
      have [en ed] := Frac.inv_of_poly_canon _ nU fU.
      rewrite en ed PreTerm.poly_size_one; nia.
    * have [en ed] := Frac.mul_unit_part_canon r M eM.
      have en' : Frac.num (Frac.mul r (PreTerm.frac_of (unfold_term x))) =
                 Poly.mono M by rewrite ef en.
      have := bound x _ en'; rewrite ef en ed !PreTerm.poly_size_monoE.
      nia.
Qed.

Lemma tsize_exps_lt t' t :
  t' ∈ exps t → negb (is_mod t') → tsize t' < tsize t.
Proof.
move=> t't Nt'; have xt := is_exp_of_exps t't.
have := tsize_expo_lt _ xt.
have a_t' := factors_atoms t't Nt'.
case Me: (is_mod (expo t)).
  have := tsize_atoms_lt _ _ (ltac:(by rewrite Me) : is_mod (expo t)) a_t'.
  lia.
have Ne : negb (is_mod (expo t)) by rewrite Me.
by move: a_t'; rewrite (atoms_atom _ _ Ne) => ->.
Qed.
