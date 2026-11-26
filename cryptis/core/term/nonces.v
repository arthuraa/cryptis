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
From cryptis.core.term Require Import base algebra tsize repr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Implicit Types (t k : term) (ts : list term).

(* nonces_of_term and its theory.  The nonces of a term are those of its
   atoms ([nonces_of_term_atoms]), of its factors ([nonces_of_term_factors])
   and of its group factors ([nonces_of_term_gfactors]). *)

lock Definition nonces_of_term (t : term) :=
  nonces_of_pre_term (unfold_term t).

Lemma nonces_of_termE' t :
  nonces_of_term t =
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | TNonce l => {[l]}
  | TKey _ t => nonces_of_term t
  | TSeal t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | THash t => nonces_of_term t
  | TNonFree pt _ _ => nonces_of_pre_term pt
  end.
Proof.
by rewrite [nonces_of_term]unlock; case: t => //=.
Qed.

Lemma nonces_of_term_fold pt :
  PreTerm.wf pt -> nonces_of_term (fold_term pt) = nonces_of_pre_term pt.
Proof. move => wf. by rewrite [nonces_of_term]unlock (@fold_termK pt wf). Qed.

(** ** Atoms *)

Lemma elem_of_nonces_of_frac (n : PreTerm.pre_term → gset nonce) F x :
  x ∈ nonces_of_frac n F ↔ ∃ y, PreTerm.in_lists F y ∧ x ∈ n y.
Proof.
have M (ms : list (list PreTerm.pre_term)) :
    x ∈ ⋃ map (λ m, ⋃ map n m) ms ↔ ∃ m y, m ∈ ms ∧ y ∈ m ∧ x ∈ n y.
  rewrite elem_of_union_list; split.
  - case=> X [/list_elem_of_fmap [m [-> mms]]] /elem_of_union_list.
    by case=> Y [/list_elem_of_fmap [y [-> ym]] xy]; exists m, y.
  - case=> m [y [mms [ym xy]]]; exists (⋃ map n m); split.
      exact: (list_elem_of_fmap_2 (λ m, ⋃ map n m) ms m mms).
    apply/elem_of_union_list; exists (n y); split=> //.
    exact: (list_elem_of_fmap_2 n m y ym).
rewrite /nonces_of_frac !elem_of_union !M; split.
- by case=> [[[|]|]|] [m [y [hm [ym xy]]]]; exists y; split=> //; exists m;
    split=> //; tauto.
- case=> y [[m [hm ym]] xy].
  by case: hm => [h|[h|[h|h]]];
    [left; left; left|left; left; right|left; right|right]; exists m, y.
Qed.

Lemma nonces_of_pre_term_mod_of_frac r :
  nonces_of_pre_term (PreTerm.mod_of_frac r) ≡
  ⋃ map nonces_of_pre_term (Frac.vars r).
Proof.
move=> x; rewrite elem_of_union_list.
have R : x ∈ nonces_of_pre_term (PreTerm.PTMod (PreTerm.frac_lists_of r)) ↔
         ∃ X, X ∈ map nonces_of_pre_term (Frac.vars r) ∧ x ∈ X.
  rewrite [nonces_of_pre_term _]/= elem_of_nonces_of_frac; split.
  - case=> y [/PreTerm.in_lists_frac_lists_of yr xy]; exists
      (nonces_of_pre_term y).
    by split=> //; exact: (list_elem_of_fmap_2 nonces_of_pre_term _ y yr).
  - case=> X [/list_elem_of_fmap [y [-> yr]] xy]; exists y.
    by split=> //; exact/PreTerm.in_lists_frac_lists_of.
rewrite /PreTerm.mod_of_frac /PreTerm.mod_of_lists.
case E: (PreTerm.lone_atom (PreTerm.frac_lists_of r)) => [z|]; last exact: R.
have Ez : PreTerm.frac_lists_of r = (([[z]], []), ([[]], [])).
  exact/PreTerm.lone_atom_Some.
rewrite -R Ez /= /nonces_of_frac /=.
set_solver.
Qed.

Lemma nonces_of_term_atoms t :
  nonces_of_term t = ⋃ map nonces_of_term (atoms t).
Proof.
apply: leibniz_equiv.
have E : nonces_of_term t =
    nonces_of_pre_term (PreTerm.mod_of_frac (PreTerm.frac_of (unfold_term t))).
  by rewrite [nonces_of_term]unlock PreTerm.mod_of_frac_frac_of.
rewrite E nonces_of_pre_term_mod_of_frac => x; rewrite !elem_of_union_list.
split.
- case=> X [/list_elem_of_fmap [y [-> yr]] xy].
  have [wy _] := PreTerm.atoms_wf _ _ (wf_unfold_term t) yr.
  exists (nonces_of_term (fold_term y)); split.
    apply: (list_elem_of_fmap_2 nonces_of_term (atoms t) (fold_term y)).
    by apply/elem_of_atoms; exists y.
  by rewrite (nonces_of_term_fold wy).
- case=> X [/list_elem_of_fmap [z [-> /elem_of_atoms [y [-> yr]]]] xz].
  have [wy _] := PreTerm.atoms_wf _ _ (wf_unfold_term t) yr.
  exists (nonces_of_pre_term y); split.
    exact: (list_elem_of_fmap_2 nonces_of_pre_term _ y yr).
  by rewrite -(nonces_of_term_fold wy).
Qed.

(** ** Diffie-Hellman maps *)

Definition dh_nonces (m : PreTerm.dhmap) : gset nonce :=
  ⋃ ((λ p, nonces_of_pre_term p.1 ∪
           ⋃ (nonces_of_pre_term <$> Frac.vars p.2))
       <$> FMap.to_list m).

Lemma elem_of_dh_nonces m x :
  x ∈ dh_nonces m ↔
  ∃ k : PreTerm.pre_term, m !!! k ≠ Frac.zero ∧
       (x ∈ nonces_of_pre_term k ∨
        ∃ y, y ∈ Frac.vars (m !!! k) ∧ x ∈ nonces_of_pre_term y).
Proof.
rewrite /dh_nonces elem_of_union_list; split.
- case=> X [/list_elem_of_fmap [[k r] [-> /FMap.elem_of_to_list [mk nr]]]].
  rewrite /= elem_of_union elem_of_union_list => h.
  exists k; rewrite mk.
  split=> //.
  case: h => [|[Y [/list_elem_of_fmap [y [-> yr]] xy]]].
    tauto.
  by right; exists y.
- case=> k [nk h].
  exists (nonces_of_pre_term k ∪
          ⋃ (nonces_of_pre_term <$> Frac.vars (m !!! k))).
  split.
    apply: (list_elem_of_fmap_2
      (λ p : PreTerm.pre_term * Frac.frac PreTerm.pre_term,
       nonces_of_pre_term p.1 ∪
       ⋃ (nonces_of_pre_term <$> Frac.vars p.2))
      _ (k, m !!! k)).
    exact/FMap.elem_of_to_list.
  rewrite elem_of_union elem_of_union_list.
  case: h => [|[y [yr xy]]]; first tauto.
  right; exists (nonces_of_pre_term y); split=> //.
  exact: list_elem_of_fmap_2.
Qed.

Lemma dh_nonces_atom b x :
  x ∈ dh_nonces {[b := Frac.one]} ↔ x ∈ nonces_of_pre_term b.
Proof.
rewrite elem_of_dh_nonces; split.
- case=> k [nk h]; move: nk h; rewrite FMap.lookup_singleton.
  case: bool_decide_reflect => [->|_]; last by move=> /(_ eq_refl).
  by move=> _ [//|[y [/(Frac.vars_one y) []]]].
- move=> h; exists b; rewrite FMap.lookup_singleton bool_decide_eq_true_2 //.
  by split; [exact: Frac.one_neq0|left].
Qed.

Lemma nonces_of_pre_term_dh pt x :
  PreTerm.wf pt →
  x ∈ nonces_of_pre_term pt ↔ x ∈ dh_nonces (PreTerm.dh_map pt).
Proof.
case: pt => [o|o t|o t1 t2|F|l] wpt; try by rewrite [PreTerm.dh_map _]/=
  dh_nonces_atom.
have El := PreTerm.entries_of_entries _ wpt.
rewrite [PreTerm.dh_map _]/= [nonces_of_pre_term _]/= -{1}El.
set m := PreTerm.of_entries l.
rewrite elem_of_union_list elem_of_dh_nonces; split.
- case=> X [/list_elem_of_fmap [[k F] [-> /PreTerm.elem_of_entries [-> nk]]]].
  rewrite /= elem_of_union elem_of_nonces_of_frac => h.
  exists k; split=> //; case: h
    => [|[y [/PreTerm.in_lists_frac_lists_of yr xy]]]; first tauto.
  by right; exists y.
- case=> k [nk h].
  exists (nonces_of_pre_term k ∪
          nonces_of_frac nonces_of_pre_term (PreTerm.frac_lists_of (m !!! k))).
  split.
    apply: (list_elem_of_fmap_2 (λ e : PreTerm.entry,
      nonces_of_pre_term e.1 ∪ nonces_of_frac nonces_of_pre_term e.2)
      _ (k, PreTerm.frac_lists_of (m !!! k))).
    exact/PreTerm.elem_of_entries.
  rewrite elem_of_union elem_of_nonces_of_frac.
  case: h => [|[y [yr xy]]]; first tauto.
  by right; exists y; split=> //; exact/PreTerm.in_lists_frac_lists_of.
Qed.

Lemma nonces_of_term_dh t x :
  x ∈ nonces_of_term t ↔ x ∈ dh_nonces (dh_map t).
Proof.
rewrite [nonces_of_term]unlock /dh_map.
exact: nonces_of_pre_term_dh (wf_unfold_term t).
Qed.

Lemma elem_of_union_list_nonces x u ts :
  u ∈ ts → x ∈ nonces_of_term u → x ∈ ⋃ map nonces_of_term ts.
Proof.
move=> uts xu; apply/elem_of_union_list; exists (nonces_of_term u).
by split=> //; exact: (list_elem_of_fmap_2 nonces_of_term ts u uts).
Qed.

Lemma nonces_of_term_TGMul_subseteq s :
  nonces_of_term (TGMul s) ⊆ ⋃ map nonces_of_term (elements s).
Proof.
move=> x /nonces_of_term_dh /elem_of_dh_nonces [k [+ h]].
rewrite dh_map_TGMul => nk; move: h; rewrite dh_map_TGMul.
case=> [xk|[y [/(Frac.vars_ssum _ s y) [u [us yu]] xy]]].
- have [u [us uk]] := Frac.ssum_nonzero _ _ nk.
  apply: (elem_of_union_list_nonces (u := u)).
    exact/SMS.elem_of_elements.
  by apply/nonces_of_term_dh/elem_of_dh_nonces; exists k; split=> //; left.
- have uk : dh_map u !!! k ≠ Frac.zero.
    by move=> e; move: yu; rewrite e => /(Frac.vars_zero y).
  apply: (elem_of_union_list_nonces (u := u)).
    exact/SMS.elem_of_elements.
  apply/nonces_of_term_dh/elem_of_dh_nonces; exists k; split=> //.
  by right; exists y.
Qed.

Lemma nonces_of_frac_var t y x :
  y ∈ Frac.vars (PreTerm.frac_of (unfold_term t)) →
  x ∈ nonces_of_pre_term y → x ∈ nonces_of_term t.
Proof.
move=> yt xy; have [wy _] := PreTerm.atoms_wf _ _ (wf_unfold_term t) yt.
rewrite nonces_of_term_atoms.
apply: (elem_of_union_list_nonces (u := fold_term y)).
  by apply/elem_of_atoms; exists y.
by rewrite (nonces_of_term_fold wy).
Qed.

Lemma nonces_of_term_TMul_subseteq s :
  nonces_of_term (TMul s) ⊆ ⋃ map nonces_of_term (elements s).
Proof.
move=> x; rewrite nonces_of_term_atoms => /elem_of_union_list.
case=> X [/list_elem_of_fmap [z [-> /elem_of_atoms [y [-> yt]]]] xz].
have [wy _] := PreTerm.atoms_wf _ _ (wf_unfold_term _) yt.
move: yt xz; rewrite /PreTerm.atoms pre_frac_TMul (nonces_of_term_fold wy).
move=> /(Frac.vars_sprod _ s y) [u [us yu]] xy.
apply: (elem_of_union_list_nonces (u := u)); first exact/SMS.elem_of_elements.
exact: nonces_of_frac_var yu xy.
Qed.

Lemma nonces_of_term_TSum_subseteq s :
  nonces_of_term (TSum s) ⊆ ⋃ map nonces_of_term (elements s).
Proof.
move=> x; rewrite nonces_of_term_atoms => /elem_of_union_list.
case=> X [/list_elem_of_fmap [z [-> /elem_of_atoms [y [-> yt]]]] xz].
have [wy _] := PreTerm.atoms_wf _ _ (wf_unfold_term _) yt.
have E : PreTerm.frac_of (unfold_term (TSum s)) =
         Frac.ssum (λ u, PreTerm.frac_of (unfold_term u)) s.
  rewrite -unfold_frac_of frac_of_TSum.
  rewrite (Frac.map_ssum unfold_term unfold_term_inj).
  by apply: Frac.ssum_ext => u _; rewrite unfold_frac_of.
move: yt xz; rewrite /PreTerm.atoms E (nonces_of_term_fold wy).
move=> /(Frac.vars_ssum _ s y) [u [us yu]] xy.
apply: (elem_of_union_list_nonces (u := u)); first exact/SMS.elem_of_elements.
exact: nonces_of_frac_var yu xy.
Qed.

Lemma nonces_of_term_TExp_subseteq t e :
  nonces_of_term (TExp t e) ⊆ nonces_of_term t ∪ nonces_of_term e.
Proof.
move=> x /nonces_of_term_dh /elem_of_dh_nonces [k [+ h]].
rewrite dh_map_TExp unfold_frac_of => nk; move: h.
rewrite dh_map_TExp unfold_frac_of.
have tk : dh_map t !!! k ≠ Frac.zero.
  by move=> e0; apply: nk; rewrite e0 Frac.mul_zero_l.
case=> [xk|[y [/(Frac.vars_mul _ _ y) [yt|ye] xy]]].
- apply/elem_of_union; left; apply/nonces_of_term_dh/elem_of_dh_nonces.
  by exists k; split=> //; left.
- apply/elem_of_union; left; apply/nonces_of_term_dh/elem_of_dh_nonces.
  by exists k; split=> //; right; exists y.
- by apply/elem_of_union; right; exact: nonces_of_frac_var ye xy.
Qed.

Lemma nonces_of_term_TInv t : nonces_of_term (TInv t) = nonces_of_term t.
Proof.
apply: leibniz_equiv.
have sub u : nonces_of_term (TInv u) ⊆ nonces_of_term u.
  move=> x /nonces_of_term_TMul_subseteq /elem_of_union_list.
  case=> X [/list_elem_of_fmap [v [-> /SMS.elem_of_elements]]].
  move=> /SMS.elem_of_count; rewrite SMS.count_inv => h.
  have : v ∈ ({[+ u +]} : tsms) by apply/SMS.elem_of_count; lia.
  by move/SMS.elem_of_singleton => ->.
move=> x; split; first exact: sub.
by rewrite -{1}(TInvK t); exact: sub.
Qed.

Lemma nonces_of_term_TGInv t : nonces_of_term (TGInv t) = nonces_of_term t.
Proof.
apply: leibniz_equiv.
have sub u : nonces_of_term (TGInv u) ⊆ nonces_of_term u.
  move=> x /nonces_of_term_TGMul_subseteq /elem_of_union_list.
  case=> X [/list_elem_of_fmap [v [-> /SMS.elem_of_elements]]].
  move=> /SMS.elem_of_count; rewrite SMS.count_inv => h.
  have : v ∈ ({[+ u +]} : tsms) by apply/SMS.elem_of_count; lia.
  by move/SMS.elem_of_singleton => ->.
move=> x; split; first exact: sub.
by rewrite -{1}(TGInvK t); exact: sub.
Qed.

Lemma nonces_of_term_TMul s :
  (∀ u, u ∈ s → negb (is_mod u)) →
  nonces_of_term (TMul s) = ⋃ map nonces_of_term (elements s).
Proof.
move=> Hs; apply: leibniz_equiv => x; split.
  exact: nonces_of_term_TMul_subseteq.
case/elem_of_union_list=> X [/list_elem_of_fmap [u [-> /SMS.elem_of_elements]]].
move=> us xu; rewrite nonces_of_term_atoms.
apply: (elem_of_union_list_nonces (u := u)) xu.
by apply: (factors_atoms _ (Hs u us)); rewrite factors_TMul_atoms.
Qed.

Lemma nonces_of_term_TExp t e :
  negb (is_exp t) → negb (is_gmul t) → frac_of e ≠ Frac.zero →
  nonces_of_term (TExp t e) = nonces_of_term t ∪ nonces_of_term e.
Proof.
move=> Nx Ng ne; apply: leibniz_equiv => x; split.
  exact: nonces_of_term_TExp_subseteq.
have Ht : dh_map t = {[unfold_term t := Frac.one]}.
  rewrite /dh_map PreTerm.dh_map_Ngnf //.
  rewrite /PreTerm.is_gnon_free -is_exp_unfold -is_gmul_unfold.
  by move: Nx Ng; case: (is_exp t); case: (is_gmul t).
have re : PreTerm.frac_of (unfold_term e) ≠ Frac.zero.
  rewrite -unfold_frac_of => h; apply: ne.
  by apply: (Frac.map_inj unfold_term unfold_term_inj); rewrite h Frac.map_zero.
have lk : dh_map (TExp t e) !!! unfold_term t = PreTerm.frac_of (unfold_term e).
  rewrite dh_map_TExp unfold_frac_of Ht FMap.lookup_singleton.
  by rewrite bool_decide_eq_true_2 // (left_id Frac.one Frac.mul).
move=> /elem_of_union [xt|xe]; apply/nonces_of_term_dh/elem_of_dh_nonces.
- exists (unfold_term t); rewrite lk; split=> //; left.
  by move: xt; rewrite [nonces_of_term]unlock.
- exists (unfold_term t); rewrite lk; split=> //; right.
  move: xe; rewrite nonces_of_term_atoms => /elem_of_union_list.
  case=> X [/list_elem_of_fmap [z [-> /elem_of_atoms [y [-> yt]]]] xz].
  have [wy _] := PreTerm.atoms_wf _ _ (wf_unfold_term e) yt.
  by exists y; split=> //; rewrite -(nonces_of_term_fold wy).
Qed.

Lemma nonces_of_term_base_expo t :
  nonces_of_term t = nonces_of_term (base t) ∪ nonces_of_term (expo t).
Proof.
apply: leibniz_equiv => x; rewrite elem_of_union.
case G: (is_gmul t).
  have nE : negb (is_exp t) by apply: is_gmul_Nexp; rewrite G.
  rewrite (base_expN nE) (expo_expN nE).
  have E0 : x ∉ nonces_of_term (TMul ∅).
    move=> /nonces_of_term_TMul_subseteq.
    by rewrite SMS.elements_empty /= => /elem_of_empty.
  by split; [left|case].
have Nt : negb (PreTerm.is_gmul (unfold_term t)) by rewrite -is_gmul_unfold G.
have we := PreTerm.wf_expo _ (wf_unfold_term t).
have EB : nonces_of_term (base t) =
          nonces_of_pre_term (PreTerm.base (unfold_term t)).
  by rewrite [nonces_of_term]unlock unfold_base.
have EE : x ∈ nonces_of_term (expo t) ↔
    ∃ y, y ∈ Frac.vars (PreTerm.frac_of (PreTerm.expo (unfold_term t)))
         ∧ x ∈ nonces_of_pre_term y.
  rewrite [nonces_of_term]unlock unfold_expo
    -{1}(PreTerm.mod_of_frac_frac_of _ we).
  rewrite nonces_of_pre_term_mod_of_frac elem_of_union_list; split.
  - by case=> X [/list_elem_of_fmap [y [-> yr]] xy]; exists y.
  - case=> y [yr xy]; exists (nonces_of_pre_term y); split=> //.
    exact: list_elem_of_fmap_2.
rewrite nonces_of_term_dh /dh_map
  (PreTerm.dh_map_Ngmul _ (wf_unfold_term t) Nt).
rewrite elem_of_dh_nonces EB EE; split.
- case=> k [nk h]; move: nk h; rewrite FMap.lookup_singleton.
  case: bool_decide_reflect => [->|_]; last by move=> /(_ eq_refl).
  by move=> _ [xk|[y [yr xy]]]; [left|right; exists y].
- move=> h; exists (PreTerm.base (unfold_term t)).
  rewrite FMap.lookup_singleton bool_decide_eq_true_2 //; split.
    exact: Frac.mono_num_neq0 (PreTerm.mono_num_expo _ (wf_unfold_term t) Nt).
  by case: h => [xb|[y [yr xy]]]; [left|right; exists y].
Qed.

(** ** Factors *)

Lemma nonces_of_term_factors_sub t u :
  u ∈ factors t → nonces_of_term u ⊆ nonces_of_term t.
Proof.
move=> /elem_of_factors_unfold ut x.
rewrite (nonces_of_term_atoms u) => /elem_of_union_list.
case=> X [/list_elem_of_fmap [z [-> /elem_of_atoms [y [-> yu]]]] xz].
have [wy _] := PreTerm.atoms_wf _ _ (wf_unfold_term u) yu.
move: xz; rewrite (nonces_of_term_fold wy) => xy.
exact: nonces_of_frac_var
  (PreTerm.factors_atoms_sub _ _ _ (wf_unfold_term t) ut yu) xy.
Qed.

Lemma nonces_of_term_factors t :
  nonces_of_term t = ⋃ map nonces_of_term (elements (factors t)).
Proof.
apply: leibniz_equiv => x; split.
- move=> xt; apply: (@nonces_of_term_TMul_subseteq (factors t) x).
  by rewrite factorsK.
- case/elem_of_union_list=> X [/list_elem_of_fmap [u [-> ]]].
  by move=> /SMS.elem_of_elements ut; exact: nonces_of_term_factors_sub.
Qed.

(** ** Group factors *)

Lemma nonces_of_term_gfactors_sub t u :
  u ∈ gfactors t → nonces_of_term u ⊆ nonces_of_term t.
Proof.
move=> /elem_of_gfactors_unfold ut x.
have [b [r [nb [Eu [nr vr]]]]] := PreTerm.gfactors_dh_vars _ _
  (wf_unfold_term t) ut.
rewrite !nonces_of_term_dh /dh_map Eu !elem_of_dh_nonces.
case=> k [+ h]; rewrite FMap.lookup_singleton.
case: bool_decide_reflect => [ek|_]; last by move=> /(_ eq_refl).
subst k => _; exists b; split=> //.
case: h => [xb|[y [yr xy]]]; first by left.
right; exists y; split=> //; apply: vr.
by move: yr; rewrite FMap.lookup_singleton bool_decide_eq_true_2.
Qed.

Lemma nonces_of_term_gfactors t :
  nonces_of_term t = ⋃ map nonces_of_term (elements (gfactors t)).
Proof.
apply: leibniz_equiv => x; split.
- move=> xt; apply: (@nonces_of_term_TGMul_subseteq (gfactors t) x).
  by rewrite gfactorsK.
- case/elem_of_union_list=> X [/list_elem_of_fmap [u [-> ]]].
  move=> /SMS.elem_of_elements ut xu.
  exact: (nonces_of_term_gfactors_sub ut xu).
Qed.

Lemma nonces_of_term_base_exps t :
  nonces_of_term t =
  nonces_of_term (base t) ∪ ⋃ map nonces_of_term (elements (exps t)).
Proof.
rewrite {1}nonces_of_term_base_expo.
by rewrite [nonces_of_term (expo t)]nonces_of_term_factors.
Qed.

Definition nonces_of_termE :=
  (nonces_of_term_TInv, nonces_of_term_TGInv, nonces_of_termE').
