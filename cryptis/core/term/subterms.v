From cryptis Require Import lib.
From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import sorting gmap.
From cryptis.lib Require Import list_sort mathcomp_compat fmap mset sms frac.
From iris.heap_lang Require locations.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core Require Export pre_term.
From cryptis.core.term Require Import base algebra tsize log repr nonces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Implicit Types (t k : term) (ts : list term).

(* The immediate subterms of an exponent are its atoms, those of a power are
   its base and the atoms of its exponent, and those of a group product are
   its group factors.  On terms of other kinds these constructors only relate
   a term to itself.  [nonces_of_termP] links the relation to
   [nonces_of_term].  The atoms of a logarithm are subterms
   ([subterm_log]), so a logarithm avoids atoms too large to occur in its
   term or containing a subterm that it lacks ([log_small], [log_fresh]). *)

Inductive subterm (t : term) : term → Prop :=
| STRefl : subterm t t
| STPair1 t1 t2 of subterm t t1 : subterm t (TPair t1 t2)
| STPair2 t1 t2 of subterm t t2 : subterm t (TPair t1 t2)
| STKey kt t' of subterm t t' : subterm t (TKey kt t')
| STSeal1 k t' of subterm t k : subterm t (TSeal k t')
| STSeal2 k t' of subterm t t' : subterm t (TSeal k t')
| STHash t' of subterm t t' : subterm t (THash t')
| STAtom t' t'' of t'' ∈ atoms t' & subterm t t'' : subterm t t'
| STBase t' of subterm t (base t') : subterm t t'
| STExpo t' t'' of t'' ∈ atoms (expo t') & subterm t t'' : subterm t t'
| STGFactor t' t'' of t'' ∈ gfactors t' & subterm t t'' : subterm t t'.

#[global] Instance subterm_refl : Reflexive subterm.
Proof. exact: STRefl. Qed.
#[global] Hint Resolve STRefl : core.

#[global] Instance subterm_trans : Transitive subterm.
Proof.
move=> t1 t2 t3 sub12 sub23; elim: t3 / sub23; by eauto using subterm.
Qed.

Lemma subterm_atoms t b u : u ∈ atoms b → subterm t u → subterm t b.
Proof. exact: STAtom. Qed.

Lemma subterm_factors t b u :
  u ∈ factors b → negb (is_mod u) → subterm t u → subterm t b.
Proof. by move=> ub nu; apply: STAtom; exact: factors_atoms. Qed.

Lemma subterm_gfactors t b u : u ∈ gfactors b → subterm t u → subterm t b.
Proof. exact: STGFactor. Qed.

Lemma subterm_base t : subterm (base t) t.
Proof. exact: STBase. Qed.

Lemma subterm_exps t1 t2 :
  t1 ∈ exps t2 → negb (is_mod t1) → subterm t1 t2.
Proof.
by move=> h n1; apply: (@STExpo _ _ t1) => //; exact: factors_atoms.
Qed.

Lemma subterm_TExp_g g (x : nonce) :
  negb (is_exp g) → negb (is_gmul g) → subterm (TNonce x) (TExp g x).
Proof.
move=> gNX gNm; apply: (@STExpo _ _ (TNonce x)) => //.
rewrite (expo_TExp_expN gNX gNm);
  last exact: laurent_mono_num (laurent_atom _ _).
exact/atoms_atom.
Qed.

Lemma subterm_nonces_of_term t1 t2 :
  subterm t1 t2 → nonces_of_term t1 ⊆ nonces_of_term t2.
Proof.
elim: t2 / => //;
  try by intros; rewrite [X in _ ⊆ X]nonces_of_termE; set_solver.
- move=> t' t'' t''_t' _ IH x /IH xt''.
  by rewrite nonces_of_term_atoms; exact: elem_of_union_list_nonces xt''.
- move=> t' _ IH x /IH xb.
  by rewrite (nonces_of_term_base_expo t'); apply/elem_of_union; left.
- move=> t' t'' t''_e _ IH x /IH xt''.
  rewrite (nonces_of_term_base_expo t'); apply/elem_of_union; right.
  by rewrite nonces_of_term_atoms; exact: elem_of_union_list_nonces xt''.
- move=> t' t'' t''_t' _ IH x /IH xt''.
  exact: (nonces_of_term_gfactors_sub t''_t' xt'').
Qed.

Lemma nonces_of_termP (a : nonce) t :
  subterm (TNonce a) t ↔ a ∈ nonces_of_term t.
Proof.
split.
  move=> /subterm_nonces_of_term; apply.
  by rewrite nonces_of_termE'; exact/elem_of_singleton.
elim/term_lt_ind: t => t IH.
case Em: (is_mod t).
  rewrite nonces_of_term_atoms => /elem_of_union_list.
  case=> X [/list_elem_of_fmap [y [-> yt]] ay].
  apply: (@STAtom _ _ y) => //; apply: IH ay.
  by apply: tsize_atoms_lt; rewrite ?Em.
case Ex: (is_exp t).
  rewrite nonces_of_term_base_expo => /elem_of_union [ab|ae].
    apply: STBase; apply: IH ab.
    by apply: tsize_base_lt; rewrite Ex.
  move: ae; rewrite nonces_of_term_atoms => /elem_of_union_list.
  case=> X [/list_elem_of_fmap [y [-> ye]] ay].
  apply: (@STExpo _ _ y) => //; apply: IH ay.
  have := tsize_expo_lt t ltac:(by rewrite Ex).
  case Me: (is_mod (expo t)).
    by have := @tsize_atoms_lt y (expo t) ltac:(by rewrite Me) ye; lia.
  by move: ye; rewrite atoms_atom ?Me // => ->; lia.
case Eg: (is_gmul t).
  move=> at'; have := @nonces_of_term_TGMul_subseteq (gfactors t) a.
  rewrite gfactorsK => /(_ at') /elem_of_union_list.
  case=> X [/list_elem_of_fmap [u [-> /SMS.elem_of_elements ut]] au].
  apply: (@STGFactor _ _ u) => //; apply: IH au.
  by apply: tsize_gfactors_lt; rewrite ?Eg.
case: t IH Em Ex Eg => [n|ta tb|a'|kt tt|kk tt|tt|pt wf nf] IH Em Ex Eg.
- by rewrite nonces_of_termE' /= => /elem_of_empty.
- rewrite nonces_of_termE' /= => /elem_of_union [H|H].
  + apply: STPair1; apply: (IH ta _ H).
    by rewrite [tsize (TPair ta tb)]tsize_eq; lia.
  + apply: STPair2; apply: (IH tb _ H).
    by rewrite [tsize (TPair ta tb)]tsize_eq; lia.
- by rewrite nonces_of_termE' /= => /elem_of_singleton ->.
- rewrite nonces_of_termE' /= => H.
  apply: STKey; apply: (IH tt _ H).
  by rewrite [tsize (TKey kt tt)]tsize_eq; lia.
- rewrite nonces_of_termE' /= => /elem_of_union [H|H].
  + apply: STSeal1; apply: (IH kk _ H).
    by rewrite [tsize (TSeal kk tt)]tsize_eq; lia.
  + apply: STSeal2; apply: (IH tt _ H).
    by rewrite [tsize (TSeal kk tt)]tsize_eq; lia.
- rewrite nonces_of_termE' /= => H.
  apply: STHash; apply: (IH tt _ H).
  by rewrite [tsize (THash tt)]tsize_eq; lia.
- have := nf; rewrite /is_non_free PreTerm.is_dh_exp_gmul.
  by move: Em Ex Eg; rewrite /is_mod /is_exp /is_gmul /= => -> -> ->.
Qed.

Lemma subterm_tsize t1 t2 : subterm t1 t2 → tsize t1 ≤ tsize t2.
Proof.
elim: t2 / => //.
- move=> t1' t2' _ IH; rewrite [tsize (TPair _ _)]tsize_eq; lia.
- move=> t1' t2' _ IH; rewrite [tsize (TPair _ _)]tsize_eq; lia.
- move=> kt t' _ IH; rewrite [tsize (TKey _ _)]tsize_eq; lia.
- move=> k t' _ IH; rewrite [tsize (TSeal _ _)]tsize_eq; lia.
- move=> k t' _ IH; rewrite [tsize (TSeal _ _)]tsize_eq; lia.
- move=> t' _ IH; rewrite [tsize (THash _)]tsize_eq; lia.
- move=> t' t'' t''_t' _ IH.
  case Em: (is_mod t').
    by have := @tsize_atoms_lt t'' t' ltac:(by rewrite Em) t''_t'; lia.
  by move: t''_t' IH; rewrite atoms_atom ?Em // => ->.
- move=> t' _ IH; case Ex: (is_exp t').
    by have := @tsize_base_lt t' ltac:(by rewrite Ex); lia.
  by move: IH; rewrite base_expN ?Ex.
- move=> t' t'' t''_e _ IH; case Ex: (is_exp t').
    have := @tsize_expo_lt t' ltac:(by rewrite Ex).
    case Em: (is_mod (expo t')).
      by have := @tsize_atoms_lt t'' (expo t') ltac:(by rewrite Em) t''_e; lia.
    by move: t''_e IH; rewrite atoms_atom ?Em // => ->; lia.
  move: t''_e; rewrite expo_expN ?Ex // => /elem_of_atoms [y [_]].
  rewrite /PreTerm.atoms unfold_TMul_empty PreTerm.frac_of_one => yo.
  by case: (Frac.vars_one y yo).
- move=> t' t'' t''_t' _ IH.
  by have := tsize_gfactors_le _ _ t''_t'; lia.
Qed.

Lemma subterm_log x k t : x ∈ atoms (log k t) → subterm x t.
Proof.
move=> /elem_of_atoms [y [-> yl]].
move: yl; rewrite /PreTerm.atoms pre_frac_log.
have -> : dh_map t !!! unfold_term k =
          Frac.ssum (λ u, dh_map u !!! unfold_term k) (gfactors t).
  by rewrite -dh_map_TGMul gfactorsK.
move=> /(Frac.vars_ssum _ (gfactors t) y) [u [ut yu]].
have Nu := Ngmul_gfactors _ _ ut.
move: yu; rewrite (dh_map_Ngmul Nu) FMap.lookup_singleton.
case: bool_decide; last by move=> yz; case: (Frac.vars_zero y yz).
move=> yu; apply: (@STGFactor _ _ u ut).
apply: (@STExpo _ _ (fold_term y)); last exact: STRefl.
apply/elem_of_atoms; exists y; split=> //.
by rewrite /PreTerm.atoms unfold_expo.
Qed.

Lemma log_small h k t : tsize t < tsize h → h ∉ atoms (log k t).
Proof. by move=> lt /subterm_log /subterm_tsize; lia. Qed.

Lemma log_fresh n h k t : subterm n h → ¬ subterm n t → h ∉ atoms (log k t).
Proof. by move=> nh nt /subterm_log ht; apply: nt; transitivity h. Qed.
