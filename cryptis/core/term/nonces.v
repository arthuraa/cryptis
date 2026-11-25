From cryptis Require Import lib.
From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import sorting gmap.
From cryptis.lib Require Import list_sort mathcomp_compat mset sms.
From iris.heap_lang Require locations.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core Require Export pre_term.
From cryptis.core.term Require Import base algebra tsize repr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Implicit Types (t k : term) (ts : list term).

(* nonces_of_term and its theory. *)

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

Lemma nonces_elements_make_sub (X Y : list PreTerm.pre_term) :
  ⋃ map nonces_of_pre_term
      (elements (SMS.make (MSet.of_list X) (MSet.of_list Y))) ⊆
  ⋃ map nonces_of_pre_term X ∪ ⋃ map nonces_of_pre_term Y.
Proof.
rewrite -union_list_app_L -map_app; apply: union_list_fmap_mono => u.
rewrite SMS.elem_of_elements elem_of_app => /SMS.elem_of_make.
by rewrite !MSet.elem_of_of_list.
Qed.

Lemma nonces_of_pre_term_factors_sub e :
  ⋃ map nonces_of_pre_term (elements (PreTerm.factors e)) ⊆
  nonces_of_pre_term e.
Proof.
case Em: (PreTerm.is_mul e).
  case: e Em => [o|o1 e1|o2 e1 e2|ps ns|l] // _.
  exact: nonces_elements_make_sub.
rewrite PreTerm.factors_Nmul ?Em // SMS.elements_singleton /=; set_solver.
Qed.

Lemma nonces_of_pre_term_factors e :
  PreTerm.wf e →
  nonces_of_pre_term e =
  ⋃ map nonces_of_pre_term (elements (PreTerm.factors e)).
Proof.
case Em: (PreTerm.is_mul e) => wf_e; last first.
  rewrite PreTerm.factors_Nmul ?Em // SMS.elements_singleton /=.
  by rewrite union_empty_r_L.
case: e Em wf_e => [o|o1 e1|o2 e1 e2|ps ns|l] // _ wf_e.
by rewrite PreTerm.elements_factors //= map_app union_list_app_L.
Qed.

Lemma nonces_bind_factors_sub s :
  ⋃ map nonces_of_pre_term (elements (SMS.bind PreTerm.factors s)) ⊆
  ⋃ map nonces_of_pre_term (elements s).
Proof.
move=> a /elem_of_union_list [Y [/list_elem_of_fmap [u [-> u_b]] a_u]].
move: u_b; rewrite SMS.elem_of_elements => /SMS.elem_of_bind [v [v_s u_v]].
apply/elem_of_union_list; exists (nonces_of_pre_term v); split.
  by apply/list_elem_of_fmap; exists v; split => //;
     rewrite SMS.elem_of_elements.
apply: nonces_of_pre_term_factors_sub.
apply/elem_of_union_list; exists (nonces_of_pre_term u); split => //.
by apply/list_elem_of_fmap; exists u; split => //; rewrite SMS.elem_of_elements.
Qed.

Lemma nonces_of_pre_term_mul_aux s :
  nonces_of_pre_term (PreTerm.mul_aux s) =
  ⋃ map nonces_of_pre_term (elements s).
Proof.
case Es: (PreTerm.single (PreTerm.lists s)).
  have [t ->] := PreTerm.single_lists s ltac:(by rewrite Es).
  rewrite (PreTerm.mul_aux_single _ t) ?PreTerm.lists_singleton //.
  by rewrite SMS.elements_singleton /= union_empty_r_L.
rewrite PreTerm.mul_aux_Nsingle ?Es //.
by rewrite SMS.elements_pos_neg map_app union_list_app_L.
Qed.

Lemma nonces_of_pre_term_mul_sub s :
  nonces_of_pre_term (PreTerm.mul s) ⊆ ⋃ map nonces_of_pre_term (elements s).
Proof.
rewrite PreTerm.mulE nonces_of_pre_term_mul_aux.
exact: nonces_bind_factors_sub.
Qed.

Lemma nonces_of_pre_term_mk_exp b p :
  nonces_of_pre_term (PreTerm.mk_exp b p) =
  nonces_of_pre_term b ∪ nonces_of_pre_term p.
Proof.
rewrite /PreTerm.mk_exp.
by case: (bool_decide_reflect (p = PreTerm.PTMul [] [])) => [->|_] /=;
  set_solver.
Qed.

Lemma nonces_of_pre_term_dh l :
  nonces_of_pre_term (PreTerm.PTDH l) =
  ⋃ map (λ e, nonces_of_pre_term e.1 ∪ ⋃ map nonces_of_pre_term e.2.1 ∪
               ⋃ map nonces_of_pre_term e.2.2) l.
Proof. done. Qed.

Lemma nonces_sub_union_list p ps :
  p ∈ ps → nonces_of_pre_term p ⊆ ⋃ map nonces_of_pre_term ps.
Proof.
move=> p_in a a_p; apply/elem_of_union_list.
exists (nonces_of_pre_term p); split => //.
by apply/list_elem_of_fmap; exists p.
Qed.

Lemma nonces_of_pre_term_gfactors_sub e :
  ⋃ map nonces_of_pre_term (elements (PreTerm.gfactors e)) ⊆
  nonces_of_pre_term e.
Proof.
case Em: (PreTerm.is_gmul e); last first.
  rewrite PreTerm.gfactors_Ngmul ?Em // SMS.elements_singleton /=; set_solver.
case: e Em => // l Em.
have -> : PreTerm.gfactors (PreTerm.PTDH l) = PreTerm.dh_factors l.
  by case: l Em => [|[b [[|e [|??]] [|??]]] [|??]].
move=> a /elem_of_union_list [Y [/list_elem_of_fmap [u [-> u_in]] a_u]].
move: u_in; rewrite SMS.elem_of_elements.
case/PreTerm.elem_of_dh_factors => [[b [ps ns]] [x [e_l [x_e eu]]]].
rewrite eu nonces_of_pre_term_mk_exp in a_u.
rewrite nonces_of_pre_term_dh; apply/elem_of_union_list.
eexists; split; first by apply/list_elem_of_fmap; exists (b, (ps, ns)).
move: x_e; rewrite /PreTerm.of_lists => /SMS.elem_of_make /=.
rewrite !MSet.elem_of_of_list.
by case=> /nonces_sub_union_list ?; set_solver.
Qed.

Lemma nonces_of_pre_term_gfactors e :
  PreTerm.wf e →
  nonces_of_pre_term e =
  ⋃ map nonces_of_pre_term (elements (PreTerm.gfactors e)).
Proof.
case Em: (PreTerm.is_gmul e) => wf_e; last first.
  rewrite PreTerm.gfactors_Ngmul ?Em // SMS.elements_singleton /=.
  by rewrite union_empty_r_L.
apply: leibniz_equiv => a; split.
  2: by apply: nonces_of_pre_term_gfactors_sub.
case: e Em wf_e => // l Em wf_l.
have elemsE := PreTerm.elements_gfactors _ wf_l.
have fac b p : (b, p) ∈ (λ e, (e.1, e.2.1 ++ e.2.2)) <$> l →
    ∀ q, q ∈ p →
    nonces_of_pre_term (PreTerm.mk_exp b q) ⊆
    ⋃ map nonces_of_pre_term (elements (PreTerm.gfactors (PreTerm.PTDH l))).
  move=> /list_elem_of_fmap [e [[-> ->] e_l]] q q_in.
  apply: nonces_sub_union_list; rewrite elemsE.
  by apply/PreTerm.elem_of_dh_elements; exists e, q.
move: (wf_l); rewrite PreTerm.wf_dhE.
move=> /andb_True [/andb_True [_ /bool_decide_unpack [_ vs]] _].
rewrite nonces_of_pre_term_dh.
move=> /elem_of_union_list [Y [/list_elem_of_fmap [[b [ps ns]] [-> e_l]] a_e]].
have be : (b, ps ++ ns) ∈ (λ e, (e.1, e.2.1 ++ e.2.2)) <$> l.
  by apply/list_elem_of_fmap; exists (b, (ps, ns)).
have [p p_in] : ∃ p, p ∈ ps ++ ns.
  move: (proj1 (list.Forall_forall _ _) vs _ e_l) => /=.
  case: ps {be a_e e_l} => [|p ps] ne; last by exists p; left.
  by case: ns ne => [|n ns] ne; [case: ne|exists n; left].
move: a_e => /= /elem_of_union [/elem_of_union [a_b|a_ps]|a_ns].
- apply: (fac _ _ be p p_in); rewrite nonces_of_pre_term_mk_exp; set_solver.
- move: a_ps => /elem_of_union_list [Y' [/list_elem_of_fmap [q [-> q_in]] a_q]].
  apply: (fac _ _ be q); first by rewrite elem_of_app; left.
  rewrite nonces_of_pre_term_mk_exp; set_solver.
- move: a_ns => /elem_of_union_list [Y' [/list_elem_of_fmap [q [-> q_in]] a_q]].
  apply: (fac _ _ be q); first by rewrite elem_of_app; right.
  rewrite nonces_of_pre_term_mk_exp; set_solver.
Qed.

Lemma nonces_bind_gfactors_sub s :
  ⋃ map nonces_of_pre_term (elements (SMS.bind PreTerm.gfactors s)) ⊆
  ⋃ map nonces_of_pre_term (elements s).
Proof.
move=> a /elem_of_union_list [Y [/list_elem_of_fmap [u [-> u_b]] a_u]].
move: u_b; rewrite SMS.elem_of_elements => /SMS.elem_of_bind [v [v_s u_v]].
apply/elem_of_union_list; exists (nonces_of_pre_term v); split.
  by apply/list_elem_of_fmap; exists v; split => //;
     rewrite SMS.elem_of_elements.
apply: nonces_of_pre_term_gfactors_sub.
apply/elem_of_union_list; exists (nonces_of_pre_term u); split => //.
by apply/list_elem_of_fmap; exists u; split => //; rewrite SMS.elem_of_elements.
Qed.

Lemma nonces_of_pre_term_gmul_aux s :
  PreTerm.wf_gfactors s →
  nonces_of_pre_term (PreTerm.gmul_aux s) =
  ⋃ map nonces_of_pre_term (elements s).
Proof.
move=> wfs; rewrite (nonces_of_pre_term_gfactors (PreTerm.wf_gmul_aux _ wfs)).
by rewrite PreTerm.gmul_auxK.
Qed.

Lemma nonces_of_pre_term_gmul_sub s :
  (∀ pt, pt ∈ s → PreTerm.wf pt) →
  nonces_of_pre_term (PreTerm.gmul s) ⊆ ⋃ map nonces_of_pre_term (elements s).
Proof.
move=> wfs; rewrite /PreTerm.gmul nonces_of_pre_term_gmul_aux.
- exact: nonces_bind_gfactors_sub.
- exact: PreTerm.wf_bind_gfactors.
Qed.

Lemma nonces_of_term_factors t :
  nonces_of_term t = ⋃ map nonces_of_term (elements (factors t)).
Proof.
have wfs : Forall PreTerm.wf (elements (PreTerm.factors (unfold_term t))).
  apply/Forall_forall => x /SMS.elem_of_elements xin.
  exact: PreTerm.wf_factors_wf (PreTerm.wf_wf_factors _ (wf_unfold_term t)) xin.
rewrite [nonces_of_term]unlock (nonces_of_pre_term_factors (wf_unfold_term t)).
rewrite elements_factors; congr union_list.
elim: (elements _) wfs => [//|pt pts IH] /Forall_cons [wpt wpts] /=.
by rewrite (fold_termK pt wpt) (IH wpts).
Qed.

Lemma nonces_of_term_gfactors t :
  nonces_of_term t = ⋃ map nonces_of_term (elements (gfactors t)).
Proof.
have wfs : Forall PreTerm.wf (elements (PreTerm.gfactors (unfold_term t))).
  apply/Forall_forall => x /SMS.elem_of_elements xin.
  exact: PreTerm.wf_gfactors_wf
    (PreTerm.wf_wf_gfactors _ (wf_unfold_term t)) xin.
rewrite [nonces_of_term]unlock (nonces_of_pre_term_gfactors (wf_unfold_term t)).
rewrite elements_gfactors; congr union_list.
elim: (elements _) wfs => [//|pt pts IH] /Forall_cons [wpt wpts] /=.
by rewrite (fold_termK pt wpt) (IH wpts).
Qed.

Lemma nonces_of_pre_term_base_expo pt :
  nonces_of_pre_term pt =
  nonces_of_pre_term (PreTerm.base pt) ∪ nonces_of_pre_term (PreTerm.expo pt).
Proof. by case: (PreTerm.is_expP pt) => [b e ->|_ -> ->] /=; set_solver. Qed.

Lemma nonces_of_term_base_exps t :
  nonces_of_term t =
  nonces_of_term (base t) ∪ ⋃ map nonces_of_term (elements (exps t)).
Proof.
rewrite /exps -(nonces_of_term_factors (expo t)).
rewrite ![nonces_of_term]unlock unfold_base unfold_expo.
exact: nonces_of_pre_term_base_expo.
Qed.

Lemma nonces_of_term_TInv t : nonces_of_term (TInv t) = nonces_of_term t.
Proof.
rewrite nonces_of_term_factors factors_TInv [in RHS]nonces_of_term_factors.
by rewrite SMS.elements_inv.
Qed.

Lemma nonces_of_term_TGInv t : nonces_of_term (TGInv t) = nonces_of_term t.
Proof.
rewrite nonces_of_term_gfactors gfactors_TGInv [in RHS]nonces_of_term_gfactors.
by rewrite SMS.elements_inv.
Qed.

Lemma nonces_of_pre_term_exp_aux_sub (pt pe : PreTerm.pre_term) :
  nonces_of_pre_term (PreTerm.exp_aux pt pe)
  ⊆ nonces_of_pre_term pt ∪ nonces_of_pre_term pe.
Proof.
have mk : forall X Y, nonces_of_pre_term (PreTerm.mk_exp X Y)
                    ⊆ nonces_of_pre_term X ∪ nonces_of_pre_term Y.
  by move=> X Y; rewrite /PreTerm.mk_exp; case: bool_decide => /=; set_solver.
rewrite /PreTerm.exp_aux.
have Hbe := nonces_of_pre_term_base_expo pt.
pose proof (@nonces_of_pre_term_mul_sub {[+ PreTerm.expo pt; pe +]}) as Hmul.
have Hel :
    ⋃ map nonces_of_pre_term
        (elements ({[+ PreTerm.expo pt; pe +]} : SMS.sms _)) ⊆
    nonces_of_pre_term (PreTerm.expo pt) ∪ nonces_of_pre_term pe.
  trans (⋃ map nonces_of_pre_term [PreTerm.expo pt; pe]).
  - apply: (union_list_fmap_mono nonces_of_pre_term
      (elements ({[+ PreTerm.expo pt; pe +]} : SMS.sms _))
      [PreTerm.expo pt; pe]) => u.
    rewrite SMS.elem_of_elements => /SMS.elem_of_disj_union.
    case=> /SMS.elem_of_singleton ->; first exact: list_elem_of_here.
    by apply: list_elem_of_further; exact: list_elem_of_here.
  - by rewrite /= union_empty_r_L.
pose proof (transitivity Hmul Hel) as H; clear Hmul Hel.
etrans; first exact: mk.
rewrite Hbe; move: H.
move: (nonces_of_pre_term (PreTerm.mul {[+ PreTerm.expo pt; pe +]})) => X.
clear mk Hbe; set_solver.
Qed.

Lemma nonces_of_pre_term_exp_sub (pb pe : PreTerm.pre_term) :
  PreTerm.wf pb → PreTerm.wf pe →
  nonces_of_pre_term (PreTerm.exp pb pe)
  ⊆ nonces_of_pre_term pb ∪ nonces_of_pre_term pe.
Proof.
move=> wf_b wf_e; rewrite /PreTerm.exp.
have wfg := PreTerm.wf_wf_gfactors _ wf_b.
etrans.
  apply: nonces_of_pre_term_gmul_sub => pt /SMS.elem_of_map [v [-> v_b]].
  apply: PreTerm.wf_exp_aux => //.
  - exact: PreTerm.wf_gfactors_wf wfg v_b.
  - exact: PreTerm.wf_gfactors_Ngmul wfg v_b.
move=> a /elem_of_union_list [Y [/list_elem_of_fmap [u [-> u_in]] a_u]].
move: u_in; rewrite SMS.elem_of_elements => /SMS.elem_of_map [v [e_u v_pb]].
subst u.
have /elem_of_union [a_v|a_pe] := @nonces_of_pre_term_exp_aux_sub v pe a a_u.
  apply/elem_of_union; left; apply: (@nonces_of_pre_term_gfactors_sub pb).
  apply/elem_of_union_list; exists (nonces_of_pre_term v); split => //.
  by apply/list_elem_of_fmap; exists v; split => //;
     rewrite SMS.elem_of_elements.
by apply/elem_of_union; right.
Qed.

Lemma union_list_map_unfold ts :
  ⋃ map nonces_of_term ts = ⋃ map nonces_of_pre_term (map unfold_term ts).
Proof.
congr union_list; elim: ts => [|t' ts IH] //=.
by rewrite IH [nonces_of_term]unlock.
Qed.

Lemma nonces_of_term_TMul_subseteq s :
  nonces_of_term (TMul s) ⊆ ⋃ map nonces_of_term (elements s).
Proof.
rewrite union_list_map_unfold [nonces_of_term]unlock unfold_TMul.
etrans; first exact: nonces_of_pre_term_mul_sub.
by rewrite (SMS.elements_map_inj _ _ unfold_term_inj).
Qed.

Lemma nonces_of_term_TGMul_subseteq s :
  nonces_of_term (TGMul s) ⊆ ⋃ map nonces_of_term (elements s).
Proof.
rewrite union_list_map_unfold [nonces_of_term]unlock unfold_TGMul.
etrans.
  apply: nonces_of_pre_term_gmul_sub => pt /SMS.elem_of_map [t [-> _]].
  exact: wf_unfold_term.
by rewrite (SMS.elements_map_inj _ _ unfold_term_inj).
Qed.

Lemma nonces_of_term_TExp_subseteq t e :
  nonces_of_term (TExp t e) ⊆ nonces_of_term t ∪ nonces_of_term e.
Proof.
rewrite ![nonces_of_term]unlock unfold_TExp.
exact: nonces_of_pre_term_exp_sub (wf_unfold_term _) (wf_unfold_term _).
Qed.

Lemma nonces_of_term_TMul s :
  (∀ u, u ∈ s → negb (is_mul u)) ->
  nonces_of_term (TMul s) = ⋃ map nonces_of_term (elements s).
Proof. by move=> Hs; rewrite nonces_of_term_factors factors_TMul_atoms. Qed.

Lemma nonces_of_term_TGMul s :
  (∀ u, u ∈ s → negb (is_gmul u)) ->
  nonces_of_term (TGMul s) = ⋃ map nonces_of_term (elements s).
Proof. by move=> Hs; rewrite nonces_of_term_gfactors gfactors_TGMul_atoms. Qed.

Lemma nonces_of_term_TExp_TMul t s :
  negb (is_exp t) -> negb (is_gmul t) ->
  (∀ u, u ∈ s → negb (is_mul u)) ->
  nonces_of_term (TExp t (TMul s)) =
  nonces_of_term t ∪ ⋃ map nonces_of_term (elements s).
Proof.
move=> tNexp tNm Hs.
rewrite (nonces_of_term_base_exps (TExp t (TMul s))).
by rewrite (base_TExp _ _ tNm) (base_expN _ tNexp) exps_TExp_TMul.
Qed.

Definition nonces_of_termE :=
  (nonces_of_term_TInv, nonces_of_term_TGInv, nonces_of_term_TExp_TMul,
   nonces_of_term_TMul, nonces_of_term_TGMul, nonces_of_termE').
