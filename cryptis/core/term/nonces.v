From cryptis Require Import lib.
From elpi.apps Require Import locker.
From mathcomp Require Import ssreflect.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import sorting gmap.
From cryptis.lib Require Import list_sort mathcomp_compat sms.
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

Definition nonces_of_term_def (t : term) :=
  nonces_of_pre_term (unfold_term t).
Arguments nonces_of_term_def /.
Definition nonces_of_term_aux : seal nonces_of_term_def. by eexists. Qed.
Definition nonces_of_term := unseal nonces_of_term_aux.
Lemma nonces_of_term_unseal : nonces_of_term = nonces_of_term_def.
Proof. exact: seal_eq. Qed.

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
by rewrite nonces_of_term_unseal; case: t => //=.
Qed.

Lemma nonces_of_term_fold pt :
  PreTerm.wf pt -> nonces_of_term (fold_term pt) = nonces_of_pre_term pt.
Proof. move => wf. by rewrite nonces_of_term_unseal /nonces_of_term_def (@fold_termK pt wf). Qed.

Lemma nonces_of_pre_term_factors e :
  nonces_of_pre_term e = ⋃ map nonces_of_pre_term (PreTerm.factors e).
Proof. by case: e => [o|o1 e1|o2 e1 e2|es] //=; rewrite union_empty_r_L. Qed.

Lemma nonces_of_pre_term_inv_aux x :
  nonces_of_pre_term (PreTerm.inv_aux x) = nonces_of_pre_term x.
Proof. by case: x => [o|[kt||] e|o e1 e2|es] //=. Qed.

Lemma union_list_map_merge_sort {A X} `{Countable X} (f : A → gset X)
  (R : relation A) `{!RelDecision R} l :
  ⋃ map f (merge_sort R l) = ⋃ map f l.
Proof.
apply: union_list_permutation_proper_L; apply: Permutation_map.
exact: (merge_sort_Permutation R l).
Qed.

Lemma union_list_map_to_pt {X} `{Countable X}
  (f : PreTerm.pre_term → gset X) l :
  (forall x, x ∈ l -> PreTerm.inv_aux x ∉ l) ->
  ⋃ map f (SMS.to pt_order PreTerm.inv_aux l) = ⋃ map f l.
Proof.
move=> nc; apply: union_list_permutation_proper_L; apply: Permutation_map.
exact: (SMS.to_id_perm pt_order PreTerm.inv_aux l nc).
Qed.

Lemma nonces_of_pre_term_inv pt :
  PreTerm.wf pt ->
  nonces_of_pre_term (PreTerm.inv pt) = nonces_of_pre_term pt.
Proof.
case: pt => [o|o t|o t1 t2|ts] wf;
  try by rewrite PreTerm.inv_Nmul // nonces_of_pre_term_inv_aux.
rewrite /PreTerm.inv /PreTerm.mul.
(* [mul_aux] only collapses a singleton, which does not change the union. *)
have mulauxE : forall X, nonces_of_pre_term (PreTerm.mul_aux X)
                       = ⋃ map nonces_of_pre_term X.
  by case=> [|x [|y l]] //=; rewrite union_empty_r_L.
have wfF : PreTerm.wf_factors ts by move: wf => /andb_True [].
have wfx : forall x, x ∈ ts -> PreTerm.wf x.
  by move=> x xin; apply: PreTerm.wf_factors_wf wfF xin.
have sms : SMS.wf pt_order PreTerm.inv_aux ts by apply: PreTerm.wf_factors_sms wfF.
have nopairs : forall x, x ∈ ts -> PreTerm.inv_aux x ∉ ts.
  by apply: SMS.wf_no_pairs sms.
have invol : forall x, x ∈ ts -> PreTerm.inv_aux (PreTerm.inv_aux x) = x.
  by apply: SMS.wf_invol sms.
(* Inverting a well-formed non-product never produces a product. *)
have NmI : forall x, x ∈ ts -> negb (PreTerm.is_mul (PreTerm.inv_aux x)).
  move=> x xin; have := wfx x xin.
  by case: x {xin} => [o|[k| |] t|o t1 t2|ts'] //= /andb_True [] /andb_True [] _.
have flat : forall l, (forall x, x ∈ l -> negb (PreTerm.is_mul x)) ->
              mbind PreTerm.factors l = l.
  elim=> [//|x l IH] H /=.
  rewrite PreTerm.factors_Nmul; last by apply: H; apply/elem_of_cons; left.
  by rewrite -/(mbind PreTerm.factors l) IH // => y yin; apply: H;
     apply/elem_of_cons; right.
(* [inv_aux] is an involution on [ts], so it maps the no-inverse-pair condition
   to itself. *)
have nopairsI : forall y, y ∈ (PreTerm.inv_aux <$> ts) ->
                  PreTerm.inv_aux y ∉ (PreTerm.inv_aux <$> ts).
  move=> _ /list_elem_of_fmap [x [-> xin]].
  rewrite (invol x xin) => /list_elem_of_fmap [x' [e x'in]].
  by apply: (nopairs x' x'in); rewrite -e.
rewrite mulauxE /PreTerm.normalize_factors.
rewrite flat; last by move=> _ /list_elem_of_fmap [x [-> xin]]; exact: NmI.
rewrite (union_list_map_to_pt nonces_of_pre_term nopairsI) /=.
by elim: ts {wf wfF wfx sms nopairs invol NmI flat nopairsI}
  => [//|x l IH] /=; rewrite nonces_of_pre_term_inv_aux IH.
Qed.

Lemma nonces_of_term_TInv t : nonces_of_term (TInv t) = nonces_of_term t.
Proof.
rewrite !nonces_of_term_unseal /nonces_of_term_def unfold_TInv.
exact: nonces_of_pre_term_inv (wf_unfold_term t).
Qed.

Lemma nonces_of_term_factors t :
  nonces_of_term t = ⋃ map nonces_of_term (factors t).
Proof.
have wfs : Forall PreTerm.wf (PreTerm.factors (unfold_term t)).
  apply/Forall_forall => x xin.
  by apply: PreTerm.wf_factors_wf
       (PreTerm.wf_wf_factors _ (wf_unfold_term t)) xin.
rewrite nonces_of_term_unseal /nonces_of_term_def
  (nonces_of_pre_term_factors (unfold_term t)) /factors.
congr union_list.
elim: (PreTerm.factors (unfold_term t)) wfs
  => [//|pt pts IH] /Forall_cons [wpt wpts] /=.
by rewrite (fold_termK pt wpt) (IH wpts).
Qed.

Lemma nonces_of_pre_term_base_expo pt :
  nonces_of_pre_term pt =
  nonces_of_pre_term (PreTerm.base pt) ∪ nonces_of_pre_term (PreTerm.expo pt).
Proof. by case: pt => [o|o1 e1|[||] e1 e2|es] //=; rewrite union_empty_r_L. Qed.

Lemma nonces_of_term_base_exps t :
  nonces_of_term t = nonces_of_term (base t) ∪ ⋃ map nonces_of_term (exps t).
Proof.
rewrite /exps -(nonces_of_term_factors (expo t)).
rewrite !nonces_of_term_unseal /nonces_of_term_def unfold_base unfold_expo.
exact: nonces_of_pre_term_base_expo.
Qed.

Lemma nonces_flatten_factors us :
  ⋃ map nonces_of_pre_term (mbind PreTerm.factors us) =
  ⋃ map nonces_of_pre_term us.
Proof.
elim: us => [|u us IH] //=.
by rewrite map_app union_list_app_L -(nonces_of_pre_term_factors u) IH.
Qed.

(* [PreTerm.mul] cancels/sorts/flattens its argument, so its nonces are a subset
   of the union of the factors' nonces — no atomicity needed. *)
Lemma nonces_of_pre_term_mul_sub us :
  nonces_of_pre_term (PreTerm.mul us) ⊆ ⋃ map nonces_of_pre_term us.
Proof.
have mulauxE : forall X, nonces_of_pre_term (PreTerm.mul_aux X)
                       = ⋃ map nonces_of_pre_term X.
  by case=> [|x [|y l]] //=; rewrite union_empty_r_L.
rewrite /PreTerm.mul /PreTerm.normalize_factors mulauxE.
set M := mbind PreTerm.factors us.
have HM : ⋃ map nonces_of_pre_term M = ⋃ map nonces_of_pre_term us
  by rewrite /M nonces_flatten_factors.
rewrite -HM.
move => a /elem_of_union_list [X [/list_elem_of_fmap [x [-> xL]] aX]].
apply/elem_of_union_list; exists (nonces_of_pre_term x); split => //.
apply/list_elem_of_fmap; exists x; split => //.
exact: (SMS.mem_to pt_order PreTerm.inv_aux x M xL).
Qed.

(* [PreTerm.exp] folds the new exponent into the base and cancels, so nonces are a
   subset of [nonces base ∪ nonces exponent] — no atomicity needed. *)
Lemma nonces_of_pre_term_exp_sub b e :
  nonces_of_pre_term (PreTerm.exp b e) ⊆ nonces_of_pre_term b ∪ nonces_of_pre_term e.
Proof.
rewrite /PreTerm.exp /PreTerm.exp_aux.
have Hbe := nonces_of_pre_term_base_expo b.
case: (bool_decide (PreTerm.mul [PreTerm.expo b; e] = PreTerm.PTMul [])).
- set_solver.
- have Hmul := @nonces_of_pre_term_mul_sub [PreTerm.expo b; e].
  move: Hmul => /=; set_solver.
Qed.

(* The atomicity hypothesis is not needed: [TExpN t ts = TExp t (TMulN ts)], and the
   nonces of both [exp] and [mul] are subsets of their parts regardless of atomicity. *)
Lemma nonces_of_term_TExpN_subseteq t ts :
  nonces_of_term (TExpN t ts) ⊆ nonces_of_term t ∪ ⋃ map nonces_of_term ts.
Proof.
have Hts : ⋃ map nonces_of_term ts = ⋃ map nonces_of_pre_term (map unfold_term ts).
  congr union_list. elim: ts => [|t' ts IH] //=.
  by rewrite IH nonces_of_term_unseal /nonces_of_term_def.
rewrite Hts !nonces_of_term_unseal /nonces_of_term_def.
have -> : unfold_term (TExpN t ts) =
          PreTerm.exp (unfold_term t) (PreTerm.mul (map unfold_term ts)).
  by rewrite /TExpN unfold_TExp unfold_TMulN.
etrans; first exact: (@nonces_of_pre_term_exp_sub (unfold_term t)
                        (PreTerm.mul (map unfold_term ts))).
have Hmul := @nonces_of_pre_term_mul_sub (map unfold_term ts).
set_solver.
Qed.

(* [wf_mul_list] no longer exists; [invs_canceled] (core/term/base.v) is its
   replacement: no factor is a product, and no two factors cancel. *)
Lemma nonces_of_term_TMulN ts :
  invs_canceled ts ->
  nonces_of_term (TMulN ts) = ⋃ map nonces_of_term ts.
Proof.
move=> ic.
have Nm : forall x, x ∈ (unfold_term <$> ts) -> negb (PreTerm.is_mul x).
  move=> _ /list_elem_of_fmap [t [-> tin]].
  by rewrite -is_mul_unfold; case: (ic t tin).
have nopairs : forall x, x ∈ (unfold_term <$> ts) ->
                 PreTerm.inv_aux x ∉ (unfold_term <$> ts).
  move=> _ /list_elem_of_fmap [t [-> tin]].
  have [Vnin tNm] := ic t tin.
  rewrite -PreTerm.inv_Nmul; last by rewrite -is_mul_unfold.
  rewrite -unfold_TInv => /list_elem_of_fmap [t' [/unfold_term_inj e t'in]].
  by apply: Vnin; rewrite e.
have mulauxE : forall X, nonces_of_pre_term (PreTerm.mul_aux X)
                       = ⋃ map nonces_of_pre_term X.
  by case=> [|x [|y l]] //=; rewrite union_empty_r_L.
have flat : forall l, (forall x, x ∈ l -> negb (PreTerm.is_mul x)) ->
              mbind PreTerm.factors l = l.
  elim=> [//|x l IH] H /=.
  rewrite PreTerm.factors_Nmul; last by apply: H; apply/elem_of_cons; left.
  by rewrite -/(mbind PreTerm.factors l) IH // => y yin; apply: H;
     apply/elem_of_cons; right.
rewrite nonces_of_term_unseal /nonces_of_term_def unfold_TMulN.
rewrite /PreTerm.mul /PreTerm.normalize_factors mulauxE flat //.
rewrite (union_list_map_to_pt nonces_of_pre_term nopairs).
by elim: ts {ic Nm nopairs} => [//|t l IH] /=; rewrite IH.
Qed.

(* Restated: [atomic] and [term_order] no longer exist.  [invs_canceled] plays
   the role of [atomic], and since [TMulN] is now permutation-invariant there is
   no term order left to normalise the exponent list with. *)
Lemma nonces_of_term_TExpN t ts :
  negb (is_exp t) -> invs_canceled ts ->
  nonces_of_term (TExpN t ts) = nonces_of_term t ∪ ⋃ map nonces_of_term ts.
Proof.
move=> tNexp ic.
rewrite (nonces_of_term_base_exps (TExpN t ts)).
rewrite /TExpN base_TExp (base_expN _ tNexp).
congr (_ ∪ _).
rewrite /exps expo_TExp (expo_expN _ tNexp) TMulN_cat /= TMulN1.
by rewrite -(nonces_of_term_factors (TMulN ts)) nonces_of_term_TMulN.
Qed.

Definition nonces_of_termE :=
  (nonces_of_term_TInv, nonces_of_term_TExpN, nonces_of_term_TMulN, nonces_of_termE').

