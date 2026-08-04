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
From cryptis.core.term Require Import base algebra repr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Implicit Types (t k : term) (ts : list term).

(* nonces_of_term and its theory.
   (Split out of the former monolithic core/term/base.v.) *)

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

(* Local bridge: [merge_sort] only permutes, and [⋃ ∘ map f] is
   permutation-invariant, so sorting the list before mapping is transparent. *)
Lemma union_list_map_merge_sort {A X} `{Countable X} (f : A → gset X)
  (R : relation A) `{!RelDecision R} l :
  ⋃ map f (merge_sort R l) = ⋃ map f l.
Proof.
apply: union_list_permutation_proper_L; apply: Permutation_map.
exact: (merge_sort_Permutation R l).
Qed.

(* Same for the canonical form [SMS.to pt_order inv_aux] on a list with no
   inverse pairs: there [SMS.to] only permutes ([SMS.to_id_perm]), so it too is
   transparent under [⋃ ∘ map f]. *)
Lemma union_list_map_to_pt {X} `{Countable X}
  (f : PreTerm.pre_term → gset X) l :
  (forall x, x ∈ l -> PreTerm.inv_aux x ∉ l) ->
  ⋃ map f (SMS.to pt_order PreTerm.inv_aux l) = ⋃ map f l.
Proof.
move=> nc; apply: union_list_permutation_proper_L; apply: Permutation_map.
exact: (SMS.to_id_perm pt_order PreTerm.inv_aux l nc).
Qed.

(* [inv] distributes [inv] over the factors and re-multiplies; [inv] preserves
   nonces, and (for wf [pt]) no cancellation occurs, so nonces are preserved. *)
Lemma nonces_of_pre_term_inv pt :
  PreTerm.wf pt ->
  nonces_of_pre_term (PreTerm.inv pt) = nonces_of_pre_term pt.
Proof.
move => wf.
rewrite (PreTerm.inv_factors pt wf) (nonces_of_pre_term_factors pt).
set F := PreTerm.factors pt.
have wfF : Forall PreTerm.wf F := PreTerm.wf_factors pt wf.
have NmF : Forall (fun pt => negb (PreTerm.is_mul pt)) F := PreTerm.Nmul_factors pt wf.
have cancF : forall q, q ∈ F -> PreTerm.inv q ∉ F := PreTerm.no_inv_factors pt wf.
have wfMI : Forall PreTerm.wf (PreTerm.inv_aux <$> F).
  apply/Forall_fmap; apply/Forall_forall => x xF.
  apply: PreTerm.wf_inv_aux;
    [have /list.Forall_forall H := wfF; exact: (H x xF)
    |have /list.Forall_forall H := NmF; exact: (H x xF)].
have NmMI : Forall (fun pt => negb (PreTerm.is_mul pt)) (PreTerm.inv_aux <$> F).
  apply/Forall_fmap; apply/Forall_forall => x xF.
  apply: PreTerm.is_mul_inv_aux; have /list.Forall_forall H := wfF; exact: (H x xF).
have cancMI : forall q, q ∈ (PreTerm.inv_aux <$> F) -> PreTerm.inv q ∉ (PreTerm.inv_aux <$> F)
  := PreTerm.no_inv_map_inv F wfF cancF.
rewrite (nonces_of_pre_term_factors (PreTerm.mul (PreTerm.inv_aux <$> F))).
rewrite (PreTerm.factors_mul (PreTerm.inv_aux <$> F) wfMI).
rewrite (PreTerm.flatten_factors_Nmul_id (PreTerm.inv_aux <$> F) NmMI).
rewrite union_list_map_to_pt; last exact: (PreTerm.no_inv_aux_of_no_inv _ NmMI cancMI).
rewrite /F; elim: (PreTerm.factors pt) => [//|x fs IH] /=.
by rewrite nonces_of_pre_term_inv_aux IH.
Qed.

Lemma nonces_of_term_TInv t : nonces_of_term (TInv t) = nonces_of_term t.
Proof.
rewrite !nonces_of_term_unseal /nonces_of_term_def unfold_TInv.
exact: nonces_of_pre_term_inv (wf_unfold_term t).
Qed.

(* Elementwise: folding the inverse of a well-formed atomic factor is [TInv] of
   the folded factor.  Stated as a standalone lemma to keep [fmap]'s typeclass
   instance resolved (a [have] with [<$>] in its type spuriously generalises it). *)
Lemma fmap_fold_inv_aux G :
  Forall PreTerm.wf G ->
  Forall (fun pt => negb (PreTerm.is_mul pt)) G ->
  fold_term <$> (PreTerm.inv_aux <$> G) = TInv <$> (fold_term <$> G).
Proof.
elim: G => [//|x fs IH] /Forall_cons [Wx wfs] /Forall_cons [Nmx Nms].
rewrite !fmap_cons (IH wfs Nms); congr cons.
apply: unfold_term_inj.
by rewrite unfold_TInv (fold_termK x Wx)
           (fold_termK (PreTerm.inv_aux x) (PreTerm.wf_inv_aux x Wx Nmx))
           (PreTerm.inv_Nmul x Nmx).
Qed.

(* [TInv] distributes over products: the canonical factor list of [TInv t] is
   a permutation of the inverses of the factors of [t].  Used to prove
   [public (TInv t) ⊣⊢ public t] for products by reducing to the factors. *)
Lemma tfactors_TInv t : tfactors (TInv t) ≡ₚ map TInv (tfactors t).
Proof.
rewrite /tfactors unfold_TInv (PreTerm.inv_factors (unfold_term t) (wf_unfold_term t)).
set F := PreTerm.factors (unfold_term t).
have wfF : Forall PreTerm.wf F := PreTerm.wf_factors _ (wf_unfold_term t).
have NmF : Forall (fun pt => negb (PreTerm.is_mul pt)) F := PreTerm.Nmul_factors _ (wf_unfold_term t).
have cancF : forall q, q ∈ F -> PreTerm.inv q ∉ F := PreTerm.no_inv_factors _ (wf_unfold_term t).
have wfMI : Forall PreTerm.wf (PreTerm.inv_aux <$> F).
  apply/Forall_fmap; apply/Forall_forall => x xF.
  apply: PreTerm.wf_inv_aux;
    [have /list.Forall_forall H := wfF; exact: (H x xF)
    |have /list.Forall_forall H := NmF; exact: (H x xF)].
have NmMI : Forall (fun pt => negb (PreTerm.is_mul pt)) (PreTerm.inv_aux <$> F).
  apply/Forall_fmap; apply/Forall_forall => x xF.
  apply: PreTerm.is_mul_inv_aux; have /list.Forall_forall H := wfF; exact: (H x xF).
have cancMI : forall q, q ∈ (PreTerm.inv_aux <$> F) -> PreTerm.inv q ∉ (PreTerm.inv_aux <$> F)
  := PreTerm.no_inv_map_inv F wfF cancF.
rewrite (PreTerm.factors_mul (PreTerm.inv_aux <$> F) wfMI).
rewrite (PreTerm.flatten_factors_Nmul_id (PreTerm.inv_aux <$> F) NmMI).
rewrite (SMS.to_id_perm pt_order PreTerm.inv_aux (PreTerm.inv_aux <$> F)
           (PreTerm.no_inv_aux_of_no_inv _ NmMI cancMI)).
by rewrite (fmap_fold_inv_aux wfF NmF).
Qed.

(* [1] is the only involution fixed point, derived at [T = term] from
   [tfactors_TInv] + [no_inv_tfactors] (no [PreTerm.inv_fixed]): if [t^-1 = t]
   then the factor multiset equals its own pointwise inverse, but a factor list
   has no inverse pairs, so it must be empty. *)
Lemma TInv_fixed t : (TInv t = t) <-> (t = TMulN []).
Proof.
split; last first.
  by move=> ->; apply/unfold_term_inj; rewrite unfold_TInv unfold_TMulN /=.
move=> E.
have Hperm := tfactors_TInv t; rewrite E in Hperm.
rewrite -(tfactorsK t); suff -> : tfactors t = [] by [].
case Ea: (tfactors t) => [//|a fs].
have a_t : a ∈ tfactors t by rewrite Ea; exact: list_elem_of_here.
have HTa : TInv a ∈ tfactors t.
  rewrite Hperm; apply: list_elem_of_fmap_2; exact: a_t.
exfalso; exact: (no_inv_tfactors t a a_t HTa).
Qed.

(* [SMS.count TInv] vanishes on a product query: neither a [mul] term nor its
   inverse is atomic ([Nmul_TInv] + [TInvK]), so neither occurs in the atomic list
   [tfactors X].  This lets [tfactors_count_TMulN] drop any query hypothesis. *)
Lemma tfactors_count_mul {t} X :
  is_mul t -> SMS.count TInv t (tfactors X) = 0%Z.
Proof.
move=> Mt; rewrite /SMS.count.
have /list.Forall_forall atomX := atom_tfactors X.
have tc : list_sort.count_mem t (tfactors X) = 0.
  apply/not_elem_of_count_mem => tin.
  exact: (proj1 (negb_True _) (atomX t tin) Mt).
have Tc : list_sort.count_mem (TInv t) (tfactors X) = 0.
  apply/not_elem_of_count_mem => tin.
  have Nm := Nmul_TInv (atomX (TInv t) tin); rewrite TInvK in Nm.
  exact: (proj1 (negb_True _) Nm Mt).
rewrite tc Tc; lia.
Qed.

Lemma nonces_of_pre_term_base_expo pt :
  nonces_of_pre_term pt =
  nonces_of_pre_term (PreTerm.base pt) ∪ nonces_of_pre_term (PreTerm.expo pt).
Proof. by case: pt => [o|o1 e1|[||] e1 e2|es] //=; rewrite union_empty_r_L. Qed.

Lemma nonces_of_term_base_exps t :
  nonces_of_term t = nonces_of_term (base t) ∪ ⋃ map nonces_of_term (exps t).
Proof.
transitivity (nonces_of_pre_term (PreTerm.base (unfold_term t)) ∪
              ⋃ map nonces_of_pre_term (PreTerm.exps (unfold_term t))).
  rewrite {1}nonces_of_term_unseal /nonces_of_term_def.
  rewrite (nonces_of_pre_term_base_expo (unfold_term t)).
  by rewrite (nonces_of_pre_term_factors (PreTerm.expo (unfold_term t))).
congr (_ ∪ _).
  by rewrite /base (nonces_of_term_fold (PreTerm.wf_base _ (wf_unfold_term t))).
rewrite /exps.
have wfs : Forall PreTerm.wf (PreTerm.exps (unfold_term t)) := PreTerm.wf_exps _ (wf_unfold_term t).
elim: (PreTerm.exps (unfold_term t)) wfs => [//|pt pts IH] /Forall_cons [wpt wpts] /=.
by rewrite (nonces_of_term_fold wpt) (IH wpts).
Qed.

Lemma nonces_of_term_TExpN t ts :
  negb (is_exp t) -> atomic ts ->
  nonces_of_term (TExpN t ts) = nonces_of_term t ∪ ⋃ map nonces_of_term (SMS.to term_order TInv ts).
Proof.
move => tNexp atom.
have nexp : negb (PreTerm.is_exp (unfold_term t)).
  by move: tNexp; rewrite is_exp_unfold.
have bt : base t = t by rewrite /base (PreTerm.base_expN _ nexp) unfold_termK.
have et : exps t = [] by rewrite /exps (PreTerm.exps_expN _ nexp).
rewrite (nonces_of_term_base_exps (TExpN t ts)) base_TExpN bt.
congr (_ ∪ _).
by rewrite (exps_TExpN t ts atom) et app_nil_l.
Qed.

Lemma nonces_flatten_factors us :
  ⋃ map nonces_of_pre_term (concat (PreTerm.factors <$> us)) =
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
rewrite /PreTerm.mul.
set M := concat (PreTerm.factors <$> us).
rewrite (_ : nonces_of_pre_term _ =
             ⋃ map nonces_of_pre_term (SMS.to pt_order PreTerm.inv_aux M)); last first.
  by case: (SMS.to pt_order PreTerm.inv_aux M) => [|t [|t' l]] //=;
     rewrite union_empty_r_L.
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
rewrite /PreTerm.exp; cbv zeta.
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
Global Arguments nonces_of_term_TExpN_subseteq t ts : clear implicits.

Lemma nonces_of_term_TMulN ts :
  wf_mul_list ts ->
  nonces_of_term (TMulN ts) = ⋃ map nonces_of_term ts.
Proof.
move => wf; have wfU := wf_mul_list_unfold ts wf.
have e : TMulN ts = fold_term (PreTerm.PTMul (map unfold_term ts)).
  apply: unfold_term_inj; rewrite unfold_TMulN (@fold_termK _ wfU).
  exact: (PreTerm.mul_factors _ wfU).
rewrite {1}e (nonces_of_term_fold wfU) /=.
elim: ts {wf wfU e} => [//|t' ts' IH] /=.
rewrite -IH; congr (_ ∪ _).
by rewrite nonces_of_term_unseal.
Qed.

Lemma nonces_of_term_tfactors t :
  nonces_of_term t = ⋃ map nonces_of_term (tfactors t).
Proof.
rewrite nonces_of_term_unseal /nonces_of_term_def
  (nonces_of_pre_term_factors (unfold_term t)) /tfactors.
congr union_list.
elim: (PreTerm.factors (unfold_term t)) (PreTerm.wf_factors _ (wf_unfold_term t))
  => [//|pt pts IH] /Forall_cons [wpt wpts] /=.
by rewrite (fold_termK pt wpt) (IH wpts).
Qed.

Definition nonces_of_termE :=
  (nonces_of_term_TInv, nonces_of_term_TExpN, nonces_of_term_TMulN, nonces_of_termE').

