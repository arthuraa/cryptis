(** Self-contained development of pre-term normalization: the [normalize]
    function, the definitions it depends on, and just the theory needed to prove
    that normalization is idempotent ([normalize_idem]).  The same definitions
    also live in [theory.v]; they are kept here on purpose (nothing is moved out
    of [theory.v]). *)

From cryptis Require Export mathcomp_compat.
From HB Require Import structures.
From mathcomp Require Import all_order all_boot.
From Stdlib Require Import ZArith.ZArith Lia.
From cryptis.core.pre_term Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory Order.TotalTheory.

Module PreTerm.
Import base.PreTerm.

Fixpoint height pt :=
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (height pt)
  | PT2 _ pt1 pt2 => S (maxn (height pt1) (height pt2))
  | PTMul ts => S (\max_(x <- map height ts) x)
  end.

Definition is_inv pt :=
  if pt is PTInv _ then true else false.

Definition is_exp pt :=
  if pt is PTExp _ _ then true else false.

Definition is_mul pt :=
  if pt is PTMul _ then true else false.

Definition base pt := if pt is PTExp b _ then b else pt.
Definition expo pt := if pt is PTExp _ e then e else PTMul [::].
Definition factors pt := if pt is PTMul ts then ts else [:: pt].

(** We now define smart constructors for all the operations that validate
    non-trivial equations: [inv], [mul] and [exp].  The definitions work as
    follows:

    - [inv_aux] computes the inverse of terms that do not begin with [PTMul] by
      simply adding or removing a [PTInv].

    - [mul] computes the product of a list of terms. It flattens inner terms
      that begin with [PTMul] (so that multiplication is associative) and then
      cancels out multiplicative inverses by using [inv_aux].  This works
      because, on normalized terms, consecutive occurrences of [PTMul] are
      flattened, so [inv_aux] is only called on non-multiplication terms.

    - [inv] computes the inverse of arbitrary terms by distributivity: [inv (a1
      * ... * an) = inv_aux a1 * ... inv_aux an].  Once again, this works
      because, on normalized terms, the [ai] do not begin with [PTMul].

    - [exp] combines exponents using [mul].  If the resulting exponent is [1 =
      PTMul []], we simply return the base. *)

Definition inv_aux pt :=
  match pt with
  | PTInv t => t
  | _ => PTInv pt
  end.

Definition insert_factor pt pts :=
  if inv_aux pt \in pts then rem (inv_aux pt) pts
  else pt :: pts.

Definition cancel_invs := foldr insert_factor [::].

Definition mul ts :=
  match sort <=%O (cancel_invs (flatten (map factors ts))) with
  | [:: t] => t
  | canceled => PTMul canceled
  end.

Definition inv pt :=
  if pt is PTMul ts then mul (map inv_aux ts) else inv_aux pt.

Definition exp b e :=
  let e' := mul [:: expo b; e] in
  if e' == PTMul [::] then base b
  else PTExp (base b) e'.

Fixpoint normalize pt :=
  match pt with
  | PT0 o => PT0 o
  | PTInv t => inv (normalize t)
  | PT1 o t => PT1 o (normalize t)
  | PTExp b e => exp (normalize b) (normalize e)
  | PT2 o t1 t2 => PT2 o (normalize t1) (normalize t2)
  | PTMul ts => mul (map normalize ts)
  end.

(** [invs_canceled pts] holds when all the inverses in [pts] have been canceled
    out. *)
Definition invs_canceled pts := all (fun pt => inv pt \notin pts) pts.

Fixpoint wf_term pt :=
  match pt with
  | PT0 _ => true
  | PTInv pt => [&& ~~ is_inv pt, ~~ is_mul pt & wf_term pt]
  | PT1 _ pt => wf_term pt
  | PTExp b e => [&& wf_term b, ~~ is_exp b, wf_term e & e != PTMul [::]]
  | PT2 _ pt1 pt2 => wf_term pt1 && wf_term pt2
  | PTMul ts => [&& all wf_term ts, all (fun t => ~~ is_mul t) ts,
                    sorted <=%O ts, invs_canceled ts & size ts != 1]
  end.

Lemma wf_base pt : wf_term pt -> wf_term (base pt).
Proof. by case: pt => [o|o t|[||] t1 t2|ts] //= /and4P []. Qed.

Lemma base_expN pt : ~~ is_exp pt -> base pt = pt.
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

Lemma base_Nexp pt : wf_term pt -> ~~ is_exp (base pt).
Proof. by case: pt => [o|o t|[||] t1 t2|ts] //= /and4P []. Qed.

Lemma expo_expN pt : ~~ is_exp pt -> expo pt = PTMul [::].
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

Lemma wf_expo pt : wf_term pt -> wf_term (expo pt).
Proof. by case: pt => [o|o t|[||] t1 t2|ts] //= /and4P []. Qed.

Lemma factorsN pt : ~~ is_mul pt -> factors pt = [:: pt].
Proof. by case: pt. Qed.

Lemma wf_factors pt : wf_term pt -> all wf_term (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf //=; rewrite ?andbT //.
by case/and5P: wf.
Qed.

Lemma Nmul_factors pt : wf_term pt -> all (fun t => ~~ is_mul t) (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf //=; rewrite ?andbT //.
by case/and5P: wf.
Qed.

Lemma wf_inv_aux pt : wf_term pt -> ~~ is_mul pt -> wf_term (inv_aux pt).
Proof. by case: pt => [o|[k| |] t|o t1 t2|ts] //= /and3P []. Qed.

Lemma inv_aux_Nid pt : inv_aux pt != pt.
Proof. case: pt => // - [] // ?. apply /eqP => /(congr1 height) /=. lia. Qed.

Lemma inv_auxK pt : wf_term pt -> inv_aux (inv_aux pt) = pt.
Proof. by case: pt => // - [] // [] // []. Qed.

Lemma inv_aux_eq_op pt1 pt2 :
  wf_term pt1 -> wf_term pt2 -> (inv_aux pt1 == pt2) = (pt1 == inv_aux pt2).
Proof. move => ??; by apply /(sameP eqP) /(iffP eqP) => [-> | <-]; rewrite inv_auxK. Qed.

Lemma insert_factor_subseq pt pts : subseq (insert_factor pt pts) (pt :: pts).
Proof.
rewrite /insert_factor. case: ifP => _ //.
by apply: subseq_trans; [apply rem_subseq | apply subseq_cons].
Qed.

Lemma cancel_invs_subseq pts : subseq (cancel_invs pts) pts.
elim: pts => // [?? IH]; simpl (cancel_invs _).
apply: subseq_trans; first apply insert_factor_subseq; last by simpl; rewrite eqxx.
Qed.

Lemma mem_cancel_invs pts : { subset (cancel_invs pts) <= pts }.
Proof. apply mem_subseq. exact: cancel_invs_subseq. Qed.

Lemma wf_cancel_invs pts : all wf_term pts -> all wf_term (cancel_invs pts).
Proof. move => /allP H. apply /allP => ? /mem_cancel_invs. exact: H. Qed.

Lemma Nmul_cancel_invs pts :
  all (fun t => ~~ is_mul t) pts -> all (fun t => ~~ is_mul t) (cancel_invs pts).
Proof. move => /allP H. apply /allP => ? /mem_cancel_invs. exact: H. Qed.

Lemma inv_invN pt : ~~ is_inv pt -> inv_aux pt = PTInv pt.
Proof. by case: pt => - []. Qed.

Lemma invs_canceled_atomic pts :
  all (fun pt => ~~ is_mul pt) pts ->
  invs_canceled pts = all (fun pt => inv_aux pt \notin pts) pts.
Proof.
move=> /allP atom; rewrite /invs_canceled; apply: eq_in_all => pt pt_pts.
have Nm := atom _ pt_pts; clear pt_pts.
by move: Nm; rewrite /inv; case: pt.
Qed.

Lemma invs_canceled_sort pts : invs_canceled (sort <=%O pts) = invs_canceled pts.
Proof. rewrite /invs_canceled all_sort. apply eq_all => ?. by rewrite mem_sort. Qed.

Lemma insert_factor_no_pair pt pts :
  wf_term pt -> all wf_term pts ->
  all (fun q => inv_aux q \notin pts) pts ->
  all (fun q => inv_aux q \notin insert_factor pt pts) (insert_factor pt pts).
Proof.
move => ? /allP /= wfs /allP /= canceled.
apply /allP. rewrite /insert_factor /= => pt'.
case: ifP => [_| /negP ?].
- move => /mem_rem /canceled. apply: contra. exact: mem_rem.
- rewrite !inE negb_or => /orP [/eqP -> | in_pts].
  + rewrite inv_aux_Nid. exact /negP.
  + apply /andP; split; last exact: canceled.
    have ? := wfs _ in_pts.
    apply /eqP => /eqP. rewrite inv_aux_eq_op // => /eqP eq.
    by rewrite eq in in_pts.
Qed.

Lemma cancel_invs_no_pair pts :
  all wf_term pts ->
  all (fun q => inv_aux q \notin cancel_invs pts) (cancel_invs pts).
Proof.
elim: pts => // [?? IH] /andP [??].
apply insert_factor_no_pair => //.
  exact: wf_cancel_invs.
  exact: IH.
Qed.

Lemma invs_canceled_cancel_invs pts :
  all (fun pt => ~~ is_mul pt) pts -> all wf_term pts ->
  invs_canceled (cancel_invs pts).
Proof.
move=> atom wf.
by rewrite (invs_canceled_atomic (Nmul_cancel_invs atom)); exact: cancel_invs_no_pair.
Qed.

Lemma no_pair_cons pt pts :
  all (fun q => inv_aux q \notin (pt :: pts)) (pt :: pts) ->
  all (fun q => inv_aux q \notin pts) pts.
Proof.
move=> /andP [_ /allP canceled]; apply/allP => ? /canceled.
by rewrite inE negb_or => /andP [].
Qed.

Lemma insert_factor_id pt pts :
  all (fun q => inv_aux q \notin (pt :: pts)) (pt :: pts) ->
  insert_factor pt pts = pt :: pts.
Proof.
move=> /allP canceled; rewrite /insert_factor.
have := canceled _ (mem_head _ _).
by rewrite inE negb_or => /andP [_ /negbTE ->].
Qed.

Lemma cancel_invs_id pts :
  all (fun q => inv_aux q \notin pts) pts -> cancel_invs pts = pts.
Proof.
elim: pts => // [pt pts IH] canceled /=.
rewrite (IH (no_pair_cons canceled)).
exact: (insert_factor_id canceled).
Qed.

Lemma cancel_invs_canceled pts :
  all (fun pt => ~~ is_mul pt) pts -> invs_canceled pts -> cancel_invs pts = pts.
Proof. by move=> atom; rewrite (invs_canceled_atomic atom); exact: cancel_invs_id. Qed.

Lemma invs_canceled1 t : ~~ is_mul t -> invs_canceled [:: t].
Proof.
move=> Nm; rewrite invs_canceled_atomic; last by rewrite /= Nm.
by rewrite /= andbT !inE inv_aux_Nid.
Qed.

Lemma invs_canceled_factors pt : wf_term pt -> invs_canceled (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /factors;
  try by apply: invs_canceled1.
by case/and5P: wf.
Qed.

Lemma sorted_factors pt : wf_term pt -> sorted <=%O (factors pt).
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /factors; try by [].
by case/and5P: wf.
Qed.

Lemma flatten_factors_wf ts :
  all wf_term ts -> all wf_term (flatten [seq factors t | t <- ts]).
Proof.
elim: ts => //= t ts IH /andP [wf_t /IH ?].
by rewrite all_cat wf_factors.
Qed.

Lemma flatten_factors_Nmul ts :
  all wf_term ts -> all (fun t => ~~ is_mul t) (flatten [seq factors t | t <- ts]).
Proof.
elim: ts => //= t ts IH /andP [wf_t /IH ?].
by rewrite all_cat Nmul_factors.
Qed.

Lemma wf_mul ts : all wf_term ts -> wf_term (mul ts).
Proof.
move => wf; rewrite /mul.
set c := cancel_invs _.
have wf_c : all wf_term c by apply: wf_cancel_invs; exact: flatten_factors_wf.
have wf_sc : all wf_term (sort <=%O c) by rewrite all_sort.
have Nmul_sc : all (fun t => ~~ is_mul t) (sort <=%O c).
  rewrite all_sort; apply/allP => x /mem_cancel_invs xin.
  by move/allP: (flatten_factors_Nmul wf) => /(_ x xin).
have sorted_sc : sorted <=%O (sort <=%O c) by exact: sort_le_sorted.
have inv_sc : invs_canceled (sort <=%O c).
  rewrite invs_canceled_sort; apply: invs_canceled_cancel_invs.
  - exact: flatten_factors_Nmul wf.
  - exact: flatten_factors_wf.
case E: (sort <=%O c) => [|t [|t' c']] //=.
  have : t \in sort <=%O c by rewrite E mem_head.
  by rewrite mem_sort => /(allP wf_c).
move: wf_sc Nmul_sc sorted_sc inv_sc; rewrite E => wf' Nmul' sorted' inv_aux'.
by apply/and5P; split.
Qed.

Lemma mul_wf1 t : wf_term t -> mul [:: t] = t.
Proof.
move => wf; rewrite /mul /= cats0.
rewrite (cancel_invs_canceled (Nmul_factors wf) (invs_canceled_factors wf)).
rewrite sort_le_id ?sorted_factors //.
case: t wf => [o|o t|o t1 t2|ts] //= wf.
by case/and5P: wf => _ _ _ _; case: ts => [|t [|t' c']].
Qed.

Lemma wf_exp b e : wf_term b -> wf_term e -> wf_term (exp b e).
Proof.
move => wfb wfe; rewrite /exp; case: ifP => [_|Hf].
  exact: wf_base.
have wf' : all wf_term [:: expo b; e] by rewrite /= (wf_expo wfb) wfe.
by rewrite /= wf_base //= base_Nexp //= wf_mul //= Hf.
Qed.

Lemma inv_Nmul pt : ~~ is_mul pt -> inv pt = inv_aux pt.
Proof. by case: pt. Qed.

Lemma wf_inv pt : wf_term pt -> wf_term (inv pt).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] wf; rewrite /inv /=.
- exact: (wf_inv_aux wf isT).
- exact: (wf_inv_aux wf isT).
- exact: (wf_inv_aux wf isT).
- by case/and3P: wf.
- exact: (wf_inv_aux wf isT).
- apply: wf_mul; rewrite all_map; case/and5P: wf => wf_ts Nm_ts _ _ _.
  apply/allP => t t_ts; apply: wf_inv_aux;
  [exact: (allP wf_ts) | exact: (allP Nm_ts)].
Qed.

Lemma wf_normalize pt : wf_term (normalize pt).
Proof.
elim: pt => //=.
- by case=> [k|| ] t IH /=; [exact: IH|exact: IH|exact: wf_inv].
- move => o t1 IH1 t2 IH2; case: o => /=; try by rewrite IH1 IH2.
  by apply: wf_exp.
- move => ts IHts; apply: wf_mul.
  by elim: ts IHts => //= t ts' IH [wt wts]; rewrite wt; exact: IH wts.
Qed.

Lemma normalize_wf pt : wf_term pt -> normalize pt = pt.
Proof.
elim: pt => //=.
- case=> [k|| ] t IH /=.
  + by move => wf; rewrite (IH wf).
  + by move => wf; rewrite (IH wf).
  + by move => /and3P [ni nm wf]; rewrite (IH wf) (inv_Nmul nm) (inv_invN ni).
- move => o t1 IH1 t2 IH2; case: o => /=.
  + by move => /andP [/IH1 -> /IH2 ->].
  + by move => /andP [/IH1 -> /IH2 ->].
  + move => /and4P [wfb Nxb wfe eN0].
    rewrite IH1 // IH2 // /exp expo_expN // base_expN //.
    have -> : mul [:: PTMul [::]; t2] = t2.
      have -> : mul [:: PTMul [::]; t2] = mul [:: t2] by rewrite /mul /= !cats0.
      exact: mul_wf1.
    by rewrite (negbTE eN0).
- move => ts IHts /and5P [wf_ts Nmul_ts sorted_ts inv_ts sizeN1].
  have Nts : map normalize ts = ts.
    elim: ts IHts wf_ts {Nmul_ts sorted_ts inv_ts sizeN1}
      => //= t ts' IH [IHt IHts'] /andP [wt wts].
    by rewrite IHt // IH.
  rewrite Nts /mul.
  have ff : flatten [seq factors t | t <- ts] = ts.
    elim: ts Nmul_ts {IHts wf_ts sorted_ts inv_ts sizeN1 Nts}
      => //= t ts' IH /andP [Nt Nts'].
    by rewrite (factorsN Nt) /= IH.
  rewrite ff cancel_invs_canceled // sort_le_id //.
  by case: ts sizeN1 {IHts wf_ts Nmul_ts sorted_ts inv_ts Nts ff} => // t [|??].
Qed.

Lemma normalize_idem : idempotent_fun normalize.
Proof. move => ?. apply: normalize_wf; exact: wf_normalize. Qed.

End PreTerm.
