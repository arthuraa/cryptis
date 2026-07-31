(** Pre-term algebraic laws

    This file develops the algebraic theory of the pre-term operations
    ([mul], [exp], [inv]) and destructors ([base], [expo], [factors], [exps]),
    on top of the normalization machinery of [normalize.v].  It establishes the
    *fundamental* equations on well-formed pre-terms — the group laws

    - [(g ^ a) ^ b = g ^ (a * b)]
    - [a * b = b * a]
    - [a * (b * c) = (a * b) * c]
    - [a * a^-1 = 1]
    - [a * 1 = a]
    - [g ^ 1 = g]

    (as [expA], [perm_mul], [mul_cat], [mul_invs], [exp_unit], …) together with
    the reconstruction/interaction laws for the destructors ([mul_factors],
    [factors_mul], [exp_base_expo], [inv_factors], …) and the [tsize] termination
    measure.

    The *derived* equations ([(a^-1)^-1 = a], [1^-1 = 1], cancellation, …) are
    *not* proved here: they follow from the fundamentals and are proved once, at
    the [term] layer, in [core/term/base.v] ([TInvK], [TInv_fixed],
    [TMul_cancel], …).

*)

From stdpp Require Import sorting list numbers.
From cryptis Require Import lib.
From cryptis.lib Require Import list_sort sms.
From mathcomp Require Import ssreflect.
From Stdlib Require Import Lia.
From cryptis.core.pre_term Require Export base with_stdpp normalize.

Module PreTerm.
Import base.PreTerm.
Import normalize.PreTerm.

Lemma factors_inj t1 t2 :
  wf t1 → wf t2 → factors t1 = factors t2 -> t1 = t2.
Proof.
case: t1 t2 => [o1|o1 t1|o1 t11 t12|ts1] [o2|o2 t2|o2 t21 t22|ts2] //= wf1 wf2;
do 1?congruence.
- by move=> e; rewrite -e /= andb_false_r in wf2.
- by move=> e; rewrite -e /= andb_false_r in wf2.
- by move=> e; rewrite -e /= andb_false_r in wf2.
- by move=> e; rewrite e /= andb_false_r in wf1.
- by move=> e; rewrite e /= andb_false_r in wf1.
- by move=> e; rewrite e /= andb_false_r in wf1.
Qed.

Lemma count_factors_inj t1 t2 :
  wf t1 →
  wf t2 →
  (∀ x, negb (is_mul x) → wf x →
    SMS.count inv_aux x (factors t1) = SMS.count inv_aux x (factors t2)) →
  t1 = t2.
Proof.
move=> wf1 wf2 ecount; apply: factors_inj => //.
have /SMS.to_id <- := wf_factors_sms _ wf1.
have /SMS.to_id <- := wf_factors_sms _ wf2.
have /list.Forall_forall wfs1 := wf_factors _ wf1.
have /list.Forall_forall wfs2 := wf_factors _ wf2.
have /list.Forall_forall Nmul1 := Nmul_factors _ wf1.
have /list.Forall_forall Nmul2 := Nmul_factors _ wf2.
apply: SMS.count_to_eq.
- move=> t t_t1; apply: inv_auxK; exact: wfs1.
- move=> t t_t2; apply: inv_auxK; exact: wfs2.
move=> t t_in; have [tNmul wf_t] : negb (is_mul t) ∧ wf t.
  by case/elem_of_app: t_in => t_in; eauto.
exact: ecount.
Qed.

Lemma factors_mul ts :
  Forall wf ts ->
  factors (mul ts) = SMS.to pt_order inv_aux (concat (factors <$> ts)).
Proof.
move=> wf; rewrite /mul; set c := concat (factors <$> ts).
have Nmul_c : Forall (fun t => negb (is_mul t)) (SMS.to pt_order inv_aux c).
{ apply/list.Forall_forall => x /(SMS.mem_to pt_order inv_aux) xin.
  have /list.Forall_forall H := flatten_factors_Nmul _ wf; exact: (H x xin). }
case E: (SMS.to pt_order inv_aux c) => [|t [|t' c']] //=.
have Ht : t ∈ SMS.to pt_order inv_aux c by rewrite E; exact: list_elem_of_here.
have /list.Forall_forall H := Nmul_c; by rewrite (factorsN _ (H t Ht)).
Qed.

Lemma count_factors_mul t t' ts :
  wf t →
  wf t' →
  Forall wf ts →
  SMS.count inv_aux t (factors (mul (t' :: ts))) =
  (SMS.count inv_aux t (factors t') + SMS.count inv_aux t (factors (mul ts)))%Z.
Proof.
move=> wf_t wf_t' wf_ts.
have wf_all : Forall wf (t' :: ts) by constructor.
have iKt : inv_aux (inv_aux t) = t := inv_auxK _ wf_t.
have iKcat : forall us, Forall wf us ->
    forall x, x ∈ concat (factors <$> us) -> inv_aux (inv_aux x) = x.
  move=> us /flatten_factors_wf/list.Forall_forall wfc x xin.
  exact: (inv_auxK _ (wfc _ xin)).
rewrite (factors_mul _ wf_all).
rewrite (SMS.count_to pt_order inv_aux t _ iKt (iKcat _ wf_all)) /=.
rewrite (SMS.count_app inv_aux) (factors_mul _ wf_ts).
by rewrite (SMS.count_to pt_order inv_aux t _ iKt (iKcat _ wf_ts)).
Qed.

Lemma is_mul_inv_aux pt : wf pt -> negb (is_mul (inv_aux pt)).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] wf //=.
by move: wf; rewrite /= !andb_True => - [[_ H] _].
Qed.

Lemma inv_factors pt : wf pt -> inv pt = mul (inv_aux <$> factors pt).
Proof.
case: pt => [o|[k| |] t|o t1 t2|ts] wf; rewrite /inv /factors //.
all: rewrite fmap_cons fmap_nil (mul_wf1 _ (wf_inv_aux _ wf ltac:(done))) //.
Qed.

Lemma flatten_factors_Nmul_id us :
  Forall (fun t => negb (is_mul t)) us -> concat (factors <$> us) = us.
Proof.
elim: us => [//|u us' IH] /= H.
have [Nu Nus'] := Forall_cons_1 _ _ _ H.
by rewrite (factorsN _ Nu) (IH Nus').
Qed.

Lemma count_factors_inv t t' :
  wf t →
  wf t' →
  SMS.count inv_aux t (factors (inv t')) =
  (- SMS.count inv_aux t (factors t'))%Z.
Proof.
move=> wf_t wf_t'.
have iKt : inv_aux (inv_aux t) = t := inv_auxK _ wf_t.
have /list.Forall_forall wfF := wf_factors _ wf_t'.
have /list.Forall_forall NmF := Nmul_factors _ wf_t'.
have wf_invF : Forall wf (inv_aux <$> factors t').
  apply/list.Forall_forall => x /list_elem_of_fmap [y [-> yF]].
  exact: (wf_inv_aux _ (wfF _ yF) (NmF _ yF)).
have Nm_invF : Forall (fun x => negb (is_mul x)) (inv_aux <$> factors t').
  apply/list.Forall_forall => x /list_elem_of_fmap [y [-> yF]].
  exact: (is_mul_inv_aux _ (wfF _ yF)).
have iK_F : forall x, x ∈ factors t' -> inv_aux (inv_aux x) = x.
  move=> x xF; exact: (inv_auxK _ (wfF _ xF)).
have iK_invF : forall x, x ∈ inv_aux <$> factors t' -> inv_aux (inv_aux x) = x.
  move=> x /list_elem_of_fmap [y [-> yF]]; by rewrite (inv_auxK _ (wfF _ yF)).
rewrite (inv_factors _ wf_t') (factors_mul _ wf_invF).
rewrite (flatten_factors_Nmul_id _ Nm_invF).
rewrite (SMS.count_to pt_order inv_aux t _ iKt iK_invF).
by rewrite (SMS.count_fmap_i inv_aux t _ iKt iK_F).
Qed.

(** The size of a pre-term, used as a termination measure. *)
Fixpoint tsize (pt : pre_term) : nat :=
  match pt with
  | PT0 _ => 1
  | PT1 _ pt => S (tsize pt)
  | PT2 _ t1 t2 => S (tsize t1 + tsize t2)
  | PTMul ts => S (sum_list_with tsize ts)
  end.

Lemma tsize_gt0 pt : 0 < tsize pt.
Proof. case: pt => * /=; lia. Qed.

Lemma tsize_inv pt : negb (is_inv pt) -> tsize (inv_aux pt) = S (tsize pt).
Proof. by move=> H; rewrite (inv_invN _ H). Qed.

Lemma tsize_exp_Nexp b e :
  negb (is_exp b) -> wf e -> e ≠ PTMul [] ->
  tsize (exp b e) = S (tsize b + tsize e).
Proof.
move=> Nxb wfe eN0; rewrite /exp.
have -> : mul [expo b; e] = e.
{ rewrite (expo_expN _ Nxb) mul_unit_l; exact: (mul_wf1 _ wfe). }
by rewrite (bool_decide_eq_false_2 _ eN0) (base_expN _ Nxb).
Qed.

Lemma tsize_mul ts :
  Forall (fun t => negb (is_mul t)) ts ->
  (forall q, q ∈ ts -> inv_aux q ∉ ts) -> ts ≠ [] ->
  tsize (mul ts) =
  (if bool_decide (1 < length ts) then 1 else 0) + sum_list_with tsize ts.
Proof.
move=> atom canc tsN0.
rewrite /mul (flatten_factors_Nmul_id _ atom).
have Hperm : SMS.to pt_order inv_aux ts ≡ₚ ts.
{ exact: (SMS.to_id_perm pt_order inv_aux ts canc). }
have Hlen : length (SMS.to pt_order inv_aux ts) = length ts by exact: Permutation_length Hperm.
have Hsum : sum_list_with tsize (SMS.to pt_order inv_aux ts) = sum_list_with tsize ts
  by exact: (sum_list_with_Permutation tsize _ _ Hperm).
case E: (SMS.to pt_order inv_aux ts) => [|a [|b l]].
- move: Hlen; rewrite E /= => Hlen0.
  by case: ts tsN0 Hlen0 {E atom canc Hperm Hsum} => [|x xs].
- move: Hlen Hsum; rewrite E /= => Hlen1 Hsum1.
  rewrite (bool_decide_eq_false_2 (1 < length ts)); last by rewrite -Hlen1; lia.
  by rewrite -Hsum1 /= Nat.add_0_r.
- move: Hlen Hsum; rewrite E /= => Hlen2 Hsum2.
  rewrite (bool_decide_eq_true_2 (1 < length ts)); last by rewrite -Hlen2; lia.
  rewrite -Hsum2 /=; lia.
Qed.

(* BEGIN DELETION CANDIDATES *)

(** ** Pre-term algebra infrastructure.

    Support lemmas that are not needed by the normalization machinery in
    [normalize.v] but underpin the algebraic laws below (and the [term]-layer
    development): [SMS] canonical-form plumbing, the [inv_aux] shape/no-pairs
    facts, and the right-unit law. *)

(* On [inv_aux]-lists the fixed-point pruning inside [SMS.to] is vacuous
   ([inv_aux] has no fixed points, [inv_aux_Nid]), so [SMS.to] is just
   sort-after-cancel — the shape the executable primitives ([hl_mul]/[hl_exp])
   compute.  Lets those spec proofs unfold [SMS.to] without exposing [prune]. *)
Lemma to_inv_aux X :
  SMS.to pt_order inv_aux X = merge_sort pt_order (SMS.cancel inv_aux X).
Proof. by rewrite /SMS.to (SMS.prune_id inv_aux X (fun x _ => inv_aux_Nid x)). Qed.

(** Two products are equal when their flattened factor lists carry the same
    signed [SMS.count] at every involution fixed point — the [SMS.to_eq]
    characterisation, with the per-list involution law discharged from
    well-formedness ([wf_invol]).  ([mul] depends on its arguments only
    through the canonical form [SMS.to] of the flattened factor list.) *)
Lemma mul_count_eq ts1 ts2 :
  Forall wf ts1 -> Forall wf ts2 ->
  (forall z, inv_aux (inv_aux z) = z ->
     SMS.count inv_aux z (concat (factors <$> ts1)) =
     SMS.count inv_aux z (concat (factors <$> ts2))) ->
  mul ts1 = mul ts2.
Proof.
move=> wf1 wf2 Hc.
have Heq : SMS.to pt_order inv_aux (concat (factors <$> ts1))
         = SMS.to pt_order inv_aux (concat (factors <$> ts2)).
  apply: (proj2 (SMS.to_eq pt_order inv_aux
                   (concat (factors <$> ts1)) (concat (factors <$> ts2))
                   (wf_invol _ (flatten_factors_wf _ wf1))
                   (wf_invol _ (flatten_factors_wf _ wf2)))).
  exact: Hc.
by rewrite /mul Heq.
Qed.

(** Canonicalising a suffix before concatenating does not change the canonical
    form of the whole: [SMS.to] absorbs an inner [SMS.to].  This is the generic
    engine behind the [term]-layer [exps_TExpN]. *)
Lemma to_cat_to A B :
  Forall wf A -> Forall wf B ->
  SMS.to pt_order inv_aux (A ++ SMS.to pt_order inv_aux B)
  = SMS.to pt_order inv_aux (A ++ B).
Proof.
move=> wfA wfB.
exact: (SMS.to_cat_to pt_order inv_aux A B
          (wf_invol _ wfA) (wf_invol _ wfB)).
Qed.

(* On an atomic list [inv] and [inv_aux] agree, so "no [inv] pairs" is exactly the
   [inv_aux]-form the generic [SMS.to]/[SMS.wf] lemmas consume. *)
Lemma no_inv_aux_of_no_inv X :
  Forall (fun t => negb (is_mul t)) X -> (forall q, q ∈ X -> inv q ∉ X) ->
  forall q, q ∈ X -> inv_aux q ∉ X.
Proof.
move=> /list.Forall_forall Nm H q qin.
rewrite -(inv_Nmul _ (Nm q qin)); exact: (H q qin).
Qed.

(* [PTMul []] is a right unit for [mul] (companion to [mul_unit_l] in
   [normalize.v]): dropping it from a two-element product leaves the flattened
   factor list, hence [mul], unchanged. *)
Lemma mul_unit_r X : mul [X; PTMul []] = mul [X].
Proof. by rewrite /mul /= !app_nil_r. Qed.

(** ** Additional theory on pre-terms. *)

(** The exponents of a pre-term. *)
Definition exps pt := factors (expo pt).

Lemma wf_exps pt : wf pt -> Forall wf (exps pt).
Proof. move=> wf; rewrite /exps; apply: wf_factors; exact: (wf_expo _ wf). Qed.

Lemma exps_expN pt : negb (is_exp pt) -> exps pt = [].
Proof. move=> H; rewrite /exps (expo_expN _ H) //. Qed.

Lemma base_idem pt : wf pt -> base (base pt) = base pt.
Proof. move=> wf; exact: (base_expN _ (base_Nexp _ wf)). Qed.

Lemma base_expoK pt : is_exp pt -> PTExp (base pt) (expo pt) = pt.
Proof. by case: pt => [o|o t|[||] t1 t2|ts]. Qed.

Lemma expo_exp b : expo b ≠ PTMul [] -> is_exp b.
Proof. by case: b => [o|o t|[||] t1 t2|ts] //= H; case: (H eq_refl). Qed.

Lemma expo_unit_Nexp b : wf b -> expo b = PTMul [] -> negb (is_exp b).
Proof.
case: b => [o|o t|[||] t1 t2|ts] //= wf e0.
move: wf; rewrite !andb_True => - [[[_ _] _] /bool_decide_unpack eN0].
exfalso; apply: eN0; exact: e0.
Qed.

Lemma inv_inv_aux pt : wf pt -> inv (inv_aux pt) = pt.
Proof.
move=> wf; have Nm := is_mul_inv_aux _ wf.
have -> : inv (inv_aux pt) = inv_aux (inv_aux pt).
{ rewrite /inv; by case: (inv_aux pt) Nm => [o|o t|o t1 t2|ts]. }
exact: (inv_auxK _ wf).
Qed.

Lemma no_inv_exps_pt pt : wf pt -> forall q, q ∈ exps pt -> inv q ∉ exps pt.
Proof. move=> wf; rewrite /exps; exact: (no_inv_factors _ (wf_expo _ wf)). Qed.

Lemma exps_sorted pt : wf pt -> StronglySorted pt_order (exps pt).
Proof. move=> wf; rewrite /exps; exact: (sorted_factors _ (wf_expo _ wf)). Qed.

Lemma base_exp b e : wf b -> base (exp b e) = base b.
Proof.
move=> wf; rewrite /exp; case_bool_decide as H.
- exact: (base_idem _ wf).
- done.
Qed.

Lemma perm_mul ts1 ts2 :
  Forall wf ts1 -> ts1 ≡ₚ ts2 -> mul ts1 = mul ts2.
Proof.
move=> wf1 peq.
have peq' : concat (factors <$> ts1) ≡ₚ concat (factors <$> ts2) by rewrite peq.
apply: mul_count_eq.
- exact: wf1.
- by rewrite -peq.
- by move=> z _; rewrite peq'.
Qed.

Lemma mul_factors pt : wf pt -> mul (factors pt) = pt.
Proof.
case: pt => [o|o t|o t1 t2|ts] wf; rewrite /factors; try exact: (mul_wf1 _ wf).
case: (wf_Mul_inv _ wf) => _ [Nmul [swf sizeN1]]; clear wf.
rewrite /mul (flatten_factors_Nmul_id _ Nmul) (SMS.to_id pt_order inv_aux ts swf).
by case: ts sizeN1 {Nmul swf} => [|x [|y ts']] // sizeN1; case: (sizeN1 erefl).
Qed.

Lemma exp_unit b : wf b -> exp b (PTMul []) = b.
Proof.
move=> wf; rewrite /exp.
have -> : mul [expo b; PTMul []] = expo b.
{ rewrite mul_unit_r; exact: (mul_wf1 _ (wf_expo _ wf)). }
case: (decide (expo b = PTMul [])) => [e0 | eN0].
- rewrite (bool_decide_eq_true_2 _ e0).
  by rewrite (base_expN _ (expo_unit_Nexp _ wf e0)).
- rewrite (bool_decide_eq_false_2 _ eN0).
  by rewrite (base_expoK _ (expo_exp _ eN0)).
Qed.

Lemma expo_exp_eq b e : wf b -> expo (exp b e) = mul [expo b; e].
Proof.
move=> wfb; rewrite /exp.
case: (decide (mul [expo b; e] = PTMul [])) => [heq | hne].
- rewrite (bool_decide_eq_true_2 _ heq) heq.
  by rewrite (expo_expN _ (base_Nexp _ wfb)).
- by rewrite (bool_decide_eq_false_2 _ hne).
Qed.

Lemma exp_base_expo pt : wf pt -> exp (base pt) (expo pt) = pt.
Proof.
case: pt => [o|o t|[||] t1 t2|ts] wf; rewrite /base /expo; try exact: (exp_unit _ wf).
move: wf; rewrite /= !andb_True => - [[[wfb Nxb] wfe] /bool_decide_unpack eN0].
rewrite /exp (expo_expN _ Nxb) (base_expN _ Nxb).
have -> : mul [PTMul []; t2] = t2.
{ rewrite mul_unit_l; exact: (mul_wf1 _ wfe). }
by rewrite (bool_decide_eq_false_2 _ eN0).
Qed.

Lemma exps_exp b e :
  wf b -> wf e ->
  exps (exp b e) = SMS.to pt_order inv_aux (exps b ++ factors e).
Proof.
move=> wfb wfe.
have wf' : Forall wf [expo b; e]
  by constructor; [exact: (wf_expo _ wfb) | constructor; [exact: wfe | constructor]].
rewrite /exps (expo_exp_eq _ _ wfb) (factors_mul _ wf') /=.
by rewrite app_nil_r.
Qed.

Lemma is_exp_exp b e :
  wf b -> is_exp (exp b e) = negb (bool_decide (mul [expo b; e] = PTMul [])).
Proof.
move=> wfb; rewrite /exp.
case: (decide (mul [expo b; e] = PTMul [])) => [heq | hne].
- rewrite !(bool_decide_eq_true_2 _ heq).
  move: (base_Nexp _ wfb) => Hb; by case: (is_exp (base b)) Hb.
- by rewrite !(bool_decide_eq_false_2 _ hne).
Qed.

Lemma mul_cat ts1 ts2 :
  Forall wf ts1 -> Forall wf ts2 -> mul (mul ts1 :: ts2) = mul (ts1 ++ ts2).
Proof.
move=> wf1 wf2.
have wfX1 := flatten_factors_wf _ wf1.
apply: mul_count_eq.
- constructor; [exact: (wf_mul _ wf1) | exact: wf2].
- by apply/Forall_app.
- move=> z iKz.
  rewrite fmap_cons /= (factors_mul _ wf1) fmap_app concat_app.
  by rewrite !(SMS.count_app inv_aux) (SMS.count_to pt_order inv_aux z _ iKz (wf_invol _ wfX1)).
Qed.

Lemma expo_exp_eq_key b e1 e2 :
  wf b -> wf e1 -> wf e2 ->
  mul [mul [expo b; e1]; e2] = mul [expo b; mul [e1; e2]].
Proof.
move=> wfb wfe1 wfe2.
have wfeb : wf (expo b) := wf_expo _ wfb.
have wf_e12 : Forall wf [e1; e2]
  by constructor; [exact: wfe1 | constructor; [exact: wfe2 | constructor]].
have wfm : wf (mul [e1; e2]) := wf_mul _ wf_e12.
have wf_be1 : Forall wf [expo b; e1]
  by constructor; [exact: wfeb | constructor; [exact: wfe1 | constructor]].
have wf_e2l : Forall wf [e2] by constructor; [exact: wfe2 | constructor].
have wf_ebl : Forall wf [expo b] by constructor; [exact: wfeb | constructor].
have wf_bm : Forall wf [expo b; mul [e1; e2]]
  by constructor; [exact: wfeb | constructor; [exact: wfm | constructor]].
have wf_be1e2 : Forall wf [expo b; e1; e2]
  by constructor; [exact: wfeb | exact: wf_e12].
rewrite (mul_cat [expo b; e1] [e2] wf_be1 wf_e2l).
rewrite (perm_mul [expo b; mul [e1; e2]] [mul [e1; e2]; expo b] wf_bm
           (Permutation_swap (mul [e1; e2]) (expo b) [])).
rewrite (mul_cat [e1; e2] [expo b] wf_e12 wf_ebl).
apply: perm_mul; first exact: wf_be1e2.
exact: (Permutation_cons_append [e1; e2] (expo b)).
Qed.

Lemma expA b e1 e2 :
  wf b -> wf e1 -> wf e2 -> exp (exp b e1) e2 = exp b (mul [e1; e2]).
Proof.
move=> wfb wfe1 wfe2.
by rewrite {1}/exp (base_exp _ _ wfb) (expo_exp_eq _ _ wfb)
           (expo_exp_eq_key _ _ _ wfb wfe1 wfe2).
Qed.

Lemma mul_mul2 ts1 ts2 :
  Forall wf ts1 -> Forall wf ts2 -> mul [mul ts1; mul ts2] = mul (ts1 ++ ts2).
Proof.
move=> wf1 wf2.
have wfm2 : wf (mul ts2) := wf_mul _ wf2.
have wf1m : Forall wf (ts1 ++ [mul ts2])
  by apply/Forall_app; split; [exact: wf1 | constructor; [exact: wfm2 | constructor]].
have wfm2l : Forall wf [mul ts2] by constructor; [exact: wfm2 | constructor].
rewrite (mul_cat ts1 [mul ts2] wf1 wfm2l).
rewrite (perm_mul (ts1 ++ [mul ts2]) (mul ts2 :: ts1) wf1m
                  (Permutation_app_comm ts1 [mul ts2])).
rewrite (mul_cat ts2 ts1 wf2 wf1).
apply: perm_mul; first by apply/Forall_app; split; [exact: wf2 | exact: wf1].
exact: Permutation_app_comm.
Qed.

Lemma no_inv_map_inv ts :
  Forall wf ts -> (forall q, q ∈ ts -> inv q ∉ ts) ->
  forall q, q ∈ (inv_aux <$> ts) -> inv q ∉ (inv_aux <$> ts).
Proof.
move=> /list.Forall_forall wfa canca x /list_elem_of_fmap [t [-> t_ts]].
rewrite (inv_inv_aux _ (wfa _ t_ts)) => /list_elem_of_fmap [s [e s_ts]].
move: (canca _ t_ts); rewrite e (inv_inv_aux _ (wfa _ s_ts)) => Habs.
exact: (Habs s_ts).
Qed.

Lemma mul_eq_unit ts :
  Forall (fun t => negb (is_mul t)) ts -> (forall q, q ∈ ts -> inv q ∉ ts) ->
  mul ts = PTMul [] <-> ts = [].
Proof.
move=> atom canc; split; last first.
{ move=> ->; by rewrite /mul. }
rewrite /mul (flatten_factors_Nmul_id _ atom).
have Hperm : SMS.to pt_order inv_aux ts ≡ₚ ts.
{ exact: (SMS.to_id_perm pt_order inv_aux ts (no_inv_aux_of_no_inv _ atom canc)). }
case E: (SMS.to pt_order inv_aux ts) => [|a [|b l]].
- move=> _.
  have Hlen : length ts = 0 by rewrite -(Permutation_length Hperm) E.
  by move: Hlen; case: ts {atom canc Hperm E}.
- move=> Ha.
  have Hin : a ∈ ts.
  { apply: (SMS.mem_to pt_order inv_aux); rewrite E; exact: list_elem_of_here. }
  by have /list.Forall_forall H := atom; move: (H a Hin); rewrite Ha /=.
- by move=> [].
Qed.

(* END DELETION CANDIDATES *)

End PreTerm.
