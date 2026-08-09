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
From cryptis.core.term Require Import base algebra.

Implicit Types (t k : term) (ts : list term).

(* The [tsize] measure and the well-founded induction principles it supports.
   [tsize] is [PreTerm.tsize] pulled back along [unfold_term]; the [tsize_*_lt]
   lemmas are the termination side conditions feeding [term_lt_rect] /
   [term_lt_ind].  Split out of core/term/algebra.v, which it depends on but
   which does not depend on it — no term-algebra lemma mentions [tsize]. *)

Definition tsize t := PreTerm.tsize (unfold_term t).

Lemma tsize_gt0 t : 0 < tsize t. Proof. exact: PreTerm.tsize_gt0. Qed.

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
Proof. by case: t. Qed.

Lemma tsize_TInv t : negb (is_mul t) -> negb (is_inv t) -> tsize (TInv t) = S (tsize t).
Proof.
move => Nm Ni.
rewrite /tsize (unfold_TInv_Nmul Nm) PreTerm.tsize_inv // -is_inv_unfold //.
Qed.

Lemma tsize_TExp t1 t2 :
  negb (is_exp t1) -> negb (is_mul t2) -> tsize (TExp t1 t2) = S (tsize t1 + tsize t2).
Proof.
move => Nx1 Nm2.
rewrite is_exp_unfold in Nx1; rewrite is_mul_unfold in Nm2.
have neq : unfold_term t2 ≠ PreTerm.PTMul [].
  by move=> e; move: Nm2; rewrite e.
by rewrite /tsize unfold_TExp (PreTerm.tsize_exp_Nexp _ _ Nx1 (wf_unfold_term t2) neq).
Qed.

Definition tsizeE := (tsize_TInv, tsize_TExp, tsize_eq).

Lemma tsize_lt_TInv {t} : negb (is_mul t) -> tsize (TInv t) <= S (tsize t).
Proof.
move => Nm; have NmT := Nmul_TInv Nm.
case: (decide (Is_true (is_inv t))) => [inv_t|ninv_t].
- have Ni : negb (is_inv (TInv t)) by rewrite is_inv_TInv // negb_involutive.
  rewrite -{2}[t]TInvK (tsize_TInv _ NmT Ni); lia.
- rewrite (tsize_TInv _ Nm); first lia.
  by apply/negb_True.
Qed.

Lemma tsize_TExpN t ts :
  negb (is_exp t) -> atomic ts -> (forall t', t' ∈ ts -> TInv t' ∉ ts) ->
  tsize (TExpN t ts) =
  (if bool_decide (ts ≠ []) then 1 else 0) + (if bool_decide (1 < length ts) then 1 else 0)
  + tsize t + sum_list_with tsize ts.
Proof.
move => Nxt atom nc.
have /list.Forall_forall atom' := atom.
have atomU : Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts).
  exact: (atomic_unfold _ atom).
have canc := no_inv_unfold ts nc.
have canc' := no_inv_aux_unfold ts atom' nc.
case: (decide (ts = [])) => [->|tsN0].
  have H1 : bool_decide (@nil term ≠ []) = false.
    by apply: bool_decide_eq_false_2; move=> H; exact: (H eq_refl).
  have H2 : bool_decide (1 < length (@nil term)) = false.
    by apply: bool_decide_eq_false_2; rewrite /=; lia.
  rewrite TExpN0 H1 H2 /=; lia.
have eneq : PreTerm.mul (unfold_term <$> ts) ≠ PreTerm.PTMul [].
  by move=> H; apply: tsN0; apply: (inj (fmap unfold_term)); rewrite (proj1 (PreTerm.mul_eq_unit _ atomU canc) H).
have sumeq : sum_list_with PreTerm.tsize (unfold_term <$> ts) = sum_list_with tsize ts.
  by elim: ts {atom nc canc canc' atom' atomU tsN0 eneq} => [//|t' ts IH] /=; rewrite IH.
rewrite [tsize (TExpN t ts)]/tsize /TExpN unfold_TExp unfold_TMulN.
rewrite (PreTerm.tsize_exp_Nexp _ _ _ (PreTerm.wf_mul _ (wf_unfold_terms ts)) eneq);
  last by rewrite -is_exp_unfold.
rewrite (PreTerm.tsize_mul _ atomU canc'); last first.
  by move=> H; apply: tsN0; apply: (inj (fmap unfold_term)); rewrite H.
rewrite length_fmap sumeq -[PreTerm.tsize (unfold_term t)]/(tsize t).
rewrite (bool_decide_eq_true_2 (ts ≠ [])) //; lia.
Qed.

Lemma tsize_lt_TExp_strong t1 t2 :
  negb (is_mul t2) -> TInv t2 ∉ exps t1 ->
  tsize t1 < tsize (TExp t1 t2) /\
  S (tsize t2) < tsize (TExp t1 t2).
Proof.
move => Nm2 t2_t1.
have atom : atomic (exps t1 ++ [t2]).
  by rewrite /atomic; apply/Forall_app; split; [exact: atom_exps | apply/Forall_singleton].
have canc : forall x, x ∈ exps t1 ++ [t2] -> TInv x ∉ exps t1 ++ [t2].
  have pperm : exps t1 ++ [t2] ≡ₚ t2 :: exps t1 by rewrite -Permutation_cons_append.
  apply/(no_inv_Permutation _ _ pperm).
  apply/(no_inv_cons Nm2); split; [exact: t2_t1 | exact: (no_inv_exps t1)].
have e1 : tsize t1 = (if bool_decide (exps t1 ≠ []) then 1 else 0)
                     + (if bool_decide (1 < length (exps t1)) then 1 else 0)
                     + tsize (base t1) + sum_list_with tsize (exps t1).
  by rewrite -{1}(base_expsK t1)
     (tsize_TExpN _ _ (is_exp_base_bool t1) (atom_exps t1) (no_inv_exps t1)).
rewrite TExp_expsE (tsize_TExpN _ _ (is_exp_base_bool t1) atom canc).
rewrite length_app sum_list_with_app /=.
have g1 := tsize_gt0 (base t1).
have g2 := tsize_gt0 t2.
have HP : exps t1 ++ [t2] ≠ [] by case: (exps t1).
have Hd : (if bool_decide (exps t1 ++ [t2] ≠ []) then 1 else 0) = 1
  by rewrite (bool_decide_eq_true_2 _ HP).
have Ha1 : (if bool_decide (exps t1 ≠ []) then 1 else 0) ≤ 1
  by case E: (bool_decide (exps t1 ≠ [])); simpl; lia.
have Hbc : (if bool_decide (1 < length (exps t1)) then 1 else 0)
        ≤ (if bool_decide (1 < length (exps t1) + 1) then 1 else 0).
  case E: (bool_decide (1 < length (exps t1)));
    case E': (bool_decide (1 < length (exps t1) + 1)); simpl; try lia.
  move/bool_decide_eq_true_1 in E; move/bool_decide_eq_false_1 in E'; lia.
rewrite e1 Hd; split; move: g1 g2 Ha1 Hbc; lia.
Qed.

Lemma tsize_lt_TExp t1 t2 :
  negb (is_mul t2) -> TInv t2 ∉ exps t1 ->
  tsize t1 < tsize (TExp t1 t2) /\
  tsize (TInv t2) < tsize (TExp t1 t2) /\
  tsize t2 < tsize (TExp t1 t2).
Proof.
move => Nm2 t2_t1; case: (tsize_lt_TExp_strong _ _ Nm2 t2_t1) => H1 H2.
have H3 := tsize_lt_TInv Nm2.
do !split; lia.
Qed.

Lemma tsize_TExp_TInv t1 t2 :
  negb (is_mul (TInv t2)) -> t2 ∈ exps t1 ->
  tsize t2 < tsize t1 /\
  tsize (TInv t2) < tsize t1 /\
  tsize (TExp t1 (TInv t2)) < tsize t1.
Proof.
move => NmI2 H.
have Nm2 : negb (is_mul t2) := exps_Nmul _ _ H.
rewrite -{1 2 4}(TExpK' t1 t2 NmI2 Nm2).
set t1' := TExp t1 _.
have {}H : TInv t2 ∉ exps t1'.
  have Hpos : (SMS.count TInv t2 (exps t1) > 0)%Z by apply/exps_count_gt0.
  have Hval : SMS.count TInv t2 (exps t1') = (SMS.count TInv t2 (exps t1) - 1)%Z.
    rewrite /t1' (exps_count_TExp t2 t1 (TInv t2) NmI2).
    case: (decide (t2 = TInv t2)) => [e|_].
      by case: (TInv_Nid Nm2 (eq_sym e)).
    case: (decide (t2 = TInv (TInv t2))) => [_|ne]; first done.
    by case: (ne (eq_sym (TInvK t2))).
  move=> Hin.
  have := proj2 (exps_count_gt0 (TInv t2) t1') Hin.
  rewrite exps_count_TInv Hval; lia.
by case: (tsize_lt_TExp _ _ Nm2 H) => ? [] ??; eauto.
Qed.

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

Lemma tsize_in_sumn t' ts : t' ∈ ts -> tsize t' <= sum_list_with tsize ts.
Proof.
elim: ts => [|t ts IH]; first by rewrite elem_of_nil.
rewrite elem_of_cons => -[-> /=|/IH h /=]; lia.
Qed.

Lemma tsize_base_lt t : is_exp t -> tsize (base t) < tsize t.
Proof.
rewrite is_exp_unfold => xt.
rewrite /tsize unfold_base; move: xt.
by case: (unfold_term t) => [o|o t'|[||] t1 t2|ts] //= _; lia.
Qed.

Lemma tsize_exps_lt t' t : t' ∈ exps t -> tsize t' < tsize t.
Proof.
move => t'_t.
have en : exps t ≠ [] by move=> e; rewrite e elem_of_nil in t'_t.
have xt : is_exp t.
  case E: (is_exp t) => //; move: en; rewrite (exps_expN_bool _ _) //; by rewrite E.
rewrite -{1}(base_expsK t)
  (tsize_TExpN _ _ (is_exp_base_bool t) (atom_exps t) (no_inv_exps t)).
have Hle := tsize_in_sumn _ _ t'_t.
have Hb := tsize_gt0 (base t).
rewrite (bool_decide_eq_true_2 (exps t ≠ []) en) /=; lia.
Qed.

Lemma tsize_TMulN ts :
  atomic ts -> (forall t', t' ∈ ts -> TInv t' ∉ ts) -> ts ≠ [] ->
  tsize (TMulN ts) = (if bool_decide (1 < length ts) then 1 else 0) + sum_list_with tsize ts.
Proof.
move => atom nc tsN0.
have /list.Forall_forall atom' := atom.
have atomU : Forall (fun pt => negb (PreTerm.is_mul pt)) (unfold_term <$> ts).
  exact: (atomic_unfold _ atom).
have canc := no_inv_aux_unfold ts atom' nc.
rewrite /tsize /TMulN unfold_TMulN.
rewrite (PreTerm.tsize_mul _ atomU canc); last first.
  by move=> H; apply: tsN0; apply: (inj (fmap unfold_term)); rewrite H.
rewrite length_fmap; congr Nat.add.
by elim: ts {atom nc canc tsN0 atom' atomU} => [//|t' ts IH] /=; rewrite IH.
Qed.

Lemma tsize_factors_lt t' t : is_mul t -> t' ∈ factors t -> tsize t' < tsize t.
Proof.
move => xt t'_t.
have tsN0 : factors t ≠ [] by move=> e; rewrite e elem_of_nil in t'_t.
rewrite -{1}(factorsK t)
  (tsize_TMulN _ (atom_factors t) (no_inv_factors t) tsN0).
have Hle := tsize_in_sumn _ _ t'_t.
have szge : 1 < length (factors t).
  have szN1 : length (factors t) ≠ 1.
    rewrite /factors length_fmap; move: xt; rewrite is_mul_unfold.
    case: (unfold_term t) (wf_unfold_term t) => // ts wf _.
    case: (PreTerm.wf_Mul_inv _ wf) => _ [_ [_ Hlen]]; by rewrite /PreTerm.factors.
  have : factors t ≠ [] := tsN0.
  case: (factors t) szN1 => [|?[|??]] //=; lia.
rewrite (bool_decide_eq_true_2 (1 < length (factors t)) szge) /=; lia.
Qed.

Lemma term_lt_ind (T : term -> Prop) :
  (forall t, (forall t', (tsize t' < tsize t) -> T t') -> T t) ->
  forall t, T t.
Proof. exact: term_lt_rect. Qed.
