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

Lemma tsize_gt0 t : 0 < tsize t.
Proof. rewrite /tsize; case: unfold_term => /=; lia. Qed.

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

Lemma tsize_TInv t :
  negb (is_mul t) → negb (is_inv t) → tsize (TInv t) = S (tsize t).
Proof.
rewrite /tsize is_mul_unfold is_inv_unfold unfold_TInv => Nm Ni.
rewrite PreTerm.inv_Nmul //.
by case: unfold_term Nm Ni => //=; case.
Qed.

Lemma tsize_TExp t1 t2 :
  negb (is_exp t1) → t2 ≠ TMulN [] →
  tsize (TExp t1 t2) = S (tsize t1 + tsize t2).
Proof.
rewrite /tsize is_exp_unfold unfold_TExp /PreTerm.exp=> Nx1 N12.
rewrite PreTerm.expo_expN // PreTerm.mul_unit_l PreTerm.mul1; last first.
  exact: wf_unfold_term.
rewrite PreTerm.base_expN // /PreTerm.exp_aux bool_decide_eq_false_2 //.
move=> e; apply: N12; apply: (inj unfold_term).
by rewrite unfold_TMulN.
Qed.

Lemma unfold_TMulN_strong ts :
  invs_canceled ts →
  length ts ≠ 1 →
  ∃ ts' : list _,
    unfold_term (TMulN ts) = PreTerm.PTMul ts' ∧
    ts' ≡ₚ unfold_term <$> ts.
Proof.
move=> ic tsN1; rewrite unfold_TMulN.
pose (ts' := PreTerm.normalize_factors (unfold_term <$> ts)).
have e: ts' ≡ₚ unfold_term <$> ts.
  rewrite /ts' /PreTerm.normalize_factors.
  rewrite list_fmap_bind SMS.to_id_perm; first last.
  - move=> t0 /list_elem_of_bind [/= t [] t0_t t_ts].
    admit.
  - elim: ts ic {tsN1 ts'} => //= t ts IH /invs_canceled_cons [tP [] Nm ic].
    rewrite /mbind in IH.
    by rewrite -unfold_factors factors_Nmul //= IH.
exists ts'; split => //.
rewrite -(length_fmap unfold_term) -e /ts' in tsN1.
rewrite /PreTerm.mul /ts'.
by case: PreTerm.normalize_factors tsN1 => //= ? [].
Admitted.

(* MOVE *)
Lemma sum_list_with_fmap {A B} (f : B → nat) (g : A → B) xs :
  sum_list_with f (g <$> xs) = sum_list_with (f ∘ g) xs.
Proof. by elim: xs => //= x xs ->. Qed.

Lemma tsize_TMulN ts :
  invs_canceled ts →
  tsize (TMulN ts) =
  Nat.b2n (bool_decide (length ts ≠ 1)) +
  sum_list_with tsize ts.
Proof.
move=> ic; case: (decide (length ts = 1)) => len_ts.
  rewrite bool_decide_eq_false_2 //=; last congruence.
  case: ts len_ts {ic} => // t [] //.
  rewrite TMulN1 /=; lia.
rewrite /tsize.
case: (unfold_TMulN_strong _ ic len_ts)=> ts' [] -> /= e.
by rewrite bool_decide_eq_true_2 //= e sum_list_with_fmap.
Qed.

Definition tsizeE := (tsize_TInv, tsize_TExp, tsize_TMulN, tsize_eq).

Lemma tsize_lt_TInv {t} : negb (is_mul t) → tsize (TInv t) ≤ S (tsize t).
Proof.
move=> Nm.
case: (decide (is_inv t)) => [tV|/negb_True tNV].
- rewrite -{2}[t]TInvK (tsize_TInv (TInv t)) ?is_mul_TInv //; first lia.
  by rewrite is_inv_TInv // negb_involutive.
- by rewrite tsize_TInv.
Qed.

Lemma tunitP t : t = TMulN [] ↔ factors t = [].
Proof.
by split=> [->|<-]; rewrite ?factorsK // factors_TMulN0.
Qed.

(* MOVE *)
Lemma Permutation_fmap_inv_l {A B} (f : A → B) (xs : list A) (ys : list B) :
  f <$> xs ≡ₚ ys → ∃ xs', ys = f <$> xs' ∧ xs ≡ₚ xs'.
Proof.
elim: xs ys => //= [|x xs IH] ys.
- by move=> /Permutation_nil ->; exists [].
- move=> e; have := Permutation_cons_inv_l _ _ _ e.
  case=> ys1 [] ys2 [] eys {}e.
  case: (IH _ e)=> xs' [] eys' exs.
  exists (take (length ys1) xs' ++ x :: drop (length ys1) xs').
  rewrite fmap_app fmap_take fmap_cons fmap_drop.
  rewrite -eys' take_app_length drop_app_length; split => //.
  rewrite exs -Permutation_middle.
  by rewrite take_drop.
Qed.

Global Instance list_fmap_perm_inj {A B} (f : A → B) :
  Inj (=) (=) f →
  Inj (≡ₚ) (≡ₚ) (fmap f).
Proof.
move=> inj_f xs ys /Permutation_fmap_inv_l [xs' [] e1 e2].
have {}e1: ys = xs' by apply: (inj (fmap f : list _ → _)).
by rewrite e1.
Qed.
(* /MOVE *)


Lemma factors_TMulN ts :
  invs_canceled ts →
  factors (TMulN ts) ≡ₚ ts.
Proof.
move=> ic; apply: (inj (fmap unfold_term : list _ → _)).
rewrite unfold_factors; case: (decide (length ts = 1)).
  case: ts ic => // t [] //=; rewrite TMulN1 -unfold_factors.
  move=> ic _; rewrite factors_Nmul //=.
  by have /ic [??] : t ∈ [t] by rewrite list_elem_of_singleton.
move=> tsN1; case: (unfold_TMulN_strong _ ic tsN1)=> ts' [] -> e.
symmetry in e; case/Permutation_fmap_inv_l: e=> {}ts' [] -> e.
by rewrite e.
Qed.

Lemma tsize_TExpN t ts :
  negb (is_exp t) →
  invs_canceled ts →
  tsize (TExpN t ts) =
  (if bool_decide (ts ≠ []) then 1 else 0) +
  (if bool_decide (1 < length ts) then 1 else 0)
  + tsize t + sum_list_with tsize ts.
Proof.
move=> tNx ic; rewrite /TExpN.
case: (decide (ts = [])) => [->|tsN0] /=; first by rewrite TExp_unit; lia.
rewrite bool_decide_eq_true_2 //= tsize_TExp //; first last.
  move=> /(f_equal factors) e; have /Permutation_nil ? : [] ≡ₚ ts.
    rewrite -(factors_TMulN ts) // -(factors_TMulN []) ?e //.
    exact: invs_canceled0.
  congruence.
rewrite tsize_TMulN //.
have ->: bool_decide (length ts ≠ 1) = bool_decide (1 < length ts).
  apply: bool_decide_ext; split; last lia.
  case: (ts) tsN0=> //= ? [] //=; lia.
case: bool_decide => /=; lia.
Qed.

Lemma is_expE t : is_exp t ↔ expo t ≠ TMulN [].
Proof.
rewrite is_exp_unfold.
have ->: expo t ≠ TMulN [] ↔ unfold_term (expo t) ≠ unfold_term (TMulN []).
  split; last congruence.
  by move=> n1 contra; apply: n1; apply: inj contra.
rewrite unfold_expo unfold_TMulN /= -[PreTerm.mul _]/(PreTerm.PTMul []).
case: unfold_term (wf_unfold_term t) => /=; try by intuition congruence.
case; try by intuition congruence.
by move=> t1 t2; rewrite !andb_True bool_decide_spec; case; intuition.
Qed.

Lemma is_expNE t : negb (is_exp t) ↔ expo t = TMulN [].
Proof.
rewrite negb_True is_expE; split; eauto.
exact: dec_stable.
Qed.

Lemma tsize_lt_TExp_strong t1 t2 :
  negb (is_mul t2) → TInv t2 ∉ exps t1 →
  tsize t1 < tsize (TExp t1 t2) ∧
  S (tsize t2) < tsize (TExp t1 t2).
Proof.
move=> t2Nm t2_t1; rewrite TExpE -/(TMul _ _).
have xE: TMul (expo t1) t2 = TMulN (t2 :: factors (expo t1)).
  by rewrite /TMul -{1}[expo t1]factorsK TMulN_cat TMulN_catC.
have xN1: TMul (expo t1) t2 ≠ TMulN [].
  rewrite -/(TMul _ _) => /(f_equal (TMul (TInv t2))).
  rewrite [TMul _ t2]TMulC -TMulA TMulK_l TMul1_l TMul1 => eexpo.
  move: t2_t1; rewrite /exps eexpo factors_Nmul ?is_mul_TInv //.
  rewrite list_elem_of_singleton; congruence.
have ic: invs_canceled (t2 :: factors (expo t1)).
  rewrite invs_canceled_cons; do 2!split => //.
  exact: invs_canceled_factors.
rewrite tsize_TExp //; last exact: base_Nexp.
rewrite xE tsize_TMulN //=.
have ? := tsize_gt0 (base t1); split; last lia.
rewrite -{1}[t1]TExp_base_expo.
case: (decide (expo t1 = TMulN [])) => [->|n1].
  rewrite factors_TMulN0 /= TExp_unit; lia.
rewrite tsize_TExp //; last exact: base_Nexp.
rewrite -{1}[expo t1]factorsK tsize_TMulN; last exact: invs_canceled_factors.
have ? := tsize_gt0 t2.
move: n1; rewrite tunitP; case: factors=> [|? [| ??]] //=; lia.
Qed.

Lemma tsize_lt_TExp t1 t2 :
  negb (is_mul t2) → TInv t2 ∉ exps t1 →
  tsize t1 < tsize (TExp t1 t2) ∧
  tsize (TInv t2) < tsize (TExp t1 t2) ∧
  tsize t2 < tsize (TExp t1 t2).
Proof.
move => Nm2 t2_t1; case: (tsize_lt_TExp_strong _ _ Nm2 t2_t1) => H1 H2.
have H3 := tsize_lt_TInv Nm2.
do !split; lia.
Qed.

Lemma tsize_TExp_TInv t1 t2 :
  negb (is_mul (TInv t2)) → t2 ∈ exps t1 →
  tsize t2 < tsize t1 ∧
  tsize (TInv t2) < tsize t1 ∧
  tsize (TExp t1 (TInv t2)) < tsize t1.
Proof.
move => NmI2 H.
have Nm2 : negb (is_mul t2) by rewrite is_mul_TInv in NmI2.
set t1' := TExp t1 (TInv t2).
have t1E: t1 = TExp t1' t2.
  by rewrite /t1' TExpA -/(TMul _ _) TMulK_l TExp_unit.
have {}H: TInv t2 ∉ exps t1'.
  rewrite /exps -count_gt0 in H.
  rewrite /exps -count_gt0 /t1' expo_TExp count_TMulN /=.
  rewrite !count_TInv_l count_TInv count_diag.
  case: is_mul Nm2 => //=; lia.
rewrite t1E; case: (tsize_lt_TExp _ _ Nm2 H)=> ? [] ??; eauto.
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

Lemma tsize_base_lt t : is_exp t → tsize (base t) < tsize t.
Proof.
rewrite is_exp_unfold => xt.
rewrite /tsize unfold_base; move: xt.
by case: (unfold_term t) => [o|o t'|[||] t1 t2|ts] //= _; lia.
Qed.

Lemma tsize_expo_lt t : is_exp t → tsize (expo t) < tsize t.
Proof.
rewrite /tsize is_exp_unfold unfold_expo.
case: unfold_term (wf_unfold_term t) => //=; try lia.
case=> //=; try lia.
Qed.

Lemma tsize_factors_le t t' : t ∈ factors t' → tsize t ≤ tsize t'.
Proof.
move=> ?; rewrite -[t']factorsK tsize_TMulN; last exact: invs_canceled_factors.
suff: tsize t ≤ sum_list_with tsize (factors t') by lia.
exact: sum_list_with_in.
Qed.

Lemma tsize_exps_lt t' t : t' ∈ exps t → tsize t' < tsize t.
Proof.
move => t'_t.
have en: exps t ≠ [] by move=> e; rewrite e elem_of_nil in t'_t.
have xt: is_exp t by move: en; rewrite /exps -tunitP is_expE.
have ?: tsize (expo t) < tsize t by exact: tsize_expo_lt.
have := tsize_factors_le _ _ t'_t; lia.
Qed.

Lemma tsize_factors_lt t' t : is_mul t → t' ∈ factors t → tsize t' < tsize t.
Proof.
move => xt t'_t.
have tsN0 : factors t ≠ [] by move=> e; rewrite e elem_of_nil in t'_t.
rewrite -{1}(factorsK t) tsize_TMulN; last exact: invs_canceled_factors.
have le: tsize t' ≤ sum_list_with tsize (factors t) by exact: sum_list_with_in.
rewrite -is_mulE; case: is_mul xt => //=; lia.
Qed.

Lemma term_lt_ind (T : term -> Prop) :
  (forall t, (forall t', (tsize t' < tsize t) -> T t') -> T t) ->
  forall t, T t.
Proof. exact: term_lt_rect. Qed.
