From elpi.apps Require Import locker.
From iris.heap_lang Require Import lang notation proofmode.
From mathcomp Require ssrbool order path.
From cryptis Require Import lib.repr.

Fixpoint list_match_aux (vars : list string) (l : expr) (k : expr) : expr :=
  match vars with
  | [] =>
    match: l with SOME <> => NONEV | NONE => k #() end
  | var :: vars =>
    let k' := if decide (var ∈ vars) then k else k (Fst var) in
    match: l with
      SOME var => list_match_aux vars (Snd var) k'
    | NONE => NONEV
    end
  end.

Ltac substC :=
  repeat match goal with
  | |- context [decide ?P] => destruct (decide P) as [?|?]; simpl
  | H : ?P ∧ ?Q |- _ => destruct H as [?|?]
  end.

Lemma substC x1 x2 v1 v2 e :
  x1 ≠ x2 →
  subst x1 v1 (subst x2 v2 e) = subst x2 v2 (subst x1 v1 e).
Proof. by move=> x12; elim: e => //= *; substC; by congruence. Qed.

Lemma subst_list_match_aux var v vars el ek :
  subst var v (list_match_aux vars el ek) =
  list_match_aux vars (subst var v el) (
    if decide (var ∈ vars) then ek else subst var v ek).
Proof.
elim: vars => [|var' vars IH] //= in el ek *.
case: (decide (var = var')) => [<-|ne].
  rewrite decide_False; last by intuition congruence.
  by rewrite (@decide_True _ (var ∈ var :: vars)) //; set_solver.
rewrite decide_True; last by intuition congruence.
rewrite IH; case: (decide (var ∈ vars)) => [in_vars|nin_vars] /=.
  rewrite (@decide_False _ (var = var')) //.
  by rewrite !(@decide_True  _ (var ∈ _)) //; set_solver.
rewrite decide_False // (@decide_False _ (var ∈ _)); last by set_solver.
case: decide => [in_vars'|nin_vars'] //=.
by rewrite decide_False.
Qed.

Fixpoint close_vars (vars : list string) (k : expr) : expr :=
  match vars with
  | [] => λ: <>, k
  | var :: vars =>
    (if decide (var ∈ vars) then close_vars vars k
     else λ: var, close_vars vars k)%E
  end.

Lemma subst_close_vars var v vars k :
  var ∉ vars →
  subst var v (close_vars vars k) = close_vars vars (subst var v k).
Proof.
elim: vars => [|var' vars IH] //= in k *.
case: decide => [in_vars'|nin_vars'] nin_vars /=.
  by apply: IH; set_solver.
rewrite decide_True; last by split; eauto; set_solver.
by rewrite IH //; set_solver.
Qed.

lock Definition list_match vars l k := list_match_aux vars l (close_vars vars k).

Notation "'list_match:' vars := e1 'in' e2" :=
  (list_match vars e1 e2)%E
  (at level 200, vars at level 1, e1, e2 at level 200,
  format "'[' 'list_match:'  vars  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Lemma subst_list_match var v vars el ek :
  subst var v (list_match vars el ek) =
  list_match vars (subst var v el) (
    if decide (var ∈ vars) then ek else subst var v ek).
Proof.
rewrite unlock subst_list_match_aux; case: decide => [//|nin_vars].
congr list_match_aux; elim: vars => [|var' vars IH] //= in {el} ek nin_vars *.
have neq : var ≠ var' by set_solver.
have {}nin_vars : var ∉ vars by set_solver.
case: (decide (var' ∈ vars)) => [in_vars'|nin_vars'] /=.
  by rewrite IH.
by rewrite decide_True ?IH //; intuition congruence.
Qed.

Definition binder_vars x : gset string :=
  match x with
  | BAnon => ∅
  | BNamed x => {[x]}
  end.

Lemma elem_of_binder_vars (x : string) (y : binder) :
  x ∈ binder_vars y ↔ x = y :> binder.
Proof.
case: y => /=; first by split.
by move=> ?; rewrite elem_of_singleton; split; congruence.
Qed.

Fixpoint free_vars e : gset string :=
  match e with
  | Val _ => ∅
  | Var x => {[x]}
  | Rec f x e => free_vars e ∖ binder_vars f ∖ binder_vars x
  | App e1 e2 => free_vars e1 ∪ free_vars e2
  | UnOp _ e => free_vars e
  | BinOp _ e1 e2 => free_vars e1 ∪ free_vars e2
  | If e1 e2 e3 => free_vars e1 ∪ free_vars e2 ∪ free_vars e3
  | Pair e1 e2 => free_vars e1 ∪ free_vars e2
  | Fst e | Snd e => free_vars e
  | InjL e | InjR e => free_vars e
  | Case e1 e2 e3 => free_vars e1 ∪ free_vars e2 ∪ free_vars e3
  | Fork e => free_vars e
  | AllocN e1 e2 => free_vars e1 ∪ free_vars e2
  | Free e => free_vars e
  | Load e => free_vars e
  | Store e1 e2 => free_vars e1 ∪ free_vars e2
  | CmpXchg e1 e2 e3 => free_vars e1 ∪ free_vars e2 ∪ free_vars e3
  | Xchg e1 e2 => free_vars e1 ∪ free_vars e2
  | FAA e1 e2 => free_vars e1 ∪ free_vars e2
  | NewProph => ∅
  | Resolve e1 e2 e3 => free_vars e1 ∪ free_vars e2 ∪ free_vars e3
  end.

Ltac subst_free_vars :=
  repeat match goal with
  | |- context [decide ?P] => destruct (decide P) as [?|?]
  | H : context[?x ∈ {[?y]}] |- _ => rewrite elem_of_singleton in H * => *
  | H : context[?x ∈ _ ∪ _] |- _ => rewrite elem_of_union in H * => *
  | H : context[?x ∈ _ ∖ _] |- _ => rewrite elem_of_difference in H * => *
  | H : context[?x ∈ binder_vars _] |- _ => rewrite elem_of_binder_vars in H * => *
  | H : _ ∧ _ |- _ => destruct H as [??]
  | H : ¬ (_ ∨ _) |- _ => apply Decidable.not_or in H
  | HQP : ¬ (?Q ∧ ?P), HP : ?P |- _ =>
    assert (¬ Q); [intros ?; apply HQP; by split|clear HQP]
  | HP : ?P, HPQ : ?P -> ?Q |- _ => specialize (HPQ HP)
  end.

Lemma subst_free_vars x v e : x ∉ free_vars e → subst x v e = e.
Proof. elim: e => //=; try by intros; subst_free_vars; by congruence. Qed.

Fixpoint nsubst (vars : list string) (vs : list val) (k : expr) : expr :=
  match vars, vs with
  | [], [] => k
  | var :: vars, v :: vs => subst var v (nsubst vars vs k)
  | _, _ => NONEV
  end.

Ltac subst_free_vars_rem :=
  repeat (
    simpl in *;
    match goal with
    | |- context [decide ?P] => destruct (decide P) as [?|?]
    | |- ¬ _ => intros ?
    | H : context[?x ∈ {[?y]}] |- _ => rewrite elem_of_singleton in H * => *
    | H : context[?x ∈ _ ∪ _] |- _ => rewrite elem_of_union in H * => *
    | H : context[?x ∈ _ ∖ _] |- _ => rewrite elem_of_difference in H * => *
    | H : context[?x ∈ binder_vars _] |- _ => rewrite elem_of_binder_vars in H * => *
    | H : _ ∧ _ |- _ => destruct H as [??]
    | H : ¬ (_ ∨ _) |- _ => apply Decidable.not_or in H
    | H : context[_ ∈ ∅] |- _ => rewrite -> elem_of_empty in H
    | HQP : ¬ (?Q ∧ ?P), HP : ?P |- _ =>
      assert (¬ Q); [intros ?; apply HQP; by split|clear HQP]
    | HQP : ¬ (?Q ∧ ?P) |- _ =>
      rewrite -> not_and_l in HQP; destruct HQP
    | H : ¬ ¬ _ |- _ => apply dec_stable in H
    | HP : ?P, HPQ : ?P -> ?Q |- _ => specialize (HPQ HP)
    | HNP : ¬ ?P, HP : ?P |- _ => destruct (HNP HP)
    | H : _ ∨ _ |- _ => destruct H
    | e : ?x = _ |- context[?x] => rewrite e
    end
  ).

Lemma subst_free_vars_rem var v e : var ∉ free_vars (subst var v e).
Proof. by elim: e => /=; try by intros; subst_free_vars_rem; by congruence. Qed.

Lemma free_vars_subst var v e :
  free_vars (subst var v e) = free_vars e ∖ {[var]}.
Proof. elim: e => //=; intros; subst_free_vars_rem; subst; by set_solver. Qed.

Lemma subst_nsubst var v vars vs e :
  var ∈ vars →
  subst var v (nsubst vars vs e) = nsubst vars vs e.
Proof.
elim: vars vs=> [|var' vars IH] [|v' vs]; try by rewrite ?elem_of_nil //=.
case: (decide (var = var')) => [<- _|var_var'].
  by rewrite subst_free_vars //; exact: subst_free_vars_rem.
rewrite elem_of_cons; case => var_in /=; first congruence.
by rewrite substC // IH.
Qed.

Lemma subst_nsubst_nin var v vars vs e :
  var ∉ vars →
  subst var v (nsubst vars vs e) = nsubst vars vs (subst var v e).
Proof.
elim: vars vs=> [|var' vars IH] [|v' vs]; try by rewrite ?elem_of_nil //=.
rewrite elem_of_cons; case/Decidable.not_or => var_var' var_nin.
by rewrite /= substC // IH.
Qed.

Lemma free_vars_nsubst vars vs e :
  length vars = length vs →
  free_vars (nsubst vars vs e) = free_vars e ∖ ⋃ (singleton <$> vars).
Proof.
elim: vars vs => [|var vars IH] [|v vs] //= in e *.
  by move=> _; set_solver.
case=> e_len; rewrite free_vars_subst IH //.
by set_solver.
Qed.

Section ListLemmas.

Context `{!Repr A, !Repr B, !heapGS Σ}.

Implicit Types (x : A) (xs : list A).

Fixpoint napp (vars : list string) (vs : list val) :=
  match vars, vs with
  | var :: vars, v :: vs =>
    if decide (var ∈ vars) then napp vars vs
    else AppLCtx v :: napp vars vs
  | [], [] => [AppLCtx #()]
  | _, _ => []
  end.

Lemma wp_list_match_aux E (vs : list A) evs vars k Ψ :
  elements (free_vars k) ## vars →
  (∀ Ψ, Ψ (repr_list vs) -∗ WP evs @ E {{ Ψ }}) -∗
  (if decide (length vars = length vs) then
     WP fill (napp vars (map repr vs)) k @ E {{ Ψ }}
   else Ψ NONEV) -∗
  WP list_match_aux vars evs k @ E {{ Ψ }}.
Proof.
rewrite repr_list_unseal.
elim: vars vs => [|var vars IH] [|v vs] /= in evs k *; iIntros (dis) "evs pS".
- by wp_pures; wp_bind evs; iApply "evs"; wp_pures.
- by wp_pures; wp_bind evs; iApply "evs"; wp_pures.
- by wp_pures; wp_bind evs; iApply "evs"; wp_pures.
rewrite /=; wp_pures; wp_bind evs; iApply "evs"; wp_pures.
rewrite subst_list_match_aux /=.
rewrite [if decide (var = var) then _ else _]decide_True //=.
assert (fresh_var : var ∉ free_vars k) by set_solver.
assert (dis' : elements (free_vars k) ## vars) by set_solver.
iApply (IH with "[]"); try by iIntros (Ψ') "p'"; wp_pures; eauto.
  case: decide => _ //=.
  rewrite free_vars_subst decide_True //=.
  by set_solver.
case: (decide (length vars = length vs)) => [eq_l|neq_l]; last first.
  by rewrite decide_False //; congruence.
rewrite eq_l decide_True //.
case: decide => [//|nin_vars] /=.
rewrite decide_True //= subst_free_vars //.
by wp_pures; iApply wp_bind; wp_pures; iApply wp_bind_inv.
Qed.

Lemma wp_close_vars E vars vs k Ψ :
  length vars = length vs →
  WP nsubst vars vs k @ E {{ Ψ }} -∗
  WP fill (napp vars vs) (close_vars vars k) @ E {{ Ψ }}.
Proof.
elim: vars vs => [|var vars IH] [|v vs] //= in k Ψ *.
  by iIntros (?) "p"; wp_pures.
move=> [] e; iIntros "p".
case: decide => [in_vars|nin_vars].
  rewrite subst_free_vars; first by iApply IH.
  rewrite free_vars_nsubst // elem_of_difference.
  case => _; rewrite elem_of_union_list.
  by apply; exists {[var]}; split; try set_solver.
rewrite /=.
iApply wp_bind.
wp_pures.
rewrite subst_nsubst_nin //.
iApply wp_bind_inv.
rewrite subst_close_vars //.
by iApply IH.
Qed.

Lemma wp_list_match E vars (vs : list A) k Ψ :
  (if decide (length vars = length vs) then
     WP nsubst vars (map repr vs) k @ E {{ Ψ }}
   else Ψ NONEV) ⊢
  WP list_match vars (repr vs) k @ E {{ Ψ }}.
Proof.
rewrite unlock; iIntros "post".
assert (disj : elements (free_vars (close_vars vars k)) ## vars).
  by elim: vars => [|var vars IH] /= in k *; try case: decide => ?; set_solver.
iApply (wp_list_match_aux E vs (repr vs)); eauto.
  by iIntros (?) "?"; iApply wp_value.
case: decide => ? //.
iApply (wp_close_vars with "post").
by rewrite length_map.
Qed.

End ListLemmas.
