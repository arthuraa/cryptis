From stdpp Require Import base countable gmap.
From iris.heap_lang Require Import lang notation proofmode.
From iris.algebra Require Import namespace_map gmap gset auth.
From iris.base_logic Require Import gen_heap.
From iris.base_logic.lib Require Import auth.
From iris_string_ident Require Import ltac2_string_ident.
From mathcomp Require ssrbool order path.
From deriving Require deriving.
From crypto Require Export mathcomp_compat.

(* TODO: Move to Iris? *)
Instance dom_ne {T : ofeT} :
  NonExpansive (dom (gset loc) : gmap loc T -> gset loc).
Proof. by move=> ??? e ?; rewrite !elem_of_dom e. Qed.

Lemma auth_own_prod_3 {Σ} {A B C : ucmraT} `{!authG Σ (prodUR (prodUR A B) C)}
  γ (a : A) (b : B) (c : C) :
  auth_own γ (a, b, c) ⊣⊢
  auth_own γ (a, ε, ε) ∗
  auth_own γ (ε, b, ε) ∗
  auth_own γ (ε, ε, c).
Proof.
rewrite -auth_own_op -auth_own_op.
rewrite -!pair_op /=.
by rewrite !(ucmra_unit_left_id, ucmra_unit_right_id).
Qed.

Lemma meta_meta_token `{Countable L, !gen_heapG L V Σ, Countable A} l (x : A) N E :
  ↑N ⊆ E →
  meta_token l E -∗
  meta l N x -∗
  False.
Proof.
iIntros (sub) "Htoken #Hmeta1".
pose (X := {[encode x]} : gset positive).
iMod (meta_set _ _ (fresh X) with "Htoken") as "#Hmeta2"=> //.
iAssert (meta l N (encode x)) as "Hmeta1'".
  by rewrite {1 3}/meta seal_eq.
iPoseProof (meta_agree with "Hmeta1' Hmeta2") as "%e"; iPureIntro.
assert (contra : encode x ∈ X). { by apply/elem_of_singleton. }
destruct (is_fresh X); by rewrite -e.
Qed.

(* I've made an MR for this. *)
Lemma gmap_equivI `{!EqDecision K, !Countable K, A : ofeT, M : ucmraT}
  (m1 m2 : gmap K A) :
  m1 ≡ m2 ⊣⊢@{uPredI M} (∀ i : K, m1 !! i ≡ m2 !! i).
Proof. by uPred.unseal. Qed.

Lemma dom_singleton_eq `{EqDecision K, Countable K} {T} (m : gmap K T) x :
  dom (gset K) m = {[x]} →
  ∃ y, m = {[x := y]}.
Proof.
move=> e.
have {}e: ∀ x' : K, x' ∈ dom (gset K) m ↔ x' ∈ ({[x]} : gset K) by rewrite e.
have: x ∈ ({[x]} : gset K) by rewrite elem_of_singleton.
rewrite -e elem_of_dom; case=> y m_x; exists y.
apply: map_eq=> x'; case: (decide (x' = x))=> [ {x'}->|ne].
  by rewrite lookup_singleton.
rewrite lookup_singleton_ne // -(@not_elem_of_dom _ _ (gset K)).
by rewrite e elem_of_singleton.
Qed.

Lemma option_Forall2E {A B} {R : A → B → Prop} ox oy :
  option_Forall2 R ox oy ↔
  match ox, oy with
  | Some x, Some y => R x y
  | None, None => True
  | _, _ => False
  end.
Proof.
split; first by case.
by case: ox oy=> [x|] [y|] //; constructor.
Qed.

Lemma option_equivE `{Equiv A} (ox oy : option A) :
  ox ≡ oy ↔
  match ox, oy with
  | Some x, Some y => x ≡ y
  | None, None => True
  | _, _ => False
  end.
Proof. apply option_Forall2E. Qed.

Lemma namespace_map_validI Σ (A : cmraT) (x : namespace_map A) :
  ✓ x ⊣⊢@{iPropI Σ}
  match namespace_map_token_proj x with
  | CoPset E =>
    ✓ namespace_map_data_proj x
    ∧ ⌜∀ i, namespace_map_data_proj x !! i = None ∨ i ∉ E⌝
  | CoPsetBot => False
  end.
Proof. by uPred.unseal; case: x=> [? [?|]]. Qed.


Global Instance auth_auth_cancelable (T : ucmraT) (x : T) : Cancelable (● x).
Proof.
intros n [yauth yfrag] [zauth zfrag].
rewrite auth_validN_eq /=; destruct yauth as [[yfrac yauth]|]; rewrite /=.
  destruct 1 as [contra _].
  apply exclusiveN_l in contra; first by destruct contra.
  exact frac_full_exclusive. (* ??? *)
destruct 1 as [_ (x' & ex & dec & valid)].
destruct 1 as [eauth efrag]; simpl in *.
rewrite !ucmra_unit_left_id in efrag *; move=> efrag.
split=> //.
destruct zauth as [[zfrac zauth]|]; trivial.
rewrite ucmra_unit_right_id -Some_op -pair_op in eauth * => eauth.
move/Some_dist_inj: eauth=> [/= eauth _].
enough (contra : ✓ (1%Qp ⋅ zfrac)).
  apply exclusive_l in contra; first by case: contra.
  apply frac_full_exclusive.
by rewrite -eauth.
Qed.

(* Double-check this does not exist *)
Lemma singleton_inj `{!EqDecision T, !Countable T} :
  Inj eq eq (singleton : T -> gset T).
Proof.
move=> x1 x2 e.
have : x1 ∈ ({[x1]} : gset _) by apply elem_of_singleton.
by rewrite e => /elem_of_singleton.
Qed.

Definition perm `{!EqDecision T, !Countable T} (X : gset (T * T)) :=
  forall p1 p2, p1 ∈ X → p2 ∈ X → (p1.1 = p2.1 ↔ p1.2 = p2.2).

Definition flipb {T S} (b : bool) (f : T → T → S) x y :=
  f (if b then x else y) (if b then y else x).

Class Repr A := repr : A -> val.
Arguments repr / .

Instance repr_val : Repr val := λ x, x.
Arguments repr_val / .

Instance repr_Z : Repr Z := λ x, #x.
Arguments repr_Z / .

Instance repr_option `{Repr A} : Repr (option A) := λ x,
  match x with
  | Some x => SOMEV (repr x)
  | None => NONEV
  end.
Arguments repr_option {A} {_} !_.

Definition repr_list_aux `{Repr A} :
  seal (foldr (fun x v => SOMEV (repr x, v)%V) NONEV).
  by eexists.
Qed.
Instance repr_list `{Repr A} : Repr (list A) := unseal repr_list_aux.
Arguments repr_list {A} {_} _ : simpl never.

Lemma repr_list_eq `{Repr A} :
  repr_list = foldr (fun x v => SOMEV (repr x, v)%V) NONEV.
Proof. exact: seal_eq. Qed.

Lemma repr_list_val `{Repr A} (xs : list A) :
  repr_list xs = repr_list (map repr xs).
Proof.
rewrite !repr_list_eq; by elim: xs => //= x xs ->.
Qed.

Definition leq_loc_loop : val := rec: "loop" "l1" "l2" "n" :=
  if: "l1" +ₗ "n" = "l2" then #true
  else if: "l2" +ₗ "n" = "l1" then #false
  else "loop" "l1" "l2" ("n" + #1).

Definition leq_loc : val := λ: "l1" "l2",
  leq_loc_loop "l1" "l2" #0.

Definition get_list : val := rec: "loop" "l" "n" :=
  match: "l" with NONE => NONE
  | SOME "p" =>
    if: "n" = #0 then SOME (Fst "p")
    else "loop" (Snd "p") ("n" - #1)
  end.

Notation "l !! n" := (get_list l n) : expr_scope.

Definition NILV : val := NONEV.
Definition CONSV hd tl : val := SOMEV (hd, tl).
Notation "hd :: tl" := (CONSV hd%V tl%V) : val_scope.
Notation "[ ]" := (NILV) : val_scope.
Notation "[ x ]" := (CONSV x%V NILV) : val_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (CONSV x%V (CONSV y%V .. (CONSV z%V NILV) ..)) : val_scope.

Definition NIL : expr := NONE.
Definition CONS : val := λ: "hd" "tl", SOME ("hd", "tl").
Notation "hd :: tl" := (CONS hd%E tl%E) : expr_scope.
Notation "[ ]" := (NIL) : expr_scope.
Notation "[ x ]" := (CONS x%V NIL) : expr_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (CONS x%E (CONS y%E .. (CONS z%E NIL) ..)) : expr_scope.

Definition eq_list : val := rec: "loop" "eq" "l1" "l2" :=
  match: "l1" with
    SOME "l1" =>
      match: "l2" with
        SOME "l2" =>
          let: "v1" := Fst "l1" in
          let: "l1" := Snd "l1" in
          let: "v2" := Fst "l2" in
          let: "l2" := Snd "l2" in
          "eq" "v1" "v2" && "loop" "eq" "l1" "l2"
      | NONE => #false
      end
   | NONE =>
     match: "l2" with
       SOME <> => #false
     | NONE => #true
     end
  end.

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

Definition insert_sorted : val := rec: "loop" "le" "x" "l" :=
  match: "l" with
    NONE => SOME ("x", NONE)
  | SOME "l" =>
    let: "y" := Fst "l" in
    let: "l" := Snd "l" in
    if: "le" "x" "y" then SOME ("x", SOME ("y", "l"))
    else SOME ("y", "loop" "le" "x" "l")
  end.

Definition leq_list : val := rec: "loop" "eq" "le" "l1" "l2" :=
  match: "l1" with
    NONE => #true
  | SOME "l1" =>
    match: "l2" with
      NONE => #false
    | SOME "l2" =>
      let: "x1" := Fst "l1" in
      let: "x2" := Fst "l2" in
      let: "l1" := Snd "l1" in
      let: "l2" := Snd "l2" in
      if: "eq" "x1" "x2" then "loop" "eq" "le" "l1" "l2"
      else "le" "x1" "x2"
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
Proof. by move=> x12; elim: e => //= *; substC; congruence. Qed.

Lemma subst_list_match_aux var v vars el ek :
  subst var v (list_match_aux vars el ek) =
  list_match_aux vars (subst var v el) (
    if decide (var ∈ vars) then ek else subst var v ek).
Proof.
elim: vars => [|var' vars IH] //= in el ek *.
case: (decide (var = var')) => [<-|ne].
  rewrite decide_False; last by intuition congruence.
  rewrite (@decide_True _ (var ∈ var :: vars)) //; last by set_solver.
rewrite decide_True; last by intuition congruence.
rewrite IH; case: (decide (var ∈ vars)) => [in_vars|nin_vars] /=.
  rewrite (@decide_False _ (var = var')) //.
  rewrite !(@decide_True  _ (var ∈ _)) //; set_solver.
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
  apply: IH; set_solver.
rewrite decide_True; last by split; eauto; set_solver.
rewrite IH //; set_solver.
Qed.

Fact list_match_key : unit. Proof. exact: tt. Qed.

Definition list_match :=
  locked_with list_match_key (
    λ vars l k,
      list_match_aux vars l (close_vars vars k)
  ).

Canonical list_match_unlockable := [unlockable of list_match].

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
rewrite decide_True ?IH //; by intuition congruence.
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
Proof.
elim: e => //=; try by intros; subst_free_vars; congruence.
Qed.

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
Proof.
by elim: e => /=; try by intros; subst_free_vars_rem; congruence.
Qed.

Lemma free_vars_subst var v e :
  free_vars (subst var v e) = free_vars e ∖ {[var]}.
Proof.
elim: e => //=; intros; subst_free_vars_rem; subst; set_solver.
Qed.

Lemma subst_nsubst var v vars vs e :
  var ∈ vars →
  subst var v (nsubst vars vs e) = nsubst vars vs e.
Proof.
elim: vars vs=> [|var' vars IH] [|v' vs]; try by rewrite ?elem_of_nil //=.
case: (decide (var = var')) => [<- _|var_var'].
  rewrite subst_free_vars //; exact: subst_free_vars_rem.
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
  move=> _; set_solver.
case=> e_len; rewrite free_vars_subst IH //.
set_solver.
Qed.

Section ListLemmas.

Context `{!Repr A, !heapG Σ}.

Lemma twp_get_list E (l : list A) (n : nat) Ψ :
  Ψ (repr (l !! n)) -∗
  WP repr l !! #n @ E [{ Ψ }].
Proof.
rewrite /= repr_list_eq.
elim: n l Ψ => [|n IH] [|x l] /= Ψ; iIntros "post";
wp_rec; wp_pures; eauto.
rewrite (_ : (S n - 1)%Z = n); try lia.
by iApply IH.
Qed.

Lemma wp_get_list E (l : list A) (n : nat) Ψ :
  Ψ (repr (l !! n)) -∗
  WP repr l !! #n @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_get_list. Qed.

Lemma twp_nil E Ψ :
  Ψ (repr (@nil A)) -∗
  WP []%V @ E [{ Ψ }].
Proof.
rewrite /NILV /= repr_list_eq; iIntros "?"; wp_pures.
by iApply twp_value. (* FIXME *)
Qed.

Lemma wp_nil E Ψ :
  Ψ (repr (@nil A)) -∗
  WP []%V @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_nil. Qed.

Lemma twp_cons E x xs Ψ :
  Ψ (repr (x :: xs)) -∗
  WP repr x :: repr xs @ E [{ Ψ }].
Proof.
rewrite /= repr_list_eq; iIntros "post"; by rewrite /CONS; wp_pures.
Qed.

Lemma wp_cons E x xs Ψ :
  Ψ (repr (x :: xs)) -∗
  WP repr x :: repr xs @ E {{ Ψ }}.
Proof. by iIntros "?"; iApply twp_wp; iApply twp_cons. Qed.

Definition list_to_expr :=
  foldr (fun (x : A) e => CONS (repr x) e) NILV.

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
rewrite repr_list_eq.
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
  set_solver.
case: (decide (length vars = length vs)) => [eq_l|neq_l]; last first.
  rewrite decide_False //; congruence.
rewrite eq_l decide_True //.
case: decide => [//|nin_vars] /=.
rewrite decide_True //= subst_free_vars //.
wp_pures; iApply wp_bind; wp_pures; by iApply wp_bind_inv.
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
   else Ψ NONEV) -∗
  WP list_match vars (repr vs) k @ E {{ Ψ }}.
Proof.
rewrite unlock; iIntros "post".
assert (disj : elements (free_vars (close_vars vars k)) ## vars).
  elim: vars => [|var vars IH] /= in k *; try case: decide => ?; set_solver.
iApply (wp_list_match_aux E vs (repr vs)); eauto.
  by iIntros (?) "?"; iApply wp_value.
case: decide => ? //.
iApply (wp_close_vars with "post").
by rewrite map_length.
Qed.

Lemma twp_eq_list `{EqDecision A} (f : val) (l1 l2 : list A) Φ E :
  (∀ (x1 x2 : A) Ψ,
      x1 ∈ l1 →
      Ψ #(bool_decide (x1 = x2)) -∗
      WP f (repr x1) (repr x2) @ E [{ Ψ }]) →
  Φ #(bool_decide (l1 = l2)) -∗
  WP eq_list f (repr l1) (repr l2) @ E [{ Φ }].
Proof.
rewrite repr_list_eq /=.
elim: l1 l2 Φ => [|x1 l1 IH] [|x2 l2] Φ wp_f /=;
iIntros "post" ; wp_rec; wp_pures; do 1?by iApply "post".
wp_bind (f _ _); iApply (wp_f x1 x2); first by set_solver.
case: (bool_decide_reflect (x1 = x2)) => [->|n_x1x2]; wp_pures; last first.
  rewrite bool_decide_decide decide_False; by [iApply "post"|congruence].
iApply IH; first by move=> *; iApply wp_f; set_solver.
case: (bool_decide_reflect (l1 = l2)) => [->|n_l1l2].
- by rewrite bool_decide_decide decide_True.
- by rewrite bool_decide_decide decide_False //; congruence.
Qed.

End ListLemmas.

Section Loc.

Context `{!heapG Σ}.
Import ssreflect.order deriving.instances.

Lemma twp_leq_loc_loop E (l1 l2 : loc) (n k : nat) Ψ :
  loc_car l2 = (loc_car l1 + (n + k)%nat)%Z ∨
  loc_car l1 = (loc_car l2 + (n + k)%nat)%Z ∧ n + k ≠ 0%nat →
  Ψ #(l1 <= l2)%O -∗
  WP leq_loc_loop #l1 #l2 #n @ E [{ Ψ }].
Proof.
have leq_locE l1' l2' :
    (l1' <= l2')%O = bool_decide (loc_car l1' ≤ loc_car l2')%Z.
  exact/(ssrbool.sameP (Z.leb_spec0 _ _))/bool_decide_reflect.
have eq_locE (l1' l2' : loc) :
    bool_decide (#l1' = #l2') = bool_decide (loc_car l1' = loc_car l2').
  apply: bool_decide_iff; split => [[->] //|].
  by case: l1' l2' => [?] [?] /= ->.
elim: k n => [|k IH] n e_l1l2; iIntros "post"; wp_pures; wp_rec; wp_pures.
- rewrite eq_locE.
  case: bool_decide_reflect => /= [eq|neq]; wp_pures.
    rewrite leq_locE bool_decide_decide decide_True //=.
    lia.
  rewrite eq_locE bool_decide_decide decide_True /=; try lia.
  wp_pures; rewrite leq_locE bool_decide_decide decide_False //.
  move=> H; apply: neq; rewrite /loc_add /= in H; lia.
- rewrite eq_locE bool_decide_decide decide_False; last by move=> /= ?; lia.
  wp_pures.
  rewrite eq_locE bool_decide_decide decide_False; last by move=> /= ?; lia.
  wp_pures.
  rewrite (_ : (n + 1)%Z = S n :> Z); try lia.
  iApply IH => //; lia.
Qed.

Lemma twp_leq_loc E (l1 l2 : loc) Ψ :
  Ψ #(l1 <= l2)%O -∗
  WP leq_loc #l1 #l2 @ E [{ Ψ }].
Proof.
have [off offP] :
    ∃ off : nat, (loc_car l2 = loc_car l1 + off ∨
                  loc_car l1 = loc_car l2 + off ∧ off ≠ 0%nat)%Z.
  exists (Z.to_nat (Z.abs (loc_car l1 - loc_car l2))); lia.
iIntros "post"; rewrite /leq_loc -[0%Z]/(Z.of_nat 0); wp_pures.
by iApply twp_leq_loc_loop => //.
Qed.

End Loc.

Section Ordered.

Import ssrbool seq ssreflect.order path deriving.instances.
Variable (d : unit) (A : orderType d).
Context `{!Repr A, !heapG Σ}.
Import Order Order.POrderTheory Order.TotalTheory.
Implicit Types (x y z : A) (s : seqlexi_with d A).

Lemma twp_insert_sorted (f : val) (x : A) (l : list A) E (Φ : val → iProp Σ) :
  is_true (sorted le l) →
  (∀ (y z : A) Ψ,
    Ψ #(le y z) -∗
    WP f (repr y) (repr z) @ E [{ Ψ }]) →
  Φ (repr (sort le (x :: l))) -∗
  WP insert_sorted f (repr x) (repr l) @ E [{ Φ }].
Proof.
rewrite repr_list_eq => sorted_l wp_f.
elim: l sorted_l Φ => //= [|y l IH] path_l Φ;
iIntros "post"; wp_rec; wp_pures => //.
move/(_ (path_sorted path_l)) in IH.
wp_bind (f _ _); iApply wp_f.
have [le_xy|le_yx] := boolP (x <= y)%O; wp_pures.
  by rewrite sort_le_id //= le_xy.
move: le_yx; rewrite -ltNge => /ltW le_yx.
wp_bind (insert_sorted _ _ _); iApply IH.
suff -> : sort le [:: x, y & l] = y :: sort le (x :: l) by wp_pures.
rewrite -[RHS]sort_le_id /=.
  apply/perm_sort_leP/perm_consP.
  exists 1, (l ++ [:: x])%SEQ.
  by rewrite /= perm_catC perm_sym /= perm_sort; split.
rewrite path_min_sorted ?sort_le_sorted // all_sort /= le_yx /=.
apply: order_path_min => //; apply: le_trans.
Qed.

Lemma twp_leq_list (feq : val) (fle : val) s1 s2 E (Φ : val → iProp Σ) :
  (∀ x1 x2 Ψ,
      Ψ #(eqtype.eq_op x1 x2) -∗
      WP feq (repr x1) (repr x2) @ E [{ Ψ }]) →
  (∀ x1 x2 Ψ,
      is_true (x1 \in s1) →
      Ψ #(le x1 x2) -∗
      WP fle (repr x1) (repr x2) @ E [{ Ψ }]) →
  Φ #(le s1 s2) -∗
  WP leq_list feq fle (repr s1) (repr s2) @ E [{ Φ }].
Proof.
move=> feqP.
rewrite /= repr_list_eq.
elim: s1 s2 => [|x1 s1 IH] [|x2 s2] fleP; iIntros "HΦ"; wp_rec; wp_pures => //.
rewrite lexi_cons; wp_bind (feq _ _); iApply feqP.
case: (ltgtP x1 x2) => [l_x1x2|l_x2x1|<-] /=; wp_pures.
- by iApply fleP; rewrite ?inE ?eqtype.eqxx // ltW.
- by iApply fleP; rewrite ?inE ?eqtype.eqxx // leNgt l_x2x1.
- by iApply IH => // x1' ?? x1'_in; iApply fleP; rewrite inE x1'_in orbT.
Qed.

End Ordered.

Instance repr_prod `{Repr A, Repr B} : Repr (A * B) :=
  λ p, (repr p.1, repr p.2)%V.
Arguments repr_prod {_ _ _ _} !_.
