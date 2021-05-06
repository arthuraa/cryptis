From stdpp Require Import base countable gmap.
From iris.heap_lang Require Import lang notation proofmode.
From iris.algebra Require Import namespace_map gmap gset auth.
From iris.base_logic Require Import gen_heap.
From iris.base_logic.lib Require Import auth.
From iris_string_ident Require Import ltac2_string_ident.
From mathcomp Require ssrbool order path.
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

Existing Instance repr_list.

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

Fixpoint list_match_aux (vars : list string) (l : string) (k : expr) : expr :=
  match vars with
  | [] =>
    match: l with SOME <> => NONEV | NONE => k end
  | v :: vars =>
    match: l with
      SOME l =>
      let: v := Fst l in
      let: l := Snd l in
      list_match_aux vars l k
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

Ltac substC :=
  repeat match goal with
  | |- context [decide ?P] => destruct (decide P) as [?|?]; simpl
  | H : ?P ∧ ?Q |- _ => destruct H as [?|?]
  end.

Lemma substC x1 x2 v1 v2 e :
  x1 ≠ x2 →
  subst x1 v1 (subst x2 v2 e) = subst x2 v2 (subst x1 v1 e).
Proof. by move=> x12; elim: e => //= *; substC; congruence. Qed.

Lemma subst_list_match_aux_in var v vars l k :
  var ∈ vars → l ∉ vars →
  subst var v (list_match_aux vars l k) = list_match_aux vars l k.
Proof.
elim: vars => [|var' vars IH]; first by set_solver.
case: (decide (var = var')) => [<- _|ne].
- rewrite elem_of_cons.
  case/Decidable.not_or=> l_var l_fresh /=.
  rewrite decide_False //.
  rewrite decide_True; last by split; congruence.
  rewrite decide_False //; by case; congruence.
- rewrite !elem_of_cons; case => var_in; first congruence.
  case/Decidable.not_or=> l_var' l_fresh /=.
  rewrite decide_False; last congruence.
  rewrite decide_True; last by split; congruence.
  do 2![rewrite decide_True; last by split; congruence].
  by rewrite IH.
Qed.

Lemma subst_list_match_aux var v vars l k :
  var ∉ vars → l ≠ var → l ∉ vars →
  subst var v (list_match_aux vars l k) =
  list_match_aux vars l (subst var v k).
Proof.
move=> var_in var_l.
elim: vars var_in => [|var' vars IH] /=; rewrite decide_False //.
rewrite !elem_of_cons.
case/Decidable.not_or => var_var' var_in.
case/Decidable.not_or => l_var' l_vars.
do ![rewrite decide_True; last by split; congruence].
by rewrite IH.
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
    | HP : ?P, HPQ : ?P -> ?Q |- _ => specialize (HPQ HP)
    | HNP : ¬ ?P, HP : ?P |- _ => destruct (HNP HP)
    | H : _ ∨ _ |- _ => destruct H
    end
  ).

Lemma subst_free_vars_rem var v e : var ∉ free_vars (subst var v e).
Proof.
by elim: e => /=; try by intros; subst_free_vars_rem; congruence.
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

Lemma wp_list_match_aux E vs vars (l : string) k Ψ :
  l ∉ vars →
  WP nsubst vars vs (subst l [] k) @ E {{ Ψ }} -∗
  WP subst l (repr_list vs) (list_match_aux vars l k) @ E {{ Ψ }}.
Proof.
rewrite repr_list_eq.
elim: vars vs k => [|var vars IH] [|v vs] k l_fresh /=.
- by iIntros "post"; wp_pures; rewrite decide_True //=; wp_pures.
- iIntros "post"; wp_pures; rewrite decide_True //= (lock (Val NONEV)).
  by wp_pures.
- iIntros "post"; wp_pures; rewrite decide_True //= {-2}(lock (Val NONEV)).
  by wp_pures.
- iIntros "post"; wp_pures; rewrite decide_True //=.
  wp_pures; rewrite decide_False; last by case.
  rewrite /= (@decide_True _ (l = l)) //.
  move: l_fresh; rewrite elem_of_cons => /Decidable.not_or [l_var l_fresh].
  rewrite decide_True; last by split => ?; congruence.
  rewrite decide_False; last by case.
  wp_pures.
  rewrite decide_True; last by split=> ?; congruence.
  case: (decide (var ∈ vars)) => [var_in|var_out].
    rewrite subst_list_match_aux_in // subst_nsubst //; by iApply IH.
  rewrite subst_list_match_aux // subst_nsubst_nin // substC //.
  by iApply IH.
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

Section Insertion.

Import ssrbool seq ssreflect.order path.
Variable (d : unit) (A : orderType d).
Context `{!Repr A, !heapG Σ}.
Import Order Order.POrderTheory Order.TotalTheory.

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

End Insertion.

Instance repr_prod `{Repr A, Repr B} : Repr (A * B) :=
  λ p, (repr p.1, repr p.2)%V.
Arguments repr_prod {_ _ _ _} !_.
