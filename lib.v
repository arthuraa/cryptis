From stdpp Require Import base countable gmap.
From iris.heap_lang Require Import lang notation proofmode.
From iris.algebra Require Import namespace_map gmap gset auth.
From iris.base_logic Require Import gen_heap.
From iris.base_logic.lib Require Import auth.
From iris_string_ident Require Import ltac2_string_ident.

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

Lemma Some_included_ucmra {A : ucmraT} (a b : A) : Some a ≼ Some b ↔ a ≼ b.
Proof.
split; last exact: Some_included_2.
case=> [mc]; rewrite option_equivE.
case: mc => [c|] //= e; [by exists c|exists ε].
by rewrite ucmra_unit_right_id.
Qed.

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

End ListLemmas.

Instance repr_prod `{Repr A, Repr B} : Repr (A * B) :=
  λ p, (repr p.1, repr p.2)%V.
Arguments repr_prod {_ _ _ _} !_.
