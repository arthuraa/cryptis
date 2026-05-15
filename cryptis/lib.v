From stdpp Require Import base countable gmap.
From iris.heap_lang Require Import lang notation proofmode.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.algebra Require Import gmap gset auth reservation_map.
From iris.base_logic Require Import gen_heap invariants.
From mathcomp Require ssrbool order path.
From deriving Require deriving.
From cryptis Require Export mathcomp_compat.
From cryptis.lib Require Export repr list list_match.

Lemma eq_op_bool_decide
  {T : eqtype.Equality.type}
  {_ : EqDecision (eqtype.Equality.sort T)}
  (x y : eqtype.Equality.sort T) :
  bool_decide (x = y) = (eqtype.eq_op x y).
Proof.
apply/(ssrbool.sameP).
- exact: bool_decide_reflect.
- exact: eqtype.eqP.
Qed.

Section Escrow.

Context `{invGS Σ}.

Definition escrow (N' : namespace) (P Q : iProp Σ) : iProp Σ :=
  □ (∀ E, ⌜↑N' ⊆ E⌝ -∗ P ={E}=∗ ▷ Q).

Global Typeclasses Opaque escrow.

Global Instance escrow_persistent N' P Q :
  Persistent (escrow N' P Q).
Proof. by rewrite /escrow; apply _. Qed.

Definition switch (P Q : iProp Σ) : iProp Σ := ∃ R,
  □ (P ∗ □ R -∗ Q) ∗
  □ (P ==∗ □ R).

Lemma escrowI (N' : namespace) E (P Q : iProp Σ) :
  ▷ Q -∗
  switch P Q ={E}=∗
  escrow N' P Q.
Proof.
rewrite /escrow.
iIntros "HQ (%R & #contra & #mint)".
iMod (inv_alloc N' _ (Q ∨ □ R) with "[HQ]") as "#inv".
  by eauto.
iIntros "!> %E' !> %sub HP".
iInv "inv" as "[H|#H]".
- iMod ("mint" with "HP") as "#HR".
  iModIntro.
  iSplitL "HR"; first by eauto.
  by iFrame.
- iModIntro.
  iSplitR; first by eauto.
  iModIntro. iModIntro.
  by iApply "contra"; eauto.
Qed.

Lemma escrowE N' P Q E :
  ↑N' ⊆ E →
  escrow N' P Q -∗
  P ={E}=∗
  ▷ Q.
Proof. by rewrite /escrow; iIntros "%sub #e HP"; iApply "e". Qed.

End Escrow.

Lemma or_sep1 {Σ} (P Q R : iProp Σ) : P ∨ Q -∗ P ∨ R -∗ P ∨ Q ∗ R.
Proof. by iIntros "[?|?] [?|?]"; eauto; iRight; iFrame. Qed.

Lemma or_sep2 {Σ} (P Q R : iProp Σ) :
  Persistent P →
  P ∨ Q ∗ R ⊢ (P ∨ Q) ∗ (P ∨ R).
Proof.
iIntros "% [#?|[Q R]]"; first by iSplitR; eauto.
by iSplitL "Q"; eauto.
Qed.

Lemma lc_fupd_elim_later_pers `{invGS Σ} E (P : iProp Σ) :
  £ 1 -∗ □ ▷ P ={E}=∗ □ P.
Proof.
rewrite bi.later_intuitionistically_2.
exact: lc_fupd_elim_later.
Qed.

Lemma fupd_or' `{!invGS Σ} (A B C : iProp Σ) E :
  (B ={E}=∗ C) -∗ A ∨ B ={E}=∗ A ∨ C.
Proof.
iIntros "BC [HA | HB]"; eauto.
by iMod ("BC" with "HB"); eauto.
Qed.

Definition namespace_map_data {A : cmra} (N : namespace) (a : A) :=
  reservation_map_data (positives_flatten (namespace_car N)) a.

Lemma namespace_map_alloc_update {A : cmra} E (N : namespace) (a : A) :
  ↑N ⊆ E →
  ✓ a →
  reservation_map_token E ~~> namespace_map_data N a.
Proof.
move=> sub valid; apply: reservation_map_alloc => //.
assert (H : positives_flatten (namespace_car N) ∈ (↑N : coPset)).
{ rewrite namespaces.nclose_unseal. apply elem_coPset_suffixes.
  exists 1%positive. by rewrite left_id_L. }
set_solver.
Qed.

Lemma reservation_map_disj {A : cmra} E x (a : A) :
  ✓ (reservation_map_token E ⋅ reservation_map_data x a) →
  x ∉ E.
Proof.
rewrite reservation_map_valid_eq /= right_id_L left_id_L.
by case=> _ /(_ x); rewrite lookup_singleton_eq; case.
Qed.

Lemma namespace_map_disj {A : cmra} E (N : namespace) (a : A) :
  ↑N ⊆ E →
  ✓ (reservation_map_token E ⋅ namespace_map_data N a) →
  False.
Proof.
move=> sub /reservation_map_disj.
assert (H : positives_flatten (namespace_car N) ∈ (↑N : coPset)).
{ rewrite namespaces.nclose_unseal. apply elem_coPset_suffixes.
  exists 1%positive. by rewrite left_id_L. }
set_solver.
Qed.

#[global]
Instance namespace_map_data_core_id {A : cmra} N (a : A) :
  CoreId a → CoreId (namespace_map_data N a).
Proof. apply _. Qed.

(* TODO: Move to Iris? *)
#[global]
Instance dom_ne {T : ofe} :
  NonExpansive (dom : gmap loc T -> gset loc).
Proof. by move=> ??? e ?; rewrite !elem_of_dom e. Qed.

Lemma meta_meta_token `{Countable L, !gen_heapGS L V Σ, Countable A} l (x : A) N E :
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
assert (contra : encode x ∈ X).
  by apply/elem_of_singleton.
by destruct (is_fresh X); rewrite -e.
Qed.

Lemma big_sepS_union_pers (PROP : bi) `{!BiAffine PROP, !EqDecision A, !Countable A}
  (Φ : A → PROP) (X Y : gset A) :
  (∀ x, Persistent (Φ x)) →
  ([∗ set] x ∈ (X ∪ Y), Φ x) ⊣⊢ ([∗ set] x ∈ X, Φ x) ∧ ([∗ set] x ∈ Y, Φ x).
Proof.
move=> ?; rewrite !big_sepS_forall.
apply: (anti_symm _).
- by iIntros "H"; iSplit; iIntros "%a %a_in"; iApply "H"; iPureIntro; set_solver.
- iIntros "H %x %x_XY".
  case/elem_of_union: x_XY => [x_X|x_Y].
  + by iDestruct "H" as "[H _]"; iApply "H".
  + by iDestruct "H" as "[_ H]"; iApply "H".
Qed.

Lemma big_sepS_union_list_pers
  (PROP : bi) `{!BiAffine PROP, !EqDecision A, !Countable A}
  (Φ : A → PROP) (X : list (gset A)) :
  (∀ x, Persistent (Φ x)) →
  ([∗ set] x ∈ ⋃ X, Φ x) ⊣⊢ ([∗ list] X ∈ X, [∗ set] x ∈ X, Φ x).
Proof.
move=> ?; rewrite big_sepS_forall big_sepL_forall.
apply: (anti_symm _).
- iIntros "H %k %Y %X_k"; rewrite big_sepS_forall; iIntros "%x %x_Y".
  iApply "H"; iPureIntro.
  apply/elem_of_union_list; exists Y; split => //.
  by rewrite list_elem_of_lookup; eauto.
- iIntros "H %x %x_X".
  case/elem_of_union_list: x_X => Y [Y_X x_Y].
  case/list_elem_of_lookup: Y_X => k X_k.
  iSpecialize ("H" $! _ _ X_k).
  by rewrite big_sepS_forall; iApply "H".
Qed.

Lemma and_proper_L (PROP : bi) (P : Prop) (φ ψ : PROP) :
  (P → φ ⊣⊢ ψ) →
  ⌜P⌝ ∧ φ ⊣⊢ ⌜P⌝ ∧ ψ.
Proof.
by move=> φ_ψ; apply: (anti_symm _); iIntros "[% ?]"; rewrite φ_ψ; eauto.
Qed.

#[global]
Instance if_persistent (Σ : gFunctors) (b : bool) (φ ψ : iProp Σ) :
  Persistent φ →
  Persistent ψ →
  Persistent (if b then φ else ψ).
Proof. by case: b. Qed.
(* /TODO *)

Lemma dom_singleton_eq `{EqDecision K, Countable K} {T} (m : gmap K T) x :
  dom m = {[x]} →
  ∃ y, m = {[x := y]}.
Proof.
move=> e.
have {}e: ∀ x' : K, x' ∈ dom m ↔ x' ∈ ({[x]} : gset K) by rewrite e.
have: x ∈ ({[x]} : gset K) by rewrite elem_of_singleton.
rewrite -e elem_of_dom; case=> y m_x; exists y.
apply: map_eq=> x'; case: (decide (x' = x))=> [ {x'}->|ne].
  by rewrite lookup_singleton_eq.
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
Proof. exact: option_Forall2E. Qed.

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

Fixpoint pure_expr e : bool :=
  match e with
  | Val v => pure_val v
  | Var _ => true
  | Rec f x e => pure_expr e
  | App e1 e2 => pure_expr e1 && pure_expr e2
  | UnOp _ e => pure_expr e
  | BinOp _ e1 e2 => pure_expr e1 && pure_expr e2
  | If e1 e2 e3 => pure_expr e1 && pure_expr e2 && pure_expr e3
  | Pair e1 e2 => pure_expr e1 && pure_expr e2
  | Fst e | Snd e => pure_expr e
  | InjL e | InjR e => pure_expr e
  | Case e1 e2 e3 => pure_expr e1 && pure_expr e2 && pure_expr e3
  | Fork _ => false
  | AllocN _ _ => false
  | Free _ => false
  | Load _ => false
  | Store _ _ => false
  | CmpXchg _ _ _ => false
  | Xchg _ _ => false
  | FAA _ _ => false
  | NewProph => false
  | Resolve _ _ _ => false
  end
with pure_val v : bool :=
  match v with
  | LitV _ => true
  | RecV _ _ e => pure_expr e
  | PairV v1 v2 => pure_val v1 && pure_val v2
  | InjLV v | InjRV v => pure_val v
  end.

Definition pure_item (a : ectx_item) : bool :=
  match a with
  | AppLCtx v => pure_val v
  | AppRCtx e => pure_expr e
  | UnOpCtx _ => true
  | BinOpLCtx _ v => pure_val v
  | BinOpRCtx _ e => pure_expr e
  | IfCtx e1 e2 => pure_expr e1 && pure_expr e2
  | PairLCtx v => pure_val v
  | PairRCtx e => pure_expr e
  | FstCtx | SndCtx | InjLCtx | InjRCtx => true
  | CaseCtx e1 e2 => pure_expr e1 && pure_expr e2
  | _ => false
  end.

Definition pure_ctx K : bool := forallb pure_item K.

Section WithSsrBool.

#[warnings="-ambiguous-paths"]
Import ssreflect ssrbool.

Lemma pure_expr_fill_item a (e : expr) : pure_expr (fill_item a e) = pure_item a && pure_expr e.
Proof.
case: a=> //=; try by move=> *; rewrite andbC.
- by move=> ??; rewrite [RHS]andbC andbA.
- by move=> ??; rewrite [RHS]andbC andbA.
Qed.

Lemma pure_expr_fill K (e : expr) : pure_expr (fill K e) = pure_ctx K && pure_expr e.
Proof.
elim: K=> //= a K IH in e *.
by rewrite IH pure_expr_fill_item andbA [pure_ctx K && _]andbC.
Qed.

Lemma subst_pure x v e : pure_val v → pure_expr e → pure_expr (subst x v e).
Proof.
move=> /is_trueP pure_v /is_trueP pure_e; apply/is_trueP.
elim: e pure_e => //=.
- by move=> ? _; case: decide.
- by move=> ??? IH pure_e; case: decide => // _; eauto.
- by move=> e1 IH1 e2 IH2 /andP [??]; rewrite IH1 // ?IH2.
- by move=> _ e1 IH1 e2 IH2 /andP [??]; rewrite IH1 // ?IH2.
- by move=> e1 IH1 e2 IH2 e3 IH3 /andP [/andP[??] ?]; rewrite IH1 // ?IH2 // ?IH3.
- by move=> e1 IH1 e2 IH2 /andP [??]; rewrite IH1 // ?IH2.
- by move=> e1 IH1 e2 IH2 e3 IH3 /andP [/andP[??] ?]; rewrite IH1 // ?IH2 // ?IH3.
Qed.

Lemma subst'_pure x v e : pure_val v → pure_expr e → pure_expr (subst' x v e).
Proof. case: x => //= x. exact: subst_pure. Qed.

Lemma pure_exprP (e1 : expr) σ1 κs e2 σ2 efs :
  prim_step e1 σ1 κs e2 σ2 efs →
  pure_expr e1 →
  pure_expr e2.
Proof.
move=> [K {}e1 {}e2 -> ->] Hstep; rewrite !pure_expr_fill.
case/andb_True=> /is_trueP -> //= pure_e1.
case: e1 σ1 κs e2 σ2 efs / Hstep pure_e1 => //=.
- move=> f x e1 v2 e' σ -> /= /andb_True [pure_e1 pure_e2].
  apply: subst'_pure => //.
  by apply: subst'_pure => //.
- case=> [] [] //=.
  + by case=> // [l|b] ? ? [<-].
  + by case=> // n ? ? [<-].
- move=> op v1 v2 v' σ; rewrite /bin_op_eval.
  case: (decide (op = EqOp)) => [_|be].
  + by case: decide=> // _ [<-] _; eauto.
  + case: v1 v2 => //=; case=> //= [n1|b1|l1].
    * case=> //; case=> //= n2.
      by case: op => //= in be *; case=> <-; eauto.
    * case=> //; case=> //= b2.
      by case: op => //= in be *; case=> <-; eauto.
    * by case=> // l2; case: op=> //= in be *; case: l2 => //= ? [<-]; eauto.
- by move=> ??? /andb_True [??]; eauto.
- by move=> ??? /andb_True [??]; eauto.
- by move=> ??? /andb_True [??]; eauto.
- by move=> ??? /andb_True [??]; eauto.
- by move=> ???? /is_trueP/andP [/andP[-> ->]_]; eauto.
- by move=> ???? /is_trueP/andP [/andP[-> _]->]; eauto.
Qed.

Lemma pure_expr_pure_step (e₁ : expr) σ₁ κs e₂ σ₂ efs :
  prim_step e₁ σ₁ κs e₂ σ₂ efs →
  pure_expr e₁ →
  pure_step e₁ e₂.
Proof.
move=> [K {}e₁ {}e₂ -> ->] Hstep; rewrite !pure_expr_fill.
case/andb_True=> //= pure_K pure_e₁.
apply: pure_step_ctx => //=; apply: nsteps_once_inv.
case: e₁ σ₁ κs e₂ σ₂ efs / Hstep pure_e₁ => //= *; subst; exact: pure_exec.
Qed.

End WithSsrBool.

#[global]
Instance repr_prod `{Repr A, Repr B} : Repr (A * B) :=
  λ p, (repr p.1, repr p.2)%V.
Arguments repr_prod {_ _ _ _} !_.

Fixpoint nforall {A} (n : nat) (P : list A → Prop) :=
  match n with
  | 0 => P []
  | S n => forall x : A, nforall n (λ xs, P (x :: xs))
  end.

Lemma nforallP {A} (n : nat) (P : list A -> Prop) :
  nforall n P ↔ ∀ vs, n = length vs → P vs.
Proof.
elim: n => [|n IH] /= in P *.
  split; [by move=> ? [|//]|by apply].
split.
- move=> H [|x xs] //= [e]; by move/IH: (H x); apply.
- by move=> H x; apply/IH => xs len_xs; apply: H; rewrite len_xs.
Qed.

Definition nforall_eq {A} (n : nat) (vs : list A) (P : list A -> Prop) :=
  nforall n (λ vs', vs = vs' → P vs').

Lemma nforall_eqP {A} (n : nat) (xs : list A) (P : list A -> Prop) :
  nforall_eq n xs P ↔ (n = length xs → P xs).
Proof.
rewrite /nforall_eq nforallP; split.
- by move=> H len_xs; apply: H.
- by move=> H xs' len_xs' e_xs'; rewrite e_xs' in H; apply: H.
Qed.

Arguments nforall_eq {A} /.

Lemma list_len_rect (n : nat) A (P : list A → Prop) :
  (nforall n P) →
  (∀ xs, length xs ≠ n → P xs) →
  ∀ xs, P xs.
Proof.
move=> eq_n neq_n xs.
case: (decide (n = length xs)) => [eq|neq].
- by move: xs eq; apply/nforallP.
- exact: neq_n.
Qed.

Fixpoint prod_of_list_aux_type A B n :=
  match n with
  | 0 => A
  | S n => prod_of_list_aux_type (A * B)%type B n
  end.

Fixpoint prod_of_list_aux {A B} n :
  A → list B → option (prod_of_list_aux_type A B n) :=
  match n with
  | 0 => fun x ys =>
    match ys with
    | [] => Some x
    | _  => None
    end
  | S n => fun x ys =>
    match ys with
    | [] => None
    | y :: ys => prod_of_list_aux n (x, y) ys
    end
  end.

Definition prod_of_list_type A n : Type :=
  match n with
  | 0 => unit
  | S n => prod_of_list_aux_type A A n
  end.

Fact prod_of_list_key : unit. Proof. exact: tt. Qed.

Definition prod_of_list {A} n xs : option (prod_of_list_type A n) :=
  locked_with prod_of_list_key (
    match n return list A → option (prod_of_list_type A n) with
    | 0 => fun xs => match xs with
                     | [] => Some tt
                     | _  => None
                     end
    | S n => fun xs => match xs with
                       | [] => None
                       | x :: xs => prod_of_list_aux n x xs
                       end
    end xs).

Canonical prod_of_list_unlockable A n xs :=
  [unlockable of @prod_of_list A n xs].

Lemma prod_of_list_neq {A} n (xs : list A) :
  length xs ≠ n → prod_of_list n xs = None.
Proof.
rewrite unlock; case: n xs=> [|n] [|x xs] //= ne.
have {}ne : length xs ≠ n by congruence.
suffices : ∀ B (x : B), prod_of_list_aux n x xs = None by apply.
elim: n xs {x} => [|n IH] [|y ys] //= in ne * => B x.
by rewrite IH //; congruence.
Qed.

Lemma fmap_binder_delete {A B} (f : A → B) (m : gmap string A) x :
  f <$> binder_delete x m = binder_delete x (f <$> m).
Proof. case: x => [|x] //=; by rewrite fmap_delete. Qed.

Lemma fmap_binder_insert {A B} (f : A → B) (m : gmap string A) i x :
  f <$> binder_insert i x m = binder_insert i (f x) (f <$> m).
Proof. case: i => [|i] //=; by rewrite fmap_insert. Qed.

Lemma insert_same {A} (m1 m2 : gmap string A) (i : string) (x : A) :
  (∀ j, j ≠ i → m1 !! j = m2 !! j) →
  <[i := x]>m1 = <[i := x]>m2.
Proof.
move=> e12; apply map_eq => j.
destruct (decide (j = i)) as [->|ne].
- by rewrite !lookup_insert_eq.
- by rewrite !lookup_insert_ne // e12.
Qed.

Lemma binder_insert_same {A} (m1 m2 : gmap string A) (i : binder) (x : A) :
  (∀ j : string, BNamed j ≠ i → m1 !! j = m2 !! j) →
  binder_insert i x m1 = binder_insert i x m2.
Proof.
case: i => [|i] /= e12.
- by apply: map_eq => i; apply: e12.
- by apply: insert_same => ??; apply: e12; congruence.
Qed.

Lemma binder_insert_delete {A} (m : gmap string A) (i : binder) (x : A) :
  binder_insert i x (binder_delete i m) = binder_insert i x m.
Proof. case: i => //= i; exact: insert_delete_eq. Qed.

Lemma binder_insert_delete2 {A} (m : gmap string A) (i j : binder) (x y : A) :
  binder_insert i x (binder_insert j y (binder_delete i (binder_delete j m))) =
  binder_insert i x (binder_insert j y m).
Proof.
rewrite -(binder_insert_delete m j y).
case: i j => [|i] [|j] //=.
- by rewrite insert_delete_eq.
- rewrite delete_delete !insert_delete_eq.
  destruct (decide (i = j)) as [->|i_j].
    by rewrite insert_delete_eq.
  by rewrite insert_insert_ne // insert_delete_eq insert_insert_ne //.
Qed.

Lemma binder_delete_commute {A} (m : gmap string A) i j :
  binder_delete i (binder_delete j m) =
  binder_delete j (binder_delete i m).
Proof. case: i j => [|i] [|j] //=; exact: delete_delete. Qed.

Definition nondet_nat_loop : val := rec: "loop" "n" :=
  if: nondet_bool #() then "n" else "loop" ("n" + #1).

Definition nondet_nat : val := λ: <>, nondet_nat_loop #0.

Definition nondet_int : val := λ: <>,
  let: "n" := nondet_nat #() in
  if: nondet_bool #() then "n" else - "n".

Section NonDetProofs.

Context `{!heapGS Σ}.

Implicit Types E : coPset.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.

Lemma wp_nondet_nat_loop Ψ (m : nat) :
  (∀ n : nat, Ψ #n) ⊢
  WP nondet_nat_loop #m {{ Ψ }}.
Proof.
iIntros "post"; iLöb as "IH" forall (m); wp_rec.
wp_apply nondet_bool_spec => //.
iIntros "%b _"; case: b; wp_if; first by iApply "post".
wp_pures. have -> : (m + 1)%Z = (m + 1)%nat by lia.
by iApply "IH".
Qed.

Lemma wp_nondet_nat Ψ :
  (∀ n : nat, Ψ #n) ⊢
  WP nondet_nat #() {{ Ψ }}.
Proof. by iIntros "post"; wp_lam; wp_apply (wp_nondet_nat_loop _ 0).  Qed.

Lemma wp_nondet_int Ψ :
  (∀ n : Z, Ψ #n) ⊢
  WP nondet_int #() {{ Ψ }}.
Proof.
iIntros "post"; rewrite /nondet_int; wp_pures.
wp_apply wp_nondet_nat. iIntros "%n"; wp_pures.
wp_apply nondet_bool_spec => //. iIntros "%b _".
case: b; wp_if; first by iApply "post".
by wp_pures; iApply "post".
Qed.

End NonDetProofs.
