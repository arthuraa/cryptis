From mathcomp Require Import ssreflect.
From iris.algebra Require Import excl auth frac agree gmap list.
From iris.proofmode Require Import environments tactics.
From iris.program_logic Require Import language.
From iris.program_logic Require Import lifting.
From iris.algebra Require Import gmap auth gset numbers excl agree ofe.
From iris.heap_lang Require Import notation proofmode metatheory.
From iris.heap_lang Require Import primitive_laws.
From iris.base_logic.lib Require Import invariants.
From iris_string_ident Require Import ltac2_string_ident.
Import uPred.

Definition specN := nroot .@ "spec".

(** The CMRA for the heap of the specification. *)
Definition tpoolUR : ucmraT := gmapUR nat (exclR exprO).
Definition cfgUR := prodUR tpoolUR (gen_heapUR loc (optionO valO)).

Fixpoint to_tpool_go (i : nat) (tp : list expr) : tpoolUR :=
  match tp with
  | [] => ∅
  | e :: tp => <[i:=Excl e]>(to_tpool_go (S i) tp)
  end.
Definition to_tpool : list expr → tpoolUR := to_tpool_go 0.

(** The CMRA for the thread pool. *)
Class cfgSG Σ := CFGSG { cfg_inG :> inG Σ (authR cfgUR); cfg_name : gname }.

Section definitionsS.

Context `{cfgSG Σ, invG Σ}.

Definition heapS_mapsto (l : loc) (q : Qp) (v: valO) : iProp Σ :=
  own cfg_name (◯ (ε, {[ l := (q, to_agree (Some v : leibnizO (option val))) ]})).

Definition tpool_mapsto (j : nat) (e: expr) : iProp Σ :=
  own cfg_name (◯ ({[ j := Excl e ]}, ∅)).

Definition spec_inv (ρ : cfg heap_lang) : iProp Σ :=
  (∃ tp (σ : state),
      own cfg_name (● (to_tpool tp, to_gen_heap (heap σ)))
      ∗ ⌜rtc erased_step ρ (tp,σ)⌝)%I.

Definition spec_ctx : iProp Σ :=
  (∃ ρ, inv specN (spec_inv ρ))%I.

Global Instance heapS_mapsto_timeless l q v : Timeless (heapS_mapsto l q v).
Proof. apply _. Qed.
Global Instance spec_ctx_persistent : Persistent spec_ctx.
Proof. apply _. Qed.
End definitionsS.
Typeclasses Opaque heapS_mapsto tpool_mapsto.

Notation "l ↦ₛ{ q } v" := (heapS_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : bi_scope.
Notation "l ↦ₛ v" := (heapS_mapsto l 1 v) (at level 20) : bi_scope.
Notation "j ⤇ e" := (tpool_mapsto j e) (at level 20) : bi_scope.

Ltac iAsimpl :=
  repeat match goal with
  | |- context [ (_ ⤇ ?e)%I ] => progress (
    let e' := fresh in evar (e':expr);
    assert (e = e') as ->; [simpl; unfold e'; reflexivity|];
    unfold e'; clear e')
  | |- context [ WP ?e @ _ {{ _ }}%I ] => progress (
    let e' := fresh in evar (e':expr);
    assert (e = e') as ->; [simpl; unfold e'; reflexivity|];
    unfold e'; clear e')
  end.

Section conversions.
  Context `{cfgSG Σ}.

  (** Conversion to tpools and back *)
  Lemma to_tpool_valid es : ✓ to_tpool es.
  Proof.
    rewrite /to_tpool. move: 0.
    induction es as [|e es]=> n //. by apply insert_valid.
  Qed.

  Lemma tpool_lookup tp j : to_tpool tp !! j = Excl <$> tp !! j.
  Proof.
    cut (∀ i, to_tpool_go i tp !! (i + j) = Excl <$> tp !! j).
    { intros help. apply (help 0). }
    revert j. induction tp as [|e tp IH]=> //= -[|j] i /=.
    - by rewrite Nat.add_0_r lookup_insert.
    - by rewrite -Nat.add_succ_comm lookup_insert_ne; last lia.
  Qed.
  Lemma tpool_lookup_Some tp j e : to_tpool tp !! j = Excl' e → tp !! j = Some e.
  Proof. rewrite tpool_lookup fmap_Some. naive_solver. Qed.
  Hint Resolve tpool_lookup_Some : core.

  Lemma to_tpool_insert tp j e :
    j < length tp →
    to_tpool (<[j:=e]> tp) = <[j:=Excl e]> (to_tpool tp).
  Proof.
    intros. apply: map_eq=> i. destruct (decide (i = j)) as [->|].
    - by rewrite tpool_lookup lookup_insert list_lookup_insert.
    - rewrite tpool_lookup lookup_insert_ne // list_lookup_insert_ne //.
      by rewrite tpool_lookup.
  Qed.
  Lemma to_tpool_insert' tp j e :
    is_Some (to_tpool tp !! j) →
    to_tpool (<[j:=e]> tp) = <[j:=Excl e]> (to_tpool tp).
  Proof.
    rewrite tpool_lookup fmap_is_Some lookup_lt_is_Some. apply to_tpool_insert.
  Qed.

  Lemma to_tpool_snoc tp e :
    to_tpool (tp ++ [e]) = <[length tp:=Excl e]>(to_tpool tp).
  Proof.
    intros. apply: map_eq=> i.
    destruct (lt_eq_lt_dec i (length tp)) as [[?| ->]|?].
    - rewrite lookup_insert_ne; last lia. by rewrite !tpool_lookup lookup_app_l.
    - by rewrite lookup_insert tpool_lookup lookup_app_r // Nat.sub_diag.
    - rewrite lookup_insert_ne; last lia.
      rewrite !tpool_lookup ?lookup_ge_None_2 ?app_length //=;
         change (ofe_car exprO) with expr; lia.
  Qed.

  Lemma tpool_singleton_included tp j e :
    {[j := Excl e]} ≼ to_tpool tp → tp !! j = Some e.
  Proof.
    move=> /singleton_included_l [ex [/leibniz_equiv_iff]].
    rewrite tpool_lookup fmap_Some=> [[e' [-> ->]] /Excl_included ?]. by f_equal.
  Qed.
  Lemma tpool_singleton_included' tp j e :
    {[j := Excl e]} ≼ to_tpool tp → to_tpool tp !! j = Excl' e.
  Proof. rewrite tpool_lookup. by move=> /tpool_singleton_included=> ->. Qed.

End conversions.

Section cfg.
  Context `{heapG Σ, cfgSG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types l : loc.
  Implicit Types v : val.
  Implicit Types a b : Z.

  Local Hint Resolve tpool_lookup : core.
  Local Hint Resolve tpool_lookup_Some : core.
  Local Hint Resolve to_tpool_insert : core.
  Local Hint Resolve to_tpool_insert' : core.
  Local Hint Resolve tpool_singleton_included : core.

  Lemma mapstoS_agree l q1 q2 v1 v2 : l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite /heapS_mapsto -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> -[_] /=. rewrite singleton_op singleton_valid -pair_op.
    by intros [_ ?%agree_op_invL']; congruence.
  Qed.
  Lemma mapstoS_combine l q1 q2 v1 v2 :
    l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ l ↦ₛ{q1 + q2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (mapstoS_agree with "Hl1 Hl2") as %->.
    rewrite /heapS_mapsto. iCombine "Hl1 Hl2" as "Hl". eauto with iFrame.
  Qed.
  Lemma mapstoS_valid l q v : l ↦ₛ{q} v -∗ ✓ q.
  Proof.
    rewrite /heapS_mapsto own_valid !discrete_valid -auth_frag_valid.
    by apply pure_mono=> -[_] /singleton_valid [??].
  Qed.
  Lemma mapstoS_valid_2 l q1 q2 v1 v2 : l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "H1 H2". iDestruct (mapstoS_combine with "H1 H2") as "[? ->]".
    by iApply (mapstoS_valid l _ v2).
  Qed.

  Lemma step_insert K tp j e σ κ e' σ' efs :
    tp !! j = Some (fill K e) → head_step e σ κ e' σ' efs →
    erased_step (tp, σ) (<[j:=fill K e']> tp ++ efs, σ').
  Proof.
    intros. rewrite -(take_drop_middle tp j (fill K e)) //.
    rewrite insert_app_r_alt take_length_le ?Nat.sub_diag /=;
      eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite -(assoc_L (++)) /=. eexists.
    eapply step_atomic; eauto. by apply: Ectx_step'.
  Qed.

  Lemma step_insert_no_fork K tp j e σ κ e' σ' :
    tp !! j = Some (fill K e) → head_step e σ κ e' σ' [] →
    erased_step (tp, σ) (<[j:=fill K e']> tp, σ').
  Proof. rewrite -(right_id_L [] (++) (<[_:=_]>_)). by apply step_insert. Qed.

  Lemma nsteps_inv_r {A} n (R : A → A → Prop) x y :
    relations.nsteps R (S n) x y → ∃ z, relations.nsteps R n x z ∧ R z y.
  Proof.
    revert x y; induction n; intros x y.
    - inversion 1; subst.
      match goal with H : relations.nsteps _ 0 _ _ |- _ => inversion H end; subst.
      eexists; repeat econstructor; eauto.
    - inversion 1; subst.
      edestruct IHn as [z [? ?]]; eauto.
      exists z; split; eauto using relations.nsteps_l.
  Qed.

  Lemma step_pure' E j K e e' (P : Prop) n :
    P →
    PureExec P n e e' →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K e ={E}=∗ j ⤇ fill K e'.
  Proof.
    iIntros (HP Hex ?) "[#Hinv Hj]". iDestruct "Hinv" as (ρ) "Hspec".
    rewrite /spec_ctx /tpool_mapsto.
    iInv specN as (tp σ) ">[Hown Hrtc]" "Hclose".
    iDestruct "Hrtc" as %Hrtc.
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[Htpj%tpool_singleton_included' _]%prod_included ?]%auth_both_valid.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K e'))). }
    iFrame "Hj". iApply "Hclose". iNext. iExists (<[j:=fill K e']> tp), σ.
    rewrite to_tpool_insert'; last eauto.
    iFrame. iPureIntro.
    apply rtc_nsteps in Hrtc; destruct Hrtc as [m Hrtc].
    specialize (Hex HP). apply (nsteps_rtc (m + n)).
    eapply nsteps_trans; eauto.
    revert e e' Htpj Hex.
    induction n => e e' Htpj Hex.
    - inversion Hex; subst.
      rewrite list_insert_id; eauto. econstructor.
    - apply nsteps_inv_r in Hex.
      destruct Hex as [z [Hex1 Hex2]].
      specialize (IHn _ _ Htpj Hex1).
      eapply nsteps_r; eauto.
      replace (<[j:=fill K e']> tp) with
          (<[j:=fill K e']> (<[j:=fill K z]> tp)); last first.
      { clear. revert tp; induction j; intros tp.
        - destruct tp; trivial.
        - destruct tp; simpl; auto. by rewrite IHj. }
      destruct Hex2 as [Hexs Hexd].
      specialize (Hexs σ). destruct Hexs as [e'' [σ' [efs Hexs]]].
      specialize (Hexd σ [] e'' σ' efs Hexs); destruct Hexd as [? [? [? ?]]];
        subst.
      inversion Hexs; simpl in *; subst.
      rewrite -!fill_app.
      eapply step_insert_no_fork; eauto.
      { apply list_lookup_insert. apply lookup_lt_is_Some; eauto. }
  Qed.


  Lemma do_step_pure E j K e e' `{!PureExec True 1 e e'}:
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K e ={E}=∗ j ⤇ fill K e'.
  Proof. by eapply step_pure'; last eauto. Qed.

  Lemma step_alloc E j K v:
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Alloc v) ={E}=∗ ∃ l, j ⤇ fill K #l ∗ l ↦ₛ v.
  Proof.
    iIntros (?) "[#Hinv Hj]". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx /tpool_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    destruct (exist_fresh (dom (gset loc) (heap σ))) as [l Hl%not_elem_of_dom].
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K #l))). }
    iMod (own_update with "Hown") as "[Hown Hl]".
    { eapply auth_update_alloc, prod_local_update_2,
        (alloc_singleton_local_update _ l (1%Qp,to_agree (Some v : leibnizO _)));
        last done.
      by apply lookup_to_gen_heap_None. }
    iExists l. rewrite /heapS_mapsto. iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K #l]> tp), (state_init_heap l 1 v σ).
    rewrite {1}state_init_heap_singleton /=.
    rewrite to_gen_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto.
    eapply AllocNS; first lia.
    move=> i ??; rewrite (_ : i = 0) /= ?loc_add_0 //.
    lia.
  Qed.

  Lemma step_load E j K l q v:
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Load #l) ∗ l ↦ₛ{q} v
    ={E}=∗ j ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[? ?%gen_heap_singleton_included]%prod_included ?]%auth_both_valid.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (of_val v)))). }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (of_val v)]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_store E j K l v' v:
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Store #l v) ∗ l ↦ₛ v'
    ={E}=∗ j ⤇ fill K #() ∗ l ↦ₛ v.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included _]%auth_both_valid.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[_ Hl%gen_heap_singleton_included]%prod_included _]%auth_both_valid.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K #()))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2, singleton_local_update,
        (exclusive_local_update _ (1%Qp, to_agree (Some v : leibnizO _))); last done.
      by rewrite /to_gen_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K #()]> tp), (state_upd_heap <[l:=Some v]> σ).
    rewrite to_gen_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto.
    econstructor; eauto.
  Qed.

  Lemma step_cas_fail E j K l q v' v1 v2:
    nclose specN ⊆ E → v' ≠ v1 →
    vals_compare_safe v' v1 ->
    spec_ctx ∗ j ⤇ fill K (CmpXchg #l v1 v2) ∗ l ↦ₛ{q} v'
    ={E}=∗ j ⤇ fill K (v', #false)%V ∗ l ↦ₛ{q} v'.
  Proof.
    iIntros (???) "(#Hinv & Hj & Hl)". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[_ ?%gen_heap_singleton_included]%prod_included _]%auth_both_valid.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (v', #false)%V))). }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (v', #false)%V]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto.
    change σ with (if false then state_upd_heap <[l:=Some v2]> σ else σ) at 3.
    econstructor; eauto.
    by apply/eq_sym/bool_decide_eq_false.
  Qed.

  Lemma step_cas_suc E j K l v1 v1' v2:
    nclose specN ⊆ E → v1 = v1' →
    vals_compare_safe v1 v1' →
    spec_ctx ∗ j ⤇ fill K (CmpXchg #l v1 v2) ∗ l ↦ₛ v1'
    ={E}=∗ j ⤇ fill K (v1', #true)%V ∗ l ↦ₛ v2.
  Proof.
    iIntros (???) "(#Hinv & Hj & Hl)"; subst. iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included _]%auth_both_valid.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[_ Hl%gen_heap_singleton_included]%prod_included _]%auth_both_valid.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (v1', #true)%V))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2, singleton_local_update,
        (exclusive_local_update _ (1%Qp, to_agree (Some v2 : leibnizO _))); last done.
      by rewrite /to_gen_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (v1', #true)%V]> tp), (state_upd_heap <[l:=Some v2]> σ).
    rewrite -[state_upd_heap <[l:=Some v2]> σ]/(if true then state_upd_heap <[l:=Some v2]> σ else σ).
    rewrite to_gen_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto.
    econstructor; eauto.
    by apply/eq_sym/bool_decide_eq_true.
  Qed.

  Lemma step_rec E j K f x v1 v2 `{!AsRecV v1 f x erec}:
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (App v1 v2)
    ={E}=∗ j ⤇ fill K (subst' x v2 (subst' f v1 erec)).
  Proof. move=> ?; by apply: do_step_pure. Qed.

  Lemma step_lam E j K x e1 v2 :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (App (λ: x, e1)%V v2)
    ={E}=∗ j ⤇ fill K (subst' x v2 e1).
  Proof.
    move=> ?. iIntros "H".
    iPoseProof (step_rec with "H") as "H"; eauto.
  Qed.

  Lemma step_fst E j K v1 v2 :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Fst (v1, v2)%V) ={E}=∗ j ⤇ fill K v1.
  Proof. by intros; apply: do_step_pure. Qed.

  Lemma step_snd E j K v1 v2 :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Snd (v1, v2)%V) ={E}=∗ j ⤇ fill K v2.
  Proof. by intros; apply: do_step_pure. Qed.

  Lemma step_case_inl E j K v0 e1 e2 :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Case (InjLV v0)%V e1 e2)
      ={E}=∗ j ⤇ fill K (e1 v0).
  Proof. by intros; apply: do_step_pure. Qed.

  Lemma step_case_inr E j K v0 e1 e2 :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Case (InjRV v0)%V e1 e2)
      ={E}=∗ j ⤇ fill K (e2 v0).
  Proof. by intros; apply: do_step_pure. Qed.

  Lemma step_if_false E j K e1 e2 :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (If #false e1 e2) ={E}=∗ j ⤇ fill K e2.
  Proof. by intros; apply: do_step_pure. Qed.

  Lemma step_if_true E j K e1 e2 :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (If #true e1 e2) ={E}=∗ j ⤇ fill K e1.
  Proof. by intros; apply: do_step_pure. Qed.

  Lemma step_nat_binop E j K op v1 v2 v :
    nclose specN ⊆ E →
    bin_op_eval op v1 v2 = Some v →
    spec_ctx ∗ j ⤇ fill K (BinOp op v1 v2)
      ={E}=∗ j ⤇ fill K v.
  Proof. by intros; apply: step_pure'. Qed.

  Lemma step_fork E j K e :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Fork e) ={E}=∗ ∃ j', j ⤇ fill K #() ∗ j' ⤇ e.
  Proof.
    iIntros (?) "[#Hinv Hj]". iDestruct "Hinv" as (ρ) "Hinv".
    rewrite /spec_ctx /tpool_mapsto.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid.
    assert (j < length tp) by eauto using lookup_lt_Some.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K #()))). }
    iMod (own_update with "Hown") as "[Hown Hfork]".
    { eapply auth_update_alloc, prod_local_update_1,
        (alloc_singleton_local_update _ (length tp) (Excl e)); last done.
      rewrite lookup_insert_ne ?tpool_lookup; last lia.
      by rewrite lookup_ge_None_2. }
    iExists (length tp). iFrame "Hj Hfork". iApply "Hclose". iNext.
    iExists (<[j:=fill K #()]> tp ++ [e]), σ.
    rewrite to_tpool_snoc insert_length to_tpool_insert //. iFrame. iPureIntro.
    eapply rtc_r, step_insert; eauto. econstructor; eauto.
  Qed.

Definition swp_def e Φ : iProp Σ :=
  (∀ E j K,
    ⌜nclose specN ⊆ E⌝ →
    spec_ctx ∗ j ⤇ fill K e
    ={E}=∗ ∃ v, j ⤇ fill K v ∗ Φ v).

Definition swp_aux e Φ : seal (swp_def e Φ). Proof. by eexists. Qed.
Definition swp e Φ := (swp_aux e Φ).(unseal).
Definition swp_eq e Φ : swp e Φ = swp_def e Φ := (swp_aux e Φ).(seal_eq).

Lemma swp_bind K e Φ :
  swp e (λ v, swp (fill K (Val v)) Φ)
  -∗ swp (fill K e) Φ.
Proof.
rewrite !swp_eq; iIntros "He" (E j K') "%HE [#Hspec Hj]"; rewrite -fill_app.
iCombine "Hspec Hj" as "Hj".
iMod ("He" $! E j (K ++ K') HE with "Hj") as "Hj"; eauto.
iDestruct "Hj" as (v) "[Hj Hv]"; rewrite fill_app swp_eq.
iCombine "Hspec Hj" as "Hj".
by iApply "Hv".
Qed.

Lemma tac_swp_bind `{!heapG Σ} K Δ Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (swp e (λ v, swp (f (Val v)) Φ)) →
  envs_entails Δ (swp (fill K e) Φ).
Proof. rewrite envs_entails_eq=> -> ->. by apply: swp_bind. Qed.

Lemma swp_value Φ e v :
  IntoVal e v → Φ v -∗ swp e Φ.
Proof.
rewrite swp_eq; move=> <-; iIntros "Hv" (E j K) "%HE [#Hspec ?]".
iModIntro; iExists v; iFrame.
Qed.

Lemma tac_swp_expr_eval Δ Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (swp e' Φ) → envs_entails Δ (swp e Φ).
Proof. by intros ->. Qed.

Lemma tac_swp_value Δ Φ v :
  envs_entails Δ (Φ v) →
  envs_entails Δ (swp v Φ).
Proof. by move=> ?; rewrite -swp_value. Qed.

Lemma swp_alloc v : ⊢ swp (ref v) (λ v', ∃ l, ⌜v' = #l⌝ ∗ l ↦ₛ v)%I.
Proof.
rewrite swp_eq; iIntros (E j K) "%HE Hj".
iMod (step_alloc with "Hj") as (l) "[Hj Hl]"; eauto.
by iModIntro; iExists #l; iFrame; iExists l; iFrame.
Qed.

Lemma swp_pure (P : Prop) n e1 e2 Φ :
  PureExec P n e1 e2 →
  P →
  swp e2 Φ -∗
  swp e1 Φ.
Proof.
rewrite !swp_eq; move=> HP Hstep; iIntros "He2" (E j K) "%HE [#Hspec Hj]".
iCombine "Hspec Hj" as "Hj".
iMod (step_pure' with "Hj") as "Hj"; eauto.
iCombine "Hspec Hj" as "Hj".
by iApply "He2".
Qed.

Lemma tac_swp_pure Δ K e1 e2 (P : Prop) n Φ :
  PureExec P n e1 e2 →
  P →
  envs_entails Δ (swp (fill K e2) Φ) →
  envs_entails Δ (swp (fill K e1) Φ).
Proof.
move=> Hstep HP He2; by rewrite -swp_pure.
Qed.

Lemma swp_rec Φ f x v1 v2 `{!AsRecV v1 f x erec}:
  swp (subst' x v2 (subst' f v1 erec)) Φ
  -∗ swp (App v1 v2) Φ.
Proof. apply (swp_pure True 1); eauto; apply _. Qed.

End cfg.

Ltac swp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_swp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "swp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (swp ?e ?Q) =>
    reshape_expr e ltac:(fun K e' => unify e' efoc; swp_bind_core K)
    || fail "swp_bind: cannot find" efoc "in" e
  | _ => fail "swp_bind: not an 'swp'"
  end.

Tactic Notation "swp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (swp ?e ?Q) =>
    eapply tac_swp_expr_eval;
      [let x := fresh in intros x; t; unfold x; reflexivity|]
  | _ => fail "swp_expr_eval: not an 'swp'"
  end.

Ltac swp_finish :=
  swp_expr_eval simpl;
  try first [eapply tac_swp_value].

Tactic Notation "swp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (swp ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_swp_pure _ K e');
      [iSolveTC                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *)
      |swp_finish                      (* new goal *)
      ])
    || fail "swp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "swp_pure: not an 'swp'"
  end.

Ltac swp_rec :=
  let H := fresh in
  assert (H := AsRecV_recv);
  swp_pure (App _ _);
  clear H.

Ltac swp_pures :=
  repeat (swp_pure _; []).



(*
(* HACK: move somewhere else *)
Ltac auto_equiv :=
  (* Deal with "pointwise_relation" *)
  repeat lazymatch goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  end;
  (* Normalize away equalities. *)
  repeat match goal with
  | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _) in H
  | H : _ ≡ _ |-  _ => apply leibniz_equiv in H
  | _ => progress simplify_eq
  end;
  (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
  try (f_equiv; fast_done || auto_equiv).

Ltac solve_proper_alt :=
  repeat intro; (simpl + idtac);
  by repeat match goal with H : _ ≡{_}≡ _|- _ => rewrite H end.

Ltac solve_proper ::= (repeat intros ?; simpl; auto_equiv).

Definition termN : namespace := nroot .@ "term".

Notation D := (prodO valO valO -n> iPropO Σ).
Implicit Types τi : D.
Implicit Types Δ : gmapO string D.
Implicit Types interp : gmapO string D -n> D.
Implicit Types ee : prodO exprO exprO.

Definition interp_expr (τi : gmapO string D -n> D) Δ ee : iProp Σ :=
  ∀ j K,
    j ⤇ fill K (ee.2) →
    WP ee.1 {{ v, ∃ v', j ⤇ fill K (of_val v') ∗ τi Δ (v, v') }}.
Global Instance interp_expr_ne n :
  Proper (dist n ==> dist n ==> (=) ==> dist n) interp_expr.
Proof. unfold interp_expr; solve_proper. Qed.

Program Definition ctx_lookup (x : string) : gmapO string D -n> D :=
  λne Δ, from_option id (cconst True)%I (Δ !! x).
Solve Obligations with solve_proper.

Program Definition interp_unit : gmapO string D -n> D :=
  λne Δ ww, (⌜ww.1 = #()⌝ ∧ ⌜ww.2 = #()⌝)%I.
Solve Obligations with solve_proper_alt.
Program Definition interp_nat : gmapO string D -n> D :=
  λne Δ ww, (∃ n : nat, ⌜ww.1 = #n⌝ ∧ ⌜ww.2 = #n⌝)%I.
Solve Obligations with solve_proper.

Program Definition interp_bool : gmapO string D -n> D :=
  λne Δ ww, (∃ b : bool, ⌜ww.1 = #b⌝ ∧ ⌜ww.2 = #b⌝)%I.
Solve Obligations with solve_proper.

Program Definition interp_prod interp1 interp2 : gmapO string D -n> D :=
  λne Δ ww, (∃ vv1 vv2, ⌜ww = (PairV (vv1.1) (vv2.1), PairV (vv1.2) (vv2.2))⌝ ∧
                        interp1 Δ vv1 ∧ interp2 Δ vv2)%I.
Solve Obligations with solve_proper.

Program Definition interp_sum interp1 interp2 : gmapO string D -n> D :=
  λne Δ ww, ((∃ vv, ⌜ww = (InjLV (vv.1), InjLV (vv.2))⌝ ∧ interp1 Δ vv) ∨
             (∃ vv, ⌜ww = (InjRV (vv.1), InjRV (vv.2))⌝ ∧ interp2 Δ vv))%I.
Solve Obligations with solve_proper.

Program Definition interp_arrow interp1 interp2 : gmapO string D -n> D :=
  λne Δ ww,
  (□ ∀ vv, interp1 Δ vv →
           interp_expr
             interp2 Δ (App (of_val (ww.1)) (of_val (vv.1)),
                        App (of_val (ww.2)) (of_val (vv.2))))%I.
Solve Obligations with solve_proper.

Program Definition interp_ref_inv (ll : loc * loc) : D -n> iPropO Σ :=
  λne τi, (∃ vv, ll.1 ↦ vv.1 ∗ ll.2 ↦ₛ vv.2 ∗ τi vv)%I.
Solve Obligations with solve_proper.

Program Definition interp_ref interp : gmapO string D -n> D := 
  λne Δ ww, (∃ ll : loc * loc, ⌜ww = (#ll.1, #ll.2)⌝ ∧
            inv (termN .@ ll) (interp_ref_inv ll (interp Δ)))%I.
Solve Obligations with solve_proper.

Program Definition interp_lo_term : D := λne vv,
  (∃ t1 t2, ⌜vv.1 = val_of_term t1⌝ ∗
            ⌜vv.2 = val_of_term t2⌝ ∗
            lo_term' t1 t2)%I.
Solve Obligations with solve_proper.

Class env_Persistent Δ :=
  ctx_persistentP : ∀ α τi, Δ !! α = Some τi → ∀ vv, Persistent (τi vv).
Global Instance ctx_persistent_empty : env_Persistent ∅.
Proof. by constructor. Qed.
Global Instance ctx_persistent_insert α τi Δ :
  (∀ vv, Persistent (τi vv)) → env_Persistent Δ → env_Persistent (<[α:=τi]>Δ).
Proof.
move=> τiP ΔP β τi'.
case: (decide (α = β))=> [<-{β}|ne].
  by rewrite lookup_insert; case=> {τi'} <-.
rewrite lookup_insert_ne //; exact: ΔP.
Qed.

Global Instance ctx_persistent_lookup Δ α vv :
  env_Persistent Δ → Persistent (ctx_lookup α Δ vv).
Proof.
move=> ΔP; rewrite /ctx_lookup /=.
case e: (Δ !! α)=> [τi|] //=; last by apply _.
by apply: ΔP.
Qed.

Global Instance interp_env_base_persistent Δ Γ vs :
  env_Persistent Δ → TCForall Persistent (zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs).
Proof.
  intros HΔ. revert vs.
  induction Γ => vs; simpl; destruct vs; constructor; apply _.
Qed.
Global Instance interp_env_persistent Γ Δ vvs :
  env_Persistent Δ → Persistent (⟦ Γ ⟧* Δ vvs) := _.

Lemma interp_weaken Δ1 Π Δ2 τ :
  ⟦ τ.[upn (length Δ1) (ren (+ length Π))] ⟧ (Δ1 ++ Π ++ Δ2)
                                             ≡ ⟦ τ ⟧ (Δ1 ++ Δ2).
Proof.
  revert Δ1 Π Δ2. induction τ=> Δ1 Π Δ2; simpl; auto.
  - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
  - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
  - unfold interp_expr.
    intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
  - apply fixpoint_proper=> τi ww /=.
    properness; auto. apply (IHτ (_ :: _)).
  - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
    { by rewrite !lookup_app_l. }
    (* FIXME: Ideally we wouldn't have to do this kinf of surgery. *)
    change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
    rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia.
  - unfold interp_expr.
    intros ww; simpl; properness; auto. by apply (IHτ (_ :: _)).
  - intros ww; simpl; properness; auto. by apply IHτ.
Qed.

Lemma interp_subst_up Δ1 Δ2 τ τ' :
  ⟦ τ ⟧ (Δ1 ++ interp τ' Δ2 :: Δ2)
        ≡ ⟦ τ.[upn (length Δ1) (τ' .: ids)] ⟧ (Δ1 ++ Δ2).
Proof.
  revert Δ1 Δ2; induction τ=> Δ1 Δ2; simpl; auto.
  - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
  - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
  - unfold interp_expr.
    intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
  - apply fixpoint_proper=> τi ww /=.
    properness; auto. apply (IHτ (_ :: _)).
  - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
    { by rewrite !lookup_app_l. }
    (* FIXME: Ideally we wouldn't have to do this kinf of surgery. *)
    change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
    rewrite !lookup_app_r; [|lia ..].
    case EQ: (x - length Δ1) => [|n]; simpl.
    { symmetry. asimpl. apply (interp_weaken [] Δ1 Δ2 τ'). }
    change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
    rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia.
  - unfold interp_expr.
    intros ww; simpl; properness; auto. apply (IHτ (_ :: _)).
  - intros ww; simpl; properness; auto. by apply IHτ.
Qed.

Lemma interp_subst Δ2 τ τ' v : ⟦ τ ⟧ (⟦ τ' ⟧ Δ2 :: Δ2) v ≡ ⟦ τ.[τ'/] ⟧ Δ2 v.
Proof. apply (interp_subst_up []). Qed.

Lemma interp_env_length Δ Γ vvs : ⟦ Γ ⟧* Δ vvs ⊢ ⌜length Γ = length vvs⌝.
Proof. by iIntros "[% ?]". Qed.

Lemma interp_env_Some_l Δ Γ vvs x τ :
  Γ !! x = Some τ → ⟦ Γ ⟧* Δ vvs ⊢ ∃ vv, ⌜vvs !! x = Some vv⌝ ∧ ⟦ τ ⟧ Δ vv.
Proof.
  iIntros (?) "[Hlen HΓ]"; iDestruct "Hlen" as %Hlen.
  destruct (lookup_lt_is_Some_2 vvs x) as [v Hv].
  { by rewrite -Hlen; apply lookup_lt_Some with τ. }
  iExists v; iSplit. done. iApply (big_sepL_elem_of with "HΓ").
  apply elem_of_list_lookup_2 with x.
  rewrite lookup_zip_with; by simplify_option_eq.
Qed.

Lemma interp_env_nil Δ : ⊢ ⟦ [] ⟧* Δ [].
Proof. iSplit; simpl; auto. Qed.
Lemma interp_env_cons Δ Γ vvs τ vv :
  ⟦ τ :: Γ ⟧* Δ (vv :: vvs) ⊣⊢ ⟦ τ ⟧ Δ vv ∗ ⟦ Γ ⟧* Δ vvs.
Proof.
  rewrite /interp_env /= (assoc _ (⟦ _ ⟧ _ _)) -(comm _ ⌜(_ = _)⌝%I) -assoc.
    by apply sep_proper; [apply pure_proper; lia|].
Qed.

Lemma interp_env_ren Δ (Γ : list type) vvs τi :
  ⟦ subst (ren (+1)) <$> Γ ⟧* (τi :: Δ) vvs ⊣⊢ ⟦ Γ ⟧* Δ vvs.
Proof.
  apply sep_proper; [apply pure_proper; by rewrite fmap_length|].
  revert Δ vvs τi; induction Γ=> Δ [|v vs] τi; csimpl; auto.
  apply sep_proper; auto. apply (interp_weaken [] [τi] Δ).
Qed.

Lemma interp_ref_pointsto_neq E Δ τ l w (l1 l2 l3 l4 : loc) :
  ↑logN.@(l1, l2) ⊆ E →
  l2 ≠ l4 →
  l ↦ᵢ w -∗ interp (Tref τ) Δ (LocV l1, LocV l2) -∗
    |={E ∖ ↑logN.@(l3, l4)}=> l ↦ᵢ w ∗ ⌜l ≠ l1⌝.
Proof.
  intros Hnin Hneq.
  destruct (decide (l = l1)); subst; last auto.
  iIntros "Hl1"; simpl; iDestruct 1 as ((l5, l6)) "[% Hl2]"; simplify_eq.
  iInv (logN.@(l5, l6)) as "Hi" "Hcl"; simpl.
  iDestruct "Hi" as ((v1, v2))  "(Hl3 & Hl2' & ?)".
  iMod "Hl3".
    by iDestruct (@mapsto_valid_2 with "Hl1 Hl3") as %?.
Qed.

Lemma interp_ref_pointsto_neq' E Δ τ l w (l1 l2 l3 l4 : loc) :
  ↑logN.@(l1, l2) ⊆ E →
  l1 ≠ l3 →
  l ↦ₛ w -∗ interp (Tref τ) Δ (LocV l1, LocV l2) -∗
    |={E ∖ ↑logN.@(l3, l4)}=> l ↦ₛ w ∗ ⌜l ≠ l2⌝.
Proof.
  intros Hnin Hneq.
  destruct (decide (l = l2)); subst; last auto.
  iIntros "Hl1"; simpl; iDestruct 1 as ((l5, l6)) "[% Hl2]"; simplify_eq.
  iInv (logN.@(l5, l6)) as "Hi" "Hcl"; simpl.
  iDestruct "Hi" as ((v1, v2)) "(Hl3 & >Hl2' & ?)".
    by iDestruct (mapstoS_valid_2 with "Hl1 Hl2'") as %[].
Qed.

Lemma interp_ref_open' Δ τ l l' :
  env_Persistent Δ → EqType τ →
  ⟦ Tref τ ⟧ Δ (LocV l, LocV l') -∗
             |={⊤, ⊤ ∖ ↑logN.@(l, l')}=>
∃ w w', ▷ l ↦ᵢ w ∗ ▷ l' ↦ₛ w' ∗ ▷ ⟦ τ ⟧ Δ (w, w') ∗
          ▷ (∀ z z' u u' v v',
                l ↦ᵢ z -∗ l' ↦ₛ z' -∗ ⟦ τ ⟧ Δ (u, u') -∗ ⟦ τ ⟧ Δ (v, v') -∗
                  |={⊤ ∖ ↑logN.@(l, l')}=> l ↦ᵢ z ∗
                                             l' ↦ₛ z' ∗ ⌜v = u ↔ v' = u'⌝)
          ∗ (▷ (∃ vv : val * val, l ↦ᵢ vv.1 ∗ l' ↦ₛ vv.2 ∗ ⟦ τ ⟧ Δ vv)
             ={⊤ ∖ ↑logN.@(l, l'), ⊤}=∗ True).
Proof.
  iIntros (HΔ Heqt); simpl.
  iDestruct 1 as ((l1, l1')) "[% H1]"; simplify_eq.
  iInv (logN.@(l1, l1')) as "Hi" "$"; simpl.
  iDestruct "Hi" as ((v1, v2))  "(Hl1 & Hl1' & Hrl)"; simpl in *.
  destruct Heqt; simpl in *.
  - iModIntro; iExists _, _; iFrame.
    iNext. iIntros (??????) "? ?". iIntros ([??] [??]); subst.
      by iModIntro; iFrame.
  - iModIntro; iExists _, _; iFrame.
    iNext. iIntros (??????) "? ?".
    iDestruct 1 as (?) "[% %]". iDestruct 1 as (?) "[% %]".
    simplify_eq. by iModIntro; iFrame.
  - iModIntro; iExists _, _; iFrame.
    iNext. iIntros (??????) "? ?".
    iDestruct 1 as (?) "[% %]". iDestruct 1 as (?) "[% %]".
    simplify_eq. by iModIntro; iFrame.
  - iModIntro; iExists _, _; iFrame; iFrame "#". iNext.
    iIntros (z z' u u' v v') "Hl1 Hl1' Huu". iDestruct 1 as ((l2, l2')) "[% #Hl2]";
                                               simplify_eq; simpl in *.
    iDestruct "Huu" as ((l3, l3')) "[% #Hl3]";
      simplify_eq; simpl in *.
    destruct (decide ((l1, l1') = (l2, l2'))); simplify_eq.
    + destruct (decide ((l2, l2') = (l3, l3'))); simplify_eq; first by iFrame.
      destruct (decide (l2 = l3)); destruct (decide (l2' = l3')); subst.
      * iMod (interp_ref_pointsto_neq with "Hl1 []")
          as "[Hl1 %]"; simpl; eauto.
          by iFrame.
      * iMod (interp_ref_pointsto_neq with "Hl1 []")
          as "[Hl1 %]"; simpl; eauto.
        { by iExists (_, _); iFrame "#". }
          by iFrame.
      * iMod (interp_ref_pointsto_neq' with "Hl1' []")
          as "[Hl1' %]";
          simpl; eauto.
        { by iExists (_, _); iFrame "#". }
          by iFrame.
      * iFrame; iModIntro; iPureIntro; split; by inversion 1.
    + destruct (decide ((l1, l1') = (l3, l3'))); simplify_eq.
      * destruct (decide (l2 = l3)); destruct (decide (l2' = l3')); subst.
        -- iMod (interp_ref_pointsto_neq with "Hl1 []")
            as "[Hl1 %]"; simpl; eauto.
             by iFrame.
        -- iMod (interp_ref_pointsto_neq with "Hl1 []")
            as "[Hl1 %]"; simpl; eauto.
           { iExists (_, _); iSplit; first eauto. iFrame "#". }
             by iFrame.
        -- iMod (interp_ref_pointsto_neq' with "Hl1' []")
            as "[Hl1' %]";
             simpl; eauto.
           { iExists (_, _); iSplit; first eauto. iFrame "#". }
             by iFrame.
        -- iFrame; iModIntro; iPureIntro; split; by inversion 1.
      * destruct (decide ((l2, l2') = (l3, l3'))); simplify_eq.
        -- destruct (decide (l1 = l3)); destruct (decide (l1' = l3')); subst.
           ++ iMod (interp_ref_pointsto_neq with "Hl1 []")
               as "[Hl1 %]"; simpl; eauto.
                by iFrame.
           ++ iMod (interp_ref_pointsto_neq with "Hl1 []")
               as "[Hl1 %]"; simpl; eauto.
              { by iExists (_, _); iFrame "#". }
                by iFrame.
           ++ iMod (interp_ref_pointsto_neq' with "Hl1' []")
               as "[Hl1' %]";
                simpl; eauto.
              { by iExists (_, _); iFrame "#". }
                by iFrame.
           ++ iFrame; iModIntro; iPureIntro; split; by inversion 1.
        -- iFrame.
           { destruct (decide (l2 = l3)); destruct (decide (l2' = l3'));
               simplify_eq; auto.
             + iInv (logN.@(l3, l2')) as "Hib1" "Hcl1".
               iInv (logN.@(l3, l3')) as "Hib2" "Hcl2".
               iDestruct "Hib1" as ((v11, v12)) "(Hlx1' & Hlx2 & Hr1)".
               iDestruct "Hib2" as ((v11', v12')) "(Hl1'' & Hl2' & Hr2)".
               simpl.
               iMod "Hlx1'"; iMod "Hl1''".
                 by iDestruct (@mapsto_valid_2 with "Hlx1' Hl1''") as %?.
             + iInv (logN.@(l2, l3')) as "Hib1" "Hcl1".
               iInv (logN.@(l3, l3')) as "Hib2" "Hcl2".
               iDestruct "Hib1" as ((v11, v12)) "(>Hl1 & >Hl2' & Hr1)".
               iDestruct "Hib2" as ((v11', v12')) "(>Hl1' & >Hl2'' & Hr2) /=".
                 by iDestruct (mapstoS_valid_2 with "Hl2' Hl2''") as %[].
             + iModIntro; iPureIntro; split; intros; simplify_eq. }
Qed.
End logrel.

Typeclasses Opaque interp_env.
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr (interp τ)).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
*)
