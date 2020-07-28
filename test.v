From mathcomp Require Import ssreflect.
From iris.algebra Require Import excl auth frac agree gmap list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.program_logic Require Import lifting.
From iris.algebra Require Import gmap auth gset numbers excl agree ofe.
From iris.heap_lang Require Import notation proofmode metatheory.
From iris.heap_lang Require Import primitive_laws.
From iris.base_logic.lib Require Import invariants.
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
End cfg.
