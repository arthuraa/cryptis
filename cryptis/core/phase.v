From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta.
From cryptis.core Require Import term minted term_meta public comp_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition mint_mapUR := discrete_funUR (fun _ : nat => authUR (gsetUR term)).

Class phaseGpreS Σ := PhaseGPreS {
  phaseGpreS_hon   : inG Σ comp_mapR;
  phaseGpreS_mint  : inG Σ mint_mapUR;
  phaseGpreS_meta  : metaGS Σ;
}.

Local Existing Instance phaseGpreS_hon.
Local Existing Instance phaseGpreS_mint.
Local Existing Instance publicGpreS_meta.

Class phaseGS Σ := PhaseGS {
  phase_inG : phaseGpreS Σ;
  phase_hon_name   : gname;
  phase_mint_name  : gname;
}.

Global Existing Instance phase_inG.

Definition phaseΣ : gFunctors :=
  #[GFunctor comp_mapR;
    GFunctor mint_mapUR;
    metaΣ].

Global Instance subG_phaseGpreS Σ : subG phaseΣ Σ → phaseGpreS Σ.
Proof. solve_inG. Qed.

Section Phase.

Implicit Types γ : gname.
Implicit Types N : namespace.

Context `{!heapGS Σ, !term_metaGS Σ, !publicGS Σ, !phaseGS Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Implicit Types dq : dfrac.

Definition phase_auth_def dq n : iProp :=
  own phase_hon_name (◯CM{dq|n} ({[n := ∅]}, ∅)).
Definition phase_auth_aux : seal phase_auth_def. by eexists. Qed.
Definition phase_auth := unseal phase_auth_aux.
Lemma phase_auth_unseal : phase_auth = phase_auth_def.
Proof. exact: seal_eq. Qed.

Definition honest_def n (X : gset term) : iProp :=
  own phase_hon_name (◯CM ({[n := X]}, ∅)) ∗
  [∗ set] t ∈ X, minted t.
Definition honest_aux : seal honest_def. by eexists. Qed.
Definition honest := unseal honest_aux.
Lemma honest_unseal : honest = honest_def.
Proof. exact: seal_eq. Qed.

Definition phase_frag_def n : iProp :=
  own phase_hon_name (◯CM ({[n := ∅]}, ∅)).
Definition phase_frag_aux : seal phase_frag_def. by eexists. Qed.
Definition phase_frag := unseal phase_frag_aux.
Lemma phase_frag_unseal : phase_frag = phase_frag_def.
Proof. exact: seal_eq. Qed.

Definition secret_at_def n t : iProp :=
  honest n {[t]}.
Definition secret_at_aux : seal secret_at_def. by eexists. Qed.
Definition secret_at := unseal secret_at_aux.
Lemma secret_at_unseal : secret_at = secret_at_def.
Proof. exact: seal_eq. Qed.

Definition public_at_def n t : iProp :=
  phase_frag n ∗
  own phase_hon_name (◯CM (∅, {[(n, t)]})) ∗
  public t.
Definition public_at_aux : seal public_at_def. by eexists. Qed.
Definition public_at := unseal public_at_aux.
Lemma public_at_unseal : public_at = public_at_def.
Proof. exact: seal_eq. Qed.

Definition mint_map_singleton n t : mint_mapUR :=
  discrete_fun_singleton n (◯ {[t]}).

Notation "●Ph{ dq } n" :=
  (phase_auth dq n) (at level 20, format "●Ph{ dq }  n").
Notation "●Ph{# q } n" :=
  (phase_auth (DfracOwn q) n) (at level 20, format "●Ph{# q }  n").
Notation "●Ph□ n" := (phase_auth (DfracDiscarded) n)
  (at level 20, format "●Ph□  n").
Notation "●Ph n" := (phase_auth (DfracOwn 1) n)
  (at level 20, format "●Ph  n").
Notation "◯Ph n" :=
  (phase_frag n) (at level 20, format "◯Ph  n").

Definition minted_at_def n t : iProp :=
  ◯Ph n ∗
  own phase_mint_name (mint_map_singleton n t) ∗
  minted t.
Definition minted_at_aux : seal minted_at_def. by eexists. Qed.
Definition minted_at := unseal minted_at_aux.
Lemma minted_at_unseal : minted_at = minted_at_def.
Proof. exact: seal_eq. Qed.

Definition to_mint_map (M : nat → gset term) n : mint_mapUR :=
  λ m, if decide (m < n) then ●□ M m
       else ● M m.

Definition phase_inv : iProp :=
  ∃ n H X C M,
    own phase_hon_name (●CM{n} (H, C)) ∗
    ⌜H !! n = Some X⌝ ∗
    own phase_mint_name (to_mint_map M n) ∗
    ([∗ set] t ∈ X, secret t) ∗
    ([∗ set] p ∈ C, public p.2) ∗
    □ (∀ m, (⌜m > n → M m = ∅⌝) ∗ [∗ set] t ∈ M m, minted t).

Lemma to_mint_map_alloc M n t :
  to_mint_map M n ~~>
  to_mint_map (discrete_fun_insert n ({[t]} ∪ M n) M) n ⋅
  mint_map_singleton n t.
Proof.
apply/cmra_discrete_total_update => M' valid_M k /=; move/(_ k): valid_M.
rewrite !discrete_fun_lookup_op /to_mint_map /mint_map_singleton.
case: decide => [k_n|n_k].
{ have ?: k ≠ n by lia.
  rewrite discrete_fun_lookup_singleton_ne //.
  by rewrite discrete_fun_lookup_insert_ne // ucmra_unit_right_id. }
case: (decide (k = n)) => [->|ne].
{ rewrite discrete_fun_lookup_insert discrete_fun_lookup_singleton.
  move: (M' n); apply/cmra_discrete_total_update.
  set T := {[t]} ∪ M n.
  trans (● T ⋅ ◯ T).
  - apply: auth_update_alloc.
    apply: gset_local_update.
    set_solver.
  - rewrite {2}/T -gset_op auth_frag_op (assoc op).
    exact: cmra_update_op_l. }
by rewrite discrete_fun_lookup_insert_ne // discrete_fun_lookup_singleton_ne.
Qed.

Lemma to_mint_map_bump M n : to_mint_map M n ~~> to_mint_map M (S n).
Proof.
apply/cmra_discrete_total_update => M' valid_M k /=; move/(_ k): valid_M.
rewrite !discrete_fun_lookup_op /to_mint_map.
case: (decide (k < n)) => [k_n|n_k].
{ rewrite decide_True //; lia. }
case: decide => [k_n|?] //.
move: (M' k). apply/cmra_discrete_total_update.
exact: auth_update_auth_persist.
Qed.

Lemma phase_auth_dfrac_op dq1 dq2 n :
  ●Ph{dq1 ⋅ dq2} n ⊣⊢ ●Ph{dq1} n ∗ ●Ph{dq2} n.
Proof.
rewrite phase_auth_unseal /phase_auth_def; iSplit.
- iIntros "[??]"; iFrame; eauto.
- iIntros "[L ?]"; iFrame; eauto. by iSplitL "L".
Qed.

#[global]
Instance from_sep_phase_auth dq1 dq2 n :
  FromSep (●Ph{dq1 ⋅ dq2} n) (●Ph{dq1} n) (●Ph{dq2} n).
Proof. by rewrite /FromSep phase_auth_dfrac_op. Qed.

#[global]
Instance combine_sep_as_phase_auth dq1 dq2 n :
  CombineSepAs (●Ph{dq1} n) (●Ph{dq2} n) (●Ph{dq1 ⋅ dq2} n).
Proof. exact: from_sep_phase_auth. Qed.

#[global]
Instance into_sep_phase_auth dq1 dq2 n :
  IntoSep (●Ph{dq1 ⋅ dq2} n) (●Ph{dq1} n) (●Ph{dq2} n).
Proof. by rewrite /IntoSep phase_auth_dfrac_op. Qed.

Lemma phase_auth_discard dq n : ●Ph{dq} n ==∗ ●Ph□ n.
Proof.
rewrite phase_auth_unseal. iIntros "own".
iMod (own_update _ _ (◯CM□{n} ({[n := ∅]}, ∅)) with "own") as "#own".
  exact: comp_map_frag_discard.
by iModIntro.
Qed.

#[global]
Instance phase_auth_discarded_persistent n : Persistent (●Ph□ n).
Proof. rewrite phase_auth_unseal. apply _. Qed.

#[global]
Instance honest_persistent n X : Persistent (honest n X).
Proof. rewrite honest_unseal. apply _. Qed.

#[global]
Instance secret_at_persistent n t : Persistent (secret_at n t).
Proof. rewrite secret_at_unseal. apply _. Qed.

#[global]
Instance phase_frag_persistent n : Persistent (◯Ph n).
Proof. rewrite phase_frag_unseal. apply _. Qed.

#[global]
Instance public_at_persistent n t : Persistent (public_at n t).
Proof. rewrite public_at_unseal. apply _. Qed.

Lemma public_at_public n t : public_at n t -∗ public t.
Proof. rewrite public_at_unseal. by iIntros "(? & ? & ?)". Qed.

Lemma public_at_phase_frag n t : public_at n t -∗ ◯Ph n.
Proof. rewrite public_at_unseal. by iIntros "(? & ? & ?)". Qed.

#[global]
Instance minted_at_persistent n t : Persistent (minted_at n t).
Proof. rewrite minted_at_unseal. apply _. Qed.

Lemma minted_at_minted n t : minted_at n t -∗ minted t.
Proof. rewrite minted_at_unseal. by iIntros "(? & ? & ?)". Qed.

Lemma honest_minted n X : honest n X -∗ [∗ set] t ∈ X, minted t.
Proof. rewrite honest_unseal. by iIntros "(_ & ?)". Qed.

Lemma minted_at_phase_frag n t : minted_at n t -∗ ◯Ph n.
Proof. rewrite minted_at_unseal. by iIntros "(? & _ & _)". Qed.

Lemma phase_auth_frag_agree dq n m : ●Ph{dq} n -∗ ◯Ph m -∗ ⌜m ≤ n⌝.
Proof.
rewrite phase_auth_unseal phase_frag_unseal.
iIntros "auth frag".
iPoseProof (own_valid_2 with "auth frag") as "%val".
case/comp_map_frag_valid_wf: val => /(_ m) val_H _.
rewrite dom_singleton elem_of_singleton in val_H.
by move/(_ eq_refl) in val_H.
Qed.

Lemma phase_frag_honest n : ◯Ph n -∗ honest n ∅.
Proof.
rewrite phase_frag_unseal honest_unseal.
iIntros "phase". by iSplit => //.
Qed.

Lemma phase_auth_frag dq n : ●Ph{dq} n -∗ ◯Ph n.
Proof.
rewrite phase_auth_unseal phase_frag_unseal /phase_auth_def.
set X := ({[n := ∅]}, ∅); rewrite (_ : X = X ⋅ X); last first.
  by rewrite -pair_op singleton_op !gset_op !union_idemp_L.
by rewrite comp_map_frag_op; iIntros "(_ & ?)".
Qed.

Lemma phase_auth_agree dq1 dq2 n1 n2 :
  ●Ph{dq1} n1 -∗ ●Ph{dq2} n2 -∗ ⌜n1 = n2⌝.
Proof.
rewrite phase_auth_unseal.
iIntros "own1 own2".
iPoseProof (own_valid_2 with "own1 own2") as "%val".
by have <- := comp_map_frag_bound_agree val.
Qed.

Lemma honest_public_at n X m t :
  m ≤ n →
  honest n X -∗ public_at m t -∗ ⌜t ∉ X⌝.
Proof.
rewrite honest_unseal public_at_unseal.
iIntros "%m_n (#frag1 & _) (_ & #frag2 & _)".
iPoseProof (own_valid_2 with "frag1 frag2") as "%val".
move/comp_map_frag_valid_dis/(_ n X m t): val.
rewrite lookup_singleton elem_of_singleton => dis.
iPureIntro; exact: dis.
Qed.

Lemma honest_union n T1 T2 : honest n (T1 ∪ T2) ⊣⊢ honest n T1 ∗ honest n T2.
Proof.
rewrite honest_unseal /honest_def -gset_op -{1}[∅]ucmra_unit_right_id_L.
rewrite -singleton_op pair_op comp_map_frag_op own_op big_sepS_union_pers.
iSplit.
- iIntros "[[??][??]]". by eauto.
- iIntros "[[??][??]]". by eauto.
Qed.

Lemma secret_atI n t T : t ∈ T → honest n T -∗ secret_at n t.
Proof.
move=> ?; have -> : T = {[t]} ∪ T ∖ {[t]}.
  apply: union_difference_L; set_solver.
rewrite honest_union. iIntros "[? _]".
by rewrite secret_at_unseal.
Qed.

Definition to_mint_map_share M n : mint_mapUR :=
  λ m, if decide (m < n) then ●□ M m else ε.

Lemma to_mint_map_split M n :
  to_mint_map M n ≡ to_mint_map M n ⋅ to_mint_map_share M n.
Proof.
rewrite /to_mint_map /to_mint_map_share => m.
rewrite discrete_fun_lookup_op.
case: decide=> // _.
apply core_id_dup.
apply _.
Qed.

Local Instance to_mint_map_split_core_id M n :
  CoreId (to_mint_map_share M n).
Proof.
apply/Some_proper => m.
rewrite /to_mint_map_share; case: decide => _; apply: core_id_core.
Qed.

Definition phase_ctx : iProp :=
  inv (nroot.@"cryptis".@"phase") phase_inv.

#[global]
Instance phase_ctx_persistent : Persistent phase_ctx.
Proof. apply _. Qed.

Class HasPhaseCtx (ctx : iProp) := {
  has_phase_ctx : ctx ⊢ phase_ctx;
  has_phase_ctx_persistent : Persistent ctx;
}.

Local Existing Instance has_phase_ctx_persistent.

Context `{!HasPhaseCtx ctx}.

Lemma phase_acc_gen E n :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  ctx -∗
  ◯Ph n ={E, E ∖ ↑nroot.@"cryptis".@"phase"}=∗ ∃ H C M Y m,
    ⌜n ≤ m⌝ ∗
    own phase_hon_name (●CM{m} (H, C)) ∗
    ⌜H !! m = Some Y⌝ ∗
    own phase_mint_name (to_mint_map M m) ∗
    ▷ ([∗ set] t ∈ Y, secret t) ∗
    ▷ ([∗ set] p ∈ C, public p.2) ∗
    ▷ □ (∀ m', (⌜m' > m → M m' = ∅⌝) ∗ [∗ set] t ∈ M m', minted t) ∗
    (▷ phase_inv ={E ∖ ↑nroot.@"cryptis".@"phase",E}=∗ True).
Proof.
rewrite phase_frag_unseal.
iIntros "%sub #ctx phase".
iPoseProof (has_phase_ctx with "ctx") as "{ctx} ctx".
iMod (inv_acc with "ctx") as "[inv close]" => //.
iDestruct "inv"
  as "(%m & %H & %Y & %C & %M &
       >verI & >%H_m & >own_M & sec_X & #pub_C & mint_M)".
iPoseProof (own_valid_2 with "verI phase") as "%val_bound".
case/comp_map_auth_frag_valid_agree: (val_bound) => X [H_n _].
have val_bound_l := cmra_valid_op_l _ _ val_bound.
case/comp_map_auth_valid_dis: val_bound_l => m_upper_bound _.
iExists H, C, M, Y, m. iFrame. iModIntro. do !iSplit => //.
iPureIntro. apply: m_upper_bound. by rewrite elem_of_dom H_n.
Qed.

Lemma phase_acc E dq n X :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  ctx -∗
  honest n X -∗
  ●Ph{dq} n ={E, E ∖ ↑nroot.@"cryptis".@"phase"}=∗ ∃ H C M Y,
    ●Ph{dq} n ∗
    own phase_hon_name (●CM{n} (H, C)) ∗
    ⌜H !! n = Some Y⌝ ∗
    ⌜X ⊆ Y⌝ ∗
    own phase_mint_name (to_mint_map M n) ∗
    ▷ ([∗ set] t ∈ Y, secret t) ∗
    ▷ ([∗ set] p ∈ C, public p.2) ∗
    ▷ □ (∀ m, (⌜m > n → M m = ∅⌝) ∗ [∗ set] t ∈ M m, minted t) ∗
    (▷ phase_inv ={E ∖ ↑nroot.@"cryptis".@"phase",E}=∗ True).
Proof.
iIntros "%sub #ctx #hon phase".
iPoseProof (phase_auth_frag with "phase") as "#phase_lb".
iMod (phase_acc_gen with "ctx phase_lb")
  as "(%H & %C & %M & %Y & %m &
       %n_m & verI & %H_m & own_M & sec_X & #pub_C & mint_M)" => //.
rewrite honest_unseal phase_auth_unseal.
iPoseProof (own_valid_2 with "verI phase") as "%val_bound".
move/comp_map_auth_frag_bound_agree: val_bound => -> {m n_m} in H_m *.
iDestruct "hon" as "[hon _]".
iPoseProof (own_valid_2 with "verI hon") as "%val".
case/comp_map_auth_frag_valid_agree: val.
rewrite H_m => _ [] [<-] X_Y.
iFrame. iModIntro. eauto.
Qed.

Lemma public_atI_gen E t n :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  ctx -∗
  £ 1 -∗
  ◯Ph n -∗
  public t ={E}=∗
  ∃ m, ⌜n ≤ m⌝ ∗ public_at m t.
Proof.
iIntros "%sub #ctx cred #phase_frag #p_t".
iMod (phase_acc_gen with "ctx phase_frag")
  as "(%H & %C & %M & %X & %m & %n_m & phaseI & %H_m & own_M &
       sec_X & #pub_X & #mint_M & close)" => //.
iMod (lc_fupd_elim_later with "cred sec_X") as "sec_X".
iAssert (◇ ⌜t ∉ X⌝)%I with "[sec_X]" as "#>%t_X".
{ case: (decide (t ∈ X)) => [t_X|//].
  iClear "pub_X".
  rewrite (big_sepS_delete _ X t) //.
  iDestruct "sec_X" as "[sec_t sec_X]".
  iDestruct "sec_t" as "(_ & _ & sec_t)".
  iDestruct ("sec_t" with "p_t") as ">[]". }
iMod (own_update with "phaseI") as "[phaseI phaseI']".
{ apply: comp_map_auth_split. }
have e: (H, C) = (H, C) ⋅ ({[m := ∅]}, ∅).
  rewrite -pair_op ucmra_unit_right_id_L (_ : H ⋅ {[m := ∅]} = H) //.
  rewrite -leibniz_equiv_iff => k.
  rewrite lookup_op.
  case: (decide (k = m)) => [->|k_m].
  - by rewrite lookup_singleton H_m -Some_op ucmra_unit_right_id_L.
  - by rewrite lookup_singleton_ne // ucmra_unit_right_id_L.
rewrite [in ◯CM (H, C)]e comp_map_frag_op.
iDestruct "phaseI'" as "[_ #?]".
iMod (own_update with "phaseI") as "phaseI".
  exact: comp_map_comp_update_last H_m t_X.
iDestruct "phaseI" as "[phaseI #comp]".
iMod ("close" with "[phaseI own_M sec_X]") as "_".
{ iModIntro. iExists m, H, X, ({[(m, t)]} ∪ C), M. iFrame.
  rewrite big_sepS_union_pers big_sepS_singleton /=.
  by eauto. }
iModIntro. iExists m. iSplit => //.
rewrite public_at_unseal; do !iSplit => //.
by rewrite phase_frag_unseal.
Qed.

Lemma public_atI E t dq n :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  ctx -∗
  £ 1 -∗
  ●Ph{dq} n -∗
  public t ={E}=∗
  ●Ph{dq} n ∗
  public_at n t.
Proof.
iIntros "%sub #ctx cred phase_auth #p_t".
iPoseProof (phase_auth_frag with "phase_auth") as "#phase_frag".
iMod (public_atI_gen with "ctx cred phase_frag p_t")
  as "(%m & %n_m & #p_m_t)" => //.
iPoseProof (public_at_phase_frag with "p_m_t") as "phase_frag'".
iPoseProof (phase_auth_frag_agree with "phase_auth phase_frag'") as "%".
iFrame. by have ->: m = n by lia.
Qed.

Lemma minted_atI_gen E t n :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  ctx -∗
  ◯Ph n -∗
  minted t ={E}=∗
  ∃ m, ⌜n ≤ m⌝ ∗ minted_at m t.
Proof.
iIntros "%sub #ctx #phase_frag #m_t".
iMod (phase_acc_gen with "ctx phase_frag")
  as "(%H & %C & %M & %X & %m & %n_m & phaseI & %H_m & own_M &
       sec_X & #pub_X & #mint_M & close)" => //.
iMod (own_update with "own_M") as "own_M".
{ apply: (to_mint_map_alloc t). }
iDestruct "own_M" as "[own_M #minted]".
iMod (own_update with "phaseI") as "[phaseI phaseI']".
{ apply: comp_map_auth_split. }
have e: (H, C) = (H, C) ⋅ ({[m := ∅]}, ∅).
  rewrite -pair_op ucmra_unit_right_id_L (_ : H ⋅ {[m := ∅]} = H) //.
  rewrite -leibniz_equiv_iff => k.
  rewrite lookup_op.
  case: (decide (k = m)) => [->|k_m].
  - by rewrite lookup_singleton H_m -Some_op ucmra_unit_right_id_L.
  - by rewrite lookup_singleton_ne // ucmra_unit_right_id_L.
rewrite [in ◯CM (H, C)]e comp_map_frag_op.
iDestruct "phaseI'" as "[_ #?]".
iMod ("close" with "[phaseI own_M sec_X]") as "_".
{ iModIntro. iExists m, H, X, C, _. iFrame.
  iSplit => //.
  iSplit => //.
  iIntros "!> %m'".
  iDestruct ("mint_M" $! m') as "[%finsupp #minted']". iSplit.
  - iPureIntro. move=> m_n.
    rewrite discrete_fun_lookup_insert_ne ?finsupp //.
    lia.
  - case: (decide (m' = m)) => [->|ne].
    + rewrite discrete_fun_lookup_insert.
      rewrite big_sepS_union_pers big_sepS_singleton.
      by iSplit.
    + by rewrite discrete_fun_lookup_insert_ne. }
iFrame. iExists m.
iModIntro. rewrite minted_at_unseal. do !iSplit => //.
by rewrite phase_frag_unseal.
Qed.

Lemma minted_atI E t dq n :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  ctx -∗
  ●Ph{dq} n -∗
  minted t ={E}=∗
  ●Ph{dq} n ∗
  minted_at n t.
Proof.
iIntros "%sub #ctx phase_auth #p_t".
iPoseProof (phase_auth_frag with "phase_auth") as "#phase_frag".
iMod (minted_atI_gen with "ctx phase_frag p_t")
  as "(%m & %n_m & #p_m_t)" => //.
iPoseProof (minted_at_phase_frag with "p_m_t") as "phase_frag'".
iPoseProof (phase_auth_frag_agree with "phase_auth phase_frag'") as "%".
iFrame. by have ->: m = n by lia.
Qed.

Lemma minted_at_list E dq n :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  ctx -∗
  ●Ph{dq} n ={E}=∗
  ●Ph{dq} n ∗
  ▷ ∃ Y : gset term,
  ([∗ set] t ∈ Y, minted t) ∗
  □ (∀ m t, ⌜m < n⌝ -∗ minted_at m t -∗ ⌜t ∈ Y⌝).
Proof.
iIntros "%sub #ctx phase_auth".
iPoseProof (phase_auth_frag with "phase_auth") as "#phase_frag".
iPoseProof (phase_frag_honest with "phase_frag") as "#hon".
iMod (phase_acc with "ctx hon phase_auth")
  as "(%H & %C & %M & %X & phase_auth & phaseI & %H_n & _ & own_M &
       sec_X & #pub_X & #mint_M & close)" => //.
rewrite to_mint_map_split.
iDestruct "own_M" as "[own_M #split_M]".
iMod ("close" with "[phaseI own_M sec_X]") as "_".
{ iModIntro. iExists n, H, X, C, _. iFrame. eauto. }
iFrame. iIntros "!> !>".
iExists (⋃ ((λ m, M m) <$> seq 0 n)). iSplit.
- rewrite big_sepS_union_list_pers.
  rewrite big_sepL_fmap big_sepL_forall.
  iIntros "%k %x %kP".
  by iDestruct ("mint_M" $! x) as "[#? #?]".
- rewrite minted_at_unseal. iIntros "!> %m %t %m_n (_ & #minted & _)".
  iPoseProof (own_valid_2 with "split_M minted") as "%valid".
  iPureIntro.
  move/(_ m): valid.
  rewrite discrete_fun_lookup_op /to_mint_map_share /mint_map_singleton.
  rewrite decide_True // discrete_fun_lookup_singleton.
  case/auth_both_dfrac_valid_discrete => _.
  rewrite gset_included singleton_subseteq_l; case=> ??.
  rewrite elem_of_union_list. exists (M m).
  rewrite elem_of_list_fmap. split => //. exists m.
  split => //.
  apply/elem_of_seq. lia.
Qed.

Lemma honest_public E dq t n :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  ctx -∗
  secret_at n t -∗
  ●Ph{dq} n -∗
  public t ={E}=∗
  ▷ ▷ False.
Proof.
iIntros "%sub #ctx #sec phase_auth #p_t".
rewrite secret_at_unseal.
iMod (phase_acc with "ctx sec phase_auth")
  as "(%H & %C & %M & %X & phase_auth & phaseI & %H_n & %t_X & own_M &
       sec_X & #pub_X & #mint_M & close)" => //.
have ? : t ∈ X by set_solver.
iAssert (▷ ▷ False)%I with "[sec_X]" as "#contra".
{ iClear "pub_X". rewrite (big_sepS_delete _ X) //.
  iDestruct "sec_X" as "[sec_X _]".
  iModIntro. by iApply (secret_not_public with "sec_X"). }
iMod ("close" with "[phaseI own_M sec_X]") as "_".
{ iModIntro. iExists n, H, X, C, M. iFrame. by eauto. }
by eauto.
Qed.

Lemma honest_unionE E n X Y :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  X ## Y →
  ctx -∗
  honest n (X ∪ Y) -∗
  ●Ph n ={E}=∗
  honest (S n) X ∗ ●Ph (S n) ∗ ▷ [∗ set] t ∈ Y, secret t.
Proof.
iIntros "%sub %X_Y #ctx #hon phase_auth".
iMod (phase_acc with "ctx hon phase_auth")
  as "(%H & %C & %M & %Z & phase_auth & phaseI & %H_n & %X_Z & own_M &
       sec_X & #pub_X & #mint_M & close)" => //.
rewrite phase_auth_unseal.
iPoseProof (own_valid with "phaseI") as "%val".
case/comp_map_auth_valid_dis: val => [bounds_H [] bounds_C dis].
iMod (own_update_2 with "phaseI phase_auth") as "phaseI".
  apply: (@comp_map_honest_update _ _ _ _ X).
  move=> m t t_C. have m_n: m ≤ n by apply: (bounds_C (m, t)).
  have := dis _ _ _ _ H_n t_C m_n.
  set_solver.
iDestruct "phaseI" as "[phaseI phase_auth]".
have eZ: Z = (X ∪ Y) ∪ (Z ∖ (X ∪ Y)) by apply: union_difference_L; set_solver.
rewrite eZ !big_sepS_union //; last set_solver.
iDestruct "sec_X" as "((sec_X & sec_Y) & _)".
iMod (own_update with "own_M") as "own_M".
{ exact: to_mint_map_bump. }
iMod ("close" with "[sec_X phaseI own_M]") as "_".
{ iModIntro. iExists _, _, _, _, _. iFrame.
  rewrite lookup_insert.
  do !iSplit => //. iDestruct "mint_M" as "#mint_M".
  iIntros "!> %m". iSpecialize ("mint_M" $! m).
  iDestruct "mint_M" as "[%finsupp mint_M]".
  iSplit => //.
  iPureIntro. move=> ?; apply: finsupp. lia. }
iModIntro. iFrame.
set P := ({[S n := _]}, _).
rewrite (_ : P = ({[S n := ∅]}, ∅) ⋅ P); last first.
  by rewrite -pair_op singleton_op !ucmra_unit_left_id_L.
rewrite comp_map_frag_op.
iDestruct "phase_auth" as "[phase_auth #honest]". iFrame.
rewrite honest_unseal. iSplit => //.
iDestruct "hon" as "[_ mint_XY]".
rewrite big_sepS_union //. by iDestruct "mint_XY" as "[? _]".
Qed.

Lemma honest_delete E t n X :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  t ∈ X →
  ctx -∗
  honest n X -∗
  ●Ph n ={E}=∗
  honest (S n) (X ∖ {[t]}) ∗ ●Ph (S n) ∗ ▷ secret t.
Proof.
iIntros "%sub %t_X #ctx #hon phase".
rewrite {1}[X](union_difference_singleton_L t) // [_ ∪ _]comm_L.
iMod (honest_unionE with "ctx hon phase") as "(hon' & phase & ?)" => //.
  set_solver.
rewrite big_sepS_singleton.
by iFrame.
Qed.

Lemma compromise_honest E n X :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  ctx -∗
  honest n X -∗
  ●Ph n ={E}=∗
  honest (S n) ∅ ∗ ●Ph (S n) ∗ ▷ |==> [∗ set] t ∈ X, public t.
Proof.
iIntros "%sub #ctx hon phase".
rewrite {1}(_ : X = ∅ ∪ X); last set_solver.
iMod (honest_unionE with "ctx hon phase") as "(hon & phase & sec)" => //.
iFrame. iModIntro. iModIntro. iApply big_sepS_bupd.
iApply (big_sepS_mono with "sec").
by iIntros "%t % [? _]".
Qed.

Lemma freeze_honest E n X :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  ctx -∗
  honest n X -∗
  ●Ph n ={E}=∗
  honest (S n) ∅ ∗ ●Ph (S n) ∗ ▷ |==> [∗ set] t ∈ X, □ (public t ↔ ▷ False).
Proof.
iIntros "%sub #ctx hon phase".
rewrite {1}(_ : X = ∅ ∪ X); last set_solver.
iMod (honest_unionE with "ctx hon phase") as "(hon & phase & sec)" => //.
iFrame. iModIntro. iModIntro.
iApply big_sepS_bupd. iApply (big_sepS_mono with "sec").
by iIntros "%t % (_ & ? & _)".
Qed.

Lemma honest_unionI Y E n X :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  X ## Y →
  ctx -∗
  £ 1 -∗
  honest n X -∗
  ●Ph n -∗
  ([∗ set] t ∈ Y, minted t) -∗
  ▷ ([∗ set] t ∈ Y, secret t) ={E}=∗
  honest (S n) (X ∪ Y) ∗ ●Ph (S n).
Proof.
iIntros "%sub %dis #ctx cred #hon phase #s_Y sec".
iMod (phase_acc with "ctx hon phase")
  as "(%H & %C & %M & %Z & phase & phaseI & %H_n & %X_Z & own_M &
       sec_X & #pub_X & #mint_M & close)" => //.
rewrite honest_unseal.
iCombine "pub_X sec sec_X" as "I".
iMod (lc_fupd_elim_later with "cred I") as "I".
iDestruct "I" as "{pub_X} (#pub_X & sec & sec_X)".
iDestruct "hon" as "(#hon & #min)".
iPoseProof (own_valid with "phaseI") as "%val".
case/comp_map_auth_valid_dis: val => [bounds_H [] bounds_C dis'].
iAssert (▷ ⌜∀ m t, (m, t) ∈ C → t ∉ Y⌝)%I as "#>%dis''".
{ iIntros "%m %t %t_C %t_Y".
  rewrite (big_sepS_delete _ C) // !(big_sepS_delete _ Y) //.
  iDestruct "pub_X" as "[pub_X _]".
  iDestruct "sec" as "[sec_t _]".
  by iApply (secret_not_public with "sec_t"). }
rewrite phase_auth_unseal.
iMod (own_update_2 with "phaseI phase") as "phaseI".
  apply: (@comp_map_honest_update _ _ _ _ (X ∪ Y)).
  move=> m t t_C. have m_n: m ≤ n by apply: (bounds_C (m, t)).
  have := dis' _ _ _ _ H_n t_C m_n.
  have := dis'' _ _ t_C.
  set_solver.
iMod (own_update with "own_M") as "own_M".
{ exact: to_mint_map_bump. }
iDestruct "phaseI" as "[phaseI phase]".
iMod ("close" with "[sec_X sec phaseI own_M]") as "_".
{ iModIntro. iExists _, _, (X ∪ Y), _, _.
  rewrite big_sepS_union //. iFrame. rewrite lookup_insert.
  do !iSplit=> //.
  - by iApply (big_sepS_subseteq with "sec_X").
  - iIntros "!> %m".
    iDestruct ("mint_M" $! m) as "[%finsupp #minted]".
    iSplit => //.
    iPureIntro. move=> ?; apply: finsupp. lia. }
set P := ({[S n := _]}, _).
rewrite (_ : P = ({[S n := ∅]}, ∅) ⋅ P); last first.
  by rewrite -pair_op singleton_op !ucmra_unit_left_id_L.
rewrite comp_map_frag_op.
iDestruct "phase" as "[? #?]". iFrame.
iModIntro. iSplit => //. rewrite big_sepS_union //.
by eauto.
Qed.

Lemma honest_insert t E n X :
  ↑nroot.@"cryptis".@"phase" ⊆ E →
  t ∉ X →
  ctx -∗
  £ 1 -∗
  honest n X -∗
  ●Ph n -∗
  minted t -∗
  ▷ secret t ={E}=∗
  honest (S n) (X ∪ {[t]}) ∗ ●Ph (S n).
Proof.
iIntros "%sub %t_X #ctx cred #hon phase #s_t sec".
iApply (honest_unionI with "[//] [cred] [hon] [phase]") => //.
- set_solver.
- by rewrite big_sepS_singleton.
- by rewrite big_sepS_singleton.
Qed.

End Phase.

Arguments phase_inv {Σ _ _ _}.
Arguments phase_ctx {Σ _ _ _}.
Arguments unknown_alloc {Σ _}.
Arguments known_alloc {Σ _ γ} x.

Notation "●Ph{ dq } n" :=
  (phase_auth dq n) (at level 20, format "●Ph{ dq }  n").
Notation "●Ph{# q } n" :=
  (phase_auth (DfracOwn q) n) (at level 20, format "●Ph{# q }  n").
Notation "●Ph□ n" := (phase_auth (DfracDiscarded) n)
  (at level 20, format "●Ph□  n").
Notation "●Ph n" := (phase_auth (DfracOwn 1) n)
  (at level 20, format "●Ph  n").
Notation "◯Ph n" :=
  (phase_frag n) (at level 20, format "◯Ph  n").

Lemma phaseGS_alloc `{!heapGS Σ, !term_metaGS Σ, !publicGS Σ} E :
  phaseGpreS Σ →
  ⊢ |={E}=> ∃ (H : phaseGS Σ),
             phase_ctx ∗
             honest 0 ∅ ∗
             ●Ph 0.
Proof.
move=> ?; iStartProof.
iMod (own_alloc (●CM{0} ({[0 := ∅]}, ∅) ⋅ ◯CM{0} ({[0 := ∅]}, ∅)))
    as (γ_hon) "[phaseI phase]".
  apply/view_both_valid => ? /=; do !split.
  - by move=> ?; rewrite dom_singleton elem_of_singleton => ->.
  - move=> ?; set_solver.
  - move=> *; set_solver.
  - by [].
  - by [].
iMod (own_alloc (to_mint_map (ε : discrete_fun _) 0)) as (γ_mint) "mint_auth".
{ move=> m.
  by rewrite /to_mint_map /= discrete_fun_lookup_empty auth_auth_valid. }
rewrite comp_map_frag_split.
iDestruct "phase" as "[phase_auth #phase]".
pose (H := PhaseGS _ γ_hon γ_mint).
iExists H.
rewrite honest_unseal /honest_def big_sepS_empty.
rewrite phase_auth_unseal /phase_auth_def. iFrame.
iSplitL; last by iFrame; eauto.
iApply inv_alloc.
iModIntro. iExists 0, {[0 := ∅]}, ∅, ∅, ε. iFrame.
rewrite !big_sepS_empty. do !iSplit => //.
iIntros "!> %m". by rewrite discrete_fun_lookup_empty big_opS_empty.
Qed.
