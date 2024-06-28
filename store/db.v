From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh alist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition db_stateUR : ucmra :=
  authUR (gmapUR term (exclR termO)).

Variant operation :=
| Update of term & term
| Create of term & term.

Canonical operationO := leibnizO operation.

Definition db_historyUR : ucmra :=
  authUR (max_prefix_listUR operationO).

Class dbGS Σ := DbGS {
  dbGS_state : inG Σ db_stateUR;
  dbGS_history : inG Σ db_historyUR;
}.

Local Existing Instance dbGS_state.
Local Existing Instance dbGS_history.

Definition dbΣ :=
  #[GFunctor db_stateUR;
    GFunctor db_historyUR].

Global Instance subG_dbGS Σ : subG dbΣ Σ → dbGS Σ.
Proof. solve_inG. Qed.

Module DB.

Section DB.

Implicit Types o : operationO.
Implicit Types os : list operationO.
Implicit Types db : gmap term term.
Implicit Types γ : gname.
Implicit Types n : nat.
Implicit Types b : bool.

Definition op_app db o :=
  match o with
  | Update t1 t2 => <[t1 := t2]>db
  | Create t1 t2 =>
      match db !! t1 with
      | Some _ => db
      | None => <[t1 := t2]>db
      end
  end.

Definition to_db os : gmap term term :=
  foldl op_app ∅ os.

Context `{!metaGS Σ, !dbGS Σ}.

Definition hist_auth γ os : iProp Σ :=
  nown γ (nroot.@"hist")
         (● to_max_prefix_list os ⋅ ◯ to_max_prefix_list os).

Definition hist_frag γ os : iProp Σ :=
  nown γ (nroot.@"hist")
         (◯ to_max_prefix_list os).

Local Instance persistent_hist_frag γ os : Persistent (hist_frag γ os).
Proof. apply _. Qed.

Lemma hist_auth_frag γ os :
  hist_auth γ os -∗
  hist_frag γ os.
Proof. by iIntros "[_ Hown]". Qed.

Lemma hist_frag_agree γ os1 os2 :
  length os1 = length os2 →
  hist_frag γ os1 -∗
  hist_frag γ os2 -∗
  ⌜os2 = os1⌝.
Proof.
move=> lengthE.
iIntros "#hist1 #hist2".
iPoseProof (nown_valid_2 with "hist1 hist2") as "%valid".
rewrite auth_frag_op_valid to_max_prefix_list_op_valid_L in valid.
iPureIntro.
case: valid => - [[|o os] osE].
- by rewrite app_nil_r in osE.
- rewrite osE app_length /= in lengthE; lia.
- by rewrite app_nil_r in osE.
- rewrite osE app_length /= in lengthE; lia.
Qed.

Lemma hist_frag_prefix_of os1 os2 γ :
  os1 `prefix_of` os2 →
  hist_frag γ os2 -∗
  hist_frag γ os1.
Proof.
iIntros "%os1_os2 #hist_frag". rewrite /hist_frag.
iApply nown_mono; last by eauto.
apply: auth_frag_mono. exact/to_max_prefix_list_included_L.
Qed.

Lemma hist_update γ os o :
  hist_auth γ os ==∗
  hist_auth γ (os ++ [o]) ∗
  hist_frag γ (os ++ [o]).
Proof.
iIntros "auth".
iMod (nown_update with "auth") as "auth".
{ apply: auth_update.
  apply: (max_prefix_list_local_update os (os ++ [o])).
  by exists [o]. }
iDestruct "auth" as "[auth #frag]".
iModIntro. iSplit => //. by iSplitL.
Qed.

Definition state_auth γ b db : iProp Σ :=
  if b then
    nown γ (nroot.@"state") (● (Excl <$> db) : db_stateUR)
  else True%I.

Definition mapsto γ b t1 t2 : iProp Σ :=
  if b then
    nown γ (nroot.@"state") (◯ {[t1 := Excl t2]})
  else True%I.

Lemma state_auth_mapsto γ b db t1 t2 :
  state_auth γ b db -∗
  mapsto γ b t1 t2 -∗
  ⌜b → db !! t1 = Some t2⌝.
Proof.
iIntros "Hauth Hfrag".
case: b=> //. iIntros "_".
iPoseProof (nown_valid_2 with "Hauth Hfrag") as "%valid".
rewrite auth_both_valid_discrete in valid.
case: valid => incl valid.
rewrite singleton_included_exclusive_l // lookup_fmap in incl.
pose proof (leibniz_equiv _ _ incl) as incl'.
case db_t1: (db !! t1) => [t2'|] //= in incl'.
iPureIntro. by case: incl' => <-.
Qed.

Lemma state_auth_update t2' γ b db t1 t2 :
  state_auth γ b db -∗
  mapsto γ b t1 t2 ==∗
  state_auth γ b (<[t1 := t2']>db) ∗
  mapsto γ b t1 t2'.
Proof.
case: b; last first.
{ iIntros "?? !>". iFrame. }
iIntros "Hauth Hfrag".
iMod (nown_update_2 with "Hauth Hfrag") as "own".
{ apply: auth_update.
  apply: (singleton_local_update_any _ _ _ (Excl t2') (Excl t2')) => ? _.
  exact: exclusive_local_update. }
iDestruct "own" as "[Hauth Hfrag]".
iModIntro. iSplitL "Hauth" => //.
rewrite /state_auth fmap_insert. by eauto.
Qed.

Lemma state_auth_create t1 t2 γ b db :
  state_auth γ b db ==∗
  state_auth γ b (op_app db (Create t1 t2)) ∗
  (if db !! t1 then True else mapsto γ b t1 t2).
Proof.
rewrite /=; case db_t1: (db !! t1) => [t2'|]; eauto.
case: b; last first.
{ iIntros "#?". iModIntro. iSplit; trivial. }
iIntros "Hauth".
iMod (nown_update _ _ (a' := (_ ⋅ _)) with "Hauth") as "[Hauth Hfrag]".
{ apply: auth_update_alloc.
  apply: (alloc_local_update _ _ t1 (Excl t2)) => //.
  by rewrite lookup_fmap db_t1. }
iModIntro. iSplitL "Hauth" => //.
rewrite /state_auth fmap_insert. by iFrame.
Qed.

Definition client_view γ b n : iProp Σ :=
  ∃ os,
    ⌜n = length os⌝ ∗
    hist_auth γ os ∗
    state_auth γ b (to_db os).

Definition update_at γ n t1 t2 : iProp Σ :=
  ∃ os, ⌜n = length os⌝ ∗
        hist_frag γ (os ++ [Update t1 t2]).

Definition create_at γ n t1 t2 : iProp Σ :=
  ∃ os, ⌜n = length os⌝ ∗
        hist_frag γ (os ++ [Create t1 t2]).

Definition server_view γ n db : iProp Σ :=
  ∃ os, ⌜n = length os⌝ ∗
        ⌜db = to_db os⌝ ∗
        hist_frag γ os.

Lemma alloc b : ⊢ |==> ∃ γ, client_view γ b 0 ∗ server_view γ 0 ∅.
Proof.
iIntros "".
iMod nown_token_alloc as "[%γ token]".
iMod (nown_alloc (nroot.@"hist")
        (● to_max_prefix_list [] ⋅ ◯ to_max_prefix_list []) with "token")
  as "[hist token]"; try solve_ndisj.
{ apply/auth_both_valid_discrete. split; eauto.
  exact/to_max_prefix_list_valid. }
iMod (nown_alloc (nroot.@"state")
        (● (Excl <$> to_db [] : gmap _ _)) with "token")
  as "[state token]"; try solve_ndisj.
{ apply/auth_auth_valid. by rewrite /to_db /= fmap_empty. }
iAssert (hist_frag γ []) as "#frag".
{ by iDestruct "hist" as "[??]". }
iModIntro. iExists γ. iSplitL; last by iExists []; eauto.
iExists []. iSplit; eauto. iSplitL "hist".
- by iFrame.
- by case: b.
Qed.

Lemma update_client t2' γ b n t1 t2 :
  client_view γ b n -∗
  mapsto γ b t1 t2 ==∗
  client_view γ b (S n) ∗
  update_at γ n t1 t2' ∗
  mapsto γ b t1 t2'.
Proof.
iIntros "(%os & -> & own_os & own_db) own_frag".
iMod (hist_update _ os (Update t1 t2') with "own_os") as "[auth_os #frag_os]".
iMod (state_auth_update t2' with "own_db own_frag") as "[Hstate Hmapsto]".
iModIntro. iSplitL "auth_os Hstate".
{ iExists (os ++ [Update t1 t2']).
  rewrite app_length Nat.add_comm /=. iSplit; first by [].
  iFrame. by rewrite /to_db foldl_app. }
iFrame.
{ iExists _; eauto. }
Qed.

Lemma update_server γ n db t1 t2 :
  server_view γ n db -∗
  update_at γ n t1 t2 -∗
  server_view γ (S n) (<[t1 := t2]>db).
Proof.
iIntros "(%os & -> & -> & #frag) (%os' & %lengthE & #frag')".
iPoseProof (hist_frag_agree _ lengthE with "frag []") as "->".
{ iApply (hist_frag_prefix_of with "frag'").
  by exists [Update t1 t2]. }
iExists (os ++ [Update t1 t2]). rewrite app_length Nat.add_comm /=.
do 2!iSplit => //.
by rewrite /to_db foldl_app.
Qed.

Definition free_at γ n t1 : iProp Σ :=
  ∃ os, ⌜n = length os⌝ ∗
        hist_frag γ os ∗
        ⌜to_db os !! t1 = None⌝.

Lemma free_atI γ n db t1 :
  db !! t1 = None →
  server_view γ n db -∗
  free_at γ n t1.
Proof.
iIntros "%db_t1 (%os & -> & -> & #frag)".
iExists os. by eauto.
Qed.

Lemma create_client t1 t2 γ b n :
  client_view γ b n ==∗
  create_at γ n t1 t2 ∗
  client_view γ b (S n) ∗
  (free_at γ n t1 -∗ mapsto γ b t1 t2).
Proof.
iIntros "(%os & -> & hist & state)".
iMod (hist_update _ _ (Create t1 t2) with "hist") as "[hist_auth #hist_frag]".
iMod (state_auth_create t1 t2 with "state") as "[state mapsto]".
have ->: op_app (to_db os) (Create t1 t2) = to_db (os ++ [Create t1 t2]).
{ by rewrite /to_db foldl_app. }
iModIntro. iSplitR; first by iExists os; eauto.
iSplitL "hist_auth state".
{ iExists _. iFrame. by rewrite app_length Nat.add_comm. }
iIntros "(%os' & %lengthE & #hist_frag' & %db_t1)".
iAssert (hist_frag γ os) as "#hist_frag''".
{ iApply (hist_frag_prefix_of with "hist_frag").
  by exists [Create t1 t2]. }
iPoseProof (hist_frag_agree with "hist_frag'' hist_frag'") as "->" => //.
by rewrite db_t1.
Qed.

Lemma create_client_fake t1 t2 γ b n :
  client_view γ b n -∗
  mapsto γ false t1 t2.
Proof. by iIntros "(%os & -> & hist & state)". Qed.

Lemma create_server γ n db t1 t2 :
  db !! t1 = None →
  server_view γ n db -∗
  create_at γ n t1 t2 -∗
  server_view γ (S n) (<[t1 := t2]>db).
Proof.
iIntros "%db_t1 (%os & -> & -> & #frag) (%os' & %lengthE & #frag')".
iAssert (hist_frag γ os') as "#frag''".
{ iApply (hist_frag_prefix_of with "frag'").
  by exists [Create t1 t2]. }
iPoseProof (hist_frag_agree with "frag frag''") as "->" => //.
iExists (os ++ [Create t1 t2]). rewrite app_length Nat.add_comm.
do 2!iSplit => //. iPureIntro. by rewrite /to_db foldl_app /= db_t1.
Qed.

Definition stored_at γ n t1 t2 : iProp Σ :=
  ∃ os, ⌜n = length os⌝ ∗
        hist_frag γ os ∗
        ⌜to_db os !! t1 = Some t2⌝.

Lemma load_client γ b n t1 t2 t2' :
  b →
  client_view γ b n -∗
  mapsto γ b t1 t2 -∗
  stored_at γ n t1 t2' -∗
  ⌜t2' = t2⌝.
Proof.
iIntros "%bP (%os & -> & hist & state) t1_t2 (%os' & %lengthE & #Hfrag & %os_t1)".
iPoseProof (hist_auth_frag with "hist") as "#Hfrag'".
iPoseProof (hist_frag_agree with "Hfrag Hfrag'") as "->" => //.
iPoseProof (state_auth_mapsto with "state t1_t2") as "%os_t1'".
iPureIntro. rewrite os_t1 in os_t1'. by case/(_ bP): os_t1' => ->.
Qed.

Lemma load_server γ n db t1 t2 :
  db !! t1 = Some t2 →
  server_view γ n db -∗
  stored_at γ n t1 t2.
Proof.
iIntros "%db_t1 (%os & -> & -> & view)".
iExists os; eauto.
Qed.

End DB.

End DB.
