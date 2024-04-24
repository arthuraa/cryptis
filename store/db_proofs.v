From stdpp Require Import base countable gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis.store Require Import impl shared.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition dbUR : ucmra :=
  authUR (gmapUR term (exclR termO)).

Class dbGpreS Σ :=  DbGpreS {
  dbGpreS_tlock : tlockG Σ;
  dbGpreS_db : inG Σ dbUR;
}.

Local Existing Instance dbGpreS_tlock.
Local Existing Instance dbGpreS_db.

Class dbGS Σ := DbGS {
  db_inG : dbGpreS Σ;
}.

Local Existing Instance db_inG.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !dbGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (γ : gname) (l : loc) (t : term) (v : val).
Implicit Types (kvs : list (term * term)) (db : gmap term term).

Definition is_alist kvs db : Prop :=
  ∀ k, db !! k = snd <$> find (λ p, bool_decide (p.1 = k)) kvs.

Definition stores_db l db : iProp :=
  ∃ kvs, l ↦ repr kvs ∗ ⌜is_alist kvs db⌝.

Definition db_auth db : dbUR :=
  ● (Excl <$> db).

Definition db_frag db : dbUR :=
  ◯ (Excl <$> db).

Lemma valid_db_auth db : ✓ db_auth db.
Proof.
apply/auth_auth_valid => k; rewrite lookup_fmap; by case: (db !! k).
Qed.

Lemma valid_db_frag db : ✓ db_frag db.
Proof.
apply/auth_frag_valid => k; rewrite lookup_fmap; by case: (db !! k).
Qed.

Hint Resolve valid_db_auth : core.

Lemma db_auth_db_frag_valid db1 db2 :
  ✓ (db_auth db1 ⋅ db_frag db2) →
  ∀ t1 t2, db2 !! t1 = Some t2 -> db1 !! t1 = Some t2.
Proof.
rewrite /db_auth /db_frag => /auth_both_valid_discrete [incl_12 valid_1] t1 t2.
move: incl_12; rewrite lookup_included; move/(_ t1).
rewrite !lookup_fmap => incl_12 db2_t1.
rewrite db2_t1 /= in incl_12.
case db1_t1: (db1 !! t1) => [t2'|] /= in incl_12 *.
- by move/Excl_included/(leibniz_equiv _ _): incl_12 => ->.
- by case/option_included: incl_12 => // - [] ? [] ? [] ? [] ?.
Qed.

Lemma db_auth_db_frag1_valid db t1 t2 :
  ✓ (db_auth db ⋅ db_frag {[t1 := t2]}) →
  db !! t1 = Some t2.
Proof.
move=> valid_12; apply: (db_auth_db_frag_valid valid_12).
by rewrite lookup_singleton.
Qed.

Lemma db_auth_db_frag_update db t1 t2 t2' :
  db_auth db ⋅ db_frag {[t1 := t2]} ~~>
  db_auth (<[t1 := t2']> db) ⋅ db_frag {[t1 := t2']}.
Proof.
apply/auth_update; rewrite fmap_insert !map_fmap_singleton.
apply: singleton_local_update_any => x _.
by apply: exclusive_local_update.
Qed.

Definition db_res γ l : iProp :=
  ∃ db, stores_db l db ∗ own γ (db_auth db).

Definition is_db v : iProp :=
  ∃ l vlock γkvs γlock,
    ⌜v = (#l, vlock)%V⌝ ∗
    meta l (nroot.@"kvs") γkvs ∗
    meta l (nroot.@"lock") γlock ∗
    is_lock γlock vlock (db_res γkvs l).

Global Instance is_db_persistent v : Persistent (is_db v).
Proof. apply _. Qed.

Lemma wp_db_new :
  {{{ True }}}
    DB.new #()
  {{{ v, RET v; is_db v }}}.
Proof.
iIntros "%Φ _ Hpost"; wp_lam; wp_pures.
wp_bind (ref _)%E; iApply wp_alloc => //.
iIntros "!> %l [Hl meta]".
rewrite (meta_token_difference _ (↑(nroot.@"kvs")) _) //.
iDestruct "meta" as "[meta_kvs meta]".
iMod (own_alloc (db_auth ∅)) as "[%γkvs own_γkvs]" => //.
iMod (meta_set _ _ γkvs (nroot.@"kvs") with "meta_kvs") as "#meta_kvs" => //.
wp_pures; wp_bind (newlock _).
iApply (newlock_spec (db_res γkvs l) with "[Hl own_γkvs]").
{ iExists ∅. iFrame. iExists [].
  rewrite /=. rewrite repr_list_unseal /=. iFrame.
  by iPureIntro => k; rewrite lookup_empty. }
iIntros "!> %vlock %γlock #lock".
iMod (meta_set _ _ γlock (nroot.@"lock") with "meta") as "#meta_lock".
{ solve_ndisj. }
wp_pures. iApply "Hpost". iExists l, vlock, γkvs, γlock. eauto.
Qed.

Lemma wp_find kvs db t :
  is_alist kvs db →
  {{{ True }}}
    DB.find (repr kvs) t
  {{{ RET (repr (db !! t)); True }}}.
Proof.
iIntros "%kvs_db %Φ _ Hpost"; wp_lam; wp_pures.
wp_bind (find_list _ _).
iApply (wp_find_list (λ x, bool_decide (x.1 = t)) _ kvs) => //.
{ move=> [k t']; iIntros "%Φ' _ Hpost".
  wp_pures. iApply wp_eq_term. by iApply "Hpost". }
iIntros "!> _"; rewrite kvs_db.
by case: find => [[k' t']|] /=; wp_pures; iApply "Hpost".
Qed.

Lemma wp_with_locked_db v Φ (f : val) :
  (∀ γkvs l vlock,
      ⌜v = (#l, vlock)%V⌝ -∗
      meta l (nroot.@"kvs") γkvs -∗
      db_res γkvs l -∗
      WP f #l {{ res, Φ res ∗ db_res γkvs l }}) -∗
  is_db v -∗
  WP DB.with_locked_db v f {{ res, Φ res }}.
Proof.
iIntros "wp_f (%l & %vlock & %γkvs & %γloc & -> & #m_kvs & #m_lock & #lock)".
wp_lam; wp_pures.
wp_bind (acquire _); iApply (acquire_spec with "lock").
iIntros "!> (locked & db_res)".
wp_pures; wp_bind (f _).
iPoseProof ("wp_f" with "[//] m_kvs db_res") as "wp_f".
iApply (wp_wand with "wp_f").
iIntros "%res [post db_res]".
wp_pures; wp_bind (release _); iApply (release_spec with "[locked db_res]").
{ iFrame. iSplitR; eauto. }
iIntros "!> _"; wp_pures; eauto.
Qed.

Definition db_mapsto v t1 t2 : iProp :=
  ∃ l vlock γkvs,
    ⌜v = (#l, vlock)%V⌝ ∗
    meta l (nroot.@"kvs") γkvs ∗
    own γkvs (db_frag {[t1 := t2]}).

Lemma db_mapsto_inv l v γkvs t1 t2 :
  db_mapsto (#l, v)%V t1 t2 -∗
  meta l (nroot.@"kvs") γkvs -∗
  own γkvs (db_frag {[t1 := t2]}).
Proof.
iIntros "(%l' & %v' & %γkvs' & %E & #meta' & own) #meta".
case: E => <- _ {l' v'}.
now iPoseProof (meta_agree with "meta meta'") as "<-".
Qed.

Lemma is_alist_cons kvs db k t :
  is_alist kvs db ->
  is_alist ((k, t) :: kvs) (<[k := t]>db).
Proof.
move=> kvs_db k' /=; case: bool_decide_reflect => [<-|ne].
- by rewrite lookup_insert.
- by rewrite lookup_insert_ne.
Qed.

Lemma wp_set v t1 t2 t2' :
  {{{ is_db v ∗ db_mapsto v t1 t2 }}}
    DB.set v t1 t2'
  {{{ RET #(); db_mapsto v t1 t2' }}}.
Proof.
iIntros "%Φ [#vP t1_t2] Hpost".
wp_lam; wp_pures; iApply (wp_with_locked_db with "[t1_t2 Hpost] vP").
iIntros "%γkvs %l %vlock -> #m_kvs lP".
iPoseProof (db_mapsto_inv with "t1_t2 m_kvs") as "t1_t2".
iDestruct "lP" as "(%db & (%kvs & l_kvs & %kvs_db) & dbP)".
iPoseProof (own_valid_2 with "dbP t1_t2") as "%valid_12".
have {valid_12} db_t1 := db_auth_db_frag1_valid valid_12.
wp_pures. wp_load. wp_pures. change (t1, t2')%V with (repr (t1, t2')).
(* FIXME: The wp_cons tactic cannot proceed here because it undoes the previous
   change, which brings the goal to a shape where the tac_wp_cons lemma does not
   apply. *)
wp_bind (_ :: _)%E. iApply (wp_cons _ (t1, t2') kvs). wp_store.
iMod (own_update_2 with "dbP t1_t2") as "Hown".
  exact: (db_auth_db_frag_update t2').
iDestruct "Hown" as "[dbP t1_t2]".
iModIntro. iSplitL "Hpost t1_t2".
- iApply "Hpost". iExists l, vlock, γkvs; eauto.
- iExists _; iFrame. iExists _. iFrame. iPureIntro.
  exact: is_alist_cons.
Qed.

Lemma wp_get v t1 t2 :
  {{{ is_db v ∗ db_mapsto v t1 t2 }}}
    DB.get v t1
  {{{ RET (repr t2); db_mapsto v t1 t2 }}}.
Proof.
iIntros "%Φ [#vP t1_t2] Hpost".
wp_lam; wp_pures; iApply (wp_with_locked_db with "[t1_t2 Hpost] vP").
iIntros "%γkvs %l %vlock -> #m_kvs lP".
iPoseProof (db_mapsto_inv with "t1_t2 m_kvs") as "t1_t2".
iDestruct "lP" as "(%db & (%kvs & l_kvs & %kvs_db) & dbP)".
iPoseProof (own_valid_2 with "dbP t1_t2") as "%valid_12".
have {valid_12} db_t1 := db_auth_db_frag1_valid valid_12.
wp_pures. wp_load. wp_bind (DB.find _ _)%E. iApply wp_find; eauto.
iIntros "!> _". rewrite db_t1. wp_pures. iModIntro.
iSplitL "Hpost t1_t2".
- iApply "Hpost". iExists l, vlock, γkvs. eauto.
- iExists _; iFrame. iExists _. iFrame. eauto.
Qed.

End Verif.
