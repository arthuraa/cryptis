From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.

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

Module DB.

Definition new : val := λ: <>,
  let: "kvs" := ref [] in
  let: "lock" := newlock #() in
  ("kvs", "lock").

Definition find : val := λ: "kvs" "k",
  let: "res" := find_list (λ: "kv", eq_term (Fst "kv") "k") "kvs" in
  match: "res" with
    SOME "res" => SOME (Snd "res")
  | NONE => NONE
  end.

Definition while_locked : val := λ: "db" "f",
  let: "kvs" := Fst "db" in
  let: "lock" := Snd "db" in
  acquire "lock";;
  let: "res" := "f" "kvs" in
  release "lock";;
  "res".

Definition set : val := λ: "db" "k" "v",
  while_locked "db" (λ: "kvs",
      "kvs" <- ("k", "v") :: !"kvs";;
      #()
  ).

Definition get : val := λ: "db" "k",
  while_locked "db" (λ: "kvs",
      match: find !"kvs" "k" with
        SOME "res" => "res"
      | NONE => #() (* Error *)
      end
  ).

Definition create : val := λ: "db" "k" "v",
  while_locked "db" (λ: "kvs",
    match: find !"kvs" "k" with
      SOME <> => #false
    | NONE => "kvs" <- ("k", "v") :: !"kvs";; #true
    end
  ).

Definition delete : val := λ: "db" "k",
  while_locked "db" (λ: "kvs",
    "kvs" <- filter_list (λ: "p", ~ (eq_term "k" (Fst "p"))) !"kvs";;
    #()
  ).

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !dbGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (γ : gname) (l : loc) (t : term) (v : val).
Implicit Types (kvs : list (term * term)) (db : gmap term term).

Definition is_alist kvs db : Prop :=
  ∀ k, db !! k = snd <$> List.find (λ p, bool_decide (p.1 = k)) kvs.

Definition stores_db l db : iProp :=
  ∃ kvs, l ↦ repr kvs ∗ ⌜is_alist kvs db⌝.

Definition auth db : dbUR := ● (Excl <$> db).
Definition frag db : dbUR := ◯ (Excl <$> db).

Lemma valid_auth db : ✓ auth db.
Proof.
apply/auth_auth_valid => k; rewrite lookup_fmap; by case: (db !! k).
Qed.

Lemma valid_frag db : ✓ frag db.
Proof.
apply/auth_frag_valid => k; rewrite lookup_fmap; by case: (db !! k).
Qed.

Hint Resolve valid_auth : core.

Lemma auth_frag_valid db1 db2 :
  ✓ (auth db1 ⋅ frag db2) →
  ∀ t1 t2, db2 !! t1 = Some t2 -> db1 !! t1 = Some t2.
Proof.
rewrite /auth /frag => /auth_both_valid_discrete [incl_12 valid_1] t1 t2.
move: incl_12; rewrite lookup_included; move/(_ t1).
rewrite !lookup_fmap => incl_12 db2_t1.
rewrite db2_t1 /= in incl_12.
case db1_t1: (db1 !! t1) => [t2'|] /= in incl_12 *.
- by move/Excl_included/(leibniz_equiv _ _): incl_12 => ->.
- by case/option_included: incl_12 => // - [] ? [] ? [] ? [] ?.
Qed.

Lemma auth_frag1_valid db t1 t2 :
  ✓ (auth db ⋅ frag {[t1 := t2]}) →
  db !! t1 = Some t2.
Proof.
move=> valid_12; apply: (auth_frag_valid valid_12).
by rewrite lookup_singleton.
Qed.

Lemma auth_frag_update db t1 t2 t2' :
  auth db ⋅ frag {[t1 := t2]} ~~>
  auth (<[t1 := t2']> db) ⋅ frag {[t1 := t2']}.
Proof.
apply/auth_update; rewrite fmap_insert !map_fmap_singleton.
apply: singleton_local_update_any => x _.
by apply: exclusive_local_update.
Qed.

Lemma auth_frag_alloc db t1 t2 :
  db !! t1 = None ->
  auth db ~~> auth (<[t1 := t2]> db) ⋅ frag {[t1 := t2]}.
Proof.
move=> db_t1. apply/auth_update_alloc; rewrite fmap_insert map_fmap_singleton.
by apply: alloc_singleton_local_update => //; rewrite lookup_fmap db_t1.
Qed.

Lemma auth_frag_delete db t1 t2 :
  db !! t1 = Some t2 ->
  auth db ⋅ frag {[t1 := t2]} ~~> auth (base.delete t1 db).
Proof.
move=> db_t1. apply/auth_update_dealloc.
rewrite map_fmap_singleton fmap_delete.
exact/delete_singleton_local_update.
Qed.

Definition db_res γ l : iProp :=
  ∃ db, stores_db l db ∗ own γ (auth db).

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
iMod (own_alloc (auth ∅)) as "[%γkvs own_γkvs]" => //.
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
by case: List.find => [[k' t']|] /=; wp_pures; iApply "Hpost".
Qed.

Lemma wp_while_locked v Φ (f : val) :
  (∀ γkvs l vlock,
      ⌜v = (#l, vlock)%V⌝ -∗
      meta l (nroot.@"kvs") γkvs -∗
      db_res γkvs l -∗
      WP f #l {{ res, Φ res ∗ db_res γkvs l }}) -∗
  is_db v -∗
  WP while_locked v f {{ res, Φ res }}.
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

Definition mapsto v t1 t2 : iProp :=
  ∃ l vlock γkvs,
    ⌜v = (#l, vlock)%V⌝ ∗
    meta l (nroot.@"kvs") γkvs ∗
    own γkvs (frag {[t1 := t2]}).

Lemma mapsto_inv l v γkvs t1 t2 :
  mapsto (#l, v)%V t1 t2 -∗
  meta l (nroot.@"kvs") γkvs -∗
  own γkvs (frag {[t1 := t2]}).
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

Lemma is_alist_filter kvs db k :
  is_alist kvs db ->
  is_alist (List.filter (λ p, negb (bool_decide (k = p.1))) kvs)
           (base.delete k db).
Proof.
move=> kvs_db k' /=; case: (decide (k = k')) => [<- {k'}|neq].
- rewrite lookup_delete. case eq_find: List.find => [[t1 t2]|] //=.
  case/(@find_some _ _ _ _): eq_find => /= in_filter.
  case: bool_decide_reflect => // -> in in_filter *.
  rewrite filter_In /= in in_filter; case: in_filter => _.
  by rewrite bool_decide_eq_true_2.
- rewrite lookup_delete_ne // {}kvs_db.
  elim: kvs => //= - [/= t1 t2] kvs IH.
  case: bool_decide_reflect => [-> {t1}|neq'] /=.
  + by rewrite bool_decide_eq_false_2 //= bool_decide_eq_true_2.
  + rewrite IH. case: bool_decide_reflect => //= neq''.
    by rewrite bool_decide_eq_false_2.
Qed.

Lemma wp_set v t1 t2 t2' :
  {{{ is_db v ∗ mapsto v t1 t2 }}}
    DB.set v t1 t2'
  {{{ RET #(); mapsto v t1 t2' }}}.
Proof.
iIntros "%Φ [#vP t1_t2] Hpost".
wp_lam; wp_pures; iApply (wp_while_locked with "[t1_t2 Hpost] vP").
iIntros "%γkvs %l %vlock -> #m_kvs lP".
iPoseProof (mapsto_inv with "t1_t2 m_kvs") as "t1_t2".
iDestruct "lP" as "(%db & (%kvs & l_kvs & %kvs_db) & dbP)".
iPoseProof (own_valid_2 with "dbP t1_t2") as "%valid_12".
have {valid_12} db_t1 := auth_frag1_valid valid_12.
wp_pures. wp_load. wp_pures. change (t1, t2')%V with (repr (t1, t2')).
(* FIXME: The wp_cons tactic cannot proceed here because it undoes the previous
   change, which brings the goal to a shape where the tac_wp_cons lemma does not
   apply. *)
wp_bind (_ :: _)%E. iApply (wp_cons _ (t1, t2') kvs). wp_store.
iMod (own_update_2 with "dbP t1_t2") as "Hown".
  exact: (auth_frag_update t2').
iDestruct "Hown" as "[dbP t1_t2]".
iModIntro. iSplitL "Hpost t1_t2".
- iApply "Hpost". iExists l, vlock, γkvs; eauto.
- iExists _; iFrame. iExists _. iFrame. iPureIntro.
  exact: is_alist_cons.
Qed.

Lemma wp_get v t1 t2 :
  {{{ is_db v ∗ mapsto v t1 t2 }}}
    DB.get v t1
  {{{ RET (repr t2); mapsto v t1 t2 }}}.
Proof.
iIntros "%Φ [#vP t1_t2] Hpost".
wp_lam; wp_pures; iApply (wp_while_locked with "[t1_t2 Hpost] vP").
iIntros "%γkvs %l %vlock -> #m_kvs lP".
iPoseProof (mapsto_inv with "t1_t2 m_kvs") as "t1_t2".
iDestruct "lP" as "(%db & (%kvs & l_kvs & %kvs_db) & dbP)".
iPoseProof (own_valid_2 with "dbP t1_t2") as "%valid_12".
have {valid_12} db_t1 := auth_frag1_valid valid_12.
wp_pures. wp_load. wp_bind (DB.find _ _)%E. iApply wp_find; eauto.
iIntros "!> _". rewrite db_t1. wp_pures. iModIntro.
iSplitL "Hpost t1_t2".
- iApply "Hpost". iExists l, vlock, γkvs. eauto.
- iExists _; iFrame. iExists _. iFrame. eauto.
Qed.

Lemma wp_create v t1 t2 :
  {{{ is_db v }}}
    DB.create v t1 t2
  {{{ (b : bool), RET #b;
      if b then mapsto v t1 t2 else True }}}.
Proof.
iIntros "%Φ #vP Hpost".
wp_lam; wp_pures. iApply (wp_while_locked with "[Hpost] vP").
iIntros "%γkvs %l %vlock -> #m_kvs lP".
iDestruct "lP" as "(%db & (%kvs & l_kvs & %kvs_db) & dbP)".
wp_pures. wp_load. wp_bind (DB.find _ _)%E. iApply wp_find; eauto.
iIntros "!> _". case db_t1: (db !! t1) => [t2'|]; wp_pures.
  iModIntro. iSplitL "Hpost"; first by iApply "Hpost".
  iExists _; iFrame. iExists _. iFrame. eauto.
wp_load. wp_pures. change (t1, t2)%V with (repr (t1, t2)).
wp_bind (_ :: _)%E. iApply (wp_cons _ _ kvs). wp_store.
iMod (own_update with "dbP") as "Hown".
{ exact: (auth_frag_alloc t2). }
iDestruct "Hown" as "[dbP t1_t2]".
iModIntro. iSplitL "Hpost t1_t2".
- iApply "Hpost". iExists l, vlock, γkvs; iFrame. by eauto.
- iExists _. iFrame. iExists _. iFrame. iPureIntro. exact: is_alist_cons.
Qed.

Lemma wp_delete v t1 t2 :
  {{{ is_db v ∗ mapsto v t1 t2 }}}
    DB.delete v t1
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ [#vP t1_t2] Hpost".
wp_lam; wp_pures; iApply (wp_while_locked with "[t1_t2 Hpost] vP").
iIntros "%γkvs %l %vlock -> #m_kvs lP".
iPoseProof (mapsto_inv with "t1_t2 m_kvs") as "t1_t2".
iDestruct "lP" as "(%db & (%kvs & l_kvs & %kvs_db) & dbP)".
iPoseProof (own_valid_2 with "dbP t1_t2") as "%valid_12".
have {valid_12} db_t1 := auth_frag1_valid valid_12.
wp_pures. wp_load. wp_pures. wp_bind (filter_list _ _).
iApply (wp_filter_list (λ p : term * term, negb (bool_decide (t1 = p.1))))
       => //.
{ iIntros "%p %Ψ _ Hpost". wp_pures. wp_bind (eq_term _ _).
  iApply wp_eq_term. wp_pures. by iApply "Hpost". }
iIntros "!> _". wp_store.
iMod (own_update_2 with "dbP t1_t2") as "dbP".
{ exact: auth_frag_delete. }
iModIntro. iSplitL "Hpost"; first by iApply "Hpost".
iExists _. iFrame. iExists _. iFrame. iPureIntro.
exact: is_alist_filter.
Qed.

End Verif.

End DB.
