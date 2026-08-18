(** * Recursive tagged DB protocol (plan.org July: "Define protocol for DB example").

    Realizes the plan's [db_st] sketch on top of the tagged select/branch
    machinery of tag.v: [iProto_tag]/[iMsg_tag] plus its send-side and algebra
    lemmas.  The protocol is RECURSIVE (Iris [fixpoint]
    over the [gmap term term -d> iProto] COFE) and parameterized by [auth]
    (the [db_auth] slot, returned to the client at close/ack). *)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn.
From cryptis.examples.sess Require impl.
From cryptis.examples.sess.proofs Require Import base.
From cryptis.examples.sess Require Import proofs tag.
From actris.channel Require Import proto_model proto.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation dbtN := (nroot.@"dbt").
Definition dbt_store_N := dbtN.@"store".
Definition dbt_load_N := dbtN.@"load".
Definition dbt_close_N := dbtN.@"close".

Section DBTagged.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ, !sessG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types (db : gmap term term).

(** ** The recursive protocol, client view (Send at the tagged node).

    store: send (k, v), continue at db extended.
    load : send k (must be present), receive its value, continue unchanged.
    close: send close, receive ack carrying [auth db], END. *)
Definition db_arms (auth : gmap term term → iProp)
    (rec : gmap term term -d> iProto Σ term)
    (db : gmap term term) : gmap namespace (iMsg Σ term) :=
  {[ dbt_store_N :=
       (∃ k, ∃ v, MSG Spec.of_list [k; v] {{ True }}; rec (<[k := v]> db))%msg;
     dbt_load_N :=
       (∃ k, MSG k {{ ⌜is_Some (db !! k)⌝ }};
          (<? v> MSG v {{ ⌜db !! k = Some v⌝ }}; rec db)%proto)%msg;
     dbt_close_N :=
       (MSG (TInt 0) {{ True }};
          (<?> MSG (TInt 0) {{ auth db }}; END)%proto)%msg ]}.

Definition db_st_aux (auth : gmap term term → iProp)
    (rec : gmap term term -d> iProto Σ term) :
    gmap term term -d> iProto Σ term :=
  λ db, iProto_tag Send (db_arms auth rec db).

Global Instance db_st_aux_contractive auth : Contractive (db_st_aux auth).
Proof.
move=> n r1 r2 Hr db.
rewrite /db_st_aux /iProto_tag /db_arms.
f_equiv.
apply iMsg_tag_ne.
solve_proto_contractive.
Qed.

Definition db_st (auth : gmap term term → iProp) :
    gmap term term -d> iProto Σ term :=
  fixpoint (db_st_aux auth).

Lemma db_st_unfold auth db :
  db_st auth db ≡ iProto_tag Send (db_arms auth (db_st auth) db).
Proof. exact: (fixpoint_unfold (db_st_aux auth) db). Qed.

(** Server view: the dual normalizes back to a tagged RECV node over the
    dualized arms — the exact shape Arthur's [wp_select] consumes. *)
Lemma db_st_dual_unfold auth db :
  iProto_dual (db_st auth db)
  ≡ iProto_tag Recv (iMsg_dual <$> db_arms auth (db_st auth) db).
Proof.
rewrite db_st_unfold iProto_dual_tag //.
Qed.

(** ** Helper: turn a protocol equivalence into a subtyping proof. *)
Lemma iProto_le_of_equiv (p q : iProto Σ term) : p ≡ q → ⊢ p ⊑ q.
Proof. intros E. setoid_rewrite E. iApply iProto_le_refl. Qed.

(** ** Client operations (runtime code). *)
Definition db_store : val := λ: "cs" "k" "v",
  impl.send "cs" (tag (Tag dbt_store_N) (term_of_list ["k"; "v"])).

Definition db_load : val := λ: "cs" "k",
  impl.send "cs" (tag (Tag dbt_load_N) "k");;
  impl.recv "cs".

Definition db_close : val := λ: "cs",
  impl.send "cs" (tag (Tag dbt_close_N) (TInt 0));;
  impl.recv "cs".

(** Distinctness of the three tags (used for the map lookups). *)
Lemma dbt_store_load : dbt_store_N ≠ dbt_load_N.
Proof. move=> e; case: (ndot_inj _ _ _ _ e) => _ e2; by discriminate e2. Qed.
Lemma dbt_store_close : dbt_store_N ≠ dbt_close_N.
Proof. move=> e; case: (ndot_inj _ _ _ _ e) => _ e2; by discriminate e2. Qed.
Lemma dbt_load_close : dbt_load_N ≠ dbt_close_N.
Proof. move=> e; case: (ndot_inj _ _ _ _ e) => _ e2; by discriminate e2. Qed.

(** ** Client specs. *)

Lemma wp_db_store auth skI skR rl cs db k v :
  {{{ connected skI skR rl cs (db_st auth db) ∗ public k ∗ public v }}}
    db_store (repr cs) k v
  {{{ RET #(); connected skI skR rl cs (db_st auth (<[k := v]> db)) }}}.
Proof.
iIntros (Φ) "(conn & #p_k & #p_v) post".
wp_lam; wp_pures.
wp_list.
wp_term_of_list.
wp_bind (tag _ _). iApply wp_tag.
iApply (wp_send_msg _ _ _ _
          (iMsg_tag (db_arms auth (db_st auth) db)) _
          (db_st auth (<[k := v]> db)) with "[conn] post").
iSplitL "conn".
{ iApply (connected_le with "conn"). iNext.
  iApply iProto_le_of_equiv. exact: db_st_unfold. }
iSplitR.
{ rewrite public_tag public_of_list /=. by iFrame "#". }
iRight.
iApply (iMsg_tag_intro _ _ (lookup_insert _ _ _)).
rewrite iMsg_exist_eq /=. iExists k. iExists v.
rewrite iMsg_base_eq /=.
do 2 (iSplit; first done).
auto.
Qed.

Lemma wp_db_load auth skI skR rl cs db k v :
  db !! k = Some v →
  {{{ connected skI skR rl cs (db_st auth db) ∗ public k }}}
    db_load (repr cs) k
  {{{ t', RET (repr t');
      connected skI skR rl cs (db_st auth db) ∗
      public t' ∗
      (public (si_key cs) ∨ ⌜t' = v⌝) }}}.
Proof.
move=> Hk. iIntros (Φ) "(conn & #p_k) post".
wp_lam; wp_pures.
wp_bind (tag _ _). iApply wp_tag.
wp_bind (impl.send _ _).
iApply (wp_send_msg _ _ _ _
          (iMsg_tag (db_arms auth (db_st auth) db)) _
          (<? v'> MSG v' {{ ⌜db !! k = Some v'⌝ }}; db_st auth db)%proto
          with "[conn]").
{ iSplitL "conn".
  { iApply (connected_le with "conn"). iNext.
    iApply iProto_le_of_equiv. exact: db_st_unfold. }
  iSplitR; first by rewrite public_tag.
  iRight.
  have HNl : db_arms auth (db_st auth) db !! dbt_load_N
             = Some (∃ k', MSG k' {{ ⌜is_Some (db !! k')⌝ }};
                       (<? v'> MSG v' {{ ⌜db !! k' = Some v'⌝ }};
                        db_st auth db)%proto)%msg.
  { rewrite /db_arms lookup_insert_ne; last exact: dbt_store_load.
    by rewrite lookup_insert. }
  iApply (iMsg_tag_intro _ _ HNl).
  rewrite iMsg_exist_eq /=. iExists k.
  rewrite iMsg_base_eq /=.
  iSplit; first done.
  iSplit; first by eauto.
  auto. }
iIntros "!> conn". wp_pures.
wp_apply (wp_recv with "conn").
iIntros (t' p') "(#p_t' & conn & disj)".
iDestruct "disj" as "[#fail | car]".
- iApply "post". iFrame "p_t'".
  iSplitL; last by eauto.
  iDestruct "conn" as "[gc _]". iFrame "gc". by iLeft.
- rewrite iMsg_exist_eq /=.
  iDestruct "car" as (v') "car".
  rewrite iMsg_base_eq /=.
  iDestruct "car" as "(-> & Heq & %Hv')".
  rewrite later_equivI_1.
  iApply "post". iFrame "p_t'".
  iSplitL; last by rewrite Hk in Hv'; case: Hv' => ->; eauto.
  iApply (connected_le with "conn"). iNext.
  iRewrite -"Heq". iApply iProto_le_refl.
Qed.

Lemma wp_db_close auth skI skR rl cs db :
  {{{ connected skI skR rl cs (db_st auth db) }}}
    db_close (repr cs)
  {{{ t', RET (repr t');
      connected skI skR rl cs END ∗
      (public (si_key cs) ∨ auth db) }}}.
Proof.
iIntros (Φ) "conn post".
wp_lam; wp_pures.
wp_bind (tag _ _). iApply wp_tag.
wp_bind (impl.send _ _).
iApply (wp_send_msg _ _ _ _
          (iMsg_tag (db_arms auth (db_st auth) db)) _
          (<?> MSG (TInt 0) {{ auth db }}; END)%proto
          with "[conn]").
{ iSplitL "conn".
  { iApply (connected_le with "conn"). iNext.
    iApply iProto_le_of_equiv. exact: db_st_unfold. }
  iSplitR; first by rewrite public_tag public_TInt.
  iRight.
  have HNc : db_arms auth (db_st auth) db !! dbt_close_N
             = Some (MSG (TInt 0) {{ True }};
                       (<?> MSG (TInt 0) {{ auth db }}; END)%proto)%msg.
  { rewrite /db_arms lookup_insert_ne; last exact: dbt_store_close.
    rewrite lookup_insert_ne; last exact: dbt_load_close.
    by rewrite lookup_singleton. }
  iApply (iMsg_tag_intro _ _ HNc).
  rewrite iMsg_base_eq /=.
  do 2 (iSplit; first done).
  auto. }
iIntros "!> conn". wp_pures.
wp_apply (wp_recv with "conn").
iIntros (t' p') "(#p_t' & conn & disj)".
iDestruct "disj" as "[#fail | car]".
- iApply "post".
  iSplitL; last by eauto.
  iDestruct "conn" as "[gc _]". iFrame "gc". by iLeft.
- rewrite iMsg_base_eq /=.
  iDestruct "car" as "(_ & Heq & auth)".
  rewrite later_equivI_1.
  iApply "post". iFrame "auth".
  iApply (connected_le with "conn"). iNext.
  iRewrite -"Heq". iApply iProto_le_refl.
Qed.

End DBTagged.
