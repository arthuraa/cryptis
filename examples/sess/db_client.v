(** * DB client layer: ghost state + store-parity specs + connect (SOLUTIONS).

    Reference implementation for plan.org "What are missing", phases 1-3:
      Phase 1  instantiate the client ghost state with the store example's
               [DB] module (db_state / mapsto), allocated from term_token;
      Phase 2  the state predicate [db_client_connected] hiding the logical
               db, and client specs in the STORE-EXAMPLE style: load takes a
               pointsto, store updates it (Arthur: "not dependent on db, just
               a pointsto in the precondition");
      Phase 3  [db_st0]: the fixed initial protocol whose single connect
               message instantiates the session's [db] and carries a
               caller-chosen resource [R db].

    The tutorial version with the proofs removed is db_client_exercises.v;
    the guide is db_client_tutorial.md. *)

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
From cryptis.examples.sess Require Import proofs tag db_tagged.
From cryptis.examples.store Require Import db.
From actris.channel Require Import proto_model proto.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DBClient.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ,
          !sessG Σ, !dbGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t k v : term).
Implicit Types (db : gmap term term).

(** The protocol's [auth] slot (the close-ack payload) stays ABSTRACT here:
    it is the server-side resource, still under design.  The CLIENT-side
    ghost state below is a separate thing: the [DB] authority + pointstos. *)
Variable auth : gmap term term → iProp.

(** ** Phase 1 — client ghost state, from the store example's [DB] module. *)

Definition db_mapsto skI skR k v : iProp := DB.mapsto skI skR dbtN k v.
Definition db_free skI skR T : iProp := DB.free_at skI skR dbtN T.

Lemma db_client_alloc skI skR E :
  ↑dbtN.@"client".@(skR : term).@"state" ⊆ E →
  term_token skI E ==∗
  DB.db_state skI skR dbtN ∅ ∗
  db_free skI skR ⊤ ∗
  term_token skI (E ∖ ↑dbtN.@"client".@(skR : term).@"state").
Proof. exact: DB.client_alloc. Qed.

(** ** Phase 2 — the state predicate.

    The logical database is hidden existentially; the invariant is that the
    protocol INDEX and the ghost AUTHORITY advance in lockstep, so agreement
    between the authority and a pointsto yields facts about the index. *)
Definition db_client_connected skI skR rl cs : iProp :=
  ∃ db, connected skI skR rl cs (db_st auth db) ∗
        DB.db_state skI skR dbtN db.

(** Store-parity load: precondition is a POINTSTO, not a fact about [db]. *)
Lemma wp_db_load' skI skR rl cs k v :
  {{{ db_client_connected skI skR rl cs ∗
      db_mapsto skI skR k v ∗
      public k }}}
    db_load (repr cs) k
  {{{ t', RET (repr t');
      db_client_connected skI skR rl cs ∗
      db_mapsto skI skR k v ∗
      public t' ∗
      (public (si_key cs) ∨ ⌜t' = v⌝) }}}.
Proof.
iIntros (Φ) "((%db & conn & state) & frag & #p_k) post".
iPoseProof (DB.db_state_mapsto with "state frag") as "%Hk".
wp_apply (wp_db_load _ _ _ _ _ Hk with "[$conn $p_k]").
iIntros (t') "(conn & #p_t' & disj)".
iApply "post". iFrame "frag p_t' disj".
iExists db. iFrame.
Qed.

(** Store-parity store: updates the pointsto; ghost authority and protocol
    index advance in the same step (the "lockstep" lemma). *)
Lemma wp_db_store' skI skR rl cs k v v' :
  {{{ db_client_connected skI skR rl cs ∗
      db_mapsto skI skR k v' ∗
      public k ∗ public v }}}
    db_store (repr cs) k v
  {{{ RET #();
      db_client_connected skI skR rl cs ∗
      db_mapsto skI skR k v }}}.
Proof.
iIntros (Φ) "((%db & conn & state) & frag & #p_k & #p_v) post".
iMod (DB.db_state_update v with "state frag") as "[state frag]".
wp_apply (wp_db_store auth skI skR rl cs _ k v with "[$conn $p_k $p_v]").
iIntros "conn".
iApply "post". iFrame "frag".
iExists (<[k := v]> db). iFrame.
Qed.

(** Store-parity create: a FRESH key, consuming a token from [db_free]. *)
Lemma wp_db_create' skI skR rl cs k v :
  {{{ db_client_connected skI skR rl cs ∗
      db_free skI skR {[k]} ∗
      public k ∗ public v }}}
    db_store (repr cs) k v
  {{{ RET #();
      db_client_connected skI skR rl cs ∗
      db_mapsto skI skR k v }}}.
Proof.
iIntros (Φ) "((%db & conn & state) & free & #p_k & #p_v) post".
iMod (DB.db_state_create k v with "state free") as "(_ & state & frag)".
wp_apply (wp_db_store auth skI skR rl cs _ k v with "[$conn $p_k $p_v]").
iIntros "conn".
iApply "post". iFrame "frag".
iExists (<[k := v]> db). iFrame.
Qed.

(** ** Phase 3 — [db_st0]: the connect handshake.

    The initial protocol is STATICALLY known (so it can be baked into
    [ctx N p] / [sess_params]); the first message's LOGICAL existential
    instantiates [db] and its payload carries a caller-chosen resource
    [R db] to the server.  [R] is a parameter: [λ _, True] for the minimal
    fresh-session story (db := ∅), a replica receipt for reconnection. *)
Variable R : gmap term term → iProp.

Definition db_connect_N := dbtN.@"connect".

Definition db_st0 : iProto Σ term :=
  iProto_tag Send {[ db_connect_N :=
    (∃ db, MSG (TInt 0) {{ R db }}; db_st auth db)%msg ]}.

Definition db_connect : val := λ: "cs",
  impl.send "cs" (tag (Tag db_connect_N) (TInt 0)).

Lemma wp_db_connect skI skR rl cs db :
  {{{ connected skI skR rl cs db_st0 ∗
      (public (si_key cs) ∨ R db) }}}
    db_connect (repr cs)
  {{{ RET #(); connected skI skR rl cs (db_st auth db) }}}.
Proof.
iIntros (Φ) "(conn & HR) post".
wp_lam; wp_pures.
wp_bind (tag _ _). iApply wp_tag.
iApply (wp_send_msg _ _ _ _
          (iMsg_tag {[ db_connect_N :=
             (∃ db', MSG (TInt 0) {{ R db' }}; db_st auth db')%msg ]}) _
          (db_st auth db) with "[conn HR] post").
iSplitL "conn"; first by rewrite /db_st0 /iProto_tag.
iSplitR; first by rewrite public_tag public_TInt.
iDestruct "HR" as "[#fail|HR]"; first by iLeft.
iRight.
iApply (iMsg_tag_intro _ _ (lookup_singleton _ _)).
rewrite iMsg_exist_eq /=. iExists db.
rewrite iMsg_base_eq /=.
iSplit; first done.
iSplitR "HR"; first by auto.
iExact "HR".
Qed.

(** Connecting from an allocated-but-fresh client: the [R db]-payload picks
    [db := ∅], matching the freshly allocated authority. *)
Lemma wp_db_connect_fresh skI skR rl cs :
  {{{ connected skI skR rl cs db_st0 ∗
      DB.db_state skI skR dbtN ∅ ∗
      (public (si_key cs) ∨ R ∅) }}}
    db_connect (repr cs)
  {{{ RET #(); db_client_connected skI skR rl cs }}}.
Proof.
iIntros (Φ) "(conn & state & HR) post".
wp_apply (wp_db_connect with "[$conn $HR]").
iIntros "conn". iApply "post". iExists ∅. iFrame.
Qed.

End DBClient.
