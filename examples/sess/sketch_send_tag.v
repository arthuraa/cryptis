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
From actris.channel Require Import proto_model proto.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SketchSendTag.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ, !sessG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).

Lemma sess_send_msg skI skR si rl (m : iMsg Σ term) t p ts_send ts_recv :
  sess_own skI skR si rl (<!> m) -∗
  iMsg_car m t (Next p) -∗
  ▷ GenConn.chan_inv_for sess_ctx skI skR si rl ts_send ts_recv
  ={⊤ ∖ ↑GenConn.connN, ∅}=∗ |={∅}▷=>^(S (length ts_recv)) |={∅, ⊤ ∖ ↑GenConn.connN}=>
    GenConn.chan_inv_for sess_ctx skI skR si rl (ts_send ++ [t]) ts_recv ∗
    sess_own skI skR si rl p.
Proof.
Admitted.

Lemma wp_send_msg skI skR rl cs (m : iMsg Σ term) t p :
  {{{ connected skI skR rl cs (<!> m) ∗
      public t ∗
      (public (si_key cs) ∨ iMsg_car m t (Next p)) }}}
    impl.send (repr cs) t
  {{{ RET #(); connected skI skR rl cs p }}}.
Proof.
Admitted.

Lemma iMsg_tag_intro (ms : gmap namespace (iMsg Σ term)) N m t' pp :
  ms !! N = Some m →
  iMsg_car m t' pp -∗ iMsg_car (iMsg_tag ms) (Spec.tag (Tag N) t') pp.
Proof.
Admitted.

Lemma wp_send_tag {TT : tele} skI skR rl cs
    (ms : gmap namespace (iMsg Σ term)) N
    (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) (x : TT) :
  ms !! N = Some (∃.. y, MSG t y {{ P y }}; p y)%msg →
  {{{ connected skI skR rl cs (iProto_tag Send ms) ∗
      public (t x) ∗
      (public (si_key cs) ∨ P x) }}}
    impl.send (repr cs) (Spec.tag (Tag N) (t x))
  {{{ RET #(); connected skI skR rl cs (p x) }}}.
Proof.
Admitted.

Lemma iMsg_dual_tag (ms : gmap namespace (iMsg Σ term)) :
  iMsg_dual (iMsg_tag ms) ≡ iMsg_tag (iMsg_dual <$> ms).
Proof.
Admitted.

Lemma iMsg_app_tag (ms : gmap namespace (iMsg Σ term)) (q : iProto Σ term) :
  (iMsg_tag ms <++> q)%msg ≡ iMsg_tag ((λ m, (m <++> q)%msg) <$> ms).
Proof.
Admitted.

Lemma iProto_dual_tag (a : action) (ms : gmap namespace (iMsg Σ term)) :
  iProto_dual (iProto_tag a ms)
  ≡ iProto_tag (action_dual a) (iMsg_dual <$> ms).
Proof.
Admitted.

Lemma iProto_app_tag (a : action) (ms : gmap namespace (iMsg Σ term))
    (q : iProto Σ term) :
  (iProto_tag a ms <++> q)%proto
  ≡ iProto_tag a ((λ m, (m <++> q)%msg) <$> ms).
Proof.
Admitted.

Lemma iMsg_tag_proper :
  Proper ((≡) ==> (≡)) (iMsg_tag (Σ:=Σ)).
Proof.
Admitted.

End SketchSendTag.
