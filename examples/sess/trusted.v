From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn sess.
From actris.channel Require Import proto_model proto.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Trusted.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ, !Sess.sessG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types v : val.

(** * Trusted connected

A wrapper around [Sess.connected] that additionally asserts that the session
key can never become public.  When both parties are permanently honest (i.e.,
their signing keys satisfy [□ (public sk → ▷ False)]), the session key inherits
this property via the iso-DH handshake.  The honesty hypothesis uses [False]
(not [▷ False]) so that the adversary branch can be eliminated in any context,
not just under a WP.  The [▷] from the key secrecy chain is consumed inside the
(admitted) connect/confirm proofs, which run in WP context. *)

Definition trusted_connected skI skR rl cs p : iProp :=
  Sess.connected skI skR rl cs p ∗
  □ (public (si_key cs) →  ▷ False).

Global Instance trusted_connected_proper skI skR rl cs :
  Proper ((≡) ==> (≡)) (trusted_connected skI skR rl cs).
Proof. solve_proper. Qed.

Lemma trusted_connected_connected skI skR rl cs p :
  trusted_connected skI skR rl cs p -∗
  Sess.connected skI skR rl cs p.
Proof. rewrite /trusted_connected. by iIntros "[$ _]". Qed.

Lemma trusted_connected_honest skI skR rl cs p :
  trusted_connected skI skR rl cs p -∗
  □ (public (si_key cs) →  ▷  False).
Proof. rewrite /trusted_connected. by iIntros "[_ #$]". Qed.

Lemma trusted_connected_le skI skR rl cs p1 p2 :
  trusted_connected skI skR rl cs p1 ⊢
  ▷ (p1 ⊑ p2) -∗ trusted_connected skI skR rl cs p2.
Proof.
rewrite /trusted_connected.
iIntros "[conn #hon] le".
iFrame "hon". by iApply (Sess.connected_le with "conn le").
Qed.

(** ** Send *)

Lemma trusted_wp_send skI skR rl cs (t : term) p :
  {{{ trusted_connected skI skR rl cs (<!> MSG t; p) ∗ public t }}}
    Sess.send (repr cs) t
  {{{ RET #(); trusted_connected skI skR rl cs p }}}.
Proof.
iIntros (Φ) "[tc #p_t] post".
iDestruct "tc" as "[conn #hon]".
iApply (Sess.wp_send with "[$conn $p_t]").
iIntros "!> conn". iApply "post".
rewrite /trusted_connected. iFrame "conn hon".
Qed.

Lemma trusted_wp_send_tele {TT : tele} skI skR rl cs (tt : TT)
    (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) :
  {{{ trusted_connected skI skR rl cs (<!.. x> MSG t x {{ P x }}; p x) ∗
      public (t tt) ∗ P tt }}}
    Sess.send (repr cs) (t tt)
  {{{ RET #(); trusted_connected skI skR rl cs (p tt) }}}.
Proof.
iIntros (Φ) "(tc & #p_t & HP) post".
iDestruct "tc" as "[conn #hon]".
iApply (Sess.wp_send_tele with "[$conn $p_t $HP]").
iIntros "!> conn". iApply "post".
rewrite /trusted_connected. iFrame "conn hon".
Qed.

(** ** Recv

The key advantage: no disjunction in the postcondition.  The adversary branch
is eliminated by the honesty hypothesis carried in [trusted_connected]. *)

Lemma trusted_wp_recv {TT : tele} skI skR rl cs
  (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) :
  {{{ trusted_connected skI skR rl cs (<?.. x> MSG t x {{ ▷ P x }}; p x) }}}
    Sess.recv (repr cs) 
  {{{ x , RET (repr (t x)); public (t x) ∗
     trusted_connected skI skR rl cs (p x) ∗ P x }}}.
Proof.
iIntros (Φ) "tc post".
iDestruct "tc" as "[conn #hon]".
(* wp_pure _ credit: "c". *)
(* wp_pures. *)
iApply (wp_fupd).
iApply (Sess.wp_recv with "conn").
iIntros "!> %t' (p_t' & [fail | inv])".
- iMod ("hon" with "fail") as "[]". 
-
  iDestruct "inv" as (x) "(-> & conn & Px)".
  iApply "post". iFrame "p_t'".
  iFrame "Px".
  (* iSplit => //. *)
  rewrite /trusted_connected. iFrame "conn hon".
  auto.
Qed.

(* Lemma trusted_wp_recv_term skI skR rl cs *)
(*   (P : term → iProp) (p : term → iProto Σ term) : *)
(*   {{{ trusted_connected skI skR rl cs (<? t> MSG t {{ ▷ P t }}; p t) }}} *)
(*     Sess.recv (repr cs) *)
(*   {{{ t, RET (repr t); public t ∗ *)
(*       trusted_connected skI skR rl cs (p t) ∗ P t }}}. *)
(* Proof. *)
(* iIntros (Φ) "tc post". *)
(* iDestruct "tc" as "[conn #hon]". *)
(* iApply (Sess.wp_recv_term with "conn"). *)
(* iIntros "!> %t (p_t & conn & [fail | Pt])". *)
(* - iExFalso. by iApply "hon". *)
(* - iApply "post". iFrame "p_t". iFrame "Pt". *)
(*   rewrite /trusted_connected. iFrame "conn hon". *)
(* Qed. *)

(** ** Connect and confirm

The hypothesis [□ (public skI → ▷ False)] for both keys flows to
[□ (public (si_key cs) → False)] through the iso-DH key secrecy chain:
  1. [freeze_secret] gives [□ (public sk ↔ ▷ False)] from [secret sk]
  2. [secret_session] gives [session_ok si] from both keys being secret
  3. [unreleased_key_secrecy] gives [□ (public (si_key si) ↔ ▷ False)]
     from [session_ok si] and [□ (¬ released_session si)]
The [▷] is eliminated using a later credit from the WP context of the
connect/confirm operations themselves. *)

Lemma trusted_wp_connect N p c skI skR :
  channel c -∗
  cryptis_ctx -∗
  Sess.ctx N p -∗
  minted skI -∗
  minted skR -∗
  □ (public skI → ▷ False) -∗
  □ (public skR → ▷ False) -∗
  {{{ GenConn.failure skI skR ∨ True }}}
    Sess.connect c skI (Spec.pkey skR) (Tag N)
  {{{ cs, RET (repr cs);
      trusted_connected skI skR Init cs p ∗
      release_token (si_init_share cs) }}}.
Proof.
Admitted.

Lemma trusted_wp_confirm N p c skI skR ga :
  channel c -∗
  cryptis_ctx -∗
  Sess.ctx N p -∗
  minted skI -∗
  minted skR -∗
  □ (public skI → ▷ False) -∗
  □ (public skR → ▷ False) -∗
  {{{ public ga ∗ minted skI ∗ minted skR ∗
      (GenConn.failure skI skR ∨ True) }}}
    Sess.confirm c skR (Tag N) (ga, Spec.pkey skI)%V
  {{{ cs, RET (repr cs);
      trusted_connected skI skR Resp cs (iProto_dual p) }}}.
Proof.
Admitted.

End Trusted.
