From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn sess.
From cryptis.examples.sess Require Import proofmode trusted.
From actris.channel Require Import proto_model proto.
From iris.heap_lang Require Import lib.spin_lock.
From iris.bi Require Import telescopes.

From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.heap_lang Require Import proofmode notation.
From cryptis.examples Require Import proofmode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Send42Example.
Implicit Types skI skR pkI pkR : sign_key.
Implicit Types N : namespace.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ, !Sess.sessG Σ}.
(* Notation iProp := (iProp Σ). *)

Definition send42_proto : iProto Σ  :=
  (<! t> MSG t {{ ⌜t = TInt 42⌝ }}; END)%proto.

Definition send42_proto_dual : iProto Σ  :=
  (<? t> MSG t {{ ⌜t = TInt 42⌝ }}; END)%proto.


Definition initiator_send42 : val :=
  λ: "c" "skI" "pkR" "tagN",
    let: "cs" := Sess.connect "c" "skI" "pkR" "tagN" in
    Sess.send "cs" (TInt 42);;
    "cs".

Definition responder_recv42 : val :=
  λ: "c" "skR" "tagN",
    let: "req" := Sess.listen "c" in
    let: "cs" := Sess.confirm "c" "skR" "tagN" "req" in
    let: "msg" := Sess.recv "cs" in
    ("cs", "msg").

Lemma wp_initiator_send42 c skI skR N :
  channel c -∗
  cryptis_ctx -∗
  Sess.ctx N send42_proto -∗
  minted skI -∗
  minted skR -∗
  {{{ GenConn.failure skI skR ∨ True }}}
    initiator_send42 c skI (Spec.pkey skR) (Tag N)
  {{{ cs, RET (repr cs);
      Sess.connected skI skR Init cs END ∗
      release_token (si_init_share cs) ∗
      (public (si_key cs) ∨ True) }}}.
Proof.
  iIntros "#? #? #? #? #? % !> #P post".
  rewrite /initiator_send42.
  wp_lam.
  wp_pures.
  wp_apply (Sess.wp_connect with "[] [P]"); eauto 10.
  iIntros " % ( p1 & p2 & #p3 )".
  wp_send with "[//]".
  - by rewrite public_TInt.
  - wp_pures. iApply "post". by iFrame.
Qed.

Lemma send42_dual_equiv:
  iProto_dual send42_proto ≡ send42_proto_dual.
Proof.
  rewrite /send42_proto /send42_proto_dual.
  rewrite iProto_dual_message. f_equiv.
  rewrite iMsg_dual_exist.
  setoid_rewrite iMsg_dual_base.
  by setoid_rewrite iProto_dual_end.
Qed.

Lemma wp_responder_recv42 c skR N :
  channel c -∗
  cryptis_ctx -∗
  Sess.ctx N send42_proto -∗
  minted skR -∗
  {{{ True }}}
    responder_recv42 c skR (Tag N)
  {{{ cs msg skI, RET (repr cs, msg)%V;
      minted skI ∗
      Sess.connected skI skR Resp cs END ∗
      public msg ∗
      (public (si_key cs) ∨ ⌜msg = TInt 42⌝) }}}.
Proof.
  iIntros "#Hch #Hctx #Hsess #HskR !> %Φ _ post".
  rewrite /responder_recv42. wp_lam. wp_pures.
  wp_apply (Sess.wp_listen with "[] []") ; [done|done|done|].
  iIntros (ga skI) "[#Hpub #HskI]".
  wp_pures.
  wp_apply (Sess.wp_confirm True with "[] []"); try iFrame; eauto 10.
  iIntros (cs) "[Hconn _]".
  wp_pures.
  wp_recv (t) as "[Hconn' Hdisj']".
  wp_pures. iModIntro.
  iApply ("post" $! cs t skI).
  iFrame "HskI". iFrame.
Qed.
End Send42Example.


Section TrustedSend42Example.
Implicit Types skI skR pkI pkR : sign_key.
Implicit Types N : namespace.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ, !Sess.sessG Σ}.
(* Notation iProp := (iProp Σ). *)

Definition trusted_send42_proto : iProto Σ :=
  (<!> MSG (TInt 42); END)%proto.


Definition trusted_initiator_send42 : val :=
  λ: "c" "skI" "pkR" "tagN",
    let: "cs" := Sess.connect "c" "skI" "pkR" "tagN" in
    Sess.send "cs" (TInt 42);;
    "cs".

Definition trusted_responder_recv42 : val :=
  λ: "c" "skR" "tagN",
    let: "req" := Sess.listen "c" in
    let: "cs" := Sess.confirm "c" "skR" "tagN" "req" in
    let: "msg" := Sess.recv "cs" in
    ("cs", "msg").

Lemma trusted_wp_initiator_send42 c skI skR N :
  channel c -∗
  cryptis_ctx -∗
  Sess.ctx N trusted_send42_proto -∗
  minted skI -∗
  minted skR -∗
  □ (public skI → ▷ False) -∗
  □ (public skR → ▷ False) -∗
  {{{ True }}}
    trusted_initiator_send42 c skI (Spec.pkey skR) (Tag N)
  {{{ cs, RET (repr cs);
      trusted_connected skI skR Init cs END }}}.
Proof.
  iIntros "#? #? #? #? #? #? #? %Φ !> _ post".
  rewrite /trusted_initiator_send42. wp_lam. wp_pures.
  wp_apply (trusted_wp_connect with "[]"); eauto 10.
  iIntros "%cs tc". wp_pures.
  iAssert (public (TInt 42)) as "#p42". { by rewrite public_TInt. }
  wp_apply (trusted_wp_send with "[$tc $p42]").
  iIntros "tc". wp_pures. iApply "post". iFrame. done.
Qed.

Lemma trusted_wp_responder_recv42 c skR N :
  channel c -∗
  cryptis_ctx -∗
  Sess.ctx N trusted_send42_proto -∗
  minted skR -∗
  □ (public skR → ▷ False) -∗
  □ (∀ skI, minted skI -∗ □ (public skI → ▷ False)) -∗
  {{{ True }}}
    trusted_responder_recv42 c skR (Tag N)
  {{{ cs msg skI, RET (repr cs, msg)%V;
      minted skI ∗
      trusted_connected skI skR Resp cs END ∗
      ⌜msg = repr (TInt 42)⌝ }}}.
Proof.
  iIntros "#? #? #? #? #? #Hpki %Φ !> _ post".
  rewrite /trusted_responder_recv42. wp_lam. wp_pures.
  wp_apply (Sess.wp_listen with "[]"); [done|done|done|].
  iIntros (ga skI) "[#Hpub #HskI]".
  iDestruct ("Hpki" $! skI with "HskI") as "#HhonI".
  wp_pures.
  wp_apply (trusted_wp_confirm with "[]"); eauto 10.
  iIntros (cs) "tc". wp_pures.
  iEval (rewrite /trusted_send42_proto iProto_dual_message iMsg_dual_base
                 iProto_dual_end /action_dual) in "tc".
  wp_apply (trusted_wp_recv_base with "tc").
  iIntros "(#p_t & tc2)". wp_pures. iModIntro.
  iApply ("post" $! cs (repr (TInt 42)) skI).
  iFrame "HskI tc2". done.
Qed.
End TrustedSend42Example.
