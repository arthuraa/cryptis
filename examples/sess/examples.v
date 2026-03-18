From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn sess.
(* From crypti *)
(* From cryptis.examples.sess Require impl. *)
(* From cryptis.examples.sess.proofs Require Import base. *)
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
  (<!> MSG  (TInt 42); END)%proto.


Definition send42_proto_dual : iProto Σ  :=
  (<?> MSG (TInt 42); END)%proto.


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
  wp_bind (impl.connect _ _ _ _).
  wp_apply (Sess.wp_connect with "[] [P]"); eauto 10.
  iIntros " % ( p1 & p2 & p3 )".


  wp_pures.
  wp_apply (Sess.wp_send with "[] [p1]"); eauto 10.
iIntros.
wp_seq.
iModIntro.
iApply "post".
by iFrame.
Qed.


Lemma send42_dual_equiv:

  iProto_dual send42_proto ≡ send42_proto_dual.
  Proof.
    unfold send42_proto_dual.
    Search iProto_dual.
   Search iMsg_dual.
    rewrite /send42_proto iProto_dual_message /= iMsg_dual_base  iProto_dual_end.
    reflexivity.
    Qed.

(* Lemma connected_send42_proper skI skR rl cs: *)


(* Lemma wp_responder_confirm . *)

  (* Lemma tac_wp_recv `{!chanG Σ, !heapGS Σ} {TT : tele} Δ i j K c p m tv tP tP' tp Φ : *)
  (* envs_lookup i Δ = Some (false, c ↣ p)%I → *)
  (* ProtoNormalize false p [] (<?> m) → *)
  (* MsgTele m tv tP tp → *)
  (* (∀.. x, MaybeIntoLaterN false 1 (tele_app tP x) (tele_app tP' x)) → *)
  (* let Δ' := envs_delete false i false Δ in *)
  (* (∀.. x : TT, *)
  (*   match envs_app false *)
  (*       (Esnoc (Esnoc Enil j (tele_app tP' x)) i (c ↣ tele_app tp x)) Δ' with *)
  (*   | Some Δ'' => envs_entails Δ'' (WP fill K (of_val (tele_app tv x)) {{ Φ }}) *)
  (*   | None => False *)
  (*   end) → *)
  (* envs_entails Δ (WP fill K (recv c) {{ Φ }}). *)
(* Lemma tac_wp_recv `{!chanG Σ, !heapGS Σ} {TT : tele} Δ i j K c p m tv tP tP' tp Φ : *)
(*   envs_lookup i Δ = Some (false, Sess.connected c p)%I → *)
(*   ProtoNormalize false p [] (<?> m) → *)
(*   MsgTele m tv tP tp → *)
(*   (∀.. x, MaybeIntoLaterN false 1 (tele_app tP x) (tele_app tP' x)) → *)
(*   let Δ' := envs_delete false i false Δ in *)
(*   (∀.. x : TT, *)
(*     match envs_app false *)
(*         (Esnoc (Esnoc Enil j (tele_app tP' x)) i ( connected c tele_app tp x)) Δ' with *)
(*     | Some Δ'' => envs_entails Δ'' (WP fill K (of_val (tele_app tv x)) {{ Φ }}) *)
(*     | None => False *)
(*     end) → *)
(*   envs_entails Δ (WP fill K (recv c) {{ Φ }}). *)


Lemma wp_responder_recv42 c skI skR N :
  channel c -∗
  cryptis_ctx -∗
  Sess.ctx N send42_proto -∗
  minted skI -∗
  minted skR -∗
  {{{ True }}}
    responder_recv42 c skR (Tag N)
  {{{ cs msg, RET (repr cs, msg);
      Sess.connected skI skR Resp cs END ∗
      release_token (si_resp_share cs) ∗
      (public (si_key cs) ∨ True) ∗
      ⌜msg = TInt 42⌝ }}}.

Proof.
  iIntros "#? #? #? #HskI #HskR % !> #P post".
  rewrite /responder_recv42.
  wp_lam.
    wp_pures.
    wp_bind (impl.listen _).
    wp_apply (Sess.wp_listen with "[] [P]"); eauto 10.
    (* iIntros. *)
    iIntros (ga skI0) "[#Hpub #Hmint]".
    wp_pures.
    wp_bind (impl.confirm _ _ _ _).
    wp_apply (Sess.wp_confirm True with "[] [P]"); eauto 10.
    (* iFrame " Hmint Hpub HskR". *)
    (* iRight. *)

    iIntros (cs) "[Hconn H']".
    wp_pures.
    wp_bind (impl.recv _).
    (* rewrite /send42_proto_dual /iProto_dual /=. *)

    Search iProto_dual.
    (* Search tele_unit. *)
    wp_apply (Sess.wp_recv
            (* (TT := tele_unit) *)
            (* (skI := skI0) (skR := skR) (rl := Resp) (cs := cs) *)
            (* (N := N) (p0 := send42_proto) *)
            (* (t := λ _, TInt 42) *)
            (* (P := λ _, True%I) *)
                (* _             (* TT *) *)
                (* _  *)
                (*  _ _ _ _ _ *)
                (TT := TeleO)
                skI0 skR Resp cs N send42_proto
                (* (fun _ => TInt 42) *)
                (tele_app _)
                (fun _ => True%I)
                (fun _ => END)
          with "[] [Hconn]"); eauto 10.
    (* wp_apply (Sess.wp_recv with "[] [Hconn]"); eauto 10. *)
    (* rewrite send42_proto iProto_dual_message. *)
    (* unfold send42_proto. *)
    simpl.
    Search iProto_dual.
    Existing Instance Sess.connected_proper.
    (* iEval (rewrite /base.connected; rewrite [iProto_dual send42_proto]helper) in "Hconn". *)
    (* rewrite /send42_proto  helper. *)
    (* rewrite /send42_proto iProto_dual_message . /= iMsg_dual_base  iProto_dual_end. *)
    (* rewrite helper in "Hconn". *)
    (* iAssert (base.connected skI0 skR Resp cs send42_proto_dual) with "[Hconn]" as "Hconn". *)
(* { rewrite -send42_dual_equiv. *)

    (* iEval (rewrite send42_dual_equiv) in "Hconn". *)
    rewrite send42_dual_equiv .
    unfold send42_proto_dual.
    (* iExact "Hconn". *)

    iApply "Hconn".
    iIntros (t') "Hh".
    wp_pures.
    iModIntro.
    iApply "post".
    iFrame.
    iAssert  (⌜skI0 = skI⌝)%I as "%Heq_skI".
    { admit. }
    subst skI0.
    iFrame.
(* iDes *)
    (* iIntros (t') "[Hpubt'  [H1 | [H2 H3 ]]] ". *)
    admit.

    wp_pures.
    iModIntro.
    iApply "post".
     iFrame.

    iSplitL "H3".
    { iDestruct "H3" as "[Hc Ht]". by iFrame. }
    iFrame.


Admitted.






End Send42Example.
