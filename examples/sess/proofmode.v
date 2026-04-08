(** This file contains the definitions of Actris's tactics for symbolic
execution of message-passing programs. The API of these tactics is documented
in the [README.md] file. The implementation follows the same pattern for the
implementation of these tactics that is used in Iris. In addition, it uses a
standard pattern using type classes to perform the normalization.

In addition to the tactics for symbolic execution, this file defines the tactic
[solve_proto_contractive], which can be used to automatically prove that
recursive protocols are contractive. *)
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.heap_lang Require Export proofmode notation.
From actris Require Export channel.


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
From cryptis.examples.sess Require Import proofs.
From actris.channel Require Import proto_model proto.
From iris.heap_lang Require Import lib.spin_lock.
From iris.bi Require Import telescopes.

From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.heap_lang Require Export proofmode notation.

Notation iProto Σ := (iProto Σ term).
Notation iMsg Σ := (iMsg Σ term).

(** * Tactics for proving contractiveness of protocols *)
Ltac f_dist_le :=
  match goal with
  | H : _ ≡{?n}≡ _ |- _ ≡{?n'}≡ _ => apply (dist_le n); [apply H|lia]
  end.

Ltac solve_proto_contractive :=
  solve_proper_core ltac:(fun _ =>
    first [f_contractive; simpl in * | f_equiv | f_dist_le]).

(** * Normalization of protocols *)
Class ActionDualIf (d : bool) (a1 a2 : action) :=
  dual_action_if : a2 = if d then action_dual a1 else a1.
Global Hint Mode ActionDualIf ! ! - : typeclass_instances.

Global Instance action_dual_if_false a : ActionDualIf false a a := eq_refl.
Global Instance action_dual_if_true_send : ActionDualIf true Send Recv := eq_refl.
Global Instance action_dual_if_true_recv : ActionDualIf true Recv Send := eq_refl.

Class ProtoNormalize {Σ} (d : bool) (p : iProto Σ)
    (pas : list (bool * iProto Σ)) (q : iProto Σ) :=
  proto_normalize :
    ⊢ iProto_dual_if d p <++>
        foldr (iProto_app ∘ uncurry iProto_dual_if) END%proto pas ⊑ q.
Global Hint Mode ProtoNormalize ! ! ! ! - : typeclass_instances.
Arguments ProtoNormalize {_} _ _%_proto _%_proto _%_proto.

Notation ProtoUnfold p1 p2 := (∀ d pas q,
  ProtoNormalize d p2 pas q → ProtoNormalize d p1 pas q).

Class MsgNormalize {Σ} (d : bool) (m1 : iMsg Σ)
    (pas : list (bool * iProto Σ)) (m2 : iMsg Σ) :=
  msg_normalize a :
    ProtoNormalize d (<a> m1) pas (<(if d then action_dual a else a)> m2).
Global Hint Mode MsgNormalize ! ! ! ! - : typeclass_instances.
Arguments MsgNormalize {_} _ _%_msg _%_msg _%_msg.

Section classes.
  Context `{!heapGS Σ, !cryptisGS Σ, Conn : !GenConn.connGS Σ, !sessG Σ}.
  Implicit Types TT : tele.
  Implicit Types p : iProto Σ.
  Implicit Types m : iMsg Σ.
  Implicit Types P : iProp Σ.

  Lemma proto_unfold_eq p1 p2 : p1 ≡ p2 → ProtoUnfold p1 p2.
  Proof. rewrite /ProtoNormalize=> Hp d pas q. by rewrite Hp. Qed.

  Global Instance proto_normalize_done p : ProtoNormalize false p [] p | 0.
  Proof. rewrite /ProtoNormalize /= right_id. auto. Qed.
  Global Instance proto_normalize_done_dual p :
    ProtoNormalize true p [] (iProto_dual p) | 0.
  Proof. rewrite /ProtoNormalize /= right_id. auto. Qed.
  Global Instance proto_normalize_done_dual_end :
    ProtoNormalize (Σ:=Σ) true END [] END | 0.
  Proof. rewrite /ProtoNormalize /= right_id iProto_dual_end. auto. Qed.

  Global Instance proto_normalize_dual d p pas q :
    ProtoNormalize (negb d) p pas q →
    ProtoNormalize d (iProto_dual p) pas q.
  Proof. rewrite /ProtoNormalize. by destruct d; rewrite /= ?involutive. Qed.

  Global Instance proto_normalize_app_l d p1 p2 pas q :
    ProtoNormalize d p1 ((d,p2) :: pas) q →
    ProtoNormalize d (p1 <++> p2) pas q.
  Proof.
    rewrite /ProtoNormalize /=. rewrite assoc.
    by destruct d; by rewrite /= ?iProto_dual_app.
  Qed.

  Global Instance proto_normalize_end d d' p pas q :
    ProtoNormalize d p pas q →
    ProtoNormalize d' END ((d,p) :: pas) q | 0.
  Proof.
    rewrite /ProtoNormalize /=.
    destruct d'; by rewrite /= ?iProto_dual_end left_id.
  Qed.

  Global Instance proto_normalize_app_r d p1 p2 pas q :
    ProtoNormalize d p2 pas q →
    ProtoNormalize false p1 ((d,p2) :: pas) (p1 <++> q) | 0.
  Proof. rewrite /ProtoNormalize /= => H. by iApply iProto_le_app. Qed.

  Global Instance proto_normalize_app_r_dual d p1 p2 pas q :
    ProtoNormalize d p2 pas q →
    ProtoNormalize true p1 ((d,p2) :: pas) (iProto_dual p1 <++> q) | 0.
  Proof. rewrite /ProtoNormalize /= => H. by iApply iProto_le_app. Qed.

  Global Instance msg_normalize_base d v P p q pas :
    ProtoNormalize d p pas q →
    MsgNormalize d (MSG v {{ P }}; p) pas (MSG v {{ P }}; q).
  Proof.
    rewrite /MsgNormalize /ProtoNormalize=> H a.
    iApply iProto_le_trans; [|by iApply iProto_le_base].
    destruct d; by rewrite /= ?iProto_dual_message ?iMsg_dual_base
      iProto_app_message iMsg_app_base.
  Qed.

  Global Instance msg_normalize_exist {A} d (m1 m2 : A → iMsg Σ) pas :
    (∀ x, MsgNormalize d (m1 x) pas (m2 x)) →
    MsgNormalize d (∃ x, m1 x) pas (∃ x, m2 x).
  Proof.
    rewrite /MsgNormalize /ProtoNormalize=> H a.
    destruct d, a; simpl in *; rewrite ?iProto_dual_message ?iMsg_dual_exist
      ?iProto_app_message ?iMsg_app_exist /=; iIntros (x); iExists x; first
      [move: (H x Send); by rewrite ?iProto_dual_message ?iProto_app_message
      |move: (H x Recv); by rewrite ?iProto_dual_message ?iProto_app_message].
  Qed.

  Global Instance proto_normalize_message d a1 a2 m1 m2 pas :
    ActionDualIf d a1 a2 →
    MsgNormalize d m1 pas m2 →
    ProtoNormalize d (<a1> m1) pas (<a2> m2).
  Proof. by rewrite /ActionDualIf /MsgNormalize /ProtoNormalize=> ->. Qed.

  Global Instance proto_normalize_swap {TT1 TT2} d a m m'
      (tv1 : TT1 -t> term) (tP1 : TT1 -t> iProp Σ) (tm1 : TT1 -t> iMsg Σ)
      (tv2 : TT2 -t> term) (tP2 : TT2 -t> iProp Σ)
      (tp : TT1 -t> TT2 -t> iProto Σ) pas :
    ActionDualIf d a Recv →
    MsgNormalize d m pas m' →
    MsgTele m' tv1 tP1 (tele_bind (λ.. x1, <!> tele_app tm1 x1))%proto →
    (∀.. x1, MsgTele (tele_app tm1 x1) tv2 tP2 (tele_app tp x1)) →
    ProtoNormalize d (<a> m) pas (<!.. x2> MSG tele_app tv2 x2 {{ tele_app tP2 x2 }};
                                  <?.. x1> MSG tele_app tv1 x1 {{ tele_app tP1 x1 }};
                                  tele_app (tele_app tp x1) x2) | 1.
  Proof.
    rewrite /ActionDualIf /MsgNormalize /ProtoNormalize /MsgTele.
    rewrite tforall_forall=> Ha Hm Hm' Hm''.
    iApply iProto_le_trans; [iApply Hm|]. rewrite Hm' -Ha. clear Ha Hm Hm'.
    iApply iProto_le_texist_elim_l; iIntros (x1).
    iApply iProto_le_texist_elim_r; iIntros (x2).
    rewrite !tele_app_bind Hm'' {Hm''}.
    iApply iProto_le_trans;
      [iApply iProto_le_base; iApply (iProto_le_texist_intro_l _ x2)|].
    iApply iProto_le_trans;
      [|iApply iProto_le_base; iApply (iProto_le_texist_intro_r _ x1)]; simpl.
    iApply iProto_le_base_swap.
  Qed.

  (* TODO: Add iProto_choice to channel.v and bring this back *)
(*
  Global Instance proto_normalize_choice d a1 a2 P1 P2 p1 p2 q1 q2 pas :
    ActionDualIf d a1 a2 →
    ProtoNormalize d p1 pas q1 → ProtoNormalize d p2 pas q2 →
    ProtoNormalize d (iProto_choice a1 P1 P2 p1 p2) pas
                     (iProto_choice a2 P1 P2 q1 q2).
  Proof.
    rewrite /ActionDualIf /ProtoNormalize=> -> H1 H2. destruct d; simpl.
    - rewrite !iProto_dual_choice !iProto_app_choice.
      iApply iProto_le_choice; iSplit; by iIntros "$".
    - rewrite !iProto_app_choice. iApply iProto_le_choice; iSplit; by iIntros "$".
  Qed.
*)

  (** Automatically perform normalization of protocols in the proof mode when
  using [iAssumption] and [iFrame]. *)
  Global Instance connected_proto_from_assumption q skI skR rl cs p1 p2 :
    ProtoNormalize false p1 [] p2 →
    FromAssumption q (connected skI skR rl cs p1) (connected skI skR rl cs p2).
  Proof.
    rewrite /FromAssumption /ProtoNormalize /= right_id.
    rewrite bi.intuitionistically_if_elim.
    iIntros (?) "H". by iApply (connected_le with "H").
  Qed.
  Global Instance connected_proto_from_frame q skI skR rl cs p1 p2 :
    ProtoNormalize false p1 [] p2 →
    Frame q (connected skI skR rl cs p1) (connected skI skR rl cs p2) True.
  Proof.
    rewrite /Frame /ProtoNormalize /= right_id.
    rewrite bi.intuitionistically_if_elim.
    iIntros (?) "[H _]". by iApply (connected_le with "H").
  Qed.
End classes.

(** * Symbolic execution tactics *)
(* TODO: Maybe strip laters from other hypotheses in the future? *)
Lemma tac_wp_recv `{!heapGS Σ, !cryptisGS Σ, Conn: !GenConn.connGS Σ, !sessG Σ}
  Δ i j K skI skR rl cs p
  (tP tP' : term → iProp Σ) (tp : term → iProto Σ) Φ :
  envs_lookup i Δ = Some (false, connected skI skR rl cs p)%I →
  ProtoNormalize false p [] (<? t> MSG t {{ tP t }}; tp t) →
  (∀ t, MaybeIntoLaterN false 1 (tP t) (tP' t)) →
  let Δ' := envs_delete false i false Δ in
  (∀ t : term,
    match envs_app false
        (Esnoc (Esnoc Enil i (public t))
               j (connected skI skR rl cs (tp t) ∗
                  (public (si_key cs) ∨ tP' t))%I) Δ' with
    | Some Δ'' => envs_entails Δ'' (WP fill K (of_val (repr t)) {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (impl.recv (repr cs)) {{ Φ }}).
Proof.
  rewrite envs_entails_unseal /ProtoNormalize /MaybeIntoLaterN /= right_id.
  intros ? Hp HP HΦ. rewrite envs_lookup_sound //; simpl.
  assert (connected skI skR rl cs p ⊢
    connected skI skR rl cs (<? t> MSG t {{ ▷ tP' t }}; tp t)) as ->.
  { iIntros "Hc". iApply (connected_le with "Hc"). iIntros "!>".
    iApply iProto_le_trans; [iApply Hp|].
    iApply iProto_le_exist_elim_l; iIntros (t).
    iApply iProto_le_trans; [|iApply (iProto_le_exist_intro_r _ t)]; simpl.
    iIntros "H". by iDestruct (HP t with "H") as "$". }
  rewrite -wp_bind.
  eapply bi.wand_apply.
  - eapply bi.wand_entails.
    eapply (wp_recv_term skI skR rl cs tP' tp).
  - f_equiv. rewrite -bi.later_intro; apply bi.forall_intro=> t.
    specialize (HΦ t). destruct (envs_app _ _) as [Δ'|] eqn:HΔ'=> //.
    rewrite envs_app_sound //; simpl.
    rewrite right_id HΦ.
    iIntros "h1 (hpub & hrest)".
    iApply "h1". iFrame.
Qed.

Tactic Notation "wp_recv_core" tactic3(tac_intros) "as" tactic3(tac) :=
  let solve_pointsto _ :=
    let c := match goal with |- _ = Some (_, (connected _ _ _ ?c _)%I) => c end in
    iAssumptionCore || fail "wp_recv: cannot find" c "↣ ? @ ?" in
  wp_pures;
  let Hnew := iFresh in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_recv _ _ Hnew K))
      |fail 1 "wp_recv: cannot find 'recv' in" e];
    [solve_pointsto ()
       |tc_solve || fail 1 "wp_recv: protocol not of the shape <?>"
    |tc_solve || fail 1 "wp_recv: cannot convert to telescope"
    |pm_reduce; simpl; tac_intros;
     tac Hnew;
     wp_finish]
  | _ => fail "wp_recv: not a 'wp'"
  end.

Tactic Notation "wp_recv" "as" constr(pat) :=
  wp_recv_core (idtac) as (fun H => iDestructHyp H as pat).

Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as"
    "(" ne_simple_intropattern_list(ys) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => _iDestructHyp H ys pat).

Lemma tac_wp_send `{!heapGS Σ, !cryptisGS Σ, Conn: !GenConn.connGS Σ, !sessG Σ}
  {TT : tele} Δ neg i js K skI skR rl cs v p m tv tP tp Φ :
  envs_lookup i Δ = Some (false, connected skI skR rl cs p)%I →
  ProtoNormalize false p [] (<!> m) →
  MsgTele m tv tP tp →
  let Δ' := envs_delete false i false Δ in
  (∃.. x : TT,
    match envs_split (if neg is true then base.Right else base.Left) js Δ' with
    | Some (Δ1,Δ2) =>
       match envs_app false (Esnoc Enil i (connected skI skR rl cs (tele_app tp x))) Δ2 with
       | Some Δ2' =>
          v = tele_app tv x ∧
          envs_entails Δ (public (tele_app tv x)) ∧
          envs_entails Δ1 (tele_app tP x) ∧
          envs_entails Δ2' (WP fill K (of_val #()) {{ Φ }})
       | None => False
       end
    | None => False
    end) →
  envs_entails Δ (WP fill K (impl.send (repr cs) v) {{ Φ }}).
Proof.
  rewrite envs_entails_unseal /ProtoNormalize /MsgTele /= right_id texist_exist.
  intros ? Hp Hm [x HΦ].
  destruct (envs_split _ _ _) as [[Δ1 Δ2]|] eqn:? => //.
  destruct (envs_app _ _ _) as [Δ2'|] eqn:? => //.
  destruct HΦ as (-> & Hpub & HP & Hwp).
  apply (bi.wand_apply (of_envs Δ) (public (tele_app tv x))); last first.
  { by rewrite -bi.persistent_and_sep_1; apply bi.and_intro. }
  rewrite envs_lookup_sound //=.
  rewrite envs_split_sound //; rewrite (envs_app_sound Δ2) //; simpl.
  rewrite {}HP {}Hwp right_id assoc.
  assert (connected skI skR rl cs p ⊢
    connected skI skR rl cs (<!.. (x : TT)> MSG tele_app tv x {{ tele_app tP x }}; tele_app tp x)) as ->.
  { iIntros "Hc". iApply (connected_le with "Hc"); iIntros "!>".
    iApply iProto_le_trans; [iApply Hp|]. by rewrite Hm. }
  eapply bi.wand_intro_r.
  rewrite -assoc [(_ ∗ public _)%I]comm !assoc.
  rewrite -[(_ ∗ public _)%I]assoc -[(_ ∗ public _)%I]comm.
  eapply bi.wand_apply; [rewrite -wp_bind; by eapply bi.wand_entails, wp_send_tele|].
  by rewrite -bi.later_intro.
Qed.

Tactic Notation "wp_send_core" tactic3(tac_exist) "with" constr(pat) :=
  let solve_pointsto _ :=
    let cs := match goal with |- _ = Some (_, (connected _ _ _ ?cs _)%I) => cs end in
    iAssumptionCore || fail "wp_send: cannot find connected ? ? ?" cs "?" in
  let solve_done d :=
    lazymatch d with
    | true =>
       done ||
       let Q := match goal with |- envs_entails _ ?Q => Q end in
       fail "wp_send: cannot solve" Q "using done"
    | false => idtac
    end in
  lazymatch spec_pat.parse pat with
  | [SGoal (SpecGoal GSpatial ?neg ?Hs_frame ?Hs ?d)] =>
     let Hs' := eval cbv in (if neg then Hs else Hs_frame ++ Hs) in
     wp_pures;
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       first
         [reshape_expr e ltac:(fun K e' => eapply (tac_wp_send _ neg _ Hs' K))
         |fail 1 "wp_send: cannot find 'send' in" e];
       [solve_pointsto ()
       |tc_solve || fail 1 "wp_send: protocol not of the shape <!>"
       |tc_solve || fail 1 "wp_send: cannot convert to telescope"
       |pm_reduce; simpl; tac_exist;
        repeat lazymatch goal with
        | |- ∃ _, _ => eexists _
        end;
        lazymatch goal with
        | |- False => fail "wp_send:" Hs' "not found"
        | _ => notypeclasses refine (conj (eq_refl _) (conj _ (conj _ _)));
                [try done
                |iFrame Hs_frame; solve_done d
                |wp_finish]
        end]
     | _ => fail "wp_send: not a 'wp'"
     end
  | _ => fail "wp_send: only a single goal spec pattern supported"
  end.

Tactic Notation "wp_send" "with" constr(pat) :=
  wp_send_core (idtac) with pat.
Tactic Notation "wp_send" "(" ne_uconstr_list(xs) ")" "with" constr(pat) :=
  wp_send_core (ltac1_list_iter ltac:(fun x => eexists x) xs) with pat.

(* Lemma tac_wp_branch `{!heapGS Σ} Δ i j K *)
(*     c p P1 P2 (p1 p2 : iProto Σ) Φ : *)
(*   envs_lookup i Δ = Some (false, c ↣ p)%I → *)
(*   ProtoNormalize false p [] (p1 <{P1}&{P2}> p2) → *)
(*   let Δ' := envs_delete false i false Δ in *)
(*   (∀ b : bool, *)
(*     match envs_app false *)
(*         (Esnoc (Esnoc Enil j (if b then P1 else P2)) i (c ↣ (if b then p1 else p2))) Δ' with *)
(*     | Some Δ'' => envs_entails Δ'' (WP fill K (of_val #b) {{ Φ }}) *)
(*     | None => False *)
(*     end) → *)
(*   envs_entails Δ (WP fill K (recv c) {{ Φ }}). *)
(* Proof. *)
(*   rewrite envs_entails_unseal /ProtoNormalize /= right_id=> ? Hp HΦ. *)
(*   rewrite envs_lookup_sound //; simpl. *)
(*   rewrite (iProto_pointsto_le _ _ (p1 <{P1}&{P2}> p2)%proto) -bi.later_intro -Hp left_id. *)
(*   rewrite -wp_bind. eapply bi.wand_apply; [by eapply bi.wand_entails, branch_spec|f_equiv; first done]. *)
(*   rewrite -bi.later_intro; apply bi.forall_intro=> b. *)
(*   specialize (HΦ b). destruct (envs_app _ _) as [Δ'|] eqn:HΔ'=> //. *)
(*   rewrite envs_app_sound //; simpl. by rewrite right_id HΦ. *)
(* Qed. *)

(* Tactic Notation "wp_branch_core" "as" tactic3(tac1) tactic3(tac2) := *)
(*   let solve_pointsto _ := *)
(*     let c := match goal with |- _ = Some (_, (?c ↣ _)%I) => c end in *)
(*     iAssumptionCore || fail "wp_branch: cannot find" c "↣ ? @ ?" in *)
(*   wp_pures; *)
(*   let Hnew := iFresh in *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => eapply (tac_wp_branch _ _ Hnew K)) *)
(*       |fail 1 "wp_branch: cannot find 'recv' in" e]; *)
(*     [solve_pointsto () *)
(*        |tc_solve || fail 1 "wp_send: protocol not of the shape <&>" *)
(*     |pm_reduce; intros []; [tac1 Hnew|tac2 Hnew]; wp_finish] *)
(*   | _ => fail "wp_branch: not a 'wp'" *)
(*   end. *)

(* Tactic Notation "wp_branch" "as" constr(pat1) "|" constr(pat2) := *)
(*   wp_branch_core as (fun H => iDestructHyp H as pat1) (fun H => iDestructHyp H as pat2). *)
(* Tactic Notation "wp_branch" "as" "%" simple_intropattern(pat1) "|" constr(pat2) := *)
(*   wp_branch_core as (fun H => iPure H as pat1) (fun H => iDestructHyp H as pat2). *)
(* Tactic Notation "wp_branch" "as" constr(pat1) "|" "%" simple_intropattern(pat2) := *)
(*   wp_branch_core as (fun H => iDestructHyp H as pat1) (fun H => iPure H as pat2). *)
(* Tactic Notation "wp_branch" "as" "%" simple_intropattern(pat1) "|" "%" simple_intropattern(pat2) := *)
(*   wp_branch_core as (fun H => iPure H as pat1) (fun H => iPure H as pat2). *)
(* Tactic Notation "wp_branch" := wp_branch as % _ | % _. *)

(* Lemma tac_wp_select `{!heapGS Σ} Δ neg i js K *)
(*     c (b : bool) p P1 P2 (p1 p2 : iProto Σ) Φ : *)
(*   envs_lookup i Δ = Some (false, c ↣ p)%I → *)
(*   ProtoNormalize false p [] (p1 <{P1}+{P2}> p2) → *)
(*   let Δ' := envs_delete false i false Δ in *)
(*   match envs_split (if neg is true then base.Right else base.Left) js Δ' with *)
(*   | Some (Δ1,Δ2) => *)
(*      match envs_app false (Esnoc Enil i (c ↣ if b then p1 else p2)) Δ2 with *)
(*      | Some Δ2' => *)
(*         envs_entails Δ1 (if b then P1 else P2) ∧ *)
(*         envs_entails Δ2' (WP fill K (of_val #()) {{ Φ }}) *)
(*      | None => False *)
(*      end *)
(*   | None => False *)
(*   end → *)
(*   envs_entails Δ (WP fill K (send c #b) {{ Φ }}). *)
(* Proof. *)
(*   rewrite envs_entails_unseal /ProtoNormalize /= right_id=> ? Hp HΦ. *)
(*   rewrite envs_lookup_sound //; simpl. *)
(*   rewrite (iProto_pointsto_le _ _ (p1 <{P1}+{P2}> p2)%proto) -bi.later_intro -Hp left_id. *)
(*   rewrite -wp_bind. eapply bi.wand_apply; [by eapply bi.wand_entails, select_spec|]. *)
(*   rewrite -assoc; f_equiv; first done. *)
(*   destruct (envs_split _ _ _) as [[Δ1 Δ2]|] eqn:? => //. *)
(*   destruct (envs_app _ _ _) as [Δ2'|] eqn:? => //. *)
(*   rewrite envs_split_sound //; rewrite (envs_app_sound Δ2) //; simpl. *)
(*   destruct HΦ as [-> ->]. by rewrite -bi.later_intro right_id. *)
(* Qed. *)

(* Tactic Notation "wp_select" "with" constr(pat) := *)
(*   let solve_pointsto _ := *)
(*     let c := match goal with |- _ = Some (_, (?c ↣ _)%I) => c end in *)
(*     iAssumptionCore || fail "wp_select: cannot find" c "↣ ? @ ?" in *)
(*   let solve_done d := *)
(*     lazymatch d with *)
(*     | true => *)
(*        done || *)
(*        let Q := match goal with |- envs_entails _ ?Q => Q end in *)
(*        fail "wp_select: cannot solve" Q "using done" *)
(*     | false => idtac *)
(*     end in *)
(*   lazymatch spec_pat.parse pat with *)
(*   | [SGoal (SpecGoal GSpatial ?neg ?Hs_frame ?Hs ?d)] => *)
(*      let Hs' := eval cbv in (if neg then Hs else Hs_frame ++ Hs) in *)
(*      wp_pures; *)
(*      lazymatch goal with *)
(*      | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*        first *)
(*          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_select _ neg _ Hs' K)) *)
(*          |fail 1 "wp_select: cannot find 'send' in" e]; *)
(*        [solve_pointsto () *)
(*        |tc_solve || fail 1 "wp_select: protocol not of the shape <+>" *)
(*        |pm_reduce; *)
(*         lazymatch goal with *)
(*         | |- False => fail "wp_select:" Hs' "not fresh" *)
(*         | _ => notypeclasses refine (conj _ _); [iFrame Hs_frame; solve_done d|wp_finish] *)
(*         end] *)
(*      | _ => fail "wp_select: not a 'wp'" *)
(*      end *)
(*   | _ => fail "wp_select: only a single goal spec pattern supported" *)
(*   end. *)

(* Tactic Notation "wp_select" := wp_select with "[//]". *)

(* Tactic Notation "wp_new_chan" constr(prot) "as" *)
(*        "(" simple_intropattern(c1) simple_intropattern(c2) ")" constr(pat) := *)
(*   wp_smart_apply (new_chan_spec prot); [done|]; *)
(*   iIntros (c1); iIntros (c2); iIntros pat. *)

(* Tactic Notation "wp_fork_chan" constr(prot) "as" *)
(*        simple_intropattern(c1) constr(pat1) "and" *)
(*        simple_intropattern(c2) constr(pat2) := *)
(*   wp_smart_apply (fork_chan_spec prot); [iIntros (c2); iIntros pat2| *)
(*                                          iIntros (c1); iIntros pat1]. *)

(* Tactic Notation "wp_fork_chan" constr(prot) "as" *)
(*        simple_intropattern(c) constr(pat) := *)
(*   wp_fork_chan prot as c pat and c pat. *)

(* Tactic Notation "wp_fork_chan" constr(prot) := *)
(*   wp_fork_chan prot as ? "?". *)
