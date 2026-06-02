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

  (** Normalization through a [iProto_choice_term] node: push the dual/app
      into both branches.  This is the Cryptis analogue of Actris's
      [proto_normalize_choice]; with it, [iAssumption]/[iFrame]/[connected_le]
      automatically coerce [iProto_dual (choice Send …)] to [choice Recv …],
      so callers no longer need a hand-written dual-equivalence lemma. *)
  Global Instance proto_normalize_choice_term d a1 a2 P1 P2 p1 p2 q1 q2 pas :
    ActionDualIf d a1 a2 →
    ProtoNormalize d p1 pas q1 → ProtoNormalize d p2 pas q2 →
    ProtoNormalize d (iProto_choice_term a1 P1 P2 p1 p2) pas
                     (iProto_choice_term a2 P1 P2 q1 q2).
  Proof.
    rewrite /ActionDualIf /ProtoNormalize=> -> H1 H2. destruct d; simpl.
    - rewrite !iProto_dual_choice_term !iProto_app_choice_term.
      iApply iProto_le_choice_term; iSplit; by iIntros "$".
    - rewrite !iProto_app_choice_term.
      iApply iProto_le_choice_term; iSplit; by iIntros "$".
  Qed.

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

(** ** Tactics for select and branch

[tac_wp_select] / [tac_wp_branch] are the proof-mode glue for the proved
[wp_select] / [wp_branch] specs (proofs.v): they look up the [connected]
hypothesis automatically and normalise its protocol to a choice via
[ProtoNormalize], so the responder's [iProto_dual] is coerced transparently
(no hand-written dual-equivalence lemma). *)

Lemma tac_wp_select `{!heapGS Σ, !cryptisGS Σ, Conn: !GenConn.connGS Σ, !sessG Σ}
  Δ neg i js K skI skR rl cs (b : bool) P1 P2 p p1 p2 Φ :
  envs_lookup i Δ = Some (false, connected skI skR rl cs p)%I →
  ProtoNormalize false p [] (iProto_choice_term Send P1 P2 p1 p2) →
  let Δ' := envs_delete false i false Δ in
  match envs_split (if neg is true then base.Right else base.Left) js Δ' with
  | Some (Δ1, Δ2) =>
     match envs_app false
       (Esnoc Enil i (connected skI skR rl cs (if b then p1 else p2))) Δ2 with
     | Some Δ2' =>
        envs_entails Δ1 (public (si_key cs) ∨ if b then P1 else P2) ∧
        envs_entails Δ2' (WP fill K (of_val #()) {{ Φ }})
     | None => False
     end
  | None => False
  end →
  envs_entails Δ (WP fill K (impl.send (repr cs) (TInt (if b then 1 else 0))) {{ Φ }}).
Proof.
  rewrite envs_entails_unseal /ProtoNormalize /= right_id.
  intros Hlook Hp.
  destruct (envs_split _ _ _) as [[Δ1 Δ2]|] eqn:Hsplit => //.
  destruct (envs_app _ _ _) as [Δ2'|] eqn:Happ => //.
  intros [Hdisj Hwp].
  rewrite envs_lookup_sound //=. rewrite -wp_bind.
  iIntros "[Hc HΔ']".
  iDestruct (envs_split_sound _ _ _ _ _ Hsplit with "HΔ'") as "[HΔ1 HΔ2]".
  iApply (wp_select with "[Hc HΔ1]").
  - iSplitR "HΔ1".
    + iApply (connected_le with "Hc"). iNext. iApply Hp.
    + iApply Hdisj. iExact "HΔ1".
  - iIntros "!> Hcb".
    iDestruct (envs_app_sound _ _ _ _ Happ with "HΔ2") as "Hwand".
    iApply Hwp. iApply "Hwand". by iFrame "Hcb".
Qed.

Tactic Notation "wp_select_core" uconstr(b) "with" constr(pat) :=
  let solve_pointsto _ :=
    let cs := match goal with |- _ = Some (_, (connected _ _ _ ?cs _)%I) => cs end in
    iAssumptionCore || fail "wp_select: cannot find connected ? ? ?" cs "?" in
  lazymatch spec_pat.parse pat with
  | [SGoal (SpecGoal GSpatial ?neg ?Hs_frame ?Hs ?d)] =>
     let Hs' := eval cbv in (if neg then Hs else Hs_frame ++ Hs) in
     wp_pures;
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       first
         [reshape_expr e ltac:(fun K e' =>
            eapply (tac_wp_select _ neg _ Hs' K _ _ _ _ b))
         |fail 1 "wp_select: cannot find 'send' in" e];
       [solve_pointsto ()
       |tc_solve || fail 1 "wp_select: protocol not of the shape <+>"
       |pm_reduce;
        lazymatch goal with
        | |- False => fail "wp_select:" Hs' "not found"
        | _ => notypeclasses refine (conj _ _); [|wp_finish]
        end]
     | _ => fail "wp_select: not a 'wp'"
     end
  | _ => fail "wp_select: only a single goal spec pattern supported"
  end.

Tactic Notation "wp_select" uconstr(b) "with" constr(pat) :=
  wp_select_core b with pat.
Tactic Notation "wp_select" uconstr(b) :=
  wp_select_core b with "[]".

Lemma tac_wp_branch `{!heapGS Σ, !cryptisGS Σ, Conn: !GenConn.connGS Σ, !sessG Σ}
  Δ i j K skI skR rl cs p P1 P2 p1 p2 Φ :
  envs_lookup i Δ = Some (false, connected skI skR rl cs p)%I →
  ProtoNormalize false p [] (iProto_choice_term Recv P1 P2 p1 p2) →
  let Δ' := envs_delete false i false Δ in
  (∀ t : term,
    let b := bool_decide (t = TInt 1) in
    match envs_app false
        (Esnoc Enil j (connected skI skR rl cs (if b then p1 else p2) ∗
                       (public (si_key cs) ∨ if b then P1 else P2))) Δ' with
    | Some Δ'' => envs_entails Δ'' (WP fill K (of_val (repr t)) {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (impl.recv (repr cs)) {{ Φ }}).
Proof.
  rewrite envs_entails_unseal /ProtoNormalize /= right_id.
  intros Hlook Hp Hcont.
  rewrite envs_lookup_sound //=.
  rewrite -wp_bind.
  iIntros "(Hc & HΔ')".
  iApply (wp_branch with "[Hc]").
  { iApply (connected_le with "Hc"). iNext. iApply Hp. }
  iIntros "!> %t Hpost".
  specialize (Hcont t). simpl in Hcont.
  destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'' => //.
  iDestruct (envs_app_sound _ _ _ _ HΔ'' with "HΔ'") as "Hwand".
  iApply Hcont. iApply "Hwand". by iFrame "Hpost".
Qed.

Tactic Notation "wp_branch_core" tactic3(tac_intros) "as" tactic3(tac) :=
  let solve_pointsto _ :=
    let c := match goal with |- _ = Some (_, (connected _ _ _ ?c _)%I) => c end in
    iAssumptionCore || fail "wp_branch: cannot find connected for" c in
  wp_pures;
  let Hnew := iFresh in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_branch _ _ Hnew K))
      |fail 1 "wp_branch: cannot find 'recv' in" e];
    [solve_pointsto ()
    |tc_solve || fail 1 "wp_branch: protocol not of the shape <&>"
    |pm_reduce; simpl; tac_intros; tac Hnew; wp_finish]
  | _ => fail "wp_branch: not a 'wp'"
  end.

Tactic Notation "wp_branch" "(" simple_intropattern_list(xs) ")" "as" constr(pat) :=
  wp_branch_core (intros xs) as (fun H => iDestructHyp H as pat).
Tactic Notation "wp_branch" "as" constr(pat) :=
  wp_branch_core (idtac) as (fun H => iDestructHyp H as pat).
