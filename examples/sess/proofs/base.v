From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces coGset.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import ticket_lock.
From cryptis Require Import lib term gmeta nown saved_prop.
From cryptis Require Import cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn.
From actris.channel Require Import proto_model proto.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation sessN := (iso_dhN.@"res".@"sess").

Definition savedProtoR Σ V :=
  agreeR (laterO (iProto Σ V)).

Definition savedProtoΣ V := #[
  GFunctor (agreeRF (laterOF (protoOF (leibnizO V) idOF idOF)))
].

Class savedProtoG Σ V := savedProtoG_inG :: inG Σ (savedProtoR Σ V).

Class sessG Σ := SessG {
  #[local] sessG_protoG :: protoG Σ term;
  #[local] sessG_agreeG :: savedProtoG Σ term;
}.

Definition sessΣ := #[
  protoΣ term;
  savedProtoΣ term
].

Global Instance subG_sess Σ : subG sessΣ Σ → sessG Σ.
Proof. solve_inG. Qed.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ, !sessG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (skI skR : sign_key) (kS t : term) (ts : list term).
Implicit Types n : nat.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types (ok : Prop) (failed : bool).
Implicit Types si : sess_info.
Implicit Types (N : namespace) (E : coPset) (p : iProto Σ term).
Implicit Types γ : gname.

Definition session_names si (γs : gname * gname) : iProp :=
  term_meta (si_resp_share si) (sessN.@"names") γs.

Definition session_name_for rl : gname * gname → gname :=
  if rl is Init then fst else snd.

Lemma session_names_agree si γs1 γs2 :
  session_names si γs1 -∗
  session_names si γs2 -∗
  ⌜γs1 = γs2⌝.
Proof. iApply term_meta_agree. Qed.

Definition sess_own skI skR si (rl : role) p : iProp :=
  ∃ γs,
    session_names si γs ∗
    iProto_own (session_name_for rl γs) p.

Lemma sess_own_le skI skR si rl p1 p2 :
  sess_own skI skR si rl p1 ⊢ ▷ (p1 ⊑ p2) -∗ sess_own skI skR si rl p2.
Proof.
iIntros "(%γs & #names & own) le".
iExists γs; iFrame "#". by iApply (iProto_own_le with "[$]").
Qed.

(* Global Instance sess_own_proper skI skR si rl: *)
(*   Proper ((equiv) ==> (⊣⊢)) (sess_own skI skR si rl). *)
(* Proof. *)
(*   solve_proper. *)
(* Qed. *)
Global Instance sess_own_proper skI skR si rl :
  Proper ((≡) ==> (≡)) (sess_own skI skR si rl).
Proof. solve_proper. Qed.

Definition sess_ctx skI skR si tsI tsR : iProp :=
  ∃ γs,
    session_names si γs ∗
    iProto_ctx γs.1 γs.2 tsI tsR.

Definition sess_params p := {|
  GenConn.init_pred := λ skI skR si rl,
    sess_own skI skR si rl (if rl is Init then p else iProto_dual p);
  GenConn.chan_inv := sess_ctx;
|}%I.

(* Print bi_car. *)
(* Global Instance sess_params_proper: *)
(*   Proper ((equiv) ==> (⊣⊢)) (sess_params). *)
(* Proof. *)
(*   Admitted. *)
  (* intros p1 p2 hp. *)
  (* solve_proper. *)

Lemma sess_send skI skR si rl t p ts_send ts_recv :
  sess_own skI skR si rl (<!> MSG t; p) -∗
  ▷ GenConn.chan_inv_for sess_ctx skI skR si rl ts_send ts_recv
  ={⊤ ∖ ↑GenConn.connN, ∅}=∗ |={∅}▷=>^(S (length ts_recv)) |={∅, ⊤ ∖ ↑GenConn.connN}=>
    GenConn.chan_inv_for sess_ctx skI skR si rl (ts_send ++ [t]) ts_recv ∗
    sess_own skI skR si rl p.
Proof.
iIntros "(%γs & #Hγs & own) (%γs' & >#Hγs' & ctx)".
iPoseProof (session_names_agree with "Hγs Hγs'") as "<-".
iClear "Hγs'". case: rl => /=.
- iApply fupd_mask_intro; first set_solver.
  iIntros "close !> !>".
  iMod (iProto_send with "ctx own []") as "[ctx own]".
  { rewrite iMsg_base_eq /=; eauto. }
  iApply step_fupdN_intro => //.
  iIntros "!> !>". iMod "close" as "_".
  iModIntro. by iFrame; eauto.
- rewrite iProto_ctx_sym.
  iApply fupd_mask_intro; first set_solver.
  iIntros "close !> !>".
  iMod (iProto_send with "ctx own []") as "[ctx own]".
  { rewrite iMsg_base_eq /=; eauto. }
  iApply step_fupdN_intro => //.
  iIntros "!> !>". iMod "close" as "_".
  iModIntro. rewrite iProto_ctx_sym. by iFrame; eauto.
Qed.

Lemma sess_recv {TT : tele} skI skR si rl t'
  (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) ts_send ts_recv :
  £ 1 ∗ £ 1 -∗
  sess_own skI skR si rl (<?.. x> MSG t x {{ P x }}; p x) -∗
  ▷ GenConn.chan_inv_for sess_ctx skI skR si rl ts_send (t' :: ts_recv)
  ={⊤ ∖ ↑GenConn.connN}=∗
    ▷ (GenConn.chan_inv_for sess_ctx skI skR si rl ts_send ts_recv ∗
       ∃.. x, ⌜t' = t x⌝ ∗ sess_own skI skR si rl (p x) ∗ P x).
Proof.
iIntros "[c1 c2] (%γs & #Hγs & own) (%γs' & >#Hγs' & ctx)".
iPoseProof (session_names_agree with "Hγs Hγs'") as "<-".
iClear "Hγs'". case: rl => /=.
- iMod (lc_fupd_elim_later with "c1 ctx") as "ctx".
  iMod (iProto_recv with "ctx own") as "(%p' & ctx & own & Ht')".
  rewrite iMsg_base_eq /=.
  iMod (lc_fupd_elim_later with "c2 Ht'") as "Ht'".
  iDestruct (iMsg_texist_exist with "Ht'") as (x <-) "[Hp' HP]".
  iIntros "!> !>".
  iFrame. iSplit => //. iExists x. iFrame. iSplit => //.
  iExists _. iSplit; eauto. by iRewrite "Hp'".
- rewrite iProto_ctx_sym.
- iMod (lc_fupd_elim_later with "c1 ctx") as "ctx".
  iMod (iProto_recv with "ctx own") as "(%p' & ctx & own & Ht')".
  rewrite iMsg_base_eq /=.
  iMod (lc_fupd_elim_later with "c2 Ht'") as "Ht'".
  iDestruct (iMsg_texist_exist with "Ht'") as (x <-) "[Hp' HP]".
  iIntros "!> !>". rewrite iProto_ctx_sym.
  iFrame. iSplit => //. iExists x. iFrame. iSplit => //.
  iExists _. iSplit; eauto. by iRewrite "Hp'".
Qed.


Definition iProto_choice_term (a : action) (P1 P2 : iProp) (p1 p2 : iProto Σ term) : iProto Σ term :=
(<a @ (b : bool)> MSG (TInt (if b then 1 else 0)) {{ if b then P1 else P2 }};
if b then p1 else p2)%proto.

(** Algebra of [iProto_choice_term].  These mirror Actris's [iProto_dual_choice]
    / [iProto_app_choice] / [iProto_le_choice] (channel.v) verbatim: duality,
    append, and subtyping act only on the payload and continuation, never the
    message value, so the proofs are value-agnostic.  They are what lets the
    [ProtoNormalize] instance for choice (in proofmode.v) push duals through a
    choice node automatically. *)

Lemma iProto_dual_choice_term (a : action) (P1 P2 : iProp)
    (p1 p2 : iProto Σ term) :
  iProto_dual (iProto_choice_term a P1 P2 p1 p2)
  ≡ iProto_choice_term (action_dual a) P1 P2 (iProto_dual p1) (iProto_dual p2).
Proof.
  rewrite /iProto_choice_term iProto_dual_message /= iMsg_dual_exist.
  f_equiv; f_equiv => -[]; by rewrite iMsg_dual_base.
Qed.

Lemma iProto_app_choice_term (a : action) (P1 P2 : iProp)
    (p1 p2 q : iProto Σ term) :
  (iProto_choice_term a P1 P2 p1 p2 <++> q)%proto
  ≡ (iProto_choice_term a P1 P2 (p1 <++> q) (p2 <++> q))%proto.
Proof.
  rewrite /iProto_choice_term iProto_app_message /= iMsg_app_exist.
  f_equiv; f_equiv => -[]; by rewrite iMsg_app_base.
Qed.

Lemma iProto_le_choice_term (a : action) (P1 P2 : iProp)
    (p1 p2 p1' p2' : iProto Σ term) :
  (P1 -∗ P1 ∗ ▷ (p1 ⊑ p1')) ∧ (P2 -∗ P2 ∗ ▷ (p2 ⊑ p2')) -∗
  iProto_choice_term a P1 P2 p1 p2 ⊑ iProto_choice_term a P1 P2 p1' p2'.
Proof.
  iIntros "H". rewrite /iProto_choice_term. destruct a;
    iIntros (b) "HP"; iExists b; destruct b;
    iDestruct ("H" with "HP") as "[$ ?]"; by iModIntro.
Qed.

(** ** Namespace-tagged select/branch (additive generalization of the boolean
    [iProto_choice_term]).

    A [tagged_proto] bundles (1) a predicate on terms characterising which wire
    terms select this arm, and (2) the [iProto] continuation.  [tag_proto] builds
    a single arm whose wire term is [Spec.tag (Tag N) (t x)] (mirroring
    [sess_recv]'s message shape); [tagged_proto_or] combines two arms under a
    single [iProto_message Recv] node with a boolean selector, exactly like
    [iProto_choice_term]. *)

(** A [tagged_proto] stores (1) the selector predicate on wire terms and (2) the
    underlying [iMsg] (NOT the wrapped proto, Option B from the plan).  Storing
    the [iMsg] lets [tagged_proto_or] place both arms under one shared
    [iProto_message Recv (∃ b, …)] node, structurally identical to
    [iProto_choice_term Recv], so its algebra transfers directly.  The proto of
    a single arm is recovered as [iProto_message Recv q.2]. *)
Definition tagged_proto : Type := (term → Prop) * iMsg Σ term.

(** The [iMsg] for a single tagged arm: a telescopic receive of a term shaped
    [Spec.tag (Tag N) (t x)], carrying [P x], continuing [p x]. *)
Definition tag_msg {TT : tele} (N : namespace)
    (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) : iMsg Σ term :=
  (∃.. x, MSG Spec.tag (Tag N) (t x) {{ P x }}; p x)%msg.

Definition tag_proto {TT : tele} (N : namespace)
    (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) : tagged_proto :=
  ( (λ t', ∃ x : TT, t' = Spec.tag (Tag N) (t x)),
    tag_msg N t P p ).

(** The proto of a single tagged arm, parameterized by the action [a] (so the
    sender/client uses [Send] and the receiver/server uses [Recv], exactly as
    [iProto_choice_term] takes its action as a parameter). *)
Definition tagged_proto_proto (a : action) (q : tagged_proto) : iProto Σ term :=
  iProto_message a q.2.

(** Combine two arms: the [.1] predicate is the literal disjunction; the [.2]
    [iMsg] uses a boolean selector picking the chosen arm's message, exactly as
    [iProto_choice_term]'s [(b : bool)] selector. *)
Definition tagged_proto_or (q1 q2 : tagged_proto) : tagged_proto :=
  ( (λ t', q1.1 t' ∨ q2.1 t'),
    (∃ b : bool, if b then q1.2 else q2.2)%msg ).

(** Duality distributes through a single tagged arm onto its continuation,
    leaving the tag/payload untouched (mirrors [iMsg_dual_base]).  This lets the
    responder's dualised arm be read back as a [tag_proto] with dualised
    continuation. *)
Lemma iMsg_dual_texist {TT : tele} (m : TT → iMsg Σ term) :
  iMsg_dual (iMsg_texist m) ≡ iMsg_texist (λ x, iMsg_dual (m x)).
Proof.
  induction TT as [|X b IH] in m |- *; rewrite /iMsg_texist /=; first done.
  rewrite iMsg_dual_exist. f_equiv => x.
  apply (IH x (λ xs, m (TeleArgCons x xs))).
Qed.

Lemma iMsg_dual_tag_msg {TT : tele} (N : namespace)
    (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) :
  iMsg_dual (tag_msg N t P p) ≡ tag_msg N t P (λ x, iProto_dual (p x)).
Proof.
  rewrite /tag_msg.
  induction TT as [|X b IH] in t, P, p |- *; rewrite /iMsg_texist /=.
  - by rewrite iMsg_dual_base.
  - rewrite iMsg_dual_exist. f_equiv => x.
    apply (IH x (λ xs, t (TeleArgCons x xs)) (λ xs, P (TeleArgCons x xs))
              (λ xs, p (TeleArgCons x xs))).
Qed.

(** *** Dual algebra for [tagged_proto_or], mirroring [iProto_dual_choice_term].
    Duality acts only on the underlying messages of the two arms and flips the
    action, never the selector, so the proof is value-agnostic. *)
Lemma iProto_dual_tagged_proto_or (a : action) (q1 q2 : tagged_proto) :
  iProto_dual (tagged_proto_proto a (tagged_proto_or q1 q2))
  ≡ tagged_proto_proto (action_dual a)
      (tagged_proto_or (q1.1, iMsg_dual q1.2) (q2.1, iMsg_dual q2.2)).
Proof.
  rewrite /tagged_proto_proto /tagged_proto_or /=.
  rewrite iProto_dual_message /= iMsg_dual_exist.
  f_equiv; f_equiv => -[] //.
Qed.

Lemma iProto_app_tagged_proto_or (a : action) (q1 q2 : tagged_proto)
    (q : iProto Σ term) :
  (tagged_proto_proto a (tagged_proto_or q1 q2) <++> q)%proto
  ≡ tagged_proto_proto a
      (tagged_proto_or (q1.1, (q1.2 <++> q)%msg) (q2.1, (q2.2 <++> q)%msg)).
Proof.
  rewrite /tagged_proto_proto /tagged_proto_or /=.
  rewrite iProto_app_message /= iMsg_app_exist.
  f_equiv; f_equiv => -[] //.
Qed.

(** *** Disjointness = security.  Distinct namespaces make the two arms'
    selector predicates mutually exclusive: this is the formal content of
    plan.org's "p2 fires only when p1.1 does not hold".  Proven via the
    sanctioned [Spec.tag_inj] / [Tag_inj] round-trip lemmas (the same ones the
    rpc layer relies on), NOT raw constructor injectivity. *)
Lemma tag_proto_disj {TT1 TT2 : tele} (N1 N2 : namespace)
    (t1 : TT1 → term) (P1 : TT1 → iProp) (p1 : TT1 → iProto Σ term)
    (t2 : TT2 → term) (P2 : TT2 → iProp) (p2 : TT2 → iProto Σ term) t' :
  N1 ≠ N2 →
  (tag_proto N1 t1 P1 p1).1 t' →
  (tag_proto N2 t2 P2 p2).1 t' →
  False.
Proof.
  move=> Hne /= [x1 ->] [x2 He].
  move: He => /Spec.tag_inj [/Tag_inj HN _].
  by apply: Hne.
Qed.

(** *** Coercion of a two-arm [tagged_proto_or] receive node to a single
    telescopic receive over the SUM telescope [TeleS (λ b, if b then TT1 else
    TT2)].  This lets [wp_branch_tag] (proofs.v) reuse the generic telescopic
    [wp_recv].  The payloads gain a [▷] (a valid receiver weakening: the holder
    promises [P x], which entails [▷ P x]).  Proved by structurally peeling the
    selector bool and each arm's telescope, so no higher-order unification on
    the dependent sum telescope is needed. *)
Definition tagged_branch_tval {TT1 TT2 : tele} (N1 N2 : namespace)
    (t1 : TT1 → term) (t2 : TT2 → term)
    (y : TeleS (λ b : bool, if b then TT1 else TT2)) : term :=
  match y with TeleArgCons b xs =>
    Spec.tag (Tag (if b then N1 else N2))
      ((if b as b' return ((if b' then TT1 else TT2) → term)
        then t1 else t2) xs) end.

Definition tagged_branch_Pval {TT1 TT2 : tele}
    (P1 : TT1 → iProp) (P2 : TT2 → iProp)
    (y : TeleS (λ b : bool, if b then TT1 else TT2)) : iProp :=
  match y with TeleArgCons b xs =>
    (if b as b' return ((if b' then TT1 else TT2) → iProp)
     then P1 else P2) xs end.

Definition tagged_branch_pcont {TT1 TT2 : tele}
    (p1 : TT1 → iProto Σ term) (p2 : TT2 → iProto Σ term)
    (y : TeleS (λ b : bool, if b then TT1 else TT2)) : iProto Σ term :=
  match y with TeleArgCons b xs =>
    (if b as b' return ((if b' then TT1 else TT2) → iProto Σ term)
     then p1 else p2) xs end.

(** The combined receive node, viewed through the sum telescope
    [STT := TeleS (λ b, if b then TT1 else TT2)], equals (up to [≡]) the
    telescopic receive with [▷]-weakened payloads.  Proved by [f_equiv] over the
    selector bool and each arm's telescope (the [Proper] instances of
    [iMsg_exist]/[iMsg_base] absorb the higher-order structure, dodging the
    explicit-witness unification problems of [iProto_le_texist_intro_r]).
    [wp_branch_tag] (proofs.v) rewrites with this to reuse the telescopic
    [sess_recv] over [STT]. *)
Lemma tagged_or_branch_equiv {TT1 TT2 : tele} (N1 N2 : namespace)
    (t1 : TT1 → term) (P1 : TT1 → iProp) (p1 : TT1 → iProto Σ term)
    (t2 : TT2 → term) (P2 : TT2 → iProp) (p2 : TT2 → iProto Σ term) :
  tagged_proto_proto Recv
    (tagged_proto_or (tag_proto N1 t1 P1 p1) (tag_proto N2 t2 P2 p2))
  ≡ (<?.. y> MSG tagged_branch_tval N1 N2 t1 t2 y
              {{ tagged_branch_Pval P1 P2 y }};
              tagged_branch_pcont p1 p2 y)%proto.
Proof.
  rewrite /tagged_proto_proto /tagged_proto_or /tag_proto /tag_msg /=.
  f_equiv. f_equiv => -[] /=; done.
Qed.

(* initial proto contains a list of proto, we need the history of all past messages to know which proto is the current one *)
Definition connected skI skR rl cs p : iProp :=
  GenConn.connected sess_ctx skI skR rl cs ∗
  (public (si_key cs) ∨ sess_own skI skR cs rl p).

Lemma connected_le skI skR rl cs p1 p2 :
  connected skI skR rl cs p1 ⊢ ▷ (p1 ⊑ p2) -∗ connected skI skR rl cs p2.
Proof.
iIntros "[conn [#fail|own]] le".
- iFrame. by eauto.
- iFrame. iRight. by iApply (sess_own_le with "[$]").
Qed.

(* Global Instance connected_proper skI skR rl cs: *)
(*   Proper ((equiv) ==> (⊣⊢)) (connected skI skR rl cs). *)
(* Proof. *)
(*   unfold connected. *)

(*   (* solve_proper. *) *)
(*   (* Admitted. *) *)
(*   intros p1 p2 Hp. *)
(*   rewrite  /connected. *)
(*   f_equiv. *)
(*   - *)
(*   solve_proper. *)
(* (* Qed. *) *)


Global Instance connected_proper skI skR rl cs :
  Proper ((≡) ==> (≡)) (connected skI skR rl cs).
Proof. by move=> p1 p2 e; rewrite /connected e. Qed.

Definition ctx N p := GenConn.ctx N (sess_params p).

Lemma ctx_alloc N p E :
  ↑N ⊆ E →
  GenConn.base_ctx -∗
  iso_dh_ctx -∗
  iso_dh_token E ==∗
  ctx N p ∗ iso_dh_token (E ∖ ↑N).
Proof. exact: GenConn.ctx_alloc. Qed.

End Verif.
