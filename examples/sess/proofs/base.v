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

Lemma sess_send p0 skI skR si rl t p ts_send ts_recv :
  sess_own skI skR si rl (<!> MSG t; p) -∗
  ▷ GenConn.chan_inv_for (sess_params p0) skI skR si rl ts_send ts_recv
  ={⊤ ∖ ↑GenConn.connN, ∅}=∗ |={∅}▷=>^(S (length ts_recv)) |={∅, ⊤ ∖ ↑GenConn.connN}=>
    GenConn.chan_inv_for (sess_params p0) skI skR si rl (ts_send ++ [t]) ts_recv ∗
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

Lemma sess_recv {TT : tele} p0 skI skR si rl t'
  (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) ts_send ts_recv :
  £ 1 ∗ £ 1 -∗
  sess_own skI skR si rl (<?.. x> MSG t x {{ P x }}; p x) -∗
  ▷ GenConn.chan_inv_for (sess_params p0) skI skR si rl ts_send (t' :: ts_recv)
  ={⊤ ∖ ↑GenConn.connN}=∗
    ▷ (GenConn.chan_inv_for (sess_params p0) skI skR si rl ts_send ts_recv ∗
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

(* initial proto contains a list of proto, we need the history of all past messages to know which proto is the current one *)
Definition connected skI skR rl cs p : iProp :=
  GenConn.connected (sess_params p) skI skR rl cs ∗
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


(* FIXME: This is a hack. It relies on the definition of connected actually not
   depending on which initial protocol p is passed as a parameter of
   sess_params. *)
Global Instance connected_proper skI skR rl cs :
  Proper ((≡) ==> (≡)) (connected skI skR rl cs).
Proof. by move=> p1 p2 e; rewrite /connected {2}e. Qed.

Definition ctx N p := GenConn.ctx N (sess_params p).

Lemma ctx_alloc N p E :
  ↑N ⊆ E →
  GenConn.pre_ctx -∗
  iso_dh_token E ==∗
  ctx N p ∗ iso_dh_token (E ∖ ↑N).
Proof. exact: GenConn.ctx_alloc. Qed.

End Verif.
