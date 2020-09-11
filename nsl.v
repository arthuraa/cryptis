From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth csum gset gmap excl dra sts.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib term crypto1 primitives.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSL.

Import sts.

Context `{!resG Σ, !heapG Σ}.

Inductive session :=
| SNew
| SAnswered of term & bool.

Inductive turn := Init | Resp.

Canonical turnO := leibnizO turn.

Implicit Types tr : turn.

Lemma turn_equivI tr1 tr2 :
  tr1 ≡ tr2 ⊣⊢@{iPropI Σ}
  match tr1, tr2 with
  | Init, Init | Resp, Resp => True
  | _, _ => False
  end.
Proof.
by case: tr1 tr2=> [] []; iSplit=> //.
Qed.

Definition csum_of_turn tr : csum unit unit :=
  match tr with
  | Init => Cinl ()
  | Resp => Cinr ()
  end.

Implicit Types (s : session) (t : term).

Definition session_step : relation session := λ s1 s2,
  match s1, s2 with
  | SNew, SAnswered _ false => True
  | SAnswered t1 false, SAnswered t2 true => t1 = t2
  | _, _ => False
  end.

Definition session_token s : propset turn :=
  match s with
  | SNew => {[Init]}
  | SAnswered _ b => {[if b then Init else Resp]}
  end.

Canonical session_sts : stsT := Sts session_step session_token.

Class nslG := {
  in_nsl_sessG :> inG Σ (gmapUR term (stsR session_sts));
  in_nsl_keysG :> inG Σ (authR (gmapUR loc (csumR unitR unitR)));
  nsl_sess_name : gname;
  nsl_keys_name : gname;
}.

Context `{!nslG}.

Definition initiator_view t s :=
  own nsl_sess_name {[t := sts_frag_up s {[Init]}]}.

Definition responder_view t s :=
  own nsl_sess_name {[t := sts_frag_up s {[Resp]}]}.

Definition session_bound t s :=
  own nsl_sess_name {[t := sts_frag_up s ∅]}.

Definition initiator_key l : iProp Σ :=
  own nsl_keys_name (◯ {[l := csum_of_turn Init]}).

Global Instance initiator_key_persistent l : Persistent (initiator_key l).
Proof. apply _. Qed.

Definition responder_key l : iProp Σ :=
  own nsl_keys_name (◯ {[l := csum_of_turn Resp]}).

Global Instance responder_key_persistent l : Persistent (responder_key l).
Proof. apply _. Qed.

Definition initiator_pred lA t : iProp Σ :=
  match t with
  | TPair (TNonce nA) (TPair (TNonce nB) (TPair (TKey KAEnc lB) _)) =>
    nonceT {[lA; lB]} nA ∗
    nonceT {[lA; lB]} nB ∗
    responder_key lB ∗
    session_bound (TNonce nA) (SAnswered (TNonce nB) false)
  | _ => False
  end.

Global Instance initiator_pred_proper : NonExpansive2 initiator_pred.
Proof. solve_contractive. Qed.

Definition responder_pred lB t : iProp Σ :=
  match t with
  | TPair (TNonce nA) (TKey KAEnc lA) =>
    nonceT {[lA; lB]} nA ∗ initiator_key lA
  | TNonce nB =>
    ∃ nA lA, nonceT {[lA; lB]} nB ∗
             initiator_key lA ∗
             session_bound nA (SAnswered (TNonce nB) true)
  | _ => False
  end.

Global Instance responder_pred_proper : NonExpansive2 responder_pred.
Proof. solve_contractive. Qed.

Ltac solve_agent_pred :=
  repeat match goal with
  | |- ∀ (t : term), _ => case; try by move=> *; apply _
  | |- ∀ (kt : key_type), _ => case; try by move=> *; apply _
  | |- ∀ (x : _), _ => move=> ?
  end.

Global Instance initiator_pred_persistent lA t :
  Persistent (initiator_pred lA t).
Proof. move: t; solve_agent_pred. Qed.

Global Instance responder_pred_persistent lB t :
  Persistent (responder_pred lB t).
Proof. move: t; solve_agent_pred. Qed.

Definition agent_pred (x : turn) l :=
  match x with
  | Init => OfeMor (initiator_pred l)
  | Resp => OfeMor (responder_pred l)
  end.

Global Instance agent_pred_persistent x l t :
  Persistent (agent_pred x l t).
Proof. by case: x; apply _. Qed.

Implicit Types SM : gmap term session.
Implicit Types KM : gmap loc turn.

Definition nsl_keys_inv : iProp Σ :=
  ∃ KM, own nsl_keys_name (● (csum_of_turn <$> KM : gmap _ _)) ∗
        [∗ map] l ↦ x ∈ KM, akeyT RPub ∅ (agent_pred x l) l.

Definition nsl_sess_inv : iProp Σ :=
  ∃ SM, own nsl_sess_name ((λ s, sts_auth s ∅) <$> SM : gmap _ _).

Lemma nsl_sess_inv_timeless : Timeless nsl_sess_inv.
Proof. apply _. Qed.

Lemma initiator_move nA nB :
  nsl_sess_inv -∗
  initiator_view nA SNew -∗
  session_bound nA (SAnswered nB false) ==∗
  nsl_sess_inv ∗
  initiator_view nA (SAnswered nB true) ∗
  session_bound nA (SAnswered nB true).
Proof. Admitted.

Lemma initiator_key_akey lA :
  nsl_keys_inv -∗
  initiator_key lA -∗
  akeyT RPub ∅ (agent_pred Init lA) lA.
Proof.
iDestruct 1 as (KM) "[Hown Hkeys]"; iIntros "HlA".
iPoseProof (own_valid_2 with "Hown HlA") as "#Hvalid".
rewrite auth_both_validI.
iDestruct "Hvalid" as "(_ & Hvalid & _)".
iDestruct "Hvalid" as (KM') "HKM".
rewrite gmap_equivI; iSpecialize ("HKM" $! lA).
rewrite lookup_fmap lookup_op lookup_singleton option_equivI.
move KM_lA: (KM !! lA)=> o; case: o KM_lA=> [tr|] KM_lA; last first.
  by rewrite /=; move: (KM' !! lA); case.
rewrite /=; case: tr KM_lA=> KM_lA; last first.
  move: (KM' !! lA); case=> [ag|] /=; last first.
    by rewrite csum_equivI.
  by case: ag=> *; rewrite csum_equivI.
iClear "HKM".
by rewrite big_sepM_delete //; iDestruct "Hkeys" as "[??]".
Qed.

Lemma responder_key_akey lB :
  nsl_keys_inv -∗
  responder_key lB -∗
  akeyT RPub ∅ (agent_pred Resp lB) lB.
Proof.
iDestruct 1 as (KM) "[Hown Hkeys]"; iIntros "HlA".
iPoseProof (own_valid_2 with "Hown HlA") as "#Hvalid".
rewrite auth_both_validI.
iDestruct "Hvalid" as "(_ & Hvalid & _)".
iDestruct "Hvalid" as (KM') "HKM".
rewrite gmap_equivI; iSpecialize ("HKM" $! lB).
rewrite lookup_fmap lookup_op lookup_singleton option_equivI.
move KM_lB: (KM !! lB)=> o; case: o KM_lB=> [tr|] KM_lB; last first.
  by rewrite /=; move: (KM' !! lB); case.
rewrite /=; case: tr KM_lB=> KM_lB.
  move: (KM' !! lB); case=> [ag|] /=; last first.
    by rewrite csum_equivI.
  by case: ag=> *; rewrite csum_equivI.
iClear "HKM".
by rewrite big_sepM_delete //; iDestruct "Hkeys" as "[??]".
Qed.

Variable send recv : val.

Definition initiator (skA pkA pkB nA : val) : val := λ: <>,
  bind: "m1"   := aenc pkB (tuple nA pkA) in
  send "m1";;
  bind: "m2"   := adec skA (recv #()) in
  bind: "nA'"  := term_projV "m2" #0 in
  bind: "nB"   := term_projV "m2" #1 in
  bind: "pkB'" := term_projV "m2" #2 in
  if: eq_term "nA'" nA && eq_term "pkB'" pkB then
    bind: "m3" := aenc pkB "nB" in
    send "nB";;
    SOME "nB"
  else NONE.

Definition responder (skB pkB nB : val) : val := λ: <>,
  bind: "m1"  := adec skB (recv #()) in
  bind: "nA" := term_projV "m1" #0 in
  bind: "pkA" := term_projV "m1" #1 in
  bind: "m2" := aenc "pkA" (tuple "nA" (tuple nB pkB)) in
  send "m2";;
  bind: "nB'" := adec skB (recv #()) in
  if: "nB'" = nB then SOME "nA" else NONE.

Hypothesis wp_send : forall E t,
  ⊢ WP send t @ E {{v, ⌜v = #()⌝}}.

Hypothesis wp_recv : forall E,
  ⊢ WP recv #() @ E {{v, ∃ t, ⌜v = t⌝ ∗ termT RPub t}}.

Ltac protocol_failure :=
  by move=> *; iIntros "->"; wp_pures; iExists None.

Lemma res_own l (r1 r2 : res Σ) :
  own res_name (◯ {[l := to_agree r1]}) -∗
  own res_name (◯ {[l := to_agree r2]}) -∗
  r1 ≡ r2.
Proof.
iIntros "Hown1 Hown2".
iPoseProof (own_valid_2 with "Hown1 Hown2") as "#Hvalid".
rewrite auth_validI /= singleton_op gmap_validI.
iSpecialize ("Hvalid" $! l).
by rewrite lookup_singleton uPred.option_validI agree_validI agree_equivI.
Qed.

Lemma wp_initiator kA kB nA :
  nsl_keys_inv -∗
  nsl_sess_inv -∗
  nonceT {[kA; kB]} nA -∗
  initiator_key kA -∗
  responder_key kB -∗
  initiator_view (TNonce nA) SNew -∗
  WP initiator (TKey KADec kA) (TKey KAEnc kA) (TKey KAEnc kB) (TNonce nA) #()
     {{v, ∃ onB : option term,
          ⌜v = repr onB⌝ ∗
          match onB with
          | Some nB => initiator_view (TNonce nA) (SAnswered nB true)
          | None => True
          end}}.
Proof.
rewrite /initiator.
iIntros "Hkeys Hsess #HnA #HkA #HkB Hown".
iPoseProof (initiator_key_akey with "Hkeys HkA") as "#HkA'".
iPoseProof (responder_key_akey with "Hkeys HkB") as "#HkB'".
wp_pures; wp_bind (tuple _ _).
iApply twp_wp; iApply twp_wand; first by iApply twp_tuple.
iIntros (?) "->".
wp_bind (aenc _ _); iApply twp_wp; iApply twp_wand.
  iApply twp_aenc; first by iExists ∅.
  iLeft; iSplit; rewrite /=; last first.
    iSplit.
    - iExists {[kA; kB]}; iSplit; eauto.
      iPureIntro; set_solver.
    - iExists RPub, (agent_pred Init kA); iSplit; last by iPureIntro.
      by iExists ∅.
  by iModIntro; iSplit.
iIntros (?) "[-> #Hm1]".
wp_pures; wp_bind (send _); iApply wp_wand; first by iApply wp_send.
iIntros (?) "->"; wp_pures.
wp_bind (recv _); iApply wp_wand; first by iApply wp_recv.
iIntros (?); iDestruct 1 as (m2) "[-> #Hm2]".
wp_bind (adec _ _); iApply twp_wp; iApply twp_wand.
  iApply twp_adec; eauto.
iIntros (v).
case: m2; try by protocol_failure.
case; last by protocol_failure.
move=> k t.
case: decide; last by protocol_failure.
move=> {k} ->; iDestruct 1 as "[-> #Ht]"; wp_pures.
wp_bind (term_projV _ _).
iApply twp_wp; iApply twp_wand; first by iApply (twp_term_projV _ _ 0).
iIntros (?) "->".
case enA': (term_proj t 0)=> [nA'|]; last by wp_pures; iExists None.
wp_pures.
wp_bind (term_projV _ _).
iApply twp_wp; iApply twp_wand; first by iApply (twp_term_projV _ _ 1).
iIntros (?) "->".
case enB: (term_proj t 1)=> [nB|]; wp_pures; try by iExists None.
wp_bind (term_projV _ _).
iApply twp_wp; iApply twp_wand; first by iApply (twp_term_projV _ _ 2).
iIntros (?) "->".
case epkB': (term_proj t 2)=> [pkB'|]; wp_pures; try by iExists None.
wp_bind (eq_term _ _).
iApply twp_wp; iApply twp_wand; first by iApply twp_eq_term.
iIntros (?) "->".
case: bool_decide_reflect=> e; wp_pures; try by iExists None.
subst nA'.
wp_bind (eq_term _ _).
iApply twp_wp; iApply twp_wand; first by iApply twp_eq_term.
iIntros (?) "->".
case: bool_decide_reflect=> e; wp_pures; try by iExists None.
subst pkB'.
iDestruct "Ht" as "[Ht|(_&Ht)]"; last first.
  iPoseProof (term_proj_termT _ enA' with "Ht") as "contra".
  iDestruct "contra" as (rs_nB) "[contra1 contra2]".
  rewrite readers_subseteq_equiv.
  case: rs_nB=> [|rs_nB]; last by iDestruct "contra2" as "[]".
  iPoseProof (res_own with "HnA contra1") as "contra".
  rewrite res_equivI.
  by iPoseProof "contra" as "%contra".
iDestruct "Ht" as "[#Hagent Ht]".
case: t enA' enB epkB'=> // nA' [] // nB' [] // pkB' t' enA' enB epkB'.
rewrite /= in enA' enB epkB'; move: enA' enB epkB'=> [->] [->] [->] {nA' nB' pkB'}.
iSimpl in "Hagent".
case: nB=> // nB.
iDestruct "Hagent" as "(_&HnB&_&Hlb)".
wp_bind (aenc _ _).
iApply twp_wp; iApply twp_wand; first iApply twp_aencH.
- iExists ∅. by iApply "HkB'".
- iModIntro. iSimpl. iExists (TNonce nA), kA. iSplit; eauto.
  iSplit; eauto. admit.
- iExists {[kA; kB]}. iSplit=> //. iPureIntro. by set_solver.
iIntros (?) "[-> #Hm3]".
wp_pures.
wp_bind (send _).
iApply wp_wand; first iApply wp_send.
iIntros (?) "->"; wp_pures; iExists (Some (TNonce nB)).
Admitted.

End NSL.
