From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib guarded term crypto primitives tactics session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSL.

Context `{!cryptoG Σ, !heapG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types SM : gmap term session_data.
Implicit Types s : session_data.
Implicit Types lvl : level.
Implicit Types rl : role.

Class nslG := {
  in_nsl_sessG :> sessionG Σ;
  nsl_name : gname;
}.

Context `{!nslG}.

Definition msg1_pred kB m1 : iProp :=
  ∃ nA kA, ⌜m1 = Spec.of_list [nA; TKey Enc kA]⌝ ∗
           session_frag nsl_name nA (SessionData Init kA kB None).

Global Instance msg1_pred_persistent kB m1 : Persistent (msg1_pred kB m1).
Proof. apply _. Qed.

Definition msg2_pred kA m2 : iProp :=
  ∃ nA nB kB,
    ⌜m2 = Spec.of_list [nA; nB; TKey Enc kB]⌝ ∗
    session_frag nsl_name nB (SessionData Resp kA kB (Some nA)).

Global Instance msg2_pred_persistent kB m2 : Persistent (msg2_pred kB m2).
Proof.
case: m2; try by move=> *; apply _.
Qed.

Definition msg3_pred kB nB : iProp :=
  □ ∀ nA kA,
    session_frag nsl_name nB (SessionData Resp kA kB (Some nA)) -∗
    session_frag nsl_name nA (SessionData Init kA kB (Some nB)).

Global Instance msg3_pred_persistent kB nB : Persistent (msg3_pred kB nB).
Proof. apply _. Qed.

Definition nsl_key_inv rl k : iProp :=
  termT Pub (TKey Enc k) ∗
  stermT Sec (TKey Dec k) ∗
  match rl with
  | Init => tkey_predT "m2" (msg2_pred k) k
  | Resp => tkey_predT "m1" (msg1_pred k) k ∗
            tkey_predT "m3" (msg3_pred k) k
  end.
Arguments nsl_key_inv : simpl never.

Global Instance nsl_key_inv_persistent rl k :
  Persistent (nsl_key_inv rl k).
Proof. rewrite /nsl_key_inv; case: rl; apply _. Qed.

Lemma nsl_key_inv_pub rl k : nsl_key_inv rl k -∗ termT Pub (TKey Enc k).
Proof. by iDestruct 1 as "[??]". Qed.

Definition nsl_sess_inv rl kA (kB : term) t : iProp :=
  nsl_key_inv rl kA ∗ stermT Sec t.

Definition nsl_inv : iProp :=
  session_inv nsl_name (cryptoN.@"nsl") nsl_sess_inv.

Definition nsl_ctx : iProp :=
  session_ctx nsl_name (cryptoN.@"nsl") nsl_sess_inv.

Variable send recv gen : val.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition initiator (skA pkA pkB nA : val) : val := λ: <>,
  bind: "m1"   := tenc "m1" pkB (term_of_list [nA; pkA]) in
  send "m1";;
  bind: "m2"   := tdec "m2" skA (recv #()) in
  bind: "m2"   := list_of_term "m2" in
  bind: "nA'"  := "m2" !! #0 in
  bind: "nB"   := "m2" !! #1 in
  bind: "pkB'" := "m2" !! #2 in
  if: eq_term "nA'" nA && eq_term "pkB'" pkB then
    bind: "m3" := tenc "m3" pkB "nB" in
    send "m3";;
    SOME "nB"
  else NONE.

Definition responder (skB pkB : val) : val := λ: <>,
  bind: "m1" := tdec "m1" skB (recv #()) in
  bind: "m1" := list_of_term "m1" in
  bind: "nA" := "m1" !! #0 in
  bind: "pkA" := "m1" !! #1 in
  bind: "kt" := is_key "pkA" in
  if: "kt" = repr Enc then
    let: "nB" := gen #() in
    bind: "m2" := tenc "m2" "pkA" (term_of_list ["nA"; "nB"; pkB]) in
    send "m2";;
    bind: "m3" := tdec "m3" skB (recv #()) in
    if: eq_term "m3" "nB" then SOME ("pkA", "nA", "nB") else NONE
  else NONE.

Implicit Types Ψ : val → iProp.

Hypothesis wp_send : forall E t Ψ,
  ▷ termT Pub t -∗
  Ψ #() -∗
  WP send t @ E {{ Ψ }}.

Hypothesis wp_recv : forall E Ψ,
  (∀ t, termT Pub t -∗ Ψ t) -∗
  WP recv #() @ E {{ Ψ }}.

Hypothesis wp_gen : forall E lvl Ψ,
  (∀ t, crypto_meta_token t (↑cryptoN.@"nsl") -∗
        stermT lvl t -∗
        Ψ t) -∗
  WP gen #() @ E {{ Ψ }}.

Lemma termT_msg1 lvl kA kB (tA : term) :
  nsl_key_inv Init kA -∗
  stermT lvl tA -∗
  termT Pub (TKey Enc kB) -∗
  guarded (lvl = Sec) (nsl_key_inv Resp kB) -∗
  guarded (lvl = Sec) (session_frag nsl_name tA (SessionData Init kA kB None)) -∗
  termT Pub (TEnc kB (Spec.tag "m1" (Spec.of_list [tA; TKey Enc kA]))).
Proof.
iIntros "#HkA #HtA #HkB_lo (#HkB_hi & #HkB_hi' & #? & _) #frag".
iApply termT_tag_aenc_pub_secG; eauto.
  iApply termT_of_list => /=.
  iSplit; first by iDestruct "HtA" as "[??]".
  iSplit => //.
  iApply (@sub_termT _ _ _ Pub) => //.
  by iDestruct "HkA" as "[HkA _]".
case: lvl => //=; iModIntro; by iExists _, _; eauto.
Qed.

Lemma wp_initiator kA kB (tA : term) lvl E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  stermT lvl tA -∗
  crypto_meta_token tA (↑cryptoN.@"nsl") -∗
  nsl_key_inv Init kA -∗
  termT Pub (TKey Enc kB) -∗
  guarded (lvl = Sec) (nsl_key_inv Resp kB) -∗
  (∀ onB : option term,
      (if onB is Some tB then
         stermT lvl tB ∗
         guarded (lvl = Sec) (
           session_auth nsl_name tA (SessionData Init kA kB (Some tB)) ∗
           correspondence nsl_name kA kB tA tB
         )
       else True) -∗
      Ψ (repr onB)) -∗
  WP initiator (TKey Dec kA) (TKey Enc kA) (TKey Enc kB) tA #() @ E
     {{ Ψ }}.
Proof.
rewrite /initiator.
iIntros (?) "#Hctx #HtA unreg #HkA #HkB_lo #HkB_hi Hpost".
wp_list (_ :: _ :: []).
wp_term_of_list.
wp_tenc => /=.
iMod (@session_alloc_initG _ _ _ _ _ _ _ (lvl = Sec)
        with "Hctx [] [unreg]") as "[auth #fragA]" => //.
- by iIntros "-> /= !>"; iSplit; eauto.
- by iIntros "_".
wp_pures; wp_bind (send _); iApply wp_send.
  by iModIntro; iApply termT_msg1.
wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (m2) "#Hm2"; wp_tdec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_lookup nA' enA'; last protocol_failure.
wp_lookup nB  enB; last protocol_failure.
wp_lookup pkB' epkB'; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst pkB'.
wp_tenc.
iDestruct (termT_tag_adec_pub_sec with "Hm2 []") as (lm2) "{Hm2} [#Hm2 #fragB]".
  by iDestruct "HkA" as "(?&?&?)".
rewrite termT_of_list.
iPoseProof (big_sepL_lookup with "Hm2") as "m2_tA"; first exact: enA'.
iPoseProof (big_sepL_lookup with "Hm2") as "m2_nB"; first exact: enB.
iPoseProof (big_sepL_lookup with "Hm2") as "m2_kB"; first exact: epkB'.
set  sA := SessionData Init _ _ _.
pose sB := SessionData Resp kA kB (Some tA).
pose sA' := SessionData Init kA kB (Some nB).
iAssert (guarded (lm2 = Sec) (▷^2 session_frag nsl_name nB sB))
    as "{fragB} #fragB".
  iIntros "-> /= !> !>".
  iDestruct "fragB" as (nA' nB' kB') "/= (%em2 & #fragB)".
  move/Spec.of_list_inj in em2; subst m2.
  by case: enA' epkB' enB => [] -> [] -> [] -> {nA' nB' kB'}.
iClear (enA' enB epkB') "Hm2".
rewrite !guarded_later.
wp_pures.
iMod (session_frag_invG with "Hctx fragB") as "[#sessB #coh]" => //.
iSpecialize ("coh" with "[]"); first by eauto.
rewrite /coherent_views /=.
iPoseProof (stermTP with "HtA m2_tA") as "{m2_tA} %Hlm2".
iAssert (|={E}=> ▷ ⌜lm2 = lvl⌝)%I as "> > ->".
  case: lvl lm2 Hlm2 => [] // [] //= _.
  iDestruct "coh" as ">coh".
  iMod (session_frag_inv with "Hctx coh") as "[sessA _]"=> //.
  iDestruct "sessA" as "(_&#HtA')".
  do 2![iModIntro].
  by iApply (stermT_agree with "HtA' HtA").
iMod (session_updateG with "Hctx auth [fragB]")
    as "{fragA} [auth #fragA]" => //.
set m3 := TEnc _ _.
wp_bind (send _); iApply wp_send.
  iModIntro.
  iDestruct "HkB_hi" as "(HkB_m1 & HkB_m3 & ? & ?)".
  iApply (termT_tag_aenc_pub_secG _ lvl) => //; eauto.
  case: (lvl) => //=; iIntros "!> !> %nA' %kA' #fragB'".
  iDestruct (session_frag_agree with "fragB' fragB") as "/= %e".
  by case: e => [] _ [] -> [] _ ->.
wp_pures; iApply ("Hpost" $! (Some nB)).
case: lvl {Hlm2} => /=.
  do 2![iSplit => //]; by iModIntro; iIntros (lvl') "?".
iDestruct "sessB" as "(?&?&?)".
by iFrame; iSplit => //; iSplit.
Qed.

Lemma wp_responder kB E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  nsl_key_inv Resp kB -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ lvl kA,
           ⌜pkA = TKey Enc kA⌝ ∗
           termT Pub pkA ∗
           stermT lvl nA ∗
           stermT lvl nB ∗
           guarded (lvl = Sec) (
             session_auth nsl_name nB (SessionData Resp kA kB (Some nA)) ∗
             correspondence nsl_name kA kB nA nB
           )
       else True) -∗
       Ψ (repr ot)) -∗
  WP responder (TKey Dec kB) (TKey Enc kB) #() @ E {{ Ψ }}.
Proof.
iIntros (?) "#Hctx #HkB Hpost".
rewrite /responder; wp_pures.
wp_bind (recv _); iApply wp_recv; iIntros (m1) "#Hm1".
wp_tdec m1; last protocol_failure.
wp_list_of_term m1; last protocol_failure.
wp_lookup nA enA; last protocol_failure.
wp_lookup pkA epkA; last protocol_failure.
wp_is_key_eq kt kA et; last protocol_failure; subst pkA.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Enc)); last protocol_failure.
case: kt epkA=> // epkA _.
iPoseProof "HkB" as "(? & ? & HkB_m1 & HkB_m3)".
iDestruct (termT_tag_adec_pub_sec with "Hm1 []") as (lm1) "{Hm1} [Hm1 #fragA]"; eauto.
rewrite termT_of_list.
iPoseProof (big_sepL_lookup with "Hm1") as "HnA"; first exact: enA.
iPoseProof (big_sepL_lookup with "Hm1") as "HpkA"; first exact: epkA.
pose (Pm1 := session_frag nsl_name nA (SessionData Init kA kB None)).
iAssert (▷^2 guarded (lm1 = Sec) Pm1)%I as "{fragA} fragA".
  iApply (guarded_mono with "fragA").
  iIntros "!> {fragA} !> !> #fragA".
  iDestruct "fragA" as (nA' kA') "/= [%em1 #fragA]".
  move/Spec.of_list_inj in em1; subst m1.
  by case: enA epkA => [] -> [] -> {nA' kA'}.
wp_pures; wp_bind (gen _); iApply (wp_gen _ lm1); iIntros (nB) "unreg #HnB".
wp_let.
iMod (session_frag_invG with "Hctx fragA") as "[#HnA' _]" => //=.
iAssert (▷ termT Pub (TKey Enc kA))%I as "#HkA_lo".
  case: lm1=> //=; iModIntro.
  by iDestruct "HnA'" as "(#[??]&?)".
iDestruct "HnA'" as "/= # [HkA_hi HnA']".
wp_pures.
wp_list (_ :: _ :: _ :: []); wp_term_of_list. 
wp_tenc; wp_pures.
set m2 := Spec.of_list [nA; nB; TKey Enc kB].
set sB := SessionData Resp kA kB (Some nA).
iMod (session_alloc_respG with "Hctx [] fragA [unreg]")
    as "[auth #fragB]" => //=.
- by iIntros "-> !>"; iSplit; [done|iApply "HnB"].
- by iIntros "->".
wp_bind (send _); iApply wp_send.
  iModIntro.
  iDestruct "HkA_hi" as "#(?&?&?)".
  iApply termT_tag_aenc_pub_secG; eauto.
    iApply termT_of_list => /=.
    do !iSplit => //; try by iApply stermT_termT.
    by iApply sub_termT_pub.
  case: lm1 => //=; eauto.
  by iModIntro; iExists nA, nB, kB; iSplit; first trivial.
wp_pures; wp_bind (recv _); iApply wp_recv; iIntros (m3) "#Hm3".
wp_tdec m3; last protocol_failure.
iDestruct (termT_tag_adec_pub_sec with "Hm3 [//]") as (lm3) "/= {Hm3} [#Hm3 #Hprot3]".
wp_eq_term e; last protocol_failure; subst m3.
iAssert (⌜lm1 ⊑ lm3⌝)%I as "%lm1_lm3".
  by iDestruct "HnB" as "[_ #Hmin]"; iApply "Hmin".
iAssert (guarded (lm1 = Sec) (msg3_pred kB nB)) as "{Hprot3 Hm3} Hprot3".
  iIntros "->"; by case: lm3 lm1_lm3.
clear lm1_lm3 lm3.
wp_pures.
iApply ("Hpost" $! (Some (_, _, _))).
iExists lm1, _; do 3![iSplit => //].
  by case: lm1 => //=; rewrite (stermT_eq Pub nA).
iSplit => //.
iIntros "-> /=".
iSpecialize ("Hprot3" with "fragB").
iFrame; by iSplit.
Qed.

End NSL.
