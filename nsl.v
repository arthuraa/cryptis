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
Implicit Types s : session_view.
Implicit Types l : level.
Implicit Types rl : role.

Class nslG := {
  in_nsl_sessG :> sessionG Σ;
  nsl_sess_name : gname;
}.

Context `{!nslG}.

Definition nsl_key (k : term) : iProp :=
  termT Pub (TKey Enc k) ∗ stermT Sec (TKey Dec k).

Global Instance nsl_key_persistent k :
  Persistent (nsl_key k).
Proof. apply _. Qed.

Definition msg1_pred (kB : term) m1 : iProp :=
  ∃ nA kA, ⌜m1 = Spec.of_list [nA; TKey Enc kA]⌝ ∧
           stermT Sec nA ∧ nsl_key kA.

Global Instance msg1_pred_persistent kB m1 : Persistent (msg1_pred kB m1).
Proof. apply _. Qed.

Definition msg2_pred kA m2 : iProp :=
  ∃ nA nB kB,
    ⌜m2 = Spec.of_list [nA; nB; TKey Enc kB]⌝ ∧
    stermT Sec nB ∧
    stermT Sec (TKey Dec kB) ∧
    session nsl_sess_name Resp kA kB nA nB.

Global Instance msg2_pred_persistent kA m2 : Persistent (msg2_pred kA m2).
Proof.
case: m2; try by move=> *; apply _.
Qed.

Definition msg3_pred kB nB : iProp :=
  □ ∀ nA kA,
    session nsl_sess_name Resp kA kB nA nB -∗
    session nsl_sess_name Init kA kB nA nB ∗
    stermT Sec nA ∗
    stermT Sec (TKey Dec kA).

Global Instance msg3_pred_persistent kB nB : Persistent (msg3_pred kB nB).
Proof. apply _. Qed.

Variable nsl_sess_inv : role → term → term → term → term → iProp.

Definition nsl_inv : iProp :=
  session_inv nsl_sess_name (cryptoN.@"nsl") nsl_sess_inv.

Definition nsl_ctx : iProp :=
  session_ctx nsl_sess_name (cryptoN.@"nsl") nsl_sess_inv.

Lemma nsl_key_pub k : nsl_key k -∗ termT Pub (TKey Enc k).
Proof. by iDestruct 1 as "[??]". Qed.

Variable send recv gen : val.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition initiator (skA pkA pkB nA : val) : val := λ: <>,
  bind: "m1"   := tenc (nroot.@"m1") pkB (term_of_list [nA; pkA]) in
  send "m1";;
  bind: "m2"   := tdec (nroot.@"m2") skA (recv #()) in
  bind: "m2"   := list_of_term "m2" in
  bind: "nA'"  := "m2" !! #0 in
  bind: "nB"   := "m2" !! #1 in
  bind: "pkB'" := "m2" !! #2 in
  if: eq_term "nA'" nA && eq_term "pkB'" pkB then
    bind: "m3" := tenc (nroot.@"m3") pkB "nB" in
    send "m3";;
    SOME "nB"
  else NONE.

Definition responder (skB pkB : val) : val := λ: <>,
  bind: "m1" := tdec (nroot.@"m1") skB (recv #()) in
  bind: "m1" := list_of_term "m1" in
  bind: "nA" := "m1" !! #0 in
  bind: "pkA" := "m1" !! #1 in
  bind: "kt" := is_key "pkA" in
  if: "kt" = repr Enc then
    let: "nB" := gen #() in
    bind: "m2" := tenc (nroot.@"m2") "pkA" (term_of_list ["nA"; "nB"; pkB]) in
    send "m2";;
    bind: "m3" := tdec (nroot.@"m3") skB (recv #()) in
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

Hypothesis wp_gen : forall E l kA kB nA Ψ,
  (∀ nB,
      crypto_meta_token nB (↑cryptoN.@"nsl") -∗
      stermT l nB -∗
      guarded (l = Sec) (nsl_sess_inv Resp kA kB nA nB) -∗
      Ψ nB) -∗
  WP gen #() @ E {{ Ψ }}.

Lemma termT_msg1 E l kA kB (nA : term) :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  crypto_inv_meta (nroot.@"m1") msg1_pred -∗
  nsl_key kA -∗
  stermT l nA -∗
  termT Pub (TKey Enc kB) -∗
  stermT l (TKey Dec kB) ={E}=∗
  ▷ termT Pub (TEnc kB (Spec.tag (nroot.@"m1") (Spec.of_list [nA; TKey Enc kA]))).
Proof.
iIntros (?) "#ctx #Hm1 #HkA #HnA #HkB_lo #HkB_hi".
iAssert (guarded (l = Sec) (stermT Sec (TKey Dec kB))) as "HkB".
  by iIntros "->".
iDestruct "HkA" as "[HkA_e HkA_d]".
do 2![iModIntro].
iApply termT_aenc_pub_secG; eauto.
  iApply termT_of_list => /=.
  iSplit; first by iApply stermT_termT.
  iSplit => //.
  by iApply (@sub_termT _ _ _ Pub) => //.
by case: l => //=; iModIntro; iExists _, _; rewrite /nsl_key; eauto.
Qed.

Lemma termT_msg2 E l l_d kA kB nA nB :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  crypto_inv_meta (nroot.@"m2") msg2_pred -∗
  ▷ termT Pub (TKey Enc kA) -∗
  stermT l_d (TKey Dec kA) -∗
  guarded (l = Sec) (nsl_key kA) -∗
  nsl_key kB -∗
  stermT l nA -∗
  stermT (l ⊔ l_d) nB -∗
  guarded (l ⊔ l_d = Sec) (session nsl_sess_name Resp kA kB nA nB) ={E}=∗
  ▷ termT Pub (TEnc kA (Spec.tag (nroot.@"m2") (Spec.of_list [nA; nB; TKey Enc kB]))).
Proof.
iIntros (?) "#ctx #Hm2 #HkA_enc #HkA_dec #[_ HkA] #[??] #HnA #HnB #fragB".
do !iModIntro.
iAssert (guarded (l ⊔ l_d = Sec) (stermT Sec (TKey Dec kA))) as "{HkA} HkA".
  by case: (l) (l_d) => [] //= [] //=.
iAssert (termT (l ⊔ l_d) nA) as "{HnA} HnA".
  iPoseProof (stermT_termT with "HnA") as "?".
  iApply sub_termT; last by eauto.
  by case: (l) (l_d).
iApply termT_aenc_pub_secG; eauto.
  rewrite termT_of_list /=.
  iSplit => //.
  iSplit; first by iApply stermT_termT.
  by iSplit; first iApply sub_termT_pub.
by iIntros "!> -> /="; iExists _, _, _; do ![iSplit => //].
Qed.

Lemma msg1_pred_elimG E l (ts : list term) kA kB nA :
  ↑cryptoN.@"nsl" ⊆ E →
  ts !! 0 = Some nA →
  ts !! 1 = Some (TKey Enc kA) →
  nsl_ctx -∗
  termT l (Spec.of_list ts) -∗
  guarded (l = Sec) (msg1_pred kB (Spec.of_list ts)) ={E}=∗
  stermT l nA ∧
  ▷ termT Pub (TKey Enc kA) ∧
  guarded (l = Sec) (nsl_key kA).
Proof.
iIntros (? get_nA get_kA) "#ctx #term_ts mP".
rewrite termT_of_list.
iPoseProof (big_sepL_lookup with "term_ts") as "HnA"; first exact: get_nA.
iPoseProof (big_sepL_lookup with "term_ts") as "HkA"; first exact: get_kA.
case: l => /=; first by iModIntro; rewrite stermT_eq; eauto.
iDestruct "mP" as (nA' kA') "{HnA HkA} (%e & HnA & #HkA)".
move/Spec.of_list_inj: e get_nA get_kA => -> [] -> [] ->; eauto.
by iPoseProof "HkA" as "(?&?)"; eauto.
Qed.

Lemma msg2_pred_elimG `{Decision G} (ts : list term) kA kB nA nB :
  ts !! 0 = Some nA →
  ts !! 1 = Some nB →
  ts !! 2 = Some (TKey Enc kB) →
  guarded G (msg2_pred kA (Spec.of_list ts)) -∗
  guarded G (stermT Sec nB ∧ stermT Sec (TKey Dec kB) ∧
             session nsl_sess_name Resp kA kB nA nB).
Proof.
iIntros (get_nA get_nB get_kB) "mP".
rewrite /guarded; case: decide => //= _.
iDestruct "mP" as (nA' nB' kB') "(%e_m & nBP & frag)".
move/Spec.of_list_inj: e_m get_nA get_nB get_kB => -> /= [] -> [] -> [] ->.
by eauto.
Qed.

Lemma msg3_pred_elimG l kA kB nA nB :
  guarded (l = Sec) (msg3_pred kB nB) -∗
  guarded (l = Sec) (session nsl_sess_name Resp kA kB nA nB) -∗
  guarded (l = Sec) (session nsl_sess_name Init kA kB nA nB ∗
                     stermT Sec nA ∗
                     stermT Sec (TKey Dec kA)).
Proof.
iIntros "#HnB #sess -> /=".
by iApply "HnB"; iApply "sess".
Qed.

Lemma wp_initiator kA kB (nA : term) l E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  crypto_inv_meta (nroot.@"m1") msg1_pred -∗
  crypto_inv_meta (nroot.@"m2") msg2_pred -∗
  crypto_inv_meta (nroot.@"m3") msg3_pred -∗
  stermT l nA -∗
  (∀ nB, guarded (l = Sec) (nsl_sess_inv Init kA kB nA nB)) -∗
  crypto_meta_token nA (↑cryptoN.@"nsl") -∗
  nsl_key kA -∗
  termT Pub (TKey Enc kB) -∗
  stermT l (TKey Dec kB) -∗
  (∀ onB : option term,
      (if onB is Some nB then
         stermT l nB ∗
         guarded (l = Sec) (nsl_sess_inv Resp kA kB nA nB)
       else True) -∗
      Ψ (repr onB)) -∗
  WP initiator (TKey Dec kA) (TKey Enc kA) (TKey Enc kB) nA #() @ E
     {{ Ψ }}.
Proof.
rewrite /initiator.
iIntros (?) "#ctx #? #? #? #HnA inv_nA unreg #HkA #HkB_lo #HkB_hi Hpost".
wp_list (_ :: _ :: []).
wp_term_of_list.
wp_tenc => /=.
iMod (termT_msg1 with "ctx [//] HkA HnA HkB_lo HkB_hi") as "#Hm1" => //.
wp_pures; wp_bind (send _); iApply wp_send; eauto.
iClear "Hm1"; wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (m2) "#Hm2"; wp_tdec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_lookup nA' enA'; last protocol_failure.
wp_lookup nB  enB; last protocol_failure.
wp_lookup pkB' epkB'; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst pkB'.
wp_tenc.
iDestruct (termT_adec_pub_sec with "Hm2 []")
    as (lm2) "{Hm2} [#Hm2 #sessB]"; eauto.
wp_pures.
iPoseProof (msg2_pred_elimG with "sessB")
  as "{sessB} (HnB & HkB & sessB)"; eauto.
rewrite termT_of_list.
iPoseProof (big_sepL_lookup with "Hm2") as "m2_nA"; first exact: enA'.
iPoseProof (big_sepL_lookup with "Hm2") as "m2_nB"; first exact: enB.
iPoseProof (big_sepL_lookup with "Hm2") as "m2_pkB"; first exact: epkB'.
iAssert (⌜lm2 = l⌝)%I as "->".
  case: l lm2 => [] [] //=.
    by iDestruct (stermT_agree with "HkB_hi HkB") as "%".
  rewrite stermT_eq; iDestruct "HnA" as "[_ #contra]".
  by iDestruct ("contra" with "m2_nA") as "[]".
iSpecialize ("inv_nA" $! nB).
iMod (session_beginG (l = Sec) with "[] inv_nA [unreg]")
    as "[#sessA close]" => //.
  by iIntros "_".
iMod ("close" with "sessB") as "inv_resp" => //=.
wp_bind (send _); iApply wp_send.
  iModIntro.
  iAssert (guarded (l = Sec) (stermT Sec (TKey Dec kB))) as "?".
    by iIntros "->".
  iApply (termT_aenc_pub_secG _ _ _ l) => //; eauto.
  iIntros "!> -> !> %nA' %kA' #sessB'".
  iDestruct (session_agree with "sessB' sessB") as "/= %e" => //.
  case: e => [] -> [] _ [] -> _; iSplit => //.
  by iDestruct "HkA" as "[??]"; iSplit.
wp_pures; iApply ("Hpost" $! (Some nB)); iFrame.
by case: (l); rewrite // [stermT Pub nB]stermT_eq.
Qed.

Lemma wp_responder kB E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  crypto_inv_meta (nroot.@"m1") msg1_pred -∗
  crypto_inv_meta (nroot.@"m2") msg2_pred -∗
  crypto_inv_meta (nroot.@"m3") msg3_pred -∗
  nsl_key kB -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ l kA,
           ⌜pkA = TKey Enc kA⌝ ∗
           termT Pub pkA ∗
           stermT l (TKey Dec kA) ∗
           stermT l nA ∗
           stermT l nB ∗
           guarded (l = Sec) (nsl_sess_inv Init kA kB nA nB)
       else True) -∗
       Ψ (repr ot)) -∗
  WP responder (TKey Dec kB) (TKey Enc kB) #() @ E {{ Ψ }}.
Proof.
iIntros (?) "#ctx #? #? #? #HkB Hpost".
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
iPoseProof "HkB" as "(? & ?)".
wp_pures.
iDestruct (termT_adec_pub_sec with "Hm1 []")
  as (lm1) "{Hm1} [Hm1 #sessA]"; eauto.
iAssert (termT lm1 (TKey Enc kA)) as "He".
  rewrite termT_of_list.
  by iApply (big_sepL_lookup with "Hm1").
iDestruct (termT_TKey_swap with "He") as (l_d) "Hd".
wp_pures; wp_bind (gen _); iApply (wp_gen _ (lm1 ⊔ l_d) kA kB nA).
iIntros (nB) "unreg #HnB inv".
wp_pures.
wp_list (_ :: _ :: _ :: []); wp_term_of_list.
wp_tenc; wp_pures.
iMod (session_beginG with "[] inv [unreg]") as "[#sessB close]" => //.
  by iIntros "_".
iMod (msg1_pred_elimG with "ctx Hm1 sessA") as "# (HnA & HkA_enc & HkA)" => //.
iMod (termT_msg2 with "ctx [//] HkA_enc Hd HkA HkB HnA HnB sessB") as "#Hm2" => //.
wp_bind (send _); iApply wp_send => //.
wp_pures; wp_bind (recv _); iApply wp_recv; iIntros (m3) "#Hm3".
wp_tdec m3; last protocol_failure.
iDestruct (termT_adec_pub_sec with "Hm3 [//]")
  as (lm3) "{Hm3} [#Hm3 #Hprot3]".
wp_eq_term e; last protocol_failure; subst m3.
iAssert (⌜lm1 ⊔ l_d ⊑ lm3⌝)%I as "%lm1_lm3".
  by iDestruct "HnB" as "[_ #Hmin]"; iApply "Hmin".
iAssert (guarded (lm1 ⊔ l_d = Sec) (msg3_pred kB nB)) as "{Hprot3 Hm3} Hm3".
  iIntros "#%e".
  rewrite e in lm1_lm3.
  by case: lm3 lm1_lm3.
clear lm1_lm3 lm3.
iPoseProof (msg3_pred_elimG with "Hm3 sessB") as "{sessA} (sessA & HnA' & HkA')" => //=.
iAssert (⌜lm1 = l_d⌝)%I as "<-".
  case: (lm1) (l_d) => [] //= [] //=.
  - by iPoseProof (stermT_agree with "HnA HnA'") as "%".
  - by iPoseProof (stermT_agree with "Hd HkA'") as "%".
rewrite !level_join_idemp.
iMod ("close" with "sessA") as "inv".
wp_pures.
iApply ("Hpost" $! (Some (_, _, _))).
iExists lm1, _; do 5![iSplit => //].
Qed.

End NSL.
