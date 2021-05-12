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
Implicit Types rl : role.

Class nslG := {
  in_nsl_sessG :> sessionG Σ;
  nsl_sess_name : gname;
}.

Context `{!nslG}.

Definition msg1_pred (kB : term) m1 : iProp :=
  ∃ nA kA, ⌜m1 = Spec.of_list [nA; TKey Enc kA]⌝ ∧
           □ (pterm nA ↔ pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) ∧
           pterm (TKey Enc kA).

Global Instance msg1_pred_persistent kB m1 : Persistent (msg1_pred kB m1).
Proof. apply _. Qed.

Definition msg2_pred kA m2 : iProp :=
  ∃ nA nB kB,
    ⌜m2 = Spec.of_list [nA; nB; TKey Enc kB]⌝ ∧
    □ (pterm nB ↔ pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) ∧
    session nsl_sess_name Resp kA kB nA nB.

Global Instance msg2_pred_persistent kA m2 : Persistent (msg2_pred kA m2).
Proof.
case: m2; try by move=> *; apply _.
Qed.

Definition msg3_pred kB nB : iProp :=
  ∀ nA kA,
    session nsl_sess_name Resp kA kB nA nB -∗
    session nsl_sess_name Init kA kB nA nB ∧
    (pterm nA ↔ pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)).

Variable nsl_sess_inv : role → term → term → term → term → iProp.

Definition nsl_inv : iProp :=
  session_inv nsl_sess_name (cryptoN.@"nsl") nsl_sess_inv.

Definition nsl_ctx : iProp :=
  session_ctx nsl_sess_name (cryptoN.@"nsl") nsl_sess_inv.

Variable send recv gen : val.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition initiator : val := λ: "skA" "pkA" "pkB" "nA",
  bind: "m1"   := tenc (nroot.@"m1") "pkB" (term_of_list ["nA"; "pkA"]) in
  send "m1";;
  bind: "m2"   := tdec (nroot.@"m2") "skA" (recv #()) in
  bind: "m2"   := list_of_term "m2" in
  bind: "nA'"  := "m2" !! #0 in
  bind: "nB"   := "m2" !! #1 in
  bind: "pkB'" := "m2" !! #2 in
  if: eq_term "nA'" "nA" && eq_term "pkB'" "pkB" then
    bind: "m3" := tenc (nroot.@"m3") "pkB" "nB" in
    send "m3";;
    SOME "nB"
  else NONE.

Definition responder : val := λ: "skB" "pkB",
  bind: "m1" := tdec (nroot.@"m1") "skB" (recv #()) in
  bind: "m1" := list_of_term "m1" in
  bind: "nA" := "m1" !! #0 in
  bind: "pkA" := "m1" !! #1 in
  bind: "kt" := is_key "pkA" in
  if: "kt" = repr Enc then
    let: "nB" := gen #() in
    bind: "m2" := tenc (nroot.@"m2") "pkA" (term_of_list ["nA"; "nB"; "pkB"]) in
    send "m2";;
    bind: "m3" := tdec (nroot.@"m3") "skB" (recv #()) in
    if: eq_term "m3" "nB" then SOME ("pkA", "nA", "nB") else NONE
  else NONE.

Implicit Types Ψ : val → iProp.

Hypothesis wp_send : forall E t Ψ,
  ▷ pterm t -∗
  Ψ #() -∗
  WP send t @ E {{ Ψ }}.

Hypothesis wp_recv : forall E Ψ,
  (∀ t, pterm t -∗ Ψ t) -∗
  WP recv #() @ E {{ Ψ }}.

Hypothesis wp_gen : forall E kA kB nA Ψ,
  (∀ nB,
      crypto_meta_token nB (↑cryptoN.@"nsl".@nB) -∗
      sterm nB -∗
      □ (pterm nB ↔ pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) -∗
      nsl_sess_inv Resp kA kB nA nB -∗
      Ψ nB) -∗
  WP gen #() @ E {{ Ψ }}.

Lemma pterm_msg1I kA kB (nA : term) :
  crypto_enc (nroot.@"m1") msg1_pred -∗
  pterm (TKey Enc kA) -∗
  sterm nA -∗
  □ (pterm nA ↔ pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) -∗
  pterm (TKey Enc kB) -∗
  ▷ pterm (TEnc kB (Spec.tag (nroot.@"m1") (Spec.of_list [nA; TKey Enc kA]))).
Proof.
iIntros "#Hm1 #HkA #HnA #HnA_hi #HkB".
iModIntro.
iApply pterm_TEncIS; eauto.
- by iApply pterm_sterm.
- iModIntro.
  iExists _, _; iSplit; eauto.
  rewrite sterm_of_list /=; do !iSplit => //.
  by iApply pterm_sterm.
- iIntros "!> HkB_dec".
  rewrite pterm_of_list /=; do !iSplit => //.
  iApply "HnA_hi"; eauto.
Qed.

Lemma pterm_msg2I kA kB nA nB :
  crypto_enc (nroot.@"m2") msg2_pred -∗
  ▷ pterm (TKey Enc kA) -∗
  pterm (TKey Enc kB) -∗
  sterm nA -∗
  □ (pterm (TKey Dec kA) → pterm nA) -∗
  sterm nB -∗
  □ (pterm nB ↔ pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) -∗
  session nsl_sess_name Resp kA kB nA nB -∗
  ▷ pterm (TEnc kA (Spec.tag (nroot.@"m2") (Spec.of_list [nA; nB; TKey Enc kB]))).
Proof.
iIntros "#Hm2 #HAenc #HBenc #HnAhi #HnAlo #HnBhi #HnBlo #sess !>".
iApply pterm_TEncIS; eauto.
- by iApply pterm_sterm.
- iModIntro; iExists _, _, _; do !iSplit => //.
  rewrite sterm_of_list /=; do !iSplit => //.
  by iApply pterm_sterm.
iIntros "!> #pub".
iSpecialize ("HnAlo" with "pub").
rewrite pterm_of_list /=; do !iSplit => //.
by iApply "HnBlo"; eauto.
Qed.

Lemma pterm_msg1E ts kA kB nA :
  ts !! 0 = Some nA →
  ts !! 1 = Some (TKey Enc kA) →
  crypto_enc (nroot.@"m1") msg1_pred -∗
  pterm (TEnc kB (Spec.tag (nroot.@"m1") (Spec.of_list ts))) -∗
  ▷ (pterm (TKey Enc kA) ∧ sterm nA ∧
     (pterm nA ∨
      □ (pterm nA ↔ pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)))).
Proof.
iIntros (get_nA get_kA) "#m1P #Hts".
iDestruct (pterm_TEncE with "Hts [//]") as "{Hts} [[HkB Hts]|Hts]".
  rewrite pterm_of_list.
  iPoseProof (big_sepL_lookup with "Hts") as "HnA"; first exact: get_nA.
  iPoseProof (big_sepL_lookup with "Hts") as "HkA"; first exact: get_kA.
  iAssert (sterm nA) as "#?". by iApply pterm_sterm.
  by eauto.
iDestruct "Hts" as "(#inv & Hts & _)"; iModIntro.
iDestruct "inv" as (nA' kA') "(%e & HnA & #HkA)".
move/Spec.of_list_inj: e get_nA get_kA => -> [] -> [] ->.
rewrite sterm_of_list /=; iDestruct "Hts" as "(? & ? & ?)".
by eauto.
Qed.

Lemma pterm_msg2E (ts : list term) kA kB nA nB :
  ts !! 0 = Some nA →
  ts !! 1 = Some nB →
  ts !! 2 = Some (TKey Enc kB) →
  crypto_enc (nroot.@"m2") msg2_pred -∗
  pterm (TEnc kA (Spec.tag (nroot.@"m2") (Spec.of_list ts))) -∗
  ▷ (sterm nB ∧
     (pterm nA ∧ pterm nB ∨
      □ (pterm nB ↔ pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) ∧
      session nsl_sess_name Resp kA kB nA nB)).
Proof.
iIntros (get_nA get_nB get_kB) "#? #Hts".
iDestruct (pterm_TEncE with "Hts [//]") as "{Hts} [[_ Hts] | Hts]".
  rewrite pterm_of_list.
  iPoseProof (big_sepL_lookup with "Hts") as "HnA"; first exact: get_nA.
  iPoseProof (big_sepL_lookup with "Hts") as "HnB"; first exact: get_nB.
  iPoseProof (big_sepL_lookup with "Hts") as "HkB"; first exact: get_kB.
  iAssert (sterm nB) as "#?". by iApply pterm_sterm.
  by eauto.
iDestruct "Hts" as "(#inv & Hts & _)"; iModIntro.
iDestruct "inv" as (nA' nB' kB') "(%e_m & #nBP & frag)".
move/Spec.of_list_inj: e_m get_nA get_nB get_kB => -> /= [] -> [] -> [] ->.
rewrite sterm_of_list /=.
iDestruct "Hts" as "(?&?&?)".
by eauto.
Qed.

(*
Lemma pterm_msg3E kA kB nA nB :
  crypto_enc (nroot.@"m3") msg3_pred -∗
  pterm (TEnc kB (Spec.tag (nroot.@"m3") nB)) -∗
  ▷ (pterm nB ∨ session nsl_sess_name Init kA kB nA nB)

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
*)

Lemma wp_initiator kA kB (nA : term) E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  crypto_enc (nroot.@"m1") msg1_pred -∗
  crypto_enc (nroot.@"m2") msg2_pred -∗
  crypto_enc (nroot.@"m3") msg3_pred -∗
  pterm (TKey Enc kA) -∗
  pterm (TKey Enc kB) -∗
  sterm nA -∗
  □ (pterm nA ↔ pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) -∗
  (∀ nB, pterm nA ∨ nsl_sess_inv Init kA kB nA nB) -∗
  crypto_meta_token nA (↑cryptoN.@"nsl".@nA) -∗
  (∀ onB : option term,
      (if onB is Some nB then pterm nA ∨ nsl_sess_inv Resp kA kB nA nB
       else True) -∗
      Ψ (repr onB)) -∗
  WP initiator (TKey Dec kA) (TKey Enc kA) (TKey Enc kB) nA @ E
     {{ Ψ }}.
Proof.
rewrite /initiator.
iIntros (?) "#ctx #? #? #? #enc_kA #enc_kB #s_nA #p_nA inv unreg Hpost".
wp_list (_ :: _ :: []).
wp_term_of_list.
wp_tenc => /=.
iPoseProof (pterm_msg1I with "[//] enc_kA s_nA p_nA enc_kB") as "#Hm1".
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
iPoseProof (pterm_msg2E with "[//] Hm2") as "{Hm2} [HnB Hm2]"; eauto.
wp_pures; iDestruct "Hm2" as "[[??]|[p_nB sessB]]".
  wp_bind (send _); iApply wp_send.
    iModIntro; iApply pterm_TEncIP => //.
    by rewrite pterm_tag.
  wp_pures; iApply ("Hpost" $! (Some nB)); eauto.
iDestruct ("inv" $! nB) as "[#? | inv]".
  wp_bind (send _); iApply wp_send.
    iModIntro; iApply pterm_TEncIP => //.
    by rewrite pterm_tag; iApply "p_nB"; iApply "p_nA".
  wp_pures; iApply ("Hpost" $! (Some nB)); eauto.
iMod (session_begin with "[] inv [unreg]") as "[#sessA close]" => //.
iMod ("close" with "sessB") as "inv_resp" => //=.
wp_bind (send _); iApply wp_send.
  iModIntro; iApply pterm_TEncIS; eauto.
  - by iApply pterm_sterm.
  - iIntros "!> %nA' %kA' #sessB'".
    iDestruct (session_agree with "sessB' sessB") as "/= %e" => //.
    by case: e => [] -> [] _ [] -> _; iSplit => //.
  - iIntros "!> #dec_kB". iApply "p_nB". by eauto.
wp_pures; iApply ("Hpost" $! (Some nB)); eauto.
Qed.

Lemma wp_responder kB E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  crypto_enc (nroot.@"m1") msg1_pred -∗
  crypto_enc (nroot.@"m2") msg2_pred -∗
  crypto_enc (nroot.@"m3") msg3_pred -∗
  pterm (TKey Enc kB) -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ kA,
           ⌜pkA = TKey Enc kA⌝ ∧
           pterm pkA ∧
           sterm nA ∧
           sterm nB ∧
           □ (pterm nA ↔ pterm nB) ∧
           □ (pterm nB ↔ pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) ∧
           (pterm nA ∨ nsl_sess_inv Init kA kB nA nB)
       else True) -∗
       Ψ (repr ot)) -∗
  WP responder (TKey Dec kB) (TKey Enc kB) @ E {{ Ψ }}.
Proof.
iIntros (?) "#ctx #? #? #? #e_kB Hpost".
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
wp_pures.
iDestruct (pterm_msg1E with "[] Hm1") as "{Hm1} Hm1"; eauto.
wp_bind (gen _); iApply (wp_gen _ kA kB nA).
iIntros (nB) "unreg #s_nB #p_nB inv".
wp_pures.
iDestruct "Hm1" as "(e_kA & s_nA & Hm1)".
iAssert (□ (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB) → pterm nA))%I as "#p_nA".
  iDestruct "Hm1" as "[?|#e]"; eauto.
  by iIntros "!> ?"; iApply "e"; eauto.
wp_list (_ :: _ :: _ :: []); wp_term_of_list.
wp_tenc; wp_pures.
iMod (session_begin with "[] inv [unreg]") as "[#sessB close]" => //.
iPoseProof (pterm_msg2I with "[//] [//] e_kB s_nA [] s_nB [] sessB") as "Hm2".
- by iIntros "!> ?"; iApply "p_nA"; eauto.
- by eauto.
wp_bind (send _); iApply wp_send => //.
wp_pures; wp_bind (recv _); iApply wp_recv; iIntros (m3) "#Hm3".
wp_tdec m3; last protocol_failure.
wp_eq_term e; last protocol_failure; subst m3.
iPoseProof (pterm_TEncE with "Hm3 [//]") as "[[_ pub]|sec]".
  wp_pures. iApply ("Hpost" $! (Some (TKey Enc kA, nA, nB))).
  iExists kA; do 5!iSplit => //.
    iModIntro; iSplit; iIntros "#?" => //.
    iApply "p_nA". by iApply "p_nB".
  iSplit; eauto.
  iLeft. iApply "p_nA". by iApply "p_nB".
iDestruct "sec" as "(#HnB & _ & _)".
wp_if.
iDestruct ("HnB" with "sessB") as "{p_nA} [#sessA p_nA]".
iMod ("close" with "sessA") as "inv".
wp_pures.
iApply ("Hpost" $! (Some (TKey Enc kA, nA, nB))).
iExists kA; do 5!iSplit => //.
  iModIntro; iSplit; iIntros "#?" => //.
  + iApply "p_nB". by iApply "p_nA".
  + iApply "p_nA". by iApply "p_nB".
iSplit; eauto.
Qed.

End NSL.
