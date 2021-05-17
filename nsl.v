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
           (pterm nA ↔ ▷ (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB))) ∧
           pterm (TKey Enc kA).

Definition msg2_pred kA m2 : iProp :=
  ∃ nA nB kB,
    ⌜m2 = Spec.of_list [nA; nB; TKey Enc kB]⌝ ∧
    (pterm nB ↔ ▷ (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB))) ∧
    session nsl_sess_name Resp kA kB nA nB.

Definition msg3_pred kB nB : iProp :=
  ∀ nA kA,
    session nsl_sess_name Resp kA kB nA nB -∗
    session nsl_sess_name Init kA kB nA nB ∧
    (pterm nA ↔ ▷ (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB))).

Variable nsl_sess_inv : role → term → term → term → term → iProp.

Definition nsl_inv : iProp :=
  session_inv nsl_sess_name (cryptoN.@"nsl") nsl_sess_inv.

Definition nsl_ctx : iProp :=
  session_ctx nsl_sess_name (cryptoN.@"nsl") nsl_sess_inv.

Variable send recv : val.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition initiator : val := λ: "skA" "pkA" "pkB" "nA",
  bind: "m1"   := tenc (nroot.@"m1") "pkB" (term_of_list ["nA"; "pkA"]) in
  send "m1";;
  bind: "m2"   := tdec (nroot.@"m2") "skA" (recv #()) in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nA'"; "nB"; "pkB'"] := "m2" in
  if: eq_term "nA'" "nA" && eq_term "pkB'" "pkB" then
    bind: "m3" := tenc (nroot.@"m3") "pkB" "nB" in
    send "m3";;
    SOME "nB"
  else NONE.

Definition responder : val := λ: "skB" "pkB" "nB",
  bind: "m1" := tdec (nroot.@"m1") "skB" (recv #()) in
  bind: "m1" := list_of_term "m1" in
  list_match: ["nA"; "pkA"] := "m1" in
  bind: "kt" := is_key "pkA" in
  if: "kt" = repr Enc then
    bind: "m2" := tenc (nroot.@"m2") "pkA" (term_of_list ["nA"; "nB"; "pkB"]) in
    send "m2";;
    bind: "m3" := tdec (nroot.@"m3") "skB" (recv #()) in
    if: eq_term "m3" "nB" then SOME ("pkA", "nA") else NONE
  else NONE.

Implicit Types Ψ : val → iProp.

Hypothesis wp_send : forall E t Ψ,
  ▷ pterm t -∗
  Ψ #() -∗
  WP send t @ E {{ Ψ }}.

Hypothesis wp_recv : forall E Ψ,
  (∀ t, pterm t -∗ Ψ t) -∗
  WP recv #() @ E {{ Ψ }}.

Lemma pterm_msg1I kA kB (nA : term) :
  crypto_enc (nroot.@"m1") msg1_pred -∗
  pterm (TKey Enc kA) -∗
  sterm nA -∗
  □ (pterm nA ↔ ▷ (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB))) -∗
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
  □ (pterm nB ↔ ▷ (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB))) -∗
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

Lemma pterm_msg1E kA kB nA :
  crypto_enc (nroot.@"m1") msg1_pred -∗
  pterm (TEnc kB (Spec.tag (nroot.@"m1") (Spec.of_list [nA; TKey Enc kA]))) -∗
  ▷ (pterm (TKey Enc kA) ∧ sterm nA ∧
     (pterm nA ∨
      □ (pterm nA ↔ ▷ (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB))))).
Proof.
iIntros "#m1P #Hts".
iDestruct (pterm_TEncE with "Hts [//]") as "{Hts} [[HkB Hts]|Hts]".
  rewrite pterm_of_list /=.
  iDestruct "Hts" as "(HnA & HkA & _)".
  iAssert (sterm nA) as "#?". by iApply pterm_sterm.
  by eauto.
iDestruct "Hts" as "(#inv & Hts & _)"; iModIntro.
iDestruct "inv" as (nA' kA') "(%e & HnA & #HkA)".
move/Spec.of_list_inj: e => [] <- <-.
rewrite sterm_of_list /=; iDestruct "Hts" as "(? & ? & ?)".
by eauto.
Qed.

Lemma pterm_msg2E kA kB nA nB :
  crypto_enc (nroot.@"m2") msg2_pred -∗
  pterm (TEnc kA (Spec.tag (nroot.@"m2") (Spec.of_list [nA; nB; TKey Enc kB]))) -∗
  ▷ (sterm nB ∧
     (pterm nA ∧ pterm nB ∨
      □ (pterm nB ↔ ▷ (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB))) ∧
      session nsl_sess_name Resp kA kB nA nB)).
Proof.
iIntros "#? #Hts".
iDestruct (pterm_TEncE with "Hts [//]") as "{Hts} [[_ Hts] | Hts]".
  rewrite pterm_of_list /=.
  iDestruct "Hts" as "(? & ? & ? & ?)".
  iAssert (sterm nB) as "#?". by iApply pterm_sterm.
  by eauto.
iDestruct "Hts" as "(#inv & Hts & _)"; iModIntro.
iDestruct "inv" as (nA' nB' kB') "(%e_m & #nBP & frag)".
case/Spec.of_list_inj: e_m => <- <- <-; rewrite sterm_of_list /=.
iDestruct "Hts" as "(?&?&?)"; by eauto.
Qed.

Lemma wp_initiator kA kB (nA : term) E Ψ :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  crypto_enc (nroot.@"m1") msg1_pred -∗
  crypto_enc (nroot.@"m2") msg2_pred -∗
  crypto_enc (nroot.@"m3") msg3_pred -∗
  pterm (TKey Enc kA) -∗
  pterm (TKey Enc kB) -∗
  sterm nA -∗
  □ (pterm nA ↔ ▷ (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB))) -∗
  (∀ nB, pterm nA ∨ nsl_sess_inv Init kA kB nA nB) -∗
  crypto_meta_token nA (↑cryptoN.@"nsl".@nA) -∗
  (∀ onB : option term,
      (if onB is Some nB then
         sterm nB ∧
         ((pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) ∨
           nsl_sess_inv Resp kA kB nA nB)
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
rewrite repr_list_eq.
case: m2 => [|nA'  m2] /=; wp_pures; first protocol_failure. 
case: m2 => [|nB   m2] /=; wp_pures; first protocol_failure.  
case: m2 => [|pkB' m2] /=; wp_pures; first protocol_failure.
case: m2 => [|??] /=; wp_pures; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst pkB'.
wp_tenc.
iPoseProof (pterm_msg2E with "[//] Hm2") as "{Hm2} [HnB Hm2]"; eauto.
wp_pures; iDestruct "Hm2" as "[[p_nA' ?]|[p_nB sessB]]".
  iSpecialize ("p_nA" with "p_nA'").
  wp_bind (send _); iApply wp_send.
    iModIntro; iApply pterm_TEncIP => //.
    by rewrite pterm_tag.
  by wp_pures; iApply ("Hpost" $! (Some nB)); eauto.
iDestruct ("inv" $! nB) as "[#p_nA' | inv]".
  iSpecialize ("p_nA" with "p_nA'").
  wp_bind (send _); iApply wp_send.
    iModIntro; iApply pterm_TEncIP => //.
    by rewrite pterm_tag; iApply "p_nB"; iApply "p_nA".
  by wp_pures; iApply ("Hpost" $! (Some nB)); eauto.
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

Lemma wp_responder kB E Ψ nB :
  ↑cryptoN.@"nsl" ⊆ E →
  nsl_ctx -∗
  crypto_enc (nroot.@"m1") msg1_pred -∗
  crypto_enc (nroot.@"m2") msg2_pred -∗
  crypto_enc (nroot.@"m3") msg3_pred -∗
  pterm (TKey Enc kB) -∗
  crypto_meta_token nB (↑cryptoN.@"nsl".@nB) -∗
  sterm nB -∗
  (∀ kA nA, |==> □ (pterm nB ↔ ▷ (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB))) ∗
                 nsl_sess_inv Resp kA kB nA nB) -∗
  (∀ ot : option (term * term),
      (if ot is Some (pkA, nA) then
         ∃ kA,
           ⌜pkA = TKey Enc kA⌝ ∧
           pterm pkA ∧
           sterm nA ∧
           □ (pterm nA ↔ pterm nB) ∧
           ((pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) ∨
             nsl_sess_inv Init kA kB nA nB)
       else True) -∗
       Ψ (repr ot)) -∗
  WP responder (TKey Dec kB) (TKey Enc kB) nB @ E {{ Ψ }}.
Proof.
iIntros (?) "#ctx #? #? #? #e_kB unreg #s_nB set_nB Hpost".
rewrite /responder; wp_pures.
wp_bind (recv _); iApply wp_recv; iIntros (m1) "#Hm1".
wp_tdec m1; last protocol_failure.
wp_list_of_term m1; last protocol_failure.
rewrite repr_list_eq.
case: m1 => [|nA m1] /=; first protocol_failure.
case: m1 => [|pkA m1] /=; first protocol_failure.
case: m1 => [|??] /=; last protocol_failure.
wp_is_key_eq kt kA et; last protocol_failure; subst pkA.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Enc)); last protocol_failure.
case: kt => // _.
wp_pures.
iDestruct (pterm_msg1E with "[] Hm1") as "{Hm1} Hm1"; eauto.
wp_list (_ :: _ :: _ :: []); wp_term_of_list.
iMod ("set_nB" $! kA nA) as "[#p_nB inv]".
wp_tenc; wp_pures.
iDestruct "Hm1" as "(e_kA & s_nA & Hm1)".
iAssert (□ (▷ (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) → pterm nA))%I as "#p_nA".
  iDestruct "Hm1" as "[?|#e]"; eauto.
  by iIntros "!> ?"; iApply "e"; eauto.
iMod (session_begin with "[] inv [unreg]") as "[#sessB close]" => //.
iPoseProof (pterm_msg2I with "[//] [//] e_kB s_nA [] s_nB [] sessB") as "Hm2".
- by iIntros "!> ?"; iApply "p_nA"; eauto.
- by eauto.
wp_bind (send _); iApply wp_send => //.
wp_pures; wp_bind (recv _); iApply wp_recv; iIntros (m3) "#Hm3".
wp_tdec m3; last protocol_failure.
wp_eq_term e; last protocol_failure; subst m3.
iPoseProof (pterm_TEncE with "Hm3 [//]") as "[[_ pub]|sec]".
  iSpecialize ("p_nB" with "pub").
  wp_pures. iApply ("Hpost" $! (Some (TKey Enc kA, nA))).
  iExists kA; do 4!iSplit => //.
    iModIntro; iSplit; iIntros "#?" => //.
    iDestruct "Hm1" as "[?|#Hm1]"; eauto.
    iApply "Hm1". by iApply "p_nB".
  iLeft. by iApply "p_nB".
iDestruct "sec" as "(#HnB & _ & _)".
wp_if.
iDestruct ("HnB" with "sessB") as "{p_nA} [#sessA p_nA]".
iMod ("close" with "sessA") as "inv".
wp_pures.
iApply ("Hpost" $! (Some (TKey Enc kA, nA))).
iExists kA; do 4!iSplit => //.
  iModIntro; iSplit; iIntros "#?" => //.
  + iApply "p_nB". by iApply "p_nA".
  + iApply "p_nA". by iApply "p_nB".
by eauto.
Qed.

End NSL.

Arguments nslG Σ : clear implicits.
