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

Context `{!heapG Σ, !cryptoG Σ, !network Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types rl : role.

Class nslG := {
  in_nsl_sessG :> sessionG Σ;
  nsl_sess_name : gname;
}.

Context `{!nslG}.

Definition corruption kA kB : iProp :=
  pterm (TKey Dec kA) ∨ pterm (TKey Dec kB).

Global Instance corruptionC : Comm (⊣⊢) corruption.
Proof. by move=> k k'; rewrite /corruption [(_ ∨ _)%I]comm. Qed.

Definition msg1_pred (kB : term) m1 : iProp :=
  ∃ nA kA, ⌜m1 = Spec.of_list [nA; TKey Enc kA]⌝ ∧
           (pterm nA ↔ ▷ corruption kA kB) ∧
           pterm (TKey Enc kA).

Definition msg2_pred kA m2 : iProp :=
  ∃ nA nB kB,
    ⌜m2 = Spec.of_list [nA; nB; TKey Enc kB]⌝ ∧
    (pterm nB ↔ ▷ corruption kA kB) ∧
    session nsl_sess_name Resp kA kB nA nB.

Definition msg3_pred kB nB : iProp :=
  ∀ nA kA,
    session nsl_sess_name Resp kA kB nA nB -∗
    session nsl_sess_name Init kA kB nA nB ∧
    (pterm nA ↔ ▷ corruption kA kB).

Variable N : namespace.

Variable nsl_sess_inv : role → term → term → term → term → iProp.

Definition nsl_inv : iProp :=
  session_inv nsl_sess_name N nsl_sess_inv.

Definition nsl_ctx : iProp :=
  session_ctx nsl_sess_name N nsl_sess_inv ∧
  crypto_enc (N.@"m1") msg1_pred ∧
  crypto_enc (N.@"m2") msg2_pred ∧
  crypto_enc (N.@"m3") msg3_pred.

Global Instance persistent_nsl_ctx : Persistent nsl_ctx.
Proof. apply _. Qed.

Lemma nsl_ctx_session_ctx :
  nsl_ctx -∗
  session_ctx nsl_sess_name N nsl_sess_inv.
Proof. by iIntros "( ? & ? )". Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition nsl_init : val := λ: "skA" "pkA" "pkB" "nA",
  bind: "m1"   := tenc (N.@"m1") "pkB" (term_of_list ["nA"; "pkA"]) in
  send "m1";;
  bind: "m2"   := tdec (N.@"m2") "skA" (recv #()) in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nA'"; "nB"; "pkB'"] := "m2" in
  assert: eq_term "nA'" "nA" && eq_term "pkB'" "pkB" in
  bind: "m3" := tenc (N.@"m3") "pkB" "nB" in
  send "m3";;
  SOME "nB".

Definition nsl_resp : val := λ: "skB" "pkB" "nB",
  bind: "m1" := tdec (N.@"m1") "skB" (recv #()) in
  bind: "m1" := list_of_term "m1" in
  list_match: ["nA"; "pkA"] := "m1" in
  bind: "kt" := is_key "pkA" in
  assert: "kt" = repr Enc in
  bind: "m2" := tenc (N.@"m2") "pkA" (term_of_list ["nA"; "nB"; "pkB"]) in
  send "m2";;
  bind: "m3" := tdec (N.@"m3") "skB" (recv #()) in
  assert: eq_term "m3" "nB" in SOME ("pkA", "nA").

Implicit Types Ψ : val → iProp.

Lemma pterm_msg1I kA kB (nA : term) :
  nsl_ctx -∗
  pterm (TKey Enc kA) -∗
  sterm nA -∗
  □ (pterm nA ↔ ▷ corruption kA kB) -∗
  pterm (TKey Enc kB) -∗
  ▷ pterm (TEnc kB (Spec.tag (N.@"m1") (Spec.of_list [nA; TKey Enc kA]))).
Proof.
iIntros "(_ & #Hm1 & _ & _) #HkA #HnA #HnA_hi #HkB".
iModIntro.
iApply pterm_TEncIS; eauto.
- by iApply pterm_sterm.
- iModIntro.
  iExists _, _; iSplit; eauto.
  rewrite sterm_of_list /=; do !iSplit => //.
  by iApply pterm_sterm.
- iIntros "!> HkB_dec".
  rewrite pterm_of_list /=; do !iSplit => //.
  by iApply "HnA_hi"; rewrite /corruption; eauto.
Qed.

Lemma pterm_msg2I kA kB nA nB :
  nsl_ctx -∗
  ▷ pterm (TKey Enc kA) -∗
  pterm (TKey Enc kB) -∗
  sterm nA -∗
  □ (pterm (TKey Dec kA) → pterm nA) -∗
  sterm nB -∗
  □ (pterm nB ↔ ▷ corruption kA kB) -∗
  session nsl_sess_name Resp kA kB nA nB -∗
  ▷ pterm (TEnc kA (Spec.tag (N.@"m2") (Spec.of_list [nA; nB; TKey Enc kB]))).
Proof.
iIntros "# (_ & _ & Hm2 & _) #HAenc #HBenc #HnAhi #HnAlo #HnBhi #HnBlo #sess !>".
iApply pterm_TEncIS; eauto.
- by iApply pterm_sterm.
- iModIntro; iExists _, _, _; do !iSplit => //.
  rewrite sterm_of_list /=; do !iSplit => //.
  by iApply pterm_sterm.
iIntros "!> #pub".
iSpecialize ("HnAlo" with "pub").
rewrite pterm_of_list /=; do !iSplit => //.
by iApply "HnBlo"; rewrite /corruption; eauto.
Qed.

Lemma pterm_msg1E kA kB nA :
  nsl_ctx -∗
  pterm (TEnc kB (Spec.tag (N.@"m1") (Spec.of_list [nA; TKey Enc kA]))) -∗
  ▷ (pterm (TKey Enc kA) ∧ sterm nA ∧
     (pterm nA ∨ (pterm nA ↔ ▷ corruption kA kB))).
Proof.
iIntros "# (_ & m1P & _ & _) #Hts".
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
  nsl_ctx -∗
  □ (pterm nA ↔ ▷ corruption kA kB) -∗
  pterm (TEnc kA (Spec.tag (N.@"m2") (Spec.of_list [nA; nB; TKey Enc kB]))) -∗
  ▷ (sterm nB ∧
     (pterm nB ↔ ▷ corruption kA kB) ∧
     ▷ (corruption kA kB ∨
        session nsl_sess_name Resp kA kB nA nB)).
Proof.
iIntros "# (_ & _ & ? & _) #p_nA #Hts".
iDestruct (pterm_TEncE with "Hts [//]") as "{Hts} [[? Hts] | Hts]".
  rewrite pterm_of_list /=.
  iDestruct "Hts" as "(p_nA' & ? & ? & ?)".
  iAssert (sterm nB) as "#?". by iApply pterm_sterm.
  iPoseProof ("p_nA" with "p_nA'") as "?".
  by do 3![iSplit; eauto].
iDestruct "Hts" as "(#inv & Hts & _)"; iModIntro.
iDestruct "inv" as (nA' nB' kB') "(%e_m & #nBP & frag)".
case/Spec.of_list_inj: e_m => <- <- <-; rewrite sterm_of_list /=.
iDestruct "Hts" as "(?&?&?)"; by eauto.
Qed.

Lemma pterm_msg3I kA kB nA nB :
  nsl_ctx -∗
  pterm (TKey Enc kA) -∗
  pterm (TKey Enc kB) -∗
  □ (pterm nA ↔ ▷ corruption kA kB) -∗
  sterm nB -∗
  □ (pterm nB ↔ ▷ corruption kA kB) -∗
  session nsl_sess_name Resp kA kB nA nB -∗
  session nsl_sess_name Init kA kB nA nB -∗
  pterm (TEnc kB (Spec.tag (N.@"m3") nB)).
Proof.
iIntros "(_ & _ & _ & #Hm3) #p_kA #p_kB #p_nA #s_nB #p_nB #sessA #sessB".
iApply pterm_TEncIS => //.
- by iApply pterm_sterm.
- iModIntro. iIntros (nA' kA') "#sessA'".
  iDestruct (session_agree with "sessA sessA'") as "(-> & _ & -> & _)" => //.
  by iSplit.
by iIntros "!> ?"; iApply "p_nB"; rewrite /corruption; eauto.
Qed.

Lemma pterm_msg3E kA kB nA nB :
  nsl_ctx -∗
  session nsl_sess_name Resp kA kB nA nB -∗
  □ (pterm nB ↔ ▷ corruption kA kB) -∗
  pterm (TEnc kB (Spec.tag (N.@"m3") nB)) -∗
  ▷ (corruption kA kB ∨
     session nsl_sess_name Init kA kB nA nB ∧
     (pterm nA ↔ ▷ corruption kA kB)).
Proof.
iIntros "(_ & _ & _ & #Hm3) #sessB #p_nB #p_m3".
iDestruct (pterm_TEncE with "p_m3 [//]") as "[[_ fail]|inv]".
  by iLeft; iApply "p_nB".
iDestruct "inv" as "(#inv & _ & _)".
iModIntro; iRight.
by iApply "inv".
Qed.

Lemma wp_nsl_init kA kB (nA : term) E Ψ :
  ↑N ⊆ E →
  nsl_ctx -∗
  pterm (TKey Enc kA) -∗
  pterm (TKey Enc kB) -∗
  sterm nA -∗
  □ (pterm nA ↔ ▷ (pterm (TKey Dec kA) ∨ pterm (TKey Dec kB))) -∗
  (∀ nB, nsl_sess_inv Init kA kB nA nB) -∗
  crypto_meta_token nA (↑N) -∗
  (∀ onB : option term,
      (if onB is Some nB then
         sterm nB ∧
         ((pterm (TKey Dec kA) ∨ pterm (TKey Dec kB)) ∨
           nsl_sess_inv Resp kA kB nA nB)
       else True) -∗
      Ψ (repr onB)) -∗
  WP nsl_init (TKey Dec kA) (TKey Enc kA) (TKey Enc kB) nA @ E
     {{ Ψ }}.
Proof.
rewrite /nsl_init.
iIntros (?) "#ctx #enc_kA #enc_kB #s_nA #p_nA inv unreg Hpost".
wp_list; wp_term_of_list.
wp_tenc => /=.
iPoseProof (pterm_msg1I with "[//] enc_kA s_nA p_nA enc_kB") as "#Hm1".
wp_pures; wp_bind (send _); iApply wp_send; eauto.
iClear "Hm1"; wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (m2) "#Hm2"; wp_tdec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_pures; rewrite !subst_list_match /=.
iApply wp_list_match.
case: m2 => [|nA' [|nB [|pkB' [|??]]]] //=; try by iApply ("Hpost" $! None).
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst pkB'.
wp_tenc.
iPoseProof (pterm_msg2E with "[//] [//] Hm2")
  as "{Hm2} (s_nB & p_nB & Hm2)"; eauto.
wp_pures; iDestruct "Hm2" as "[fail|sessB]".
  wp_bind (send _); iApply wp_send.
    iModIntro; iApply pterm_TEncIP => //.
    by rewrite pterm_tag; iApply "p_nB".
  by wp_pures; iApply ("Hpost" $! (Some nB)); eauto.
iSpecialize ("inv" $! nB).
iMod (session_begin with "[] inv [unreg]") as "[#sessA close]" => //.
  by iApply nsl_ctx_session_ctx.
iMod ("close" with "sessB") as "inv_resp" => //=.
wp_bind (send _); iApply wp_send.
  by iModIntro; iApply (pterm_msg3I with "[] [] [] [] [] [] sessB sessA"); eauto.
wp_pures; iApply ("Hpost" $! (Some nB)); eauto.
Qed.

Lemma wp_nsl_resp kB E Ψ nB :
  ↑N ⊆ E →
  nsl_ctx -∗
  pterm (TKey Enc kB) -∗
  crypto_meta_token nB (↑N) -∗
  sterm nB -∗
  (∀ kA nA, |==> □ (pterm nB ↔ ▷ corruption kA kB) ∗
                 nsl_sess_inv Resp kA kB nA nB) -∗
  (∀ ot : option (term * term),
      (if ot is Some (pkA, nA) then
         ∃ kA,
           ⌜pkA = TKey Enc kA⌝ ∧
           pterm pkA ∧
           sterm nA ∧
           □ (pterm nA ↔ ▷ corruption kA kB) ∧
           (corruption kA kB ∨ nsl_sess_inv Init kA kB nA nB)
       else True) -∗
       Ψ (repr ot)) -∗
  WP nsl_resp (TKey Dec kB) (TKey Enc kB) nB @ E {{ Ψ }}.
Proof.
iIntros (?) "#ctx #e_kB unreg #s_nB set_nB Hpost".
rewrite /nsl_resp; wp_pures.
wp_bind (recv _); iApply wp_recv; iIntros (m1) "#Hm1".
wp_tdec m1; last protocol_failure.
wp_list_of_term m1; last protocol_failure.
wp_pures; rewrite !subst_list_match /=.
iApply wp_list_match.
case: m1 => [|nA [|pkA [|??]]] //=; try by iApply ("Hpost" $! None).
wp_is_key_eq kt kA et; last protocol_failure; subst pkA.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Enc)); last protocol_failure.
case: kt => // _.
wp_pures.
iDestruct (pterm_msg1E with "[] Hm1") as "{Hm1} Hm1"; eauto.
wp_list; wp_term_of_list.
iMod ("set_nB" $! kA nA) as "[#p_nB inv]".
wp_tenc; wp_pures.
iDestruct "Hm1" as "(e_kA & s_nA & Hm1)".
iAssert (□ (▷ corruption kA kB → pterm nA))%I as "#p_nA".
  iDestruct "Hm1" as "[?|#e]"; eauto.
  by iIntros "!> ?"; iApply "e"; eauto.
iMod (session_begin with "[] inv [unreg]") as "[#sessB close]" => //.
  by iApply nsl_ctx_session_ctx.
iPoseProof (pterm_msg2I with "[//] [//] e_kB s_nA [] s_nB [] sessB") as "Hm2".
- by iIntros "!> ?"; iApply "p_nA"; rewrite /corruption; eauto.
- by eauto.
wp_bind (send _); iApply wp_send => //.
wp_pures; wp_bind (recv _); iApply wp_recv; iIntros (m3) "#Hm3".
wp_tdec m3; last protocol_failure.
wp_eq_term e; last protocol_failure; subst m3.
iPoseProof (pterm_msg3E with "[] sessB p_nB []") as "[pub|sec]" => //.
  iSpecialize ("p_nB" with "pub").
  wp_pures. iApply ("Hpost" $! (Some (TKey Enc kA, nA))).
  iExists kA; do 4!iSplit => //.
    iModIntro; iSplit; iIntros "#?" => //.
    iDestruct "Hm1" as "[?|#Hm1]"; eauto.
    by iApply "Hm1".
  by iLeft.
iDestruct "sec" as "{p_nA} (sessA & p_nA)".
wp_if.
iMod ("close" with "sessA") as "inv".
wp_pures.
iApply ("Hpost" $! (Some (TKey Enc kA, nA))).
iExists kA; do 4!iSplit => //; by eauto.
Qed.

End NSL.

Arguments nslG Σ : clear implicits.
