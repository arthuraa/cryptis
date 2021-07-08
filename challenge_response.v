From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

A --> B: nA, vk(A)
B --> A: {nA, nB, vk(A)}_sk(B)
A --> B: {nA, nB, vk(B)}_sk(A)

*)


Section CR.

Context `{!heapG Σ, !cryptisG Σ, !sessionG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.

Context (N : namespace).

Definition msg2_pred γ (kB : term) t : iProp :=
  ∃ nA nB kA,
    ⌜t = Spec.of_list [nA; nB; TKey Dec kA]⌝ ∧
    session (@nonce_meta _ _) N γ Resp nA nB (kA, kB).

Definition msg3_pred γ (kA : term) m3 : iProp :=
  ∃ nA nB kB,
    ⌜m3 = Spec.of_list [nA; nB; TKey Dec kB]⌝ ∧
    session (@nonce_meta _ _) N γ Init nA nB (kA, kB).

Variable P : role → term → term → term → term → iProp.

Definition cr_sess_inv rl nA nB ks :=
  let '(kA, kB) := ks in P rl nA nB kA kB.

Definition cr_ctx γ : iProp :=
  session_ctx (@nonce_meta _ _) N cr_sess_inv γ ∧
  enc_pred (N.@"m2") (msg2_pred γ) ∧
  enc_pred (N.@"m3") (msg3_pred γ).

Lemma cr_alloc E E' :
  ↑N ⊆ E →
  enc_pred_token E ={E'}=∗ ∃ γ, cr_ctx γ.
Proof.
iIntros (sub) "token".
iMod (session_alloc (@nonce_meta _ _) N cr_sess_inv) as (γ) "#ctx".
rewrite (enc_pred_token_difference (↑N.@"m2")); last solve_ndisj.
iDestruct "token" as "[t2 token]".
iMod (enc_pred_set (N.@"m2") (msg2_pred γ) with "t2") as "#H2" => //.
rewrite (enc_pred_token_difference (↑N.@"m3")); last solve_ndisj.
iDestruct "token" as "[t3 token]".
iMod (enc_pred_set (N.@"m3") (msg3_pred γ) with "t3") as "#H3" => //.
by iModIntro; iExists γ; do !iSplit => //.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition cr_init : val := λ: "c" "skA" "pkA" "pkB",
  let:  "nA"   := mknonce #() in
  let:  "m1"   := term_of_list ["nA"; "pkA"] in
  send  "c" "m1";;
  bind: "m2"   := tdec (N.@"m2") "pkB" (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nA'"; "nB"; "pkA'"] := "m2" in
  if: eq_term "nA'" "nA" && eq_term "pkA'" "pkA" then
    let: "m3" := term_of_list ["nA"; "nB"; "pkB"] in
    let: "m3" := tenc (N.@"m3") "skA" "m3" in
    send "c" "m3";;
    SOME ("nA", "nB")
  else NONE.

Definition cr_resp : val := λ: "c" "skB" "pkB",
  bind: "m1"   := list_of_term (recv "c") in
  list_match: ["nA"; "pkA"] := "m1" in
  bind: "kt"   := is_key "pkA" in
  if: "kt" = repr Dec then
    let:  "nB"   := mknonce #() in
    let: "m2"    := tenc (N.@"m2") "skB" (term_of_list ["nA"; "nB"; "pkA"]) in
    send  "c" "m2";;
    bind: "m3"   := tdec (N.@"m3") "pkA" (recv "c") in
    bind: "m3"   := list_of_term "m3" in
    list_match: ["nA'"; "nB'"; "pkB'"] := "m3" in
    if: eq_term "nA'" "nA" && eq_term "nB'" "nB" && eq_term "pkB'" "pkB" then
      SOME ("pkA", "nA", "nB")
    else NONE
  else NONE.

Implicit Types Ψ : val → iProp.

Lemma pterm_msg2E γ m2 kA kB nA nB :
  m2 !! Z.to_nat 0 = Some nA →
  m2 !! Z.to_nat 1 = Some nB →
  m2 !! Z.to_nat 2 = Some (TKey Dec kA) →
  cr_ctx γ -∗
  pterm (TKey Dec kB) -∗
  pterm (TEnc kB (Spec.tag (N.@"m2") (Spec.of_list m2))) -∗
  ▷ (pterm nB ∧
     (pterm (TKey Enc kB) ∨
      session (@nonce_meta _ _) N γ Resp nA nB (kA, kB))).
Proof.
iIntros (enA enB ekA) "#ctx #p_d_kB #p_m2".
iDestruct "ctx" as "(_ & enc_m2 & _)".
rewrite pterm_TEnc; iDestruct "p_m2" as "[[p_e_kB p_m2]|p_m2]".
  rewrite pterm_tag pterm_of_list.
  iPoseProof (big_sepL_lookup with "p_m2") as "p_nB"; first exact: enB.
  iSplit => //.
  by eauto.
iDestruct "p_m2" as "(_ & inv & #pub)".
iSpecialize ("pub" with "p_d_kB").
rewrite pterm_tag pterm_of_list.
iPoseProof (big_sepL_lookup with "pub") as "p_nB"; first exact: enB.
iSplit => //.
iPoseProof (wf_enc_elim with "inv enc_m2") as "{inv} #inv".
iModIntro.
iDestruct "inv" as (nA' nB' kA') "(%e_m2 & #sess)".
move/Spec.of_list_inj: e_m2 enA enB ekA => -> /= [] -> [] -> [] ->.
by eauto.
Qed.

Lemma pterm_msg3E γ m3 kA kB nA nB :
  m3 !! Z.to_nat 0 = Some nA →
  m3 !! Z.to_nat 1 = Some nB →
  m3 !! Z.to_nat 2 = Some (TKey Dec kB) →
  cr_ctx γ -∗
  pterm (TKey Dec kA) -∗
  pterm (TEnc kA (Spec.tag (N.@"m3") (Spec.of_list m3))) -∗
  ▷ (pterm (TKey Enc kA) ∨
     session (@nonce_meta _ _) N γ Init nA nB (kA, kB)).
Proof.
iIntros (enA enB ekB) "#ctx #p_d_ka #p_m3".
iDestruct "ctx" as "(_ & _ & enc_m3)".
rewrite pterm_TEnc; iDestruct "p_m3" as "[[p_e_kA p_m3]|p_m3]".
  by eauto.
iDestruct "p_m3" as "(_ & inv & _)".
iPoseProof (wf_enc_elim with "inv enc_m3") as "{inv} #inv".
iModIntro.
iDestruct "inv" as (nA' nB' kB') "[%e_m3 inv]".
move/Spec.of_list_inj: e_m3 enA enB ekB => -> /= [] -> [] -> [] ->.
by eauto.
Qed.

Lemma wp_cr_init γ c kA kB E Ψ :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  cr_ctx γ -∗
  (∀ nA nB, cr_sess_inv Init nA nB (kA, kB)) -∗
  pterm (TKey Dec kA) -∗
  pterm (TKey Dec kB) -∗
  (∀ onB : option (term * term),
      (if onB is Some (nA, nB) then
         pterm nA ∧
         pterm nB ∧
         (pterm (TKey Enc kB) ∨ P Resp nA nB kA kB)
       else True) -∗
      Ψ (repr onB)) -∗
  WP cr_init c (TKey Enc kA) (TKey Dec kA) (TKey Dec kB) @ E
     {{ Ψ }}.
Proof.
rewrite /cr_init.
iIntros (??) "#? #ctx inv #d_kA #d_kB Hpost".
iPoseProof "ctx" as "(? & ? & ?)".
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (λ _, True)%I (λ _, True)%I).
iIntros (nA) "_ #p_nA _ unreg".
rewrite (term_meta_token_difference _ (↑N)) //.
iDestruct "unreg" as "[unreg _]".
iAssert (pterm nA) as "{p_nA} p_nA"; first by iApply "p_nA".
wp_list; wp_term_of_list.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by iApply pterm_of_list => /=; eauto.
wp_pures; wp_bind (recv _); iApply wp_recv => //.
iIntros (m2) "#Hm2"; wp_tdec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_list_match => [nA' nB pkB' {m2} ->|_]; wp_finish; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst pkB'.
iPoseProof (pterm_msg2E with "[//] d_kB Hm2")
  as "{Hm2} [p_nB sessB]" => //.
wp_list; wp_term_of_list.
wp_tenc; wp_pures.
iSpecialize ("inv" $! nA nB).
iMod (session_begin _ _ _ _ _ (kA, kB) with "[] [inv] [unreg]")
  as "[#sessA close]"; eauto.
iAssert (|={E}=> ▷ (pterm (TKey Enc kB) ∨ P Resp nA nB kA kB))%I
    with "[close]" as ">inv".
  iDestruct "sessB" as "[?|sessB]"; eauto.
  by iMod ("close" with "sessB") as "close"; eauto.
wp_bind (send _ _); iApply wp_send => //.
  iApply pterm_TEncIS; eauto.
  - iPoseProof (pterm_sterm with "d_kA") as "?".
    by rewrite !sterm_TKey.
  - iModIntro.
    iExists _, _, _; iSplit => //.
    by rewrite sterm_of_list /= -!pterm_sterm; eauto.
  - iIntros "!> !> _".
    by rewrite pterm_of_list /=; eauto.
wp_pures; iApply ("Hpost" $! (Some (nA, nB))); eauto.
Qed.

Lemma wp_cr_resp γ c kB E Ψ :
  ↑cryptisN ⊆ E →
  ↑N ⊆ E →
  channel c -∗
  cr_ctx γ -∗
  pterm (TKey Dec kB) -∗
  (∀ kA nA nB, cr_sess_inv Resp nA nB (kA, kB)) -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ kA,
           ⌜pkA = TKey Dec kA⌝ ∗
           pterm pkA ∧
           pterm nA ∧
           pterm nB ∧
           (pterm (TKey Enc kA) ∨ P Init nA nB kA kB)
       else True) -∗
       Ψ (repr ot)) -∗
  WP cr_resp c (TKey Enc kB) (TKey Dec kB) @ E {{ Ψ }}.
Proof.
iIntros (??) "#? #ctx #HkB inv Hpost".
iPoseProof "ctx" as "(? & ? & ?)".
rewrite /cr_resp; wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#Hm1".
wp_list_of_term m1; last protocol_failure.
wp_list_match => [nA pkA {m1} ->|_]; wp_finish; last protocol_failure.
rewrite pterm_of_list /=.
iDestruct "Hm1" as "(HnA & HpkA & _)".
wp_is_key_eq kt kA et; last protocol_failure; subst pkA.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Dec)); last protocol_failure.
case: kt=> // _.
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (λ _, True)%I (λ _, True)%I).
iIntros (nB) "_ #p_nB _ unreg".
rewrite (term_meta_token_difference _ (↑N)) //.
iDestruct "unreg" as "[token _]".
iAssert (pterm nB) as "{p_nB} HnB"; first by iApply "p_nB".
iMod (session_begin _ _ _ nA nB (kA, kB) with "[] [inv] [token]")
  as "[#sessB close]"; eauto.
wp_list; wp_term_of_list.
wp_tenc; wp_pures; wp_bind (send _ _); iApply wp_send => //.
  iApply pterm_TEncIS.
  - iPoseProof (pterm_sterm with "HkB") as "?".
    by rewrite !sterm_TKey.
  - by eauto.
  - iIntros "!>". by iExists _, _, _; eauto.
  - by rewrite sterm_of_list /= -!pterm_sterm; eauto.
  - iIntros "!> !> _".
    by rewrite pterm_of_list /=; eauto.
wp_pures; wp_bind (recv _); iApply wp_recv => //; iIntros (m3) "#Hm3".
wp_tdec m3; last protocol_failure.
wp_list_of_term m3; last protocol_failure.
wp_list_match => [nA' nB' pkB' {m3} ->|_]; wp_finish; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst nB'.
wp_eq_term e; last protocol_failure; subst pkB'.
iPoseProof (pterm_msg3E with "[//] HpkA Hm3") as "{Hm3} Hm3"; eauto.
wp_if.
iAssert (|={E}=> ▷ (pterm (TKey Enc kA) ∨ P Init nA nB kA kB))%I
    with "[close]" as ">inv".
  iDestruct "Hm3" as "[Hm3 | Hm3]"; eauto.
  iMod ("close" with "Hm3") as "close". by eauto.
wp_pures; iApply ("Hpost" $! (Some (_, _, _))).
by iExists _; do ![iSplit=> //].
Qed.

End CR.

Arguments cr_alloc {Σ _ _ _} N.
