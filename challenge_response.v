From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode.
From crypto Require Import lib guarded term crypto primitives tactics session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

A --> B: nA, vk(A)
B --> A: {nA, nB, vk(A)}_sk(B)
A --> B: {nA, nB, vk(B)}_sk(A)

*)


Section CR.

Context `{!heapG Σ, !cryptoG Σ, !network Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types s : session_view.
Implicit Types rl : role.

Class crG := {
  in_cr_sessG :> sessionG Σ;
  cr_sess_name : gname;
}.

Context `{!crG}.

Definition msg2_pred kB t : iProp :=
  ∃ nA nB kA,
    ⌜t = Spec.of_list [nA; nB; TKey Dec kA]⌝ ∧
    session cr_sess_name Resp kA kB nA nB.

Definition msg3_pred kA m3 : iProp :=
  ∃ nA nB kB,
    ⌜m3 = Spec.of_list [nA; nB; TKey Dec kB]⌝ ∧
    session cr_sess_name Init kA kB nA nB.

Variable cr_sess_inv : role → term → term → term → term → iProp.

Variable gen : val.

Definition cr_inv : iProp :=
  session_inv cr_sess_name (cryptoN.@"cr") cr_sess_inv.

Definition cr_ctx : iProp :=
  session_ctx cr_sess_name (cryptoN.@"cr") cr_sess_inv.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition initiator : val := λ: "skA" "pkA" "pkB" "nA",
  let:  "m1"   := term_of_list ["nA"; "pkA"] in
  send  "m1";;
  bind: "m2"   := tdec (nroot.@"m2") "pkB" (recv #()) in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nA'"; "nB"; "pkA'"] := "m2" in
  if: eq_term "nA'" "nA" && eq_term "pkA'" "pkA" then
    let:  "m3" := term_of_list ["nA"; "nB"; "pkB"] in
    bind: "m3" := tenc (nroot.@"m3") "skA" "m3" in
    send "m3";;
    SOME "nB"
  else NONE.

Definition responder : val := λ: "skB" "pkB",
  bind: "m1"   := list_of_term (recv #()) in
  list_match: ["nA"; "pkA"] := "m1" in
  bind: "kt"   := is_key "pkA" in
  if: "kt" = repr Dec then
    let:  "nB"   := gen #() in
    bind: "m2"   := tenc (nroot.@"m2") "skB" (term_of_list ["nA"; "nB"; "pkA"]) in
    send  "m2";;
    bind: "m3"   := tdec (nroot.@"m3") "pkA" (recv #()) in
    bind: "m3"   := list_of_term "m3" in
    list_match: ["nA'"; "nB'"; "pkB'"] := "m3" in
    if: eq_term "nA'" "nA" && eq_term "nB'" "nB" && eq_term "pkB'" "pkB" then
      SOME ("pkA", "nA", "nB")
    else NONE
  else NONE.

Implicit Types Ψ : val → iProp.

Hypothesis wp_gen : forall E kA kB nA Ψ,
  (∀ nB, cr_sess_inv Resp kA kB nA nB -∗
         crypto_meta_token nB (↑cryptoN.@"cr") -∗
         pterm nB -∗
         Ψ nB) -∗
  WP gen #() @ E {{ Ψ }}.

Lemma pterm_msg2E m2 kA kB nA nB :
  m2 !! Z.to_nat 0 = Some nA →
  m2 !! Z.to_nat 1 = Some nB →
  m2 !! Z.to_nat 2 = Some (TKey Dec kA) →
  enc_pred (nroot.@"m2") msg2_pred -∗
  pterm (TKey Dec kB) -∗
  pterm (TEnc kB (Spec.tag (nroot.@"m2") (Spec.of_list m2))) -∗
  ▷ (pterm nB ∧
     (pterm (TKey Enc kB) ∨ session cr_sess_name Resp kA kB nA nB)).
Proof.
iIntros (enA enB ekA) "#enc_m2 #p_d_kB #p_m2".
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

Lemma pterm_msg3E m3 kA kB nA nB :
  m3 !! Z.to_nat 0 = Some nA →
  m3 !! Z.to_nat 1 = Some nB →
  m3 !! Z.to_nat 2 = Some (TKey Dec kB) →
  enc_pred (nroot.@"m3") msg3_pred -∗
  pterm (TKey Dec kA) -∗
  pterm (TEnc kA (Spec.tag (nroot.@"m3") (Spec.of_list m3))) -∗
  ▷ (pterm (TKey Enc kA) ∨ session cr_sess_name Init kA kB nA nB).
Proof.
iIntros (enA enB ekB) "#enc_m3 #p_d_ka #p_m3".
rewrite pterm_TEnc; iDestruct "p_m3" as "[[p_e_kA p_m3]|p_m3]".
  by eauto.
iDestruct "p_m3" as "(_ & inv & _)".
iPoseProof (wf_enc_elim with "inv enc_m3") as "{inv} #inv".
iModIntro.
iDestruct "inv" as (nA' nB' kB') "[%e_m3 inv]".
move/Spec.of_list_inj: e_m3 enA enB ekB => -> /= [] -> [] -> [] ->.
by eauto.
Qed.

Lemma wp_initiator kA kB nA E Ψ :
  ↑cryptoN.@"cr" ⊆ E →
  cr_ctx -∗
  enc_pred (nroot.@"m2") msg2_pred -∗
  enc_pred (nroot.@"m3") msg3_pred -∗
  pterm nA -∗
  (∀ nB, cr_sess_inv Init kA kB nA nB) -∗
  crypto_meta_token nA (↑cryptoN.@"cr") -∗
  pterm (TKey Dec kA) -∗
  pterm (TKey Dec kB) -∗
  (∀ onB : option term,
      (if onB is Some nB then
         pterm nB ∧
         (pterm (TKey Enc kB) ∨ cr_sess_inv Resp kA kB nA nB)
       else True) -∗
      Ψ (repr onB)) -∗
  WP initiator (TKey Enc kA) (TKey Dec kA) (TKey Dec kB) nA @ E
     {{ Ψ }}.
Proof.
rewrite /initiator.
iIntros (?) "#ctx #inv2 #inv3 #p_nA inv unreg #d_kA #d_kB Hpost".
wp_list; wp_term_of_list.
wp_pures; wp_bind (send _); iApply wp_send.
  iModIntro.
  by iApply pterm_of_list => /=; eauto.
wp_pures; wp_bind (recv _); iApply wp_recv.
iIntros (m2) "#Hm2"; wp_tdec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_list_match => [nA' nB pkB' {m2} ->|_]; wp_finish; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst pkB'.
iPoseProof (pterm_msg2E with "[//] d_kB Hm2")
  as "{Hm2} [p_nB sessB]" => //.
wp_list; wp_term_of_list.
wp_tenc; wp_pures.
iSpecialize ("inv" $! nB).
iMod (session_begin with "[] inv [unreg]") as "[#sessA close]"; eauto.
iAssert (|={E}=> ▷ (pterm (TKey Enc kB) ∨ cr_sess_inv Resp kA kB nA nB))%I
    with "[close]" as ">inv".
  iDestruct "sessB" as "[?|sessB]"; eauto.
  by iMod ("close" with "sessB") as "close"; eauto.
wp_bind (send _); iApply wp_send.
  iModIntro; iApply pterm_TEncIS; eauto.
  - iPoseProof (pterm_sterm with "d_kA") as "?".
    by rewrite !sterm_TKey.
  - iModIntro.
    iExists _, _, _; iSplit => //.
    by rewrite sterm_of_list /= -!pterm_sterm; eauto.
  - iIntros "!> _".
    by rewrite pterm_of_list /=; eauto.
wp_pures; iApply ("Hpost" $! (Some nB)).
by iFrame.
Qed.

Lemma wp_responder kB E Ψ :
  ↑cryptoN.@"cr" ⊆ E →
  cr_ctx -∗
  enc_pred (nroot.@"m2") msg2_pred -∗
  enc_pred (nroot.@"m3") msg3_pred -∗
  pterm (TKey Dec kB) -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ kA,
           ⌜pkA = TKey Dec kA⌝ ∗
           pterm pkA ∧
           pterm nA ∧
           pterm nB ∧
           (pterm (TKey Enc kA) ∨ cr_sess_inv Init kA kB nA nB)
       else True) -∗
       Ψ (repr ot)) -∗
  WP responder (TKey Enc kB) (TKey Dec kB) @ E {{ Ψ }}.
Proof.
iIntros (?) "#ctx #enc2 #enc3 #HkB Hpost".
rewrite /responder; wp_pures.
wp_bind (recv _); iApply wp_recv; iIntros (m1) "#Hm1".
wp_list_of_term m1; last protocol_failure.
wp_list_match => [nA pkA {m1} ->|_]; wp_finish; last protocol_failure.
rewrite pterm_of_list /=.
iDestruct "Hm1" as "(HnA & HpkA & _)".
wp_is_key_eq kt kA et; last protocol_failure; subst pkA.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Dec)); last protocol_failure.
case: kt=> // _.
wp_pures; wp_bind (gen _); iApply wp_gen; iIntros (nB) "inv token #HnB".
iMod (session_begin with "[] inv [token]") as "[#sessB close]".
- by eauto.
- by eauto.
- by eauto.
wp_list; wp_term_of_list.
wp_tenc; wp_pures; wp_bind (send _); iApply wp_send.
  iModIntro.
  iApply pterm_TEncIS.
  - iPoseProof (pterm_sterm with "HkB") as "?".
    by rewrite !sterm_TKey.
  - by eauto.
  - iIntros "!>". by iExists _, _, _; eauto.
  - by rewrite sterm_of_list /= -!pterm_sterm; eauto.
  - iIntros "!> _".
    by rewrite pterm_of_list /=; eauto.
wp_pures; wp_bind (recv _); iApply wp_recv; iIntros (m3) "#Hm3".
wp_tdec m3; last protocol_failure.
wp_list_of_term m3; last protocol_failure.
wp_list_match => [nA' nB' pkB' {m3} ->|_]; wp_finish; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst nB'.
wp_eq_term e; last protocol_failure; subst pkB'.
iPoseProof (pterm_msg3E with "[//] HpkA Hm3") as "{Hm3} Hm3"; eauto.
wp_if.
iAssert (|={E}=> ▷ (pterm (TKey Enc kA) ∨ cr_sess_inv Init kA kB nA nB))%I
    with "[close]" as ">inv".
  iDestruct "Hm3" as "[Hm3 | Hm3]"; eauto.
  iMod ("close" with "Hm3") as "close". by eauto.
wp_pures; iApply ("Hpost" $! (Some (_, _, _))).
by iExists _; do ![iSplit=> //].
Qed.

End CR.
