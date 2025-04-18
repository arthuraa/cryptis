From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

A --> B: nA, vk(A)
B --> A: {nA, nB, vk(A)}_sk(B)
A --> B: {nA, nB, vk(B)}_sk(A)

*)


Section CR.

Context `{!heapGS Σ, !cryptisGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.

Context (N : namespace).

Definition msg2_pred (kB : term) t : iProp :=
  ∃ nA nB kA,
    ⌜t = Spec.of_list [nA; nB; TKey Open kA]⌝ ∧
    session N Resp nA nB (kA, kB).

Definition msg3_pred (kA : term) m3 : iProp :=
  ∃ nA nB kB,
    ⌜m3 = Spec.of_list [nA; nB; TKey Open kB]⌝ ∧
    session N Init nA nB (kA, kB).

Variable P : role → term → term → term → term → iProp.

Definition cr_sess_inv rl nA nB ks :=
  let '(kA, kB) := ks in P rl nA nB kA kB.

Definition cr_ctx : iProp :=
  session_ctx N cr_sess_inv ∧
  seal_pred (N.@"m2") msg2_pred ∧
  seal_pred (N.@"m3") msg3_pred.

Lemma cr_alloc E1 E2 E' :
  ↑N ⊆ E1 →
  ↑N ⊆ E2 →
  session_token E1 -∗
  seal_pred_token E2 ={E'}=∗
  cr_ctx ∗
  session_token (E1 ∖ ↑N) ∗
  seal_pred_token (E2 ∖ ↑N).
Proof.
iIntros (sub1 sub2) "nown_token token".
iMod (session_alloc N cr_sess_inv with "nown_token") as "[#ctx ?]"; eauto.
iFrame.
rewrite (seal_pred_token_difference (↑N)) //.
iDestruct "token" as "[t2 token]"; iFrame.
iMod (seal_pred_set (N.@"m2") msg2_pred with "t2") as "[#H2 t2]";
  try solve_ndisj.
iMod (seal_pred_set (N.@"m3") msg3_pred with "t2") as "[#H3 _]";
  try solve_ndisj.
by iModIntro; do !iSplit => //.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition cr_init : val := λ: "c" "skA" "pkB",
  let:  "pkA"  := vkey "skA" in
  let:  "nA"   := mknonce #() in
  let:  "m1"   := term_of_list ["nA"; "pkA"] in
  send  "c" "m1";;
  bind: "m2"   := verify (Tag $ N.@"m2") "pkB" (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nA'"; "nB"; "pkA'"] := "m2" in
  if: eq_term "nA'" "nA" && eq_term "pkA'" "pkA" then
    let: "m3" := term_of_list ["nA"; "nB"; "pkB"] in
    let: "m3" := sign (Tag $ N.@"m3") "skA" "m3" in
    send "c" "m3";;
    SOME ("nA", "nB")
  else NONE.

Definition cr_resp : val := λ: "c" "skB",
  let: "pkB" := vkey "skB" in
  bind: "m1"   := list_of_term (recv "c") in
  list_match: ["nA"; "pkA"] := "m1" in
  bind: "kt"   := is_key "pkA" in
  if: "kt" = repr Open then
    let:  "nB"   := mknonce #() in
    let: "m2"    := sign (Tag $ N.@"m2") "skB" (term_of_list ["nA"; "nB"; "pkA"]) in
    send  "c" "m2";;
    bind: "m3"   := verify (Tag $ N.@"m3") "pkA" (recv "c") in
    bind: "m3"   := list_of_term "m3" in
    list_match: ["nA'"; "nB'"; "pkB'"] := "m3" in
    if: eq_term "nA'" "nA" && eq_term "nB'" "nB" && eq_term "pkB'" "pkB" then
      SOME ("pkA", "nA", "nB")
    else NONE
  else NONE.

Implicit Types Ψ : val → iProp.

Lemma public_msg2E m2 kA kB nA nB :
  m2 !! Z.to_nat 0 = Some nA →
  m2 !! Z.to_nat 1 = Some nB →
  m2 !! Z.to_nat 2 = Some (TKey Open kA) →
  cr_ctx -∗
  public (TKey Open kB) -∗
  public (TSeal (TKey Seal kB) (Spec.tag (Tag $ N.@"m2") (Spec.of_list m2))) -∗
  ▷ (public nB ∧
     (public (TKey Seal kB) ∨
      session N Resp nA nB (kA, kB))).
Proof.
iIntros (enA enB ekA) "#ctx #p_d_kB #p_m2".
iDestruct "ctx" as "(_ & seal_m2 & _)".
iPoseProof (public_TSealE with "p_m2 [//]") as "{p_m2} p_m2".
iDestruct "p_m2" as "[[p_e_kB p_m2]|p_m2]".
  rewrite public_of_list.
  iPoseProof (big_sepL_lookup with "p_m2") as "p_nB"; first exact: enB.
  iSplit => //.
  by eauto.
iDestruct "p_m2" as "(#inv & m_m2 & #pub)".
iSpecialize ("pub" with "p_d_kB").
rewrite public_of_list.
iPoseProof (big_sepL_lookup with "pub") as "p_nB"; first exact: enB.
iSplit => //.
iModIntro.
iDestruct "inv" as (nA' nB' kA') "(%e_m2 & #sess)".
move/Spec.of_list_inj: e_m2 enA enB ekA => -> /= [] -> [] -> [] ->.
by eauto.
Qed.

Lemma public_msg3E m3 kA kB nA nB :
  m3 !! Z.to_nat 0 = Some nA →
  m3 !! Z.to_nat 1 = Some nB →
  m3 !! Z.to_nat 2 = Some (TKey Open kB) →
  cr_ctx -∗
  public (TKey Open kA) -∗
  public (TSeal (TKey Seal kA) (Spec.tag (Tag $ N.@"m3") (Spec.of_list m3))) -∗
  ▷ (public (TKey Seal kA) ∨
     session N Init nA nB (kA, kB)).
Proof.
iIntros (enA enB ekB) "#ctx #p_d_ka #p_m3".
iDestruct "ctx" as "(_ & _ & seal_m3)".
iDestruct (public_TSealE with "p_m3 [//]") as "{p_m3} [[p_e_kA p_m3]|p_m3]".
  by eauto.
iDestruct "p_m3" as "(#inv & _)".
iModIntro.
iDestruct "inv" as (nA' nB' kB') "[%e_m3 inv]".
move/Spec.of_list_inj: e_m3 enA enB ekB => -> /= [] -> [] -> [] ->.
by eauto.
Qed.

Lemma wp_cr_init c kA kB Ψ :
  channel c -∗
  cryptis_ctx -∗
  cr_ctx -∗
  (∀ nA nB, cr_sess_inv Init nA nB (kA, kB)) -∗
  public (TKey Open kA) -∗
  public (TKey Open kB) -∗
  (∀ onB : option (term * term),
      (if onB is Some (nA, nB) then
         public nA ∧
         public nB ∧
         (public (TKey Seal kB) ∨ P Resp nA nB kA kB)
       else True) -∗
      Ψ (repr onB)) -∗
  WP cr_init c kA (TKey Open kB) {{ Ψ }}.
Proof.
rewrite /cr_init.
iIntros "#? #? #ctx inv #d_kA #d_kB Hpost".
iPoseProof "ctx" as "(? & ? & ?)".
wp_pures. wp_apply wp_vkey. wp_pures.
wp_apply (wp_mknonce (λ _, True)%I (λ _, True)%I) => //.
iIntros (nA) "_ _ #p_nA _ unreg".
rewrite (term_token_difference _ (↑N)) //.
iDestruct "unreg" as "[unreg _]".
iAssert (public nA) as "{p_nA} p_nA"; first by iApply "p_nA".
wp_list; wp_term_of_list.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by iApply public_of_list => /=; eauto.
wp_pures; wp_bind (recv _); iApply wp_recv => //.
iIntros (m2) "#Hm2"; wp_verify m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_list_match => [nA' nB pkB' {m2} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst pkB'.
iPoseProof (public_msg2E with "[//] d_kB Hm2")
  as "{Hm2} [p_nB sessB]" => //.
wp_list; wp_term_of_list.
wp_pures. wp_apply wp_sign. wp_pures.
iSpecialize ("inv" $! nA nB).
iMod (session_begin _ _ _ _ (kA, kB) with "[] [inv] [unreg]")
  as "[#sessA close]"; eauto.
iAssert (|={⊤}=> ▷ (public (TKey Seal kB) ∨ P Resp nA nB kA kB))%I
    with "[close]" as ">inv".
  iDestruct "sessB" as "[?|sessB]"; eauto.
  by iMod ("close" with "[] sessB") as "close"; eauto.
wp_bind (send _ _); iApply wp_send => //.
  iApply public_TSealIS; eauto.
  - iPoseProof (public_minted with "d_kA") as "?".
    by rewrite !minted_TKey.
  - iModIntro.
    iExists _, _, _; iSplit => //.
    by rewrite minted_of_list /= -!public_minted; eauto.
  - iIntros "!> !> _".
    by rewrite public_of_list /=; eauto.
wp_pures; iApply ("Hpost" $! (Some (nA, nB))); eauto.
Qed.

Lemma wp_cr_resp c kB Ψ :
  channel c -∗
  cryptis_ctx -∗
  cr_ctx -∗
  public (TKey Open kB) -∗
  (∀ kA nA nB, cr_sess_inv Resp nA nB (kA, kB)) -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ kA,
           ⌜pkA = TKey Open kA⌝ ∗
           public pkA ∧
           public nA ∧
           public nB ∧
           (public (TKey Seal kA) ∨ P Init nA nB kA kB)
       else True) -∗
       Ψ (repr ot)) -∗
  WP cr_resp c kB {{ Ψ }}.
Proof.
iIntros "#? #? #ctx #HkB inv Hpost".
iPoseProof "ctx" as "(? & ? & ?)".
rewrite /cr_resp; wp_pures. wp_apply wp_vkey. wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#Hm1".
wp_list_of_term m1; last protocol_failure.
wp_list_match => [nA pkA {m1} ->|_]; last protocol_failure.
rewrite public_of_list /=.
iDestruct "Hm1" as "(HnA & HpkA & _)".
wp_is_key_eq kt kA et; last protocol_failure; subst pkA.
wp_pures.
case: (bool_decide_reflect (_ = repr_key_type Open)); last protocol_failure.
case: kt=> // _.
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce (λ _, True)%I (λ _, True)%I) => //.
iIntros (nB) "_ _ #p_nB _ unreg".
rewrite (term_token_difference _ (↑N)) //.
iDestruct "unreg" as "[token _]".
iAssert (public nB) as "{p_nB} HnB"; first by iApply "p_nB".
iMod (session_begin _ _ nA nB (kA, kB) with "[] [inv] [token]")
  as "[#sessB close]"; eauto.
wp_list; wp_term_of_list.
wp_apply wp_sign. wp_pures.
wp_apply wp_send => //.
  iApply public_TSealIS.
  - iPoseProof (public_minted with "HkB") as "?".
    by rewrite !minted_TKey.
  - by eauto.
  - iIntros "!>". by iExists _, _, _; eauto.
  - by rewrite minted_of_list /= -!public_minted; eauto.
  - iIntros "!> _".
    by rewrite public_of_list /=; eauto.
wp_pures; wp_bind (recv _); iApply wp_recv => //; iIntros (m3) "#Hm3".
wp_verify m3; last protocol_failure.
wp_list_of_term m3; last protocol_failure.
wp_list_match => [nA' nB' pkB' {m3} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst nB'.
wp_eq_term e; last protocol_failure; subst pkB'.
iPoseProof (public_msg3E with "[//] HpkA Hm3") as "{Hm3} Hm3"; eauto.
wp_if.
iAssert (|={⊤}=> ▷ (public (TKey Seal kA) ∨ P Init nA nB kA kB))%I
    with "[close]" as ">inv".
  iDestruct "Hm3" as "[Hm3 | Hm3]"; eauto.
  iMod ("close" with "[] Hm3") as "close"; by eauto.
wp_pures; iApply ("Hpost" $! (Some (_, _, _))).
by iModIntro; iExists _; do ![iSplit=> //].
Qed.

End CR.

Arguments cr_alloc {Σ _ _ _} N.
