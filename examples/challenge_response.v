From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.lib Require Import session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

A --> B: nA, pk(A)
B --> A: {nA, nB, pk(A)}_sk(B)
A --> B: {nA, nB, pk(B)}_sk(A)

*)


Section CR.

Context `{!heapGS Σ, !cryptisGS Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.

Context (N : namespace).

Implicit Types skA skB : sign_key.

Definition msg2_pred skB t : iProp :=
  ∃ nA nB skA,
    ⌜t = Spec.of_list [nA; nB; Spec.pkey skA]⌝ ∧
    session N Resp nA nB (skA : term, skB : term).

Definition msg3_pred skA m3 : iProp :=
  ∃ nA nB skB,
    ⌜m3 = Spec.of_list [nA; nB; Spec.pkey skB]⌝ ∧
    session N Init nA nB (skA : term, skB : term).

Variable P : role → term → term → sign_key → sign_key → iProp.

Definition cr_sess_inv rl nA nB (ks : term * term) : iProp :=
  ∃ skA skB, ⌜ks = (skA : term, skB : term)⌝ ∗ P rl nA nB skA skB.

Definition cr_ctx : iProp :=
  session_ctx N cr_sess_inv ∧
  sign_pred (N.@"m2") msg2_pred ∧
  sign_pred (N.@"m3") msg3_pred.

Lemma cr_alloc E1 E2 E' :
  ↑N ⊆ E1 →
  ↑N ⊆ E2 →
  session_token E1 -∗
  seal_pred_token SIGN E2 ={E'}=∗
  cr_ctx ∗
  session_token (E1 ∖ ↑N) ∗
  seal_pred_token SIGN (E2 ∖ ↑N).
Proof.
iIntros (sub1 sub2) "nown_token token".
iMod (session_alloc N cr_sess_inv with "nown_token") as "[#ctx ?]"; eauto.
iFrame.
rewrite (seal_pred_token_difference (↑N)) //.
iDestruct "token" as "[t2 token]"; iFrame.
iMod (sign_pred_set (N := N.@"m2") msg2_pred with "t2") as "[#H2 t2]";
  try solve_ndisj.
iMod (sign_pred_set (N := N.@"m3") msg3_pred with "t2") as "[#H3 _]";
  try solve_ndisj.
by iModIntro; do !iSplit => //.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None).

Definition cr_init : val := λ: "c" "skA" "pkB",
  let:  "pkA"  := pkey "skA" in
  let:  "nA"   := mk_nonce #() in
  let:  "m1"   := term_of_list ["nA"; "pkA"] in
  send  "c" "m1";;
  bind: "m2"   := verify "pkB" (Tag $ N.@"m2") (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nA'"; "nB"; "pkA'"] := "m2" in
  if: eq_term "nA'" "nA" && eq_term "pkA'" "pkA" then
    let: "m3" := term_of_list ["nA"; "nB"; "pkB"] in
    let: "m3" := sign "skA" (Tag $ N.@"m3") "m3" in
    send "c" "m3";;
    SOME ("nA", "nB")
  else NONE.

Definition cr_resp : val := λ: "c" "skB",
  let: "pkB"  := pkey "skB" in
  bind: "m1"  := list_of_term (recv "c") in
  list_match: ["nA"; "pkA"] := "m1" in
  guard: is_verify_key "pkA" in
  let: "nB"   := mk_nonce #() in
  let: "m2"   := sign "skB" (Tag $ N.@"m2") (term_of_list ["nA"; "nB"; "pkA"]) in
  send  "c" "m2";;
  bind: "m3"   := verify "pkA" (Tag $ N.@"m3") (recv "c") in
  bind: "m3"   := list_of_term "m3" in
  list_match: ["nA'"; "nB'"; "pkB'"] := "m3" in
  guard: eq_term "nA'" "nA" && eq_term "nB'" "nB" && eq_term "pkB'" "pkB" in
  SOME ("pkA", "nA", "nB").

Implicit Types Ψ : val → iProp.

Lemma wp_cr_init c skA skB Ψ :
  channel c -∗
  cryptis_ctx -∗
  cr_ctx -∗
  (∀ nA nB, P Init nA nB skA skB) -∗
  minted skA -∗
  minted skB -∗
  (∀ onB : option (term * term),
      (if onB is Some (nA, nB) then
         public nA ∧
         public nB ∧
         (public skB ∨ P Resp nA nB skA skB)
       else True) -∗
      Ψ (repr onB)) -∗
  WP cr_init c skA (Spec.pkey skB) {{ Ψ }}.
Proof.
rewrite /cr_init.
iIntros "#? #? #ctx inv #m_skA #m_skB Hpost".
iPoseProof "ctx" as "(? & ? & ?)".
wp_pures. wp_apply wp_pkey. wp_pures.
wp_apply (wp_mk_nonce (λ _, True)%I (λ _, True)%I) => //.
iIntros (nA) "_ _ #p_nA _ unreg".
rewrite (term_token_difference _ (↑N)) //.
iDestruct "unreg" as "[unreg _]".
iAssert (public nA) as "{p_nA} p_nA"; first by iApply "p_nA".
wp_list; wp_term_of_list.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  iApply public_of_list => /=. do !iSplit => //.
  by iApply public_verify_key.
wp_pures; wp_bind (recv _); iApply wp_recv => //.
iIntros (m2) "#Hm2".
wp_apply wp_verify => //; iSplit; last protocol_failure.
iIntros "{Hm2} %args #p_m2 #inv_m2".
wp_list_of_term args; last protocol_failure. wp_pures.
wp_list_match => [nA' nB pkB' {m2 args} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst pkB'.
rewrite public_of_list /=.
iDestruct "p_m2" as "(_ & p_nB & _)".
iAssert (public skB ∨ session N Resp nA nB (skA : term, skB : term))%I
  as "{inv_m2} sessB".
{ iDestruct "inv_m2" as "[?|#inv_m2]"; eauto.
  iDestruct "inv_m2" as (nA' nB' skA') "(%e_m2 & #sess)".
  case/Spec.of_list_inj: e_m2 => -> -> /Spec.sign_pkey_inj ->.
  by eauto. }
wp_list; wp_term_of_list.
iSpecialize ("inv" $! nA nB).
iMod (session_begin _ _ _ _ (skA : term, skB : term) with "[] [inv] [unreg]")
  as "[#sessA close]"; eauto.
{ iExists _, _. by iFrame. }
{ by eauto. }
iAssert (|={⊤}=> ▷ (public skB ∨ P Resp nA nB skA skB))%I
    with "[close]" as ">inv".
  iDestruct "sessB" as "[?|sessB]"; eauto.
  iMod ("close" with "[] sessB") as "close"; eauto.
  iIntros "!> !>". iDestruct "close" as "(% & % & %e & ?)".
  case: e => /term_of_sign_key_inj <- /term_of_sign_key_inj <-.
  by eauto.
wp_pures. wp_apply wp_sign; eauto.
{ rewrite public_of_list /=. do !iSplit => //.
  by iApply public_verify_key. }
{ iRight. iModIntro. iExists _, _, _. iSplit => //. }
iIntros "%m3 #p_m3". wp_pures. wp_apply wp_send => //.
wp_pures.
iApply ("Hpost" $! (Some (nA, nB))); eauto.
Qed.

Lemma wp_cr_resp c skB Ψ :
  channel c -∗
  cryptis_ctx -∗
  cr_ctx -∗
  minted skB -∗
  (∀ skA nA nB, P Resp nA nB skA skB) -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ skA,
           ⌜pkA = Spec.pkey skA⌝ ∗
           public pkA ∧
           public nA ∧
           public nB ∧
           (public skA ∨ P Init nA nB skA skB)
       else True) -∗
       Ψ (repr ot)) -∗
  WP cr_resp c skB {{ Ψ }}.
Proof.
iIntros "#? #? #ctx #m_skB inv Hpost".
iPoseProof "ctx" as "(? & ? & ?)".
rewrite /cr_resp; wp_pures. wp_apply wp_pkey. wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#Hm1".
wp_list_of_term m1; last protocol_failure.
wp_list_match => [nA pkA {m1} ->|_]; last protocol_failure.
rewrite public_of_list /=.
iDestruct "Hm1" as "(HnA & HpkA & _)".
wp_apply wp_is_verify_key.
{ by iApply public_minted. }
iSplit; last protocol_failure.
iIntros "%skA -> #m_skA".
wp_pures.
wp_pures; wp_bind (mk_nonce _).
iApply (wp_mk_nonce (λ _, True)%I (λ _, True)%I) => //.
iIntros (nB) "_ _ #p_nB _ unreg".
rewrite (term_token_difference _ (↑N)) //.
iDestruct "unreg" as "[token _]".
iAssert (public nB) as "{p_nB} HnB"; first by iApply "p_nB".
iMod (session_begin _ _ nA nB (skA : term, skB : term) with "[] [inv] [token]")
  as "[#sessB close]"; eauto.
{ iExists _, _. iSplit => //. }
{ by []. }
wp_pures.
wp_list; wp_term_of_list.
wp_apply wp_sign => //.
{ rewrite public_of_list /=. do !iSplit => //. }
{ iRight. iModIntro. iExists _, _, _. by eauto. }
iIntros "%m2 #p_m2". wp_pures. wp_apply wp_send => //.
wp_pures; wp_bind (recv _); iApply wp_recv => //; iIntros (m3) "#Hm3".
wp_apply wp_verify => //; iSplit; last protocol_failure.
iClear "Hm3" => {m3}. iIntros "%m3 #p_m3 #inv_m3".
wp_list_of_term m3; last protocol_failure.
wp_list_match => [nA' nB' pkB' {m3} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nA'.
wp_eq_term e; last protocol_failure; subst nB'.
wp_eq_term e; last protocol_failure; subst pkB'.
wp_if.
iAssert (|={⊤}=> ▷ (public skA ∨ P Init nA nB skA skB))%I
    with "[close]" as ">inv".
  iDestruct "inv_m3" as "[inv_m3 | #inv_m3]"; eauto.
  iDestruct "inv_m3" as "(% & % & % & %e & sessA)".
  case/Spec.of_list_inj: e => <- <- /Spec.sign_pkey_inj <-.
  iMod ("close" with "[] sessA") as "close"; eauto.
  iIntros "!> !>".
  iDestruct "close" as "(% & % & %e & close)".
  case: e => /term_of_sign_key_inj <- /term_of_sign_key_inj <-.
  by eauto.
wp_pures; iApply ("Hpost" $! (Some (_, _, _))).
by iModIntro; iExists _; do ![iSplit=> //].
Qed.

End CR.

Arguments cr_alloc {Σ _ _ _} N.
