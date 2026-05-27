From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.lib Require Import gmeta nown saved_prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

A --> B: nA, pk(A)
B --> A: {nA, nB, pk(A)}_sk(B)
A --> B: {nA, nB, pk(B)}_sk(A)

*)

Class crGpreS Σ := CrGPreS {
  crGpreS_meta : metaGS Σ;
  crGpreS_pred : savedPredG Σ (role * term * term * sign_key * sign_key);
}.

Local Existing Instance crGpreS_meta.
Local Existing Instance crGpreS_pred.

Class crGS Σ := CrGS {
  cr_inG : crGpreS Σ;
  cr_name : gname;
}.

Local Existing Instance cr_inG.

Definition crΣ : gFunctors :=
  #[metaΣ; savedPredΣ (role * term * term * sign_key * sign_key)].

Global Instance subG_crGpreS Σ : subG crΣ Σ → crGpreS Σ.
Proof. solve_inG. Qed.

Section CR.

Context `{!heapGS Σ, !cryptisGS Σ, !crGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types skA skB : sign_key.
Implicit Types (φ : role → term → term → sign_key → sign_key → iProp).

Definition cr_token E : iProp :=
  gmeta_token cr_name E.

Definition cr_pred N φ : iProp :=
  nown cr_name N
    (saved_pred DfracDiscarded
                (λ '(rl, nA, nB, skA, skB), φ rl nA nB skA skB)).

Lemma cr_pred_set N φ E :
  ↑N ⊆ E →
  cr_token E ==∗ cr_pred N φ ∗ cr_token (E ∖ ↑N).
Proof. by iIntros "%"; iApply nown_alloc. Qed.

Lemma cr_token_difference E1 E2 :
  E1 ⊆ E2 →
  cr_token E2 ⊣⊢ cr_token E1 ∗ cr_token (E2 ∖ E1).
Proof. exact: gmeta_token_difference. Qed.

Lemma cr_token_drop E1 E2 :
  E1 ⊆ E2 →
  cr_token E2 -∗ cr_token E1.
Proof. exact: gmeta_token_drop. Qed.

Context (N : namespace).

Definition cr_ready rl nA nB skA skB : iProp := ∀ φ,
  cr_pred N φ →
  term_token (if rl is Init then nB else nA) (↑N.@"ready") ={⊤}=∗
    ▷ φ rl nA nB skA skB.

Lemma cr_ready_alloc rl nA nB skA skB φ :
  cr_pred N φ -∗
  φ rl nA nB skA skB ={⊤}=∗
  □ cr_ready rl nA nB skA skB.
Proof.
iIntros "#N_φ φ_ts".
iMod (escrowI nroot with "φ_ts []") as "#?".
{ by iApply (term_token_switch (if rl is Init then nB else nA) (N.@"ready")). }
iIntros "!> !> %φ' #N_φ' ready".
iPoseProof (nown_valid_2 with "N_φ N_φ'") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #φ_eq]".
iSpecialize ("φ_eq" $! (rl, nA, nB, skA, skB)).
iMod (escrowE with "[//] ready") as "res" => //.
iIntros "!> !>". by iRewrite -"φ_eq".
Qed.

Definition msg2_pred skB t : iProp :=
  ∃ nA nB skA,
    ⌜t = Spec.of_list [nA; nB; Spec.pkey skA]⌝ ∧
    cr_ready Resp nA nB skA skB.

Definition msg3_pred skA m3 : iProp :=
  ∃ nA nB skB,
    ⌜m3 = Spec.of_list [nA; nB; Spec.pkey skB]⌝ ∧
    cr_ready Init nA nB skA skB.

Definition cr_ctx : iProp :=
  sign_pred (N.@"m2") msg2_pred ∗
  sign_pred (N.@"m3") msg3_pred.

Lemma cr_alloc E E' :
  ↑N ⊆ E →
  seal_pred_token SIGN E ={E'}=∗
  cr_ctx ∗
  seal_pred_token SIGN (E ∖ ↑N).
Proof.
iIntros (sub) "token".
rewrite (seal_pred_token_difference (↑N)) //.
iDestruct "token" as "[t2 token]"; iFrame.
iMod (sign_pred_set (N := N.@"m2") msg2_pred with "t2") as "[#H2 t2]";
  try solve_ndisj.
iMod (sign_pred_set (N := N.@"m3") msg3_pred with "t2") as "[#H3 _]";
  try solve_ndisj.
by iModIntro; iSplit.
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

Lemma wp_cr_init c skA skB φ Ψ :
  channel c -∗
  cryptis_ctx -∗
  cr_ctx -∗
  cr_pred N φ -∗
  (∀ nA nB, φ Init nA nB skA skB) -∗
  minted skA -∗
  minted skB -∗
  (∀ onB : option (term * term),
      (if onB is Some (nA, nB) then
         public nA ∧
         public nB ∧
         (public skB ∨ φ Resp nA nB skA skB)
       else True) -∗
      Ψ (repr onB)) -∗
  WP cr_init c skA (Spec.pkey skB) {{ Ψ }}.
Proof.
rewrite /cr_init.
iIntros "#? #? #ctx #N_φ inv #m_skA #m_skB Hpost".
iPoseProof "ctx" as "[? ?]".
wp_pures. wp_apply wp_pkey. wp_pures.
wp_apply (wp_mk_nonce (λ _, True)%I (λ _, True)%I) => //.
iIntros (nA) "_ _ #p_nA _ _ _ unreg".
rewrite (term_token_difference _ (↑N.@"ready")); last solve_ndisj.
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
iAssert (public skB ∨ cr_ready Resp nA nB skA skB)%I
  as "{inv_m2} sessB".
{ iDestruct "inv_m2" as "[?|#inv_m2]"; eauto.
  iDestruct "inv_m2" as (nA' nB' skA') "(%e_m2 & #ready)".
  case/Spec.of_list_inj: e_m2 => -> -> /Spec.sign_pkey_inj ->.
  by eauto. }
wp_list; wp_term_of_list.
iSpecialize ("inv" $! nA nB).
iMod (cr_ready_alloc Init nA nB skA skB with "N_φ inv") as "#sessA".
iAssert (|={⊤}=> ▷ (public skB ∨ φ Resp nA nB skA skB))%I
    with "[unreg]" as ">inv".
  iDestruct "sessB" as "[?|sessB]"; eauto.
  iMod ("sessB" $! φ with "N_φ unreg") as "res".
  by iIntros "!> !>"; iRight.
wp_pures. wp_apply wp_sign; eauto.
{ rewrite public_of_list /=. do !iSplit => //.
  by iApply public_verify_key. }
{ iRight. iModIntro. iExists _, _, _. by iSplit. }
iIntros "%m3 #p_m3". wp_pures. wp_apply wp_send => //.
wp_pures.
iApply ("Hpost" $! (Some (nA, nB))); eauto.
Qed.

Lemma wp_cr_resp c skB φ Ψ :
  channel c -∗
  cryptis_ctx -∗
  cr_ctx -∗
  cr_pred N φ -∗
  minted skB -∗
  (∀ skA nA nB, φ Resp nA nB skA skB) -∗
  (∀ ot : option (term * term * term),
      (if ot is Some (pkA, nA, nB) then
         ∃ skA,
           ⌜pkA = Spec.pkey skA⌝ ∗
           public pkA ∧
           public nA ∧
           public nB ∧
           (public skA ∨ φ Init nA nB skA skB)
       else True) -∗
       Ψ (repr ot)) -∗
  WP cr_resp c skB {{ Ψ }}.
Proof.
iIntros "#? #? #ctx #N_φ #m_skB inv Hpost".
iPoseProof "ctx" as "[? ?]".
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
iIntros (nB) "_ _ #p_nB _ _ _ unreg".
rewrite (term_token_difference _ (↑N.@"ready")); last solve_ndisj.
iDestruct "unreg" as "[token _]".
iAssert (public nB) as "{p_nB} HnB"; first by iApply "p_nB".
iSpecialize ("inv" $! skA nA nB).
iMod (cr_ready_alloc Resp nA nB skA skB with "N_φ inv") as "#sessB".
wp_pures.
wp_list; wp_term_of_list.
wp_apply wp_sign => //.
{ rewrite public_of_list /=. do !iSplit => //. }
{ iRight. iModIntro. iExists _, _, _. by iSplit. }
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
iAssert (|={⊤}=> ▷ (public skA ∨ φ Init nA nB skA skB))%I
    with "[token]" as ">inv".
  iDestruct "inv_m3" as "[inv_m3 | #inv_m3]"; eauto.
  iDestruct "inv_m3" as "(% & % & % & %e & sessA)".
  case/Spec.of_list_inj: e => <- <- /Spec.sign_pkey_inj <-.
  iMod ("sessA" $! φ with "N_φ token") as "res".
  by iIntros "!> !>"; iRight.
wp_pures; iApply ("Hpost" $! (Some (_, _, _))).
by iModIntro; iExists _; do ![iSplit=> //].
Qed.

End CR.

Arguments cr_alloc {Σ _ _ _} N.
Arguments cr_pred {Σ _} N φ.
Arguments cr_pred_set {Σ _} N φ E.
Arguments cr_ready {Σ _ _ _} N rl nA nB skA skB.
Arguments cr_ready_alloc {Σ _ _ _} N rl nA nB skA skB φ.

Lemma crGS_alloc `{!heapGS Σ, !cryptisGS Σ} :
  crGpreS Σ →
  ⊢ |==> ∃ (H : crGS Σ), cr_token ⊤.
Proof.
iIntros (?). iMod gmeta_token_alloc as "(%γ & ?)".
iExists (CrGS _ _). by eauto.
Qed.

Arguments crGS_alloc {Σ _ _}.
