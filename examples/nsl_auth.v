From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSL.

Context `{!heapGS Σ, !spawnG Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : aenc_key).

Variable N : namespace.

(*

A --> B: {nA; pkA}@pkB
B --> A: {nA; nB; pkB}@pkA
A --> B: {nB}@pkB

*)

Definition init : val := λ: "c" "l" "skI" "pkR",
  let: "nI" := mk_nonce #() in
  let: "pkI" := pkey "skI" in
  let: "m1" := aenc "pkR" (Tag $ N.@"m1") (term_of_list ["nI"; "pkI"]) in
  send "c" "m1";;
  bind: "m2"   := adec "skI" (Tag $ N.@"m2") (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nI'"; "nR"; "pkR'"] := "m2" in
  guard: eq_term "nI'" "nI" && eq_term "pkR'" "pkR" in
  "l" <- term_of_list ["pkI"; "pkR"; term_of_list ["nI"; "nR"]];;
  let: "m3" := aenc "pkR" (Tag $ N.@"m3") "nR" in
  send "c" "m3";;
  SOME (term_of_list ["nI"; "nR"]).

Definition resp : val := λ: "c" "lR" "skR",
  let: "pkR" := pkey "skR" in
  bind: "m1" := adec "skR" (Tag $ N.@"m1") (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["nI"; "pkI"] := "m1" in
  guard: is_aenc_key "pkI" in
  let: "nR" := mk_nonce #() in
  "lR" <- term_of_list ["pkI"; "pkR"; term_of_list ["nI"; "nR"]] ;;
  let: "m2" := aenc "pkI" (Tag $ N.@"m2") (term_of_list ["nI"; "nR"; "pkR"]) in
  send "c" "m2";;
  bind: "m3" := adec "skR" (Tag $ N.@"m3") (recv "c") in
  guard: eq_term "m3" "nR" in
  SOME ("pkI", term_of_list ["nI"; "nR"]).

Definition corrupt skI skR : iProp :=
  public skI ∨ public skR.

Global Instance corrupt_persistent kI kR :
  Persistent (corrupt kI kR).
Proof. apply _. Qed.

Lemma corruptE kI kR :
  corrupt kI kR -∗
  □ (public kI ↔ ▷ False) -∗
  □ (public kR ↔ ▷ False) -∗
  ▷ False.
Proof.
by iIntros "[cor|cor] p_kI p_kR"; [iApply "p_kI"|iApply "p_kR"].
Qed.

Definition session l skI skR (sk : term) : iProp :=
  l ↦□ (Spec.of_list [Spec.pkey skI; Spec.pkey skR; sk] : val).

Global Instance session_persistent l skI skR sk :
  Persistent (session l skI skR sk).
Proof. apply _. Qed.

Definition msg1_pred skR m1 : iProp :=
  ∃ nI skI,
    ⌜m1 = Spec.of_list [nI; Spec.pkey skI]⌝ ∧
    (public nI ↔ ▷ corrupt skI skR).

Definition msg2_pred lR skI m2 : iProp :=
  ∃ nI nR skR,
    ⌜m2 = Spec.of_list [nI; nR; Spec.pkey skR]⌝ ∧
    session lR skI skR (Spec.of_list [nI; nR]) ∧
    (public nR ↔ ▷ corrupt skI skR).

Definition msg3_pred lI lR skR nR : iProp :=
  ∃ nI skI,
    session lI skI skR (Spec.of_list [nI; nR]) ∧
    (□ (public skR ↔ ▷ False) -∗ ▷ session lR skI skR (Spec.of_list [nI; nR])).

Definition nsl_ctx lI lR : iProp :=
  aenc_pred (N.@"m1") msg1_pred ∧
  aenc_pred (N.@"m2") (msg2_pred lR) ∧
  aenc_pred (N.@"m3") (msg3_pred lI lR).

Lemma nsl_alloc lI lR E E' :
  ↑N ⊆ E →
  seal_pred_token AENC E ={E'}=∗
  nsl_ctx lI lR ∗
  seal_pred_token AENC (E ∖ ↑N).
Proof.
iIntros (sub1) "t1".
rewrite (seal_pred_token_difference _ (↑N) E) //.
iDestruct "t1" as "[t1 t1']". iFrame.
iMod (aenc_pred_set (N := N.@"m1") msg1_pred with "t1")
  as "[#H1 t1]"; try solve_ndisj.
iMod (aenc_pred_set (N := N.@"m2") (msg2_pred lR) with "t1")
  as "[#H2 t1]"; try solve_ndisj.
iMod (aenc_pred_set (N := N.@"m3") (msg3_pred lI lR) with "t1")
  as "[#H3 t1]"; try solve_ndisj.
iModIntro; iFrame; do !iSplit => //.
Qed.

Global Instance nsl_ctx_persistent lI lR :
  Persistent (nsl_ctx lI lR).
Proof. apply _. Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_init c lI v0 lR skI skR :
  {{{ channel c ∗ cryptis_ctx ∗ nsl_ctx lI lR ∗
      minted skI ∗ □ (public skI ↔ ▷ False) ∗
      minted skR ∗ lI ↦ v0 }}}
    init c #lI skI (Spec.pkey skR)
  {{{ ts, RET (repr ts);
      if ts is Some sk then
        session lI skI skR sk ∗
        □ (□ (public skR ↔ ▷ False) -∗ ▷ session lR skI skR sk)
      else True }}}.
Proof.
iIntros "%Ψ (#chan_c & #ctx & #(?&?&?) & #m_skI & #s_skI & #m_skR & Hl)".
iIntros "Hpost".
rewrite /init. wp_pures.
wp_apply (wp_mk_nonce (λ _, corrupt skI skR) (λ _, False)%I) => //.
iIntros "%nI _ #m_nI #s_nI _ token".
rewrite bi.intuitionistic_intuitionistically.
wp_pures. wp_apply wp_pkey. wp_pures.
wp_list. wp_term_of_list.
wp_apply wp_aenc; eauto.
- rewrite minted_of_list /= minted_pkey. by eauto.
- iRight. iSplit.
  + iModIntro. iExists _, _. by eauto.
  + iIntros "!> #p_skI". rewrite public_of_list /= public_aenc_key.
    do !iSplit => //.
    iApply "s_nI". by iRight.
iIntros "%m1 #p_m1". wp_pures.
wp_apply (wp_send with "[] [#]"); eauto.
wp_pures. wp_bind (recv _). iApply wp_recv; eauto.
iIntros "%m2 #p_m2". wp_apply wp_adec; eauto.
iSplit; last protocol_failure.
iClear "p_m2" => {m2}. iIntros "%m2 #m_m2 #inv_m2". wp_pures.
wp_list_of_term m2; last protocol_failure.
wp_list_match => [nI' nR pkR' {m2} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nI'.
wp_eq_term e; last protocol_failure; subst pkR'.
rewrite minted_of_list public_of_list /=.
iDestruct "m_m2" as "(_ & m_nR & _)".
wp_pure _ credit:"c".
wp_pures. wp_list. wp_bind (term_of_list (repr_list _)). wp_term_of_list.
wp_list. wp_term_of_list.
wp_store. iMod (pointsto_persist with "Hl") as "#Hl".
iAssert (▷ ((public nR ↔ ▷ corrupt skI skR) ∧
            (□ (public skR ↔ ▷ False) -∗
             ▷ session lR skI skR (Spec.of_list [nI; nR]))))%I
  as "sessR".
{ iDestruct "inv_m2" as "[(p_nI&p_nR&_)|(#inv_m2&_)]".
  - iSpecialize ("s_nI" with "p_nI"). iSplit; first by iSplit; eauto.
    iIntros "!> #s_skR".
    iDestruct (corruptE with "s_nI [//] [//]") as ">[]".
  - iDestruct "inv_m2" as "(%nI' & %nR' & %skR' & %e & ? & s_nR)".
    case/Spec.of_list_inj: e => <- <- /Spec.aenc_pkey_inj <- {nI' nR' skR'}.
    iSplit => //. by eauto. }
iMod (lc_fupd_elim_later_pers with "c sessR") as "{sessR} #[s_nR sessR]".
wp_apply wp_aenc; eauto.
{ iRight. iSplit.
  - iExists _, _. by eauto.
  - iIntros "!> #p_skR". iApply "s_nR". by iRight. }
iIntros "%m3 #p_m3". wp_pures. wp_apply wp_send => //.
wp_pures. wp_list. wp_term_of_list. wp_pures.
iApply ("Hpost" $! (Some (Spec.of_list [nI; nR]))).
iModIntro. by eauto.
Qed.

Lemma wp_resp c lI lR v0 skR :
  {{{ channel c ∗ cryptis_ctx ∗ nsl_ctx lI lR ∗
      minted skR ∗ □ (public skR ↔ ▷ False) ∗ lR ↦ v0 }}}
    resp c #lR skR
  {{{ ts, RET (repr ts);
      if ts is Some (pkI, sk) then ∃ skI,
        ⌜pkI = Spec.pkey skI⌝ ∗
        minted skI ∗
        session lR skI skR sk ∗
        □ (□ (public skI ↔ ▷ False) -∗ ▷^2 session lI skI skR sk)
      else True }}}.
Proof.
iIntros "%Ψ (#chan_c & #ctx & #(?&?&?) & #m_skR & #s_skR & Hl) Hpost".
rewrite /resp. wp_pures. wp_apply wp_pkey.
wp_pures. wp_apply wp_recv => //; iIntros (m1) "#Hm1".
wp_apply wp_adec; eauto. iSplit; last protocol_failure.
iClear "Hm1" => {m1}. iIntros "%m1 #m_m1 #inv".
wp_list_of_term m1; last protocol_failure.
wp_list_match => [nI pkI {m1} ->|_]; last protocol_failure.
rewrite minted_of_list public_of_list /=.
iDestruct "m_m1" as "(m_nI & m_pkI & _)".
wp_apply wp_is_aenc_key => //. iSplit; last protocol_failure.
iIntros "%skI -> #m_skI {m_pkI}". wp_pures.
iAssert (▷ corrupt skI skR → public nI)%I as "{inv} s_nI".
{ iDestruct "inv" as "[(? & _)|(#inv & _)]"; eauto.
  iDestruct "inv" as "(%nI' & %skI' & %e & #p_ekI & #p_nI)".
  by case/Spec.of_list_inj: e => <- /Spec.aenc_pkey_inj <- {nI' skI'}. }
wp_apply (wp_mk_nonce (λ _, corrupt skI skR) (λ _, False)%I) => //.
iIntros "%nR _ #m_nR #s_nR _ _". rewrite bi.intuitionistic_intuitionistically.
wp_pures. wp_bind (term_of_list (nI :: _)%E).
wp_list. wp_term_of_list. wp_list. wp_term_of_list.
wp_store. iMod (pointsto_persist with "Hl") as "#Hl".
wp_list; wp_term_of_list. wp_apply wp_aenc; eauto.
- rewrite minted_of_list /= minted_pkey. by eauto.
- iRight. iSplit.
  + iModIntro. iExists _, _, _. by eauto.
  + iIntros "!> #p_skI". rewrite public_of_list /= public_aenc_key.
    do !iSplit => //.
    * iApply "s_nI". by iLeft.
    * iApply "s_nR". by iLeft.
iIntros "%m2 #p_m2". wp_pures. wp_apply wp_send => //.
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m3 #p_m3".
wp_apply wp_adec; eauto. iSplit; last protocol_failure.
iClear "p_m3" => {m3}. iIntros "%m3 #m_m3 #inv_m3". wp_pures.
wp_eq_term e; last protocol_failure; subst m3.
wp_pures. wp_list. wp_term_of_list. wp_pures.
iApply ("Hpost" $! (Some (Spec.pkey skI, (Spec.of_list [nI; nR])))).
iModIntro. iExists skI. do !iSplit => //.
iIntros "!> #s_skI". iDestruct "inv_m3" as "[p_nR|[#inv_m3 _]]".
- iSpecialize ("s_nR" with "p_nR"). iModIntro.
  iDestruct (corruptE with "s_nR s_skI s_skR") as ">[]".
- iDestruct "inv_m3" as "(%nI' & %skI' & sessI & sessR)".
  iSpecialize ("sessR" with "s_skR"). iModIntro.
  iPoseProof (pointsto_agree with "sessR Hl") as "%e".
  case/(val_of_term_inj _ _)/Spec.of_list_inj: e.
  by move=> /Spec.aenc_pkey_inj -> /Spec.of_list_inj [->].
Qed.

Definition game : val := λ: <>,
  let: "c"  := init_network #() in
  let: "skI" := mk_aenc_key #() in
  let: "skR" := mk_aenc_key #() in
  let: "pkI" := pkey "skI" in
  let: "pkR" := pkey "skR" in
  send "c" "pkI";;
  send "c" "pkR";;
  let: "pkR'" := recv "c" in
  guard: is_aenc_key "pkR'" in
  let: "lI" := ref (recv "c") in
  let: "lR" := ref (recv "c") in
  let: "res" := init "c" "lI" "skI" "pkR'" ||| resp "c" "lR" "skR" in
  bind: "resI" := Fst "res" in
  bind: "resR" := Snd "res" in
  let: "pkI'" := Fst "resR" in
  if: eq_term "pkR" "pkR'" || eq_term "pkI" "pkI'" then
    SOME (eq_term !"lI" !"lR")
  else SOME #true.

Lemma wp_game :
  cryptis_ctx -∗
  seal_pred_token AENC ⊤ -∗
  WP game #() {{ v, ⌜v = NONEV ∨ v = SOMEV #true⌝ }}.
Proof.
iIntros "#ctx seal_tok"; rewrite /game; wp_pures.
wp_apply wp_init_network => //. iIntros "%c #cP".
wp_pures; wp_bind (mk_aenc_key _).
iApply (wp_mk_aenc_key with "[]"); eauto.
iIntros "%skI #m_skI s_skI tokenI". wp_pures.
wp_apply (wp_mk_aenc_key with "[]"); eauto.
iIntros "%skR #m_skR s_skR tokenR". wp_pures.
wp_apply wp_pkey. wp_pures. set pkI := Spec.pkey skI.
wp_apply wp_pkey. wp_pures. set pkR := Spec.pkey skR.
iMod (freeze_secret with "s_skI")  as "#?".
iMod (freeze_secret with "s_skR")  as "#?".
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by iApply public_aenc_key.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by iApply public_aenc_key.
wp_pures; wp_bind (recv _); iApply wp_recv => //.
iIntros (pkR') "#p_pkR'". wp_pures.
wp_apply wp_is_aenc_key; first by iApply public_minted.
iSplit; last by wp_pures; iLeft.
iIntros "%skR' -> #m_skR'".
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%vI _". wp_alloc lI as "HlI".
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%vR _". wp_alloc lR as "HlR".
iMod (nsl_alloc lI lR with "seal_tok") as "[#nsl_ctx _]" => //.
wp_pures; wp_bind (par _ _).
iApply (wp_par (λ v, ∃ a : option term, ⌜v = repr a⌝ ∗ _)%I
               (λ v, ∃ a : option (term * term), ⌜v = repr a⌝ ∗ _)%I
          with "[HlI] [HlR]").
- wp_apply (wp_init with "[HlI]").
    iFrame. by eauto 10.
  iIntros "%a H". iExists a. iSplit; first done. by iApply "H".
- wp_apply (wp_resp with "[HlR]").
    iFrame. by eauto 10.
  iIntros "%a H"; iExists a; iSplit; first done. iApply "H".
iIntros (v1 v2) "[H1 H2]".
iDestruct "H1" as (a) "[-> H1]".
iDestruct "H2" as (b) "[-> H2]".
iModIntro.
wp_pure credit:"c1".
case: a => [sess_keyI|]; wp_pure credit:"c2"; wp_pures; last by eauto.
case: b => [[pkI' sess_keyR]|]; wp_pures; last by eauto.
iDestruct "H1" as "(#sessI & #sessR)".
iDestruct "H2" as (skI') "(-> & #m_skI' & #sessR' & #sessI')".
pose (b := bool_decide (pkR = Spec.pkey skR' ∨ pkI = Spec.pkey skI')).
wp_bind (eq_term pkR _ || _)%E.
iApply (wp_wand _ _ _ (λ v, ⌜v = #b⌝)%I with "").
{ wp_eq_term e_pkR; wp_pures.
  iPureIntro. rewrite /b bool_decide_decide decide_True //. eauto.
  iApply wp_eq_term. iPureIntro. congr (# (LitBool _)).
  apply bool_decide_ext. intuition congruence. }
iIntros "% ->". rewrite {}/b.
case: (bool_decide_reflect (pkR = _ ∨ _)) => [succ|_]; last by wp_pures; eauto.
iAssert (|={⊤}=> ⌜pkR = Spec.pkey skR' ∧ pkI = Spec.pkey skI' ∧ sess_keyI = sess_keyR⌝)%I
  with "[c1 c2]" as ">%e".
{ case: succ => [/Spec.aenc_pkey_inj <-|/Spec.aenc_pkey_inj <-].
  - iSpecialize ("sessR" with "[//]").
    iMod (lc_fupd_elim_later with "c1 sessR") as "{sessR} sessR".
    iPoseProof (pointsto_agree with "sessR sessR'") as "%e".
    case/val_of_term_inj/Spec.of_list_inj: e => <- <-.
    by eauto.
  - iSpecialize ("sessI'" with "[//]").
    iMod (lc_fupd_elim_later with "c1 sessI'") as "{sessI'} #sessI'".
    iMod (lc_fupd_elim_later with "c2 sessI'") as "{sessI'} #sessI'".
    iPoseProof (pointsto_agree with "sessI sessI'") as "%e".
    case/val_of_term_inj/Spec.of_list_inj: e => -> <-.
    by eauto. }
case: e => /Spec.aenc_pkey_inj <- [] /Spec.aenc_pkey_inj <- <- {succ}.
rewrite /session. wp_pures. wp_load. wp_load.
wp_bind (eq_term _ _). iApply wp_eq_term.
rewrite bool_decide_decide decide_True //.
wp_pures; eauto.
Qed.

End NSL.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ].

Lemma nsl_secure σ₁ σ₂ (v : val) ts :
  rtc erased_step ([game nroot #()], σ₁) (Val v :: ts, σ₂) →
  v = NONEV ∨ v = SOMEV #true.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_result NotStuck _ _ (λ v _, v = NONEV ∨ v = SOMEV #true)).
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisGS_alloc _) as (?) "(#ctx & seal_tok & key_tok & ? & hon & phase)".
iApply (wp_game with "ctx [seal_tok]") => //.
Qed.
