From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par ticket_lock assert.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.primitives Require Import attacker.
From cryptis.lib Require Import term_set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Section NSL.

Context `{!heapGS Σ, !cryptisGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t kI kR nI nR sI sR kS : term).

Definition nslN := nroot.@"nsl".

Record sess_info : Type := SessInfo {
  si_init_share : term;
  si_resp_share : term;
}.

Definition si_key kI kR si :=
  Spec.derive_key (Spec.of_list [TKey Seal kI; TKey Seal kR;
                                 si_init_share si;
                                 si_resp_share si]).

Definition nsl_session kI kR si : iProp :=
  □ (public (TKey Open kI) → ▷ False) ∗
  □ (public (TKey Open kR) → ▷ False) ∗
  □ (public (si_key kI kR si) → ▷^2 False).

Lemma nsl_session_agree kI1 kI2 kR1 kR2 si1 si2 :
  si_key kI1 kR1 si1 = si_key kI2 kR2 si2 →
  (kI1, kR1, si1) = (kI2, kR2, si2).
Proof.
case/Spec.tag_inj => _.
case/Spec.of_list_inj.
by case: si1 si2 => [??] [??] /= <- <- <- <-.
Qed.

Lemma nsl_session_public_key kI kR si :
  nsl_session kI kR si -∗
  public (si_key kI kR si) -∗
  ▷^2 False.
Proof. iIntros "(_ & _ & #H) #p_t". by iApply "H". Qed.

Definition compromise pk : iProp :=
  ∃ sk, ⌜pk = TKey Seal sk⌝ ∧ public (TKey Open sk).

Lemma compromise_TKey sk :
  compromise (TKey Seal sk) ⊣⊢ public (TKey Open sk).
Proof.
iSplit.
- by iIntros "(%sk' & %e & #?)"; case: e => <-.
- by iIntros "#p_dk"; iExists _; eauto.
Qed.

Lemma nsl_session_alloc kI kR si :
  □ (public (TKey Open kI) → ▷ False) -∗
  □ (public (TKey Open kR) → ▷ False) -∗
  □ (public (si_init_share si) ↔
       ▷ □ (public (TKey Open kI) ∨ public (TKey Open kR))) -∗
  □ (public (si_resp_share si) ↔
       ▷ □ (public (TKey Open kI) ∨ public (TKey Open kR))) ==∗
  nsl_session kI kR si.
Proof.
iIntros "#s_dkI #s_dkR #s_nI #s_nR".
iAssert (□ (public (si_key kI kR si) → ▷^2 False))%I as "#s_sk".
{ iIntros "!> #p_sk".
  rewrite public_derive_key public_of_list /=.
  iDestruct "p_sk" as "(_ & _ & p_nI & _)".
  by iDestruct ("s_nI" with "p_nI") as "[contra|contra]"; iNext;
  [iApply "s_dkI"|iApply "s_dkR"]. }
iModIntro. by do !iSplit => //.
Qed.

(*

A --> B: {m1; nA; pkA}@pkB
B --> A: {m2; nA; nB; pkB}@pkA
A --> B: {m3; nB}@pkB

*)

Definition init : val := λ: "c" "skI" "pkR",
  let: "pkI" := pkey "skI" in
  let: "nI" := mknonce #() in
  let: "m1" := aenc (nslN.@"m1") "pkR" (term_of_list ["nI"; "pkI"]) in
  send "c" "m1";;
  bind: "m2"   := adec (nslN.@"m2") "skI" (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nI'"; "nR"; "pkR'"] := "m2" in
  guard: eq_term "nI'" "nI" && eq_term "pkR'" "pkR" in
  let: "m3" := aenc (nslN.@"m3") "pkR" "nR" in
  send "c" "m3";;
  let: "sess_key" := derive_key (term_of_list ["pkI"; "pkR"; "nI"; "nR"]) in
  SOME "sess_key".

Definition resp : val := λ: "c" "skR",
  let: "pkR" := pkey "skR" in
  bind: "m1" := adec (nslN.@"m1") "skR" (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["nI"; "pkI"] := "m1" in
  let: "nR" := mknonce #() in
  let: "m2" := aenc (nslN.@"m2") "pkI" (term_of_list ["nI"; "nR"; "pkR"]) in
  send "c" "m2";;
  bind: "m3" := adec (nslN.@"m3") "skR" (recv "c") in
  guard: eq_term "m3" "nR" in
  let: "sess_key" := derive_key (term_of_list ["pkI"; "pkR"; "nI"; "nR"]) in
  SOME ("pkI", "sess_key").

Definition msg1_pred kR m1 : iProp := ∃ nI kI,
  ⌜m1 = Spec.of_list [nI; TKey Seal kI]⌝ ∧
  public (TKey Seal kI) ∧
  (public nI ↔ ▷ □ (public (TKey Open kI) ∨ public (TKey Open kR))).

Definition msg2_pred kI m2 : iProp := ∃ nI nR kR,
  let sess_key :=
    Spec.derive_key (Spec.of_list [TKey Seal kI; TKey Seal kR; nI; nR]) in
  ⌜m2 = Spec.of_list [nI; nR; TKey Seal kR]⌝ ∧
  (public (TKey Open kR) → ▷ False) ∧
  (public nR ↔ ▷ □ (public (TKey Open kI) ∨ public (TKey Open kR))) ∧
  term_meta nR (nroot.@"data") sess_key.

Definition msg3_pred kR nR : iProp := ∃ kI si,
  term_meta nR (nroot.@"data") (si_key kI kR si) ∧
  nsl_session kI kR si.

Definition nsl_ctx : iProp :=
  seal_pred (nslN.@"m1") msg1_pred ∧
  seal_pred (nslN.@"m2") msg2_pred ∧
  seal_pred (nslN.@"m3") msg3_pred.

Lemma nsl_alloc E1 E2 :
  ↑nslN ⊆ E1 →
  seal_pred_token E1 ={E2}=∗
  nsl_ctx ∗
  seal_pred_token (E1 ∖ ↑nslN).
Proof.
iIntros (sub1) "t1".
rewrite (seal_pred_token_difference (↑nslN) E1) //. iDestruct "t1" as "[t1 t1']".
iMod (seal_pred_set (nslN.@"m1") msg1_pred with "t1")
  as "[#H1 t1]"; try solve_ndisj.
iMod (seal_pred_set (nslN.@"m2") msg2_pred with "t1")
  as "[#H2 t1]"; try solve_ndisj.
iMod (seal_pred_set (nslN.@"m3") msg3_pred with "t1")
  as "[#H3 t1]"; try solve_ndisj.
iModIntro; iFrame; do !iSplit => //.
Qed.

Global Instance nsl_ctx_persistent : Persistent nsl_ctx.
Proof. apply _. Qed.

Lemma init_send_1 kI kR nI :
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Seal kI) -∗
  □ (public (TKey Open kI) → ▷ False) -∗
  public (TKey Seal kR) -∗
  minted nI -∗
  □ (public nI ↔ ▷ □ (public (TKey Open kI) ∨ public (TKey Open kR))) -∗
  public (TSeal (TKey Seal kR) (Spec.tag (nslN.@"m1") (Spec.of_list [nI; TKey Seal kI]))).
Proof.
iIntros "#? (#? & _ & _) #p_ekI #s_dkI #p_ekR #m_nI #p_nI".
iApply public_TSealIS; eauto.
- iModIntro. by iExists _, _; iSplit; eauto.
- by rewrite minted_of_list /=; eauto.
- rewrite public_of_list /=. iIntros "!> #p_dkR".
  do 2?iSplit => //. iApply "p_nI". by eauto.
Qed.

Lemma resp_recv_1_send_2 pkI kR nI nR :
  let sess_key := Spec.derive_key (Spec.of_list [pkI; TKey Seal kR; nI; nR]) in
  public (TSeal (TKey Seal kR)
            (Spec.tag (nslN.@"m1")
               (Spec.of_list [nI; pkI]))) -∗
  term_token nR ⊤ -∗
  cryptis_ctx ∗
  nsl_ctx ∗
  public (TKey Seal kR) ∗
  □ (public (TKey Open kR) → ▷ False) ∗
  minted nR ∗
  □ (public nR ↔ ▷ □ (compromise pkI ∨ public (TKey Open kR))) ={⊤}▷=∗
  term_meta nR (nroot.@"data") sess_key ∗
  term_token nR (⊤ ∖ ↑nroot.@"data") ∗
  public pkI ∗
  □ (▷ □ (compromise pkI ∨ public (TKey Open kR)) → public nI) ∗
  public (TSeal pkI
            (Spec.tag (nslN.@"m2")
               (Spec.of_list [nI; nR; TKey Seal kR]))).
Proof.
iIntros "%sess_key #p_m1 nR_token".
iIntros "(#? & (#? & #? & _) & #p_ekR & #s_dkR & #m_nR & #p_nR)".
rewrite (term_token_difference nR (↑nroot.@"data")) //.
iDestruct "nR_token" as "[data nR_token]"; iFrame "nR_token".
iMod (term_meta_set' (N := nroot.@"data") sess_key with "data")
       as "[#meta _]"; first solve_ndisj.
set m2 := Spec.of_list [_; _; _].
iAssert (□ ∀ kI, ⌜pkI = TKey Seal kI⌝ → msg2_pred kI m2)%I as "#inv_m2".
{ iIntros "!> %kI ->". rewrite /msg2_pred compromise_TKey. by eauto 13. }
iDestruct (public_TSealE with "p_m1 [//]") as "[[_ fail]|succ]".
- rewrite public_of_list /=. iDestruct "fail" as "(? & ? & _)".
  iIntros "!> !> !>". do !iSplit => //.
  { by iIntros "!> _". }
  iApply public_TSealI => //.
  + by iApply public_minted.
  + rewrite minted_of_list /=.
    by do !iSplit => //; iApply public_minted.
  + iIntros "%kI %e". iSplit.
    * iModIntro. by iApply "inv_m2".
    * iIntros "!> #p_dkR". rewrite public_of_list /=.
      do !iSplit => //. iApply "p_nR". rewrite {}e.
      iLeft. iExists kI. by eauto.
- iDestruct "succ" as "(#inv_m1 & m_m1 & _)". iIntros "!> !>".
  iDestruct "inv_m1" as "(%nI' & %kI & %e & p_ekI & s_nI)".
  case/Spec.of_list_inj: e => <- -> {nI' pkI} in sess_key *.
  do 3!iSplitR => //.
  { rewrite compromise_TKey. iIntros "!> !> #fail". by iApply "s_nI". }
  iApply public_TSealIS => //.
  + by iApply public_minted.
  + iModIntro. by iApply "inv_m2".
  + rewrite !minted_of_list /=. iDestruct "m_m1" as "(? & ? & _)".
    by do !iSplit => //; iApply public_minted.
  + iIntros "!> !> #p_dkR". rewrite public_of_list /=.
    do !iSplit => //.
    * iApply "s_nI". by eauto.
    * iApply "p_nR". iLeft. iExists kI. by eauto.
Qed.

Lemma init_recv_2_send_3 kI kR nI nR :
  let si := SessInfo nI nR in
  public (TSeal (TKey Seal kI)
            (Spec.tag (nslN.@"m2")
               (Spec.of_list [nI; nR; TKey Seal kR]))) -∗
  term_token nI ⊤ -∗
  cryptis_ctx ∗
  nsl_ctx ∗
  public (TKey Seal kI) ∗
  public (TKey Seal kR) ∗
  □ (public (TKey Open kI) → ▷ False) ∗
  □ (public nI ↔ ▷ □ (public (TKey Open kI) ∨ public (TKey Open kR))) ={⊤}▷=∗
  minted nR ∗
  public (TSeal (TKey Seal kR) (Spec.tag (nslN.@"m3") nR)) ∗
  term_token nI (⊤ ∖ ↑nroot.@"data") ∗
  (public (TKey Open kR) ∗ public (si_key kI kR si)
   ∨ nsl_session kI kR si).
Proof.
iIntros "%si #p_m2 nI_token".
iIntros "(#? & (_ & #? & #?) & #p_ekI & #p_ekR & #s_dkI & #s_nI)".
rewrite (term_token_difference _ (↑nroot.@"data")) //.
iDestruct "nI_token" as "[_ nI_token]". iFrame "nI_token".
iDestruct (public_TSealE with "p_m2 [//]") as "[fail|succ]".
- rewrite !public_of_list /=.
  iDestruct "fail" as "(_ & p_nI & p_nR & _ & _)".
  iSpecialize ("s_nI" with "p_nI").
  iIntros "!> !>". iDestruct "s_nI" as "#[contra|fail]".
  { iDestruct ("s_dkI" with "contra") as ">[]". }
  iIntros "!>". iSplit; first by iApply public_minted.
  iSplit.
  + iApply public_TSealIP => //. by rewrite public_tag.
  + iLeft. do !iSplit => //.
    rewrite public_derive_key public_of_list /=. by eauto.
- iDestruct "succ" as "(#inv_m2 & m_m2 & _)".
  rewrite minted_of_list /=. iDestruct "m_m2" as "(_ & m_nR & _)".
  iIntros "!> !>".
  iDestruct "inv_m2"
    as "(%nI' & %nR' & %kR' & %e & s_dkR & s_nR & meta)".
  case/Spec.of_list_inj: e => {nI' nR' kR'} <- <- <-.
  iMod (nsl_session_alloc kI kR si with "[//] [//] [//] [//]")
    as "#key_nR'" => //.
  iFrame. iIntros "!>". iSplit => //.
  iSplit.
  { iApply public_TSealIS => //.
    + by iApply public_minted.
    + iIntros "!>". iExists kI, si. by eauto.
    + iIntros "!> #p_dkR". iApply "s_nR". by eauto. }
  iRight. by iFrame.
Qed.

Lemma resp_recv_3 pkI kR nI nR :
  let sess_key :=
    Spec.derive_key (Spec.of_list [pkI; TKey Seal kR; nI; nR]) in
  public (TSeal (TKey Seal kR) (Spec.tag (nslN.@"m3") nR)) -∗
  cryptis_ctx ∗
  nsl_ctx ∗
  term_meta nR (nroot.@"data") sess_key ∗
  public pkI ∗
  public (TKey Seal kR) ∗
  □ (public (TKey Open kR) → ▷ False) ∗
  □ (▷ □ (compromise pkI ∨ public (TKey Open kR)) → public nI) ∗
  □ (public nR ↔ ▷ □ (compromise pkI ∨ public (TKey Open kR))) ={⊤}▷=∗ ∃ kI,
  ⌜pkI = TKey Seal kI⌝ ∗
  (public (TKey Open kI) ∗ public sess_key
   ∨ nsl_session kI kR (SessInfo nI nR)).
Proof.
iIntros "%sess_key #p_m3".
iIntros "(#? & (_ & _ & #?) & #meta & #p_pkI & #p_pkR & #s_dkR & #p_nI & #s_nR)".
iDestruct (public_TSealE with "p_m3 [//]") as "{p_m3} [[_ p_nR]|p_m3]".
- iSpecialize ("s_nR" with "p_nR"). iIntros "!> !>".
  iDestruct "s_nR" as "[(%kI & -> & #p_dkI)|#p_dkR]".
  + iExists kI. rewrite public_derive_key public_of_list /= compromise_TKey.
    iModIntro. iSplit => //. iLeft. do !iSplit => //.
    iApply "p_nI". by eauto.
  + by iDestruct ("s_dkR" with "p_dkR") as ">[]".
- iDestruct "p_m3" as "(#inv_m3 & _)". iIntros "!> !>".
  iDestruct "inv_m3" as "(%kI & %si & meta' & session)".
  case: si => nI' nR'.
  iPoseProof (term_meta_agree with "meta meta'") as "%e".
  case/Spec.tag_inj: e => _ e.
  case/Spec.of_list_inj: e => /= -> <- <-.
  iModIntro. iExists kI. iSplit; eauto.
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_init c kI kR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Seal kI) -∗
  □ (public (TKey Open kI) → ▷ False) -∗
  public (TKey Seal kR) -∗
  {{{ True }}}
    init c kI (TKey Seal kR)
  {{{ si, RET (repr (si_key kI kR <$> si));
      if si is Some si then
        let sk := si_key kI kR si in
        minted sk ∗
        term_token (si_init_share si) (⊤ ∖ ↑nroot.@"data") ∗
        (public (TKey Open kR) ∗ public sk ∨ nsl_session kI kR si)
      else True }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_kI #s_kI #p_kR %Ψ !> _ Hpost".
rewrite /init. wp_pures. wp_apply wp_pkey. wp_pures.
wp_apply (wp_mknonce (λ _, public (TKey Open kI) ∨ public (TKey Open kR))%I
            (λ _, False)%I) => //.
iIntros "%nI _ #m_nI #p_nI _ token".
wp_pures. wp_list. wp_term_of_list. wp_apply wp_aenc => /=. wp_pures.
wp_bind (send _ _). iApply (wp_send with "[] [#]"); eauto.
  iApply init_send_1; eauto.
wp_pures. wp_bind (recv _). iApply wp_recv; eauto.
iIntros "%m2 #p_m2". wp_adec m2; last protocol_failure.
wp_list_of_term m2; last protocol_failure.
wp_list_match => [nI' nR pkR' {m2} ->|_]; last protocol_failure.
wp_eq_term e; last protocol_failure; subst nI'.
wp_eq_term e; last protocol_failure; subst pkR'.
iDestruct (init_recv_2_send_3 with "p_m2 [$] []") as ">H"; first by eauto 10.
wp_pure.
iMod "H" as "(#m_nR & #p_m3 & token & inv)".
wp_apply wp_aenc. wp_pures. wp_bind (send _ _). iApply wp_send => //.
wp_list. wp_term_of_list. wp_apply wp_derive_key.
set sess_key := Spec.derive_key (Spec.of_list [TKey Seal kI; _; _; _]).
wp_pures.
iApply ("Hpost" $! (Some (SessInfo nI nR))). iModIntro. iFrame.
rewrite minted_tag minted_of_list /=.
by do !iSplit => //; iApply public_minted.
Qed.

Lemma wp_resp c kR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Seal kR) -∗
  □ (public (TKey Open kR) → ▷ False) -∗
  {{{ True }}}
    resp c kR
  {{{ ts, RET (repr ts);
      if ts is Some (pkI, sk) then ∃ kI si,
        ⌜pkI = TKey Seal kI⌝ ∗
        ⌜sk = si_key kI kR si⌝ ∗
        term_token (si_resp_share si) (⊤ ∖ ↑nroot.@"data") ∗
        (public (TKey Open kI) ∗ public sk ∨ nsl_session kI kR si)
      else True }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #p_kR #honR %Ψ !> _ Hpost".
rewrite /resp. wp_pures. wp_apply wp_pkey. wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (m1) "#p_m1".
wp_adec m1; last protocol_failure.
wp_list_of_term m1; last protocol_failure.
wp_list_match => [nI pkI {m1} ->|_]; last protocol_failure.
iPoseProof (public_minted with "p_m1") as "m_m1".
rewrite minted_TSeal minted_tag minted_of_list /=.
iDestruct "m_m1" as "(_ & m_nI & m_pkI & _)".
wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce_freshN
          ∅
          (λ _, compromise pkI ∨ public (TKey Open kR))%I
          (λ _, False)%I
          (λ nR, {[nR; Spec.derive_key (Spec.of_list [pkI; TKey Seal kR; nI; nR])]})) => //.
- by iIntros "% %".
- iIntros "%nR".
  rewrite big_sepS_union_pers !big_sepS_singleton minted_tag minted_of_list /=.
  iSplit => //; iModIntro; first by iSplit; iIntros "?".
  iSplit; last by iIntros "(_ & _ & _ & ? & _)".
  iIntros "#m_nR"; do !iSplit => //.
  by iApply public_minted.
iIntros "%nR _ %nonce #m_nR #s_nR _ tokens".
set sess_key := Spec.derive_key (Spec.of_list [_; _; _; _]).
have ? : nR ≠ sess_key.
  by move=> e; rewrite e Spec.is_nonce_tag in nonce.
rewrite big_sepS_union; last set_solver.
rewrite !big_sepS_singleton. iDestruct "tokens" as "[nR_token sk_token]".
iMod (resp_recv_1_send_2 with "p_m1 nR_token []" ) as "H"; first eauto 10.
wp_pures. iMod "H" as "(#meta & nR_token & #p_pkI & #p_nI & #p_m2)".
wp_bind (term_of_list (nI :: _)%E).
wp_list. wp_term_of_list. wp_list. wp_apply wp_aenc. wp_pures.
wp_bind (send _ _). iApply wp_send => //.
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%m3 #p_m3". wp_adec m3; last protocol_failure.
wp_eq_term e; last protocol_failure; subst m3.
iPoseProof (resp_recv_3 with "p_m3 []") as ">finished"; first eauto 10.
wp_pures. iMod "finished" as "(%kI & -> & finished)".
wp_list. wp_term_of_list. wp_apply wp_derive_key. wp_pures.
iApply ("Hpost" $! (Some (TKey Seal kI, sess_key))).
iModIntro. iExists kI, (SessInfo nI nR). by eauto.
Qed.

Definition do_init_loop : val := rec: "loop" "c" "set" "skI" "pkR" :=
  Fork ("loop" "c" "set" "skI" "pkR");;
  let: "pkR'" := recv "c" in
  (bind: "kt" := is_key "pkR'" in
   guard: ("kt" = repr Seal) in
   bind: "sk" := init "c" "skI" "pkR'" in
   if: eq_term "pkR" "pkR'" then
     add_fresh_lock_term_set "sk" "set";;
     let: "guess" := recv "c" in
     assert: (~ eq_term "sk" "guess")
   else #());;
   #().

Definition do_init : val := λ: "c" "kI" "pkR",
  let: "set" := new_lock_term_set #() in
  do_init_loop "c" "set" "kI" "pkR".

Definition si_share_of rl :=
  if rl is Init then si_init_share else si_resp_share.

Definition nsl_game_inv rl sk : iProp := ∃ kI kR si,
  ⌜sk = si_key kI kR si⌝ ∧
  term_meta (si_share_of rl si) (nroot.@"fresh") ().

Lemma nsl_game_inv_fresh kI kR rl si E :
  ↑nroot.@"fresh" ⊆ E →
  term_token (si_share_of rl si) E -∗
  fresh_term (nsl_game_inv rl) (si_key kI kR si).
Proof.
iIntros "%sub token". iSplit.
- iIntros "(%kI' & %kR' & %si' & %e & #meta)".
  case/nsl_session_agree: e => _ _ <-.
  by iApply (term_meta_token with "token meta").
- iMod (term_meta_set (nroot.@"fresh") () with "token") as "#?" => //.
  iIntros "!> !>". iExists kI, kR, si. by eauto.
Qed.

Lemma wp_do_init_loop c vset kI kR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Seal kI) -∗
  □ (public (TKey Open kI) → ▷ False) -∗
  □ (public (TKey Open kR) → ▷ False) -∗
  is_lock_term_set (nsl_game_inv Init) vset -∗
  {{{ True }}}
    do_init_loop c vset kI (TKey Seal kR)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #p_pkI #s_skI #s_skR #set".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ by iApply "IH" => //. }
wp_pures. wp_apply wp_recv => //.
iIntros (ekR') "#p_ekR'".
wp_pures; wp_bind (is_key _); iApply wp_is_key. wp_pures.
case: Spec.is_keyP => [kt kR' eekR|_]; wp_pures; last by iApply "Hpost".
wp_pures.
case: bool_decide_reflect => [ekt|_]; wp_pures ; last by iApply "Hpost".
case: kt eekR ekt => // -> _.
wp_pures. wp_apply wp_init => //. iIntros "%ts tsP".
case: ts=> [sk|] => /=; wp_pures; last by iApply "Hpost".
wp_eq_term e; wp_pures; last by iApply "Hpost".
case: e => <- {kR'}.
iDestruct "tsP" as "(_ & token & [[#p_skR _]|#sess])".
  iDestruct ("s_skR" with "p_skR") as ">[]".
iPoseProof (@nsl_game_inv_fresh kI kR Init with "token")
  as "fresh" => //; try solve_ndisj.
wp_apply (wp_add_fresh_lock_term_set with "[$]"). iIntros "_".
wp_pures. wp_apply wp_recv => //. iIntros "%guess #p_guess".
wp_pures. wp_apply wp_assert.
wp_eq_term e.
  rewrite -e.
  iPoseProof (nsl_session_public_key with "sess p_guess") as "contra".
  wp_pures.
  by iDestruct "contra" as ">[]".
wp_pures. iModIntro. iSplit => //. iNext. wp_pures. by iApply "Hpost".
Qed.

Lemma wp_do_init c kI kR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Seal kI) -∗
  □ (public (TKey Open kI) → ▷ False) -∗
  □ (public (TKey Open kR) → ▷ False) -∗
  {{{ True }}}
    do_init c kI (TKey Seal kR)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #p_pkI #s_skI #s_skR %Φ _ !> post".
wp_lam. wp_pures.
wp_apply (wp_new_lock_term_set (nsl_game_inv Init)) => //.
iIntros "%set #set". wp_pures.
wp_apply wp_do_init_loop => //.
Qed.

Definition do_resp_loop : val := rec: "loop" "c" "set" "skR" "pkI" :=
  Fork ("loop" "c" "set" "skR" "pkI");;
  (bind: "res" := resp "c" "skR" in
   let: "pkI'" := Fst "res" in
   let: "sk" := Snd "res" in
   add_fresh_lock_term_set "sk" "set";;
   if: eq_term "pkI" "pkI'" then
     let: "guess" := recv "c" in
     assert: (~ eq_term "sk" "guess")
   else #());;
  #().

Definition do_resp : val := λ: "c" "skR" "pkI",
  let: "set" := new_lock_term_set #() in
  do_resp_loop "c" "set" "skR" "pkI".

Lemma wp_do_resp_loop c set kI kR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Seal kR) -∗
  □ (public (TKey Open kR) → ▷ False) -∗
  □ (public (TKey Open kI) → ▷ False) -∗
  is_lock_term_set (nsl_game_inv Resp) set -∗
  {{{ True }}}
    do_resp_loop c set kR (TKey Seal kI)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #p_ekR #s_dkR #s_dkI #set".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ iApply "IH" => //. }
wp_pures. wp_apply wp_resp => //.
iIntros "%res res".
case: res => [[ekI' sk]|]; wp_pures; last by iApply "Hpost".
iDestruct "res" as "(%kI' & %si & -> & -> & token & res)".
iPoseProof (@nsl_game_inv_fresh kI' kR Resp with "token")
  as "fresh" => //; try solve_ndisj.
wp_apply (wp_add_fresh_lock_term_set with "[$]"). iIntros "_".
wp_eq_term e; wp_pures; last by iApply "Hpost".
case: e => <- {kI'}.
iDestruct "res" as "[[#p_dkI _]|sess]".
  iDestruct ("s_dkI" with "p_dkI") as ">[]".
wp_pures. wp_apply wp_recv => //. iIntros "%guess #p_guess".
wp_pures. wp_apply wp_assert.
wp_eq_term e.
  rewrite -e.
  iPoseProof (nsl_session_public_key with "sess p_guess") as "contra".
  wp_pures.
  by iDestruct "contra" as ">[]".
wp_pures. iModIntro. iSplit => //. iNext. wp_pures. by iApply "Hpost".
Qed.

Lemma wp_do_resp c kI kR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  public (TKey Seal kR) -∗
  □ (public (TKey Open kR) → ▷ False) -∗
  □ (public (TKey Open kI) → ▷ False) -∗
  {{{ True }}}
    do_resp c kR (TKey Seal kI)
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #? #? #? #? %Φ _ !> post".
wp_lam. wp_pures.
wp_apply (wp_new_lock_term_set (nsl_game_inv Resp)) => //.
iIntros "%set #set". wp_pures.
by wp_apply wp_do_resp_loop => //.
Qed.

Definition game : val := λ: <>,
  let: "c"  := init_network #() in
  let: "kI" := mkakey #() in
  let: "kR" := mkakey #() in
  let: "pkI" := pkey "kI" in
  let: "pkR" := pkey "kR" in
  send "c" "pkI";;
  send "c" "pkR";;
  Fork (do_init "c" "kI" "pkR");;
  Fork (do_resp "c" "kR" "pkI").

Lemma wp_game :
  cryptis_ctx -∗
  seal_pred_token ⊤ -∗
  key_pred_token (⊤ ∖ ↑nroot.@"keys") -∗
  honest 0 ∅ -∗
  ●Ph 0 -∗
  WP game #() {{ _, True }}.
Proof.
iIntros "#ctx enc_tok key_tok hon phase"; rewrite /game; wp_pures.
wp_apply wp_init_network => //. iIntros "%c #cP".
wp_pures; wp_bind (mkakey _).
iApply (wp_mkakey_phase with "[] [hon] phase"); eauto.
iIntros "%kI #p_ekI hon phase tokenI". wp_pures.
wp_bind (mkakey _). iApply (wp_mkakey_phase with "[] [hon] phase"); eauto.
iIntros "%kR #p_ekR hon phase tokenR". wp_pures.
wp_apply wp_pkey. wp_pures. set pkI := TKey Seal kI.
set skI := TKey Open kI.
wp_apply wp_pkey. wp_pures. set pkR := TKey Seal kR.
set skR := TKey Open kR.
iMod (freeze_honest with "[] hon phase") as "(hon & phase & sec)" => //; eauto.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
iMod "sec" as "sec".
rewrite big_sepS_forall. wp_pures.
iAssert (□ (public skI ↔ ▷ False))%I as "#s_dkI".
  by iApply "sec"; iPureIntro; set_solver.
iAssert (□ (public skR ↔ ▷ False))%I as "#s_dkR".
  by iApply "sec"; iPureIntro; set_solver.
iMod (nsl_alloc with "enc_tok") as "[#nsl_ctx _]" => //.
wp_apply wp_fork.
{ wp_apply wp_do_init => //.
  { iIntros "!> #p_dkI".
    iDestruct ("s_dkI" with "p_dkI") as ">[]". }
  { iIntros "!> #p_dkR".
    iDestruct ("s_dkR" with "p_dkR") as ">[]". } }
wp_pures. wp_apply wp_fork => //.
wp_apply wp_do_resp => //.
{ iIntros "!> #p_dkR".
  iDestruct ("s_dkR" with "p_dkR") as ">[]". }
{ iIntros "!> #p_dkI".
  iDestruct ("s_dkI" with "p_dkI") as ">[]". }
Qed.

End NSL.

Definition F : gFunctors :=
  #[heapΣ; cryptisΣ; tlockΣ].

Lemma nsl_secure σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([game #()], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisGS_alloc _) as (?) "(#ctx & enc_tok & key_tok & ? & hon & phase)".
by iApply (wp_game with "ctx [enc_tok] [key_tok] [hon]").
Qed.
