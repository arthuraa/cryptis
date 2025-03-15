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

Implicit Types (rl : role) (t skI skR nI nR sI sR kS : term).

Definition nslN := nroot.@"nsl".

Record sess_info : Type := SessInfo {
  si_init_share : term;
  si_resp_share : term;
}.

Definition si_key skI skR si :=
  Spec.derive_key (Spec.of_list [TKey Seal skI; TKey Seal skR;
                                 si_init_share si;
                                 si_resp_share si]).

Lemma nsl_session_agree kI1 kI2 kR1 kR2 si1 si2 :
  si_key kI1 kR1 si1 = si_key kI2 kR2 si2 →
  (kI1, kR1, si1) = (kI2, kR2, si2).
Proof.
case/Spec.tag_inj => _.
case/Spec.of_list_inj.
by case: si1 si2 => [??] [??] /= <- <- <- <-.
Qed.

Definition nonce_secrecy skA pkB : iProp :=
  ∃ skB, ⌜pkB = TKey Seal skB⌝ ∗
         (compromised_key skA ∨ compromised_key skB).

Lemma nonce_secrecyE skA skB :
  nonce_secrecy skA (TKey Seal skB) ⊣⊢
  compromised_key skA ∨ compromised_key skB.
Proof.
iSplit.
- iIntros "(%skB' & %e & #comp)". by case: e => <-.
- iIntros "#?". by iExists skB; eauto.
Qed.

(*

A --> B: {m1; nA; pkA}@pkB
B --> A: {m2; nA; nB; pkB}@pkA
A --> B: {m3; nB}@pkB

*)

Definition init : val := λ: "c" "skI" "pkR",
  let: "pkI" := pkey "skI" in
  let: "nI" := mknonce #() in
  let: "m1" := aenc (Tag $ nslN.@"m1") "pkR" (term_of_list ["nI"; "pkI"]) in
  send "c" "m1";;
  bind: "m2"   := adec (Tag $ nslN.@"m2") "skI" (recv "c") in
  bind: "m2"   := list_of_term "m2" in
  list_match: ["nI'"; "nR"; "pkR'"] := "m2" in
  guard: eq_term "nI'" "nI" && eq_term "pkR'" "pkR" in
  let: "m3" := aenc (Tag $ nslN.@"m3") "pkR" "nR" in
  send "c" "m3";;
  let: "sess_key" := derive_key (term_of_list ["pkI"; "pkR"; "nI"; "nR"]) in
  SOME "sess_key".

Definition resp : val := λ: "c" "skR",
  let: "pkR" := pkey "skR" in
  bind: "m1" := adec (Tag $ nslN.@"m1") "skR" (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["nI"; "pkI"] := "m1" in
  let: "nR" := mknonce #() in
  let: "m2" := aenc (Tag $ nslN.@"m2") "pkI" (term_of_list ["nI"; "nR"; "pkR"]) in
  send "c" "m2";;
  bind: "m3" := adec (Tag $ nslN.@"m3") "skR" (recv "c") in
  guard: eq_term "m3" "nR" in
  let: "sess_key" := derive_key (term_of_list ["pkI"; "pkR"; "nI"; "nR"]) in
  SOME ("pkI", "sess_key").

Definition msg1_pred skR m1 : iProp := ∃ nI skI,
  ⌜m1 = Spec.of_list [nI; TKey Seal skI]⌝ ∧
  public (TKey Seal skI) ∧
  (public nI ↔ ▷ (compromised_key skI ∨ compromised_key skR)).

Definition msg2_pred skI m2 : iProp := ∃ nI nR skR,
  let sess_key :=
    Spec.derive_key (Spec.of_list [TKey Seal skI; TKey Seal skR; nI; nR]) in
  ⌜m2 = Spec.of_list [nI; nR; TKey Seal skR]⌝ ∧
  (public nR ↔ ▷ (compromised_key skI ∨ compromised_key skR)) ∧
  term_meta nR (nroot.@"data") (TKey Seal skI).

Definition msg3_pred skR nR : iProp := ∃ skI,
  term_meta nR (nroot.@"data") (TKey Seal skI).

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

Lemma init_send_1 skI pkR nI :
  cryptis_ctx -∗
  nsl_ctx -∗
  aenc_key skI -∗
  public pkR -∗
  minted nI -∗
  □ (public nI ↔ ▷ nonce_secrecy skI pkR) -∗
  public (TSeal pkR (Spec.tag (Tag $ nslN.@"m1") (Spec.of_list [nI; TKey Seal skI]))).
Proof.
iIntros "#? (#? & _ & _) #aencI #p_pkR #m_nI #p_nI".
iPoseProof (aenc_key_public with "aencI") as "?".
iApply public_aencIS => //.
{ rewrite minted_of_list /=. do !iSplit => //. by eauto. }
iIntros "%skR ->"; iSplit.
- rewrite nonce_secrecyE.
  iModIntro. iExists nI, skI. by do !iSplit => //.
- rewrite public_of_list /=. iIntros "!> #compR".
  do 2?iSplit => //. iApply "p_nI".
  by rewrite nonce_secrecyE; eauto.
Qed.

Lemma resp_recv_1_send_2 pkI skR nI nR :
  let sess_key := Spec.derive_key (Spec.of_list [pkI; TKey Seal skR; nI; nR]) in
  public (TSeal (TKey Seal skR)
            (Spec.tag (Tag $ nslN.@"m1")
               (Spec.of_list [nI; pkI]))) -∗
  term_token nR ⊤ -∗
  cryptis_ctx ∗
  nsl_ctx ∗
  aenc_key skR ∗
  minted nR ∗
  □ (public nR ↔ ▷ nonce_secrecy skR pkI) ={⊤}▷=∗
  term_meta nR (nroot.@"data") pkI ∗
  term_token nR (⊤ ∖ ↑nroot.@"data") ∗
  public pkI ∗
  □ (▷ nonce_secrecy skR pkI → public nI) ∗
  public (TSeal pkI
            (Spec.tag (Tag $ nslN.@"m2")
               (Spec.of_list [nI; nR; TKey Seal skR]))).
Proof.
iIntros "%sess_key #p_m1 nR_token".
iIntros "(#? & (#? & #? & _) & #aencR & #m_nR & #p_nR)".
iPoseProof (aenc_key_public with "aencR") as "?".
rewrite (term_token_difference nR (↑nroot.@"data")) //.
iDestruct "nR_token" as "[data nR_token]"; iFrame "nR_token".
iMod (term_meta_set' (N := nroot.@"data") pkI with "data")
       as "[#meta _]"; first solve_ndisj.
set m2 := Spec.of_list [_; _; _].
iAssert (□ ∀ skI, ⌜pkI = TKey Seal skI⌝ → msg2_pred skI m2)%I as "#inv_m2".
{ iIntros "!> %skI ->". iExists nI, nR, skR.
  rewrite nonce_secrecyE bi.or_comm. do !iSplit => //. }
iDestruct (public_TSealE with "p_m1 [//]") as "[[_ fail]|succ]".
- rewrite public_of_list /=. iDestruct "fail" as "(? & ? & _)".
  iIntros "!> !> !>". do !iSplit => //.
  { by iIntros "!> _". }
  iApply public_TSealI => //.
  + by iApply public_minted.
  + rewrite minted_of_list /=.
    by do !iSplit => //; iApply public_minted.
  + iIntros "%skI ->".
    rewrite nonce_secrecyE bi.or_comm. iSplit.
    * iModIntro. by iApply "inv_m2".
    * iIntros "!> #p_dkR". rewrite public_of_list /=.
      do !iSplit => //. iApply "p_nR". iLeft. by iSplit.
- iDestruct "succ" as "(#inv_m1 & m_m1 & _)". iIntros "!> !>".
  iDestruct "inv_m1" as "(%nI' & %skI & %e & p_ekI & s_nI)".
  case/Spec.of_list_inj: e => <- -> {nI' pkI} in sess_key *.
  do 3!iSplitR => //.
  { rewrite !nonce_secrecyE bi.or_comm.
    iIntros "!> !> #fail". by iApply "s_nI". }
  iApply public_TSealIS => //.
  + by iApply public_minted.
  + iModIntro. by iApply "inv_m2".
  + rewrite !minted_of_list /=. iDestruct "m_m1" as "(? & ? & _)".
    by do !iSplit => //; iApply public_minted.
  + iIntros "!> !> #p_dkR". rewrite public_of_list /=.
    do !iSplit => //.
    * iApply "s_nI". rewrite !nonce_secrecyE /compromised_key. by eauto.
    * iApply "p_nR". rewrite !nonce_secrecyE /compromised_key. by eauto.
Qed.

Lemma init_recv_2_send_3 skI pkR nI nR :
  let si := SessInfo nI nR in
  public (TSeal (TKey Seal skI)
            (Spec.tag (Tag $ nslN.@"m2")
               (Spec.of_list [nI; nR; pkR]))) -∗
  term_token nI ⊤ -∗
  cryptis_ctx ∗
  nsl_ctx ∗
  aenc_key skI ∗
  public pkR ∗
  □ (public nI ↔ ▷ nonce_secrecy skI pkR) ={⊤}▷=∗ ∃ skR,
  ⌜pkR = TKey Seal skR⌝ ∗
  minted nR ∗
  public (TSeal pkR (Spec.tag (Tag $ nslN.@"m3") nR)) ∗
  term_token nI (⊤ ∖ ↑nroot.@"data") ∗
  □ (public (si_key skI skR si) ↔
     ▷ (compromised_key skI ∨ compromised_key skR)).
Proof.
iIntros "%si #p_m2 nI_token".
iIntros "(#? & (_ & #? & #?) & #aencI & #p_pkR & #s_nI)".
iPoseProof (aenc_key_public with "aencI") as "?".
rewrite (term_token_difference _ (↑nroot.@"data")) //.
iDestruct "nI_token" as "[_ nI_token]". iFrame "nI_token".
iDestruct (public_TSealE with "p_m2 [//]") as "[fail|succ]".
- rewrite !public_of_list /=.
  iDestruct "fail" as "(_ & p_nI & p_nR & _ & _)".
  iSpecialize ("s_nI" with "p_nI").
  iIntros "!> !> !>".
  iDestruct "s_nI" as "(%skR & -> & #comp)".
  iExists skR. iSplit => //. iSplit; first by iApply public_minted.
  iSplit.
  + iApply public_TSealIP => //. by rewrite public_tag.
  + rewrite public_derive_key public_of_list /=.
    iModIntro. iSplit; by eauto 10.
- iDestruct "succ" as "(#inv_m2 & m_m2 & _)".
  rewrite minted_of_list /=. iDestruct "m_m2" as "(_ & m_nR & _)".
  iIntros "!> !>".
  iDestruct "inv_m2" as "(%nI' & %nR' & %skR & %e & s_nR & meta)".
  case/Spec.of_list_inj: e => {nI' nR' pkR} _ <- ->.
  rewrite nonce_secrecyE.
  iModIntro. iExists skR. iSplit => //. iSplit => //. iSplit.
  { iApply public_aencIS => //.
    iIntros "%skR' %e". case: e => <- {skR'}. iSplit.
    + iIntros "!>". by iExists skI.
    + iIntros "!> #comp". iApply "s_nR". by eauto. }
  rewrite public_derive_key public_of_list /=.
  iModIntro. iSplit.
  + iIntros "(_ & _ & #p_nI & _)". by iApply "s_nI".
  + iIntros "#?". do !iSplit => //.
    * by iApply "s_nI".
    * by iApply "s_nR".
Qed.

Lemma resp_recv_3 pkI skR nI nR :
  let sess_key :=
    Spec.derive_key (Spec.of_list [pkI; TKey Seal skR; nI; nR]) in
  public (TSeal (TKey Seal skR) (Spec.tag (Tag $ nslN.@"m3") nR)) -∗
  cryptis_ctx ∗
  nsl_ctx ∗
  term_meta nR (nroot.@"data") pkI ∗
  public pkI ∗
  aenc_key skR ∗
  □ (▷ nonce_secrecy skR pkI → public nI) ∗
  □ (public nR ↔ ▷ nonce_secrecy skR pkI) ={⊤}▷=∗ ∃ skI,
  ⌜pkI = TKey Seal skI⌝ ∗
  □ (public (si_key skI skR (SessInfo nI nR)) ↔
     ▷ nonce_secrecy skR pkI).
Proof.
iIntros "%sess_key #p_m3".
iIntros "(#? & (_ & _ & #?) & #meta & #p_pkI & #aencR & #s_nI & #s_nR)".
iPoseProof (aenc_key_public with "aencR") as "?".
iDestruct (public_TSealE with "p_m3 [//]") as "{p_m3} [[_ p_nR]|p_m3]".
- iSpecialize ("s_nR" with "p_nR"). iIntros "!> !> !>".
  iDestruct "s_nR" as "(%skI & -> & fail)". iExists skI.
  iSplit => //. rewrite nonce_secrecyE public_derive_key public_of_list /=.
  iModIntro. iSplit.
  + by eauto.
  + iIntros "#comp". do !iSplit => //. by iApply "s_nI".
- iDestruct "p_m3" as "(#inv_m3 & _)". iIntros "!> !> !>".
  iDestruct "inv_m3" as "(%skI & meta')".
  iPoseProof (term_meta_agree with "meta meta'") as "->".
  iExists skI. iSplit => //. iModIntro.
  rewrite public_derive_key public_of_list /=. iSplit.
  + iIntros "(_ & _ & _ & #p_nR & _)". by iApply "s_nR".
  + iIntros "#comp". do !iSplit => //.
    * by iApply "s_nI".
    * by iApply "s_nR".
Qed.

Ltac protocol_failure :=
  by intros; wp_pures; iApply ("Hpost" $! None); iFrame.

Lemma wp_init c skI pkR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  aenc_key skI -∗
  public pkR -∗
  {{{ True }}}
    init c skI pkR
  {{{ sk, RET (repr sk);
      if sk is Some sk then ∃ skR si,
        ⌜sk = si_key skI skR si⌝ ∗
        ⌜pkR = TKey Seal skR⌝ ∗
        minted sk ∗
        term_token (si_init_share si) (⊤ ∖ ↑nroot.@"data") ∗
        □ (public sk ↔ ▷ (compromised_key skI ∨ compromised_key skR))
      else True }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #aencI #p_pkR %Ψ !> _ Hpost".
iPoseProof (aenc_key_public with "aencI") as "?".
rewrite /init. wp_pures. wp_apply wp_pkey. wp_pures.
wp_apply (wp_mknonce (λ _, nonce_secrecy skI pkR)%I (λ _, False)%I) => //.
iIntros "%nI _ #m_nI #p_nI _ token".
rewrite bi.intuitionistic_intuitionistically.
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
iMod "H" as "(%skR & -> & #m_nR & #p_m3 & token & #inv)".
wp_apply wp_aenc. wp_pures. wp_bind (send _ _). iApply wp_send => //.
wp_list. wp_term_of_list. wp_apply wp_derive_key.
set sess_key := Spec.derive_key (Spec.of_list [TKey Seal skI; _; _; _]).
wp_pures.
iApply ("Hpost" $! (Some sess_key)). iModIntro.
iExists skR, (SessInfo nI nR).
rewrite minted_tag minted_of_list /=. do 2!iSplit => //. iFrame.
iSplit => //.
by do !iSplit => //; iApply public_minted.
Qed.

Lemma wp_resp c skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  aenc_key skR -∗
  {{{ True }}}
    resp c skR
  {{{ ts, RET (repr ts);
      if ts is Some (pkI, sk) then ∃ skI si,
        ⌜pkI = TKey Seal skI⌝ ∗
        ⌜sk = si_key skI skR si⌝ ∗
        term_token (si_resp_share si) (⊤ ∖ ↑nroot.@"data") ∗
        □ (public sk ↔ ▷ (compromised_key skI ∨ compromised_key skR))
      else True }}}.
Proof.
iIntros "#chan_c #ctx #ctx' #aencR %Ψ !> _ Hpost".
iPoseProof (aenc_key_public with "aencR") as "?".
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
          (λ _, nonce_secrecy skR pkI)%I
          (λ _, False)%I
          (λ nR, {[nR; Spec.derive_key (Spec.of_list [pkI; TKey Seal skR; nI; nR])]})) => //.
- by iIntros "% %".
- iIntros "%nR".
  rewrite big_sepS_union_pers !big_sepS_singleton minted_tag minted_of_list /=.
  iSplit => //; iModIntro; first by iSplit; iIntros "?".
  iSplit; last by iIntros "(_ & _ & _ & ? & _)".
  iIntros "#m_nR"; do !iSplit => //.
  by iApply public_minted.
iIntros "%nR _ %nonce #m_nR #s_nR _ tokens".
rewrite bi.intuitionistic_intuitionistically.
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
wp_pures. iMod "finished" as "(%skI & -> & #finished)".
wp_list. wp_term_of_list. wp_apply wp_derive_key. wp_pures.
iApply ("Hpost" $! (Some (TKey Seal skI, sess_key))).
iModIntro. iExists skI, (SessInfo nI nR). iFrame.
do !iSplit => //. by rewrite nonce_secrecyE bi.or_comm.
Qed.

Definition check_key_secrecy : val := λ: "c" "sk",
  let: "guess" := recv "c" in
  assert: (~ eq_term "sk" "guess").

Definition do_init_loop : val := rec: "loop" "c" "set" "skI" "pkR" :=
  Fork ("loop" "c" "set" "skI" "pkR");;
  let: "pkR'" := recv "c" in
  (bind: "sk" := init "c" "skI" "pkR'" in
   add_fresh_lock_term_set "sk" "set";;
   if: eq_term "pkR" "pkR'" then check_key_secrecy "c" "sk"
   else #());;
   #().

Definition do_init : val := λ: "c" "skI" "pkR",
  let: "set" := new_lock_term_set #() in
  do_init_loop "c" "set" "skI" "pkR".

Definition si_share_of rl :=
  if rl is Init then si_init_share else si_resp_share.

Definition nsl_game_inv rl sk : iProp := ∃ skI skR si,
  ⌜sk = si_key skI skR si⌝ ∧
  term_meta (si_share_of rl si) (nroot.@"fresh") ().

Lemma nsl_game_inv_fresh skI skR rl si E :
  ↑nroot.@"fresh" ⊆ E →
  term_token (si_share_of rl si) E -∗
  fresh_term (nsl_game_inv rl) (si_key skI skR si).
Proof.
iIntros "%sub token". iSplit.
- iIntros "(%skI' & %skR' & %si' & %e & #meta)".
  case/nsl_session_agree: e => _ _ <-.
  by iApply (term_meta_token with "token meta").
- iMod (term_meta_set (nroot.@"fresh") () with "token") as "#?" => //.
  iIntros "!> !>". iExists skI, skR, si. by eauto.
Qed.

Lemma wp_check_key_secrecy c k :
  channel c -∗
  cryptis_ctx -∗
  □ (public k → ▷^2 False) -∗
  {{{ True }}}
    check_key_secrecy c k
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #s_k %Φ !> _ post".
wp_lam. wp_pures. wp_apply wp_recv => //. iIntros "%guess #p_guess".
wp_pures. wp_apply wp_assert.
wp_eq_term e.
- rewrite -e. iPoseProof ("s_k" with "p_guess") as "contra".
  wp_pures. by iDestruct "contra" as ">[]".
- wp_pures. iModIntro. iSplit => //. by iApply "post".
Qed.

Lemma wp_do_init_loop c vset skI skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  aenc_key skI -∗
  □ (compromised_key skI → ▷ False) -∗
  □ (compromised_key skR → ▷ False) -∗
  is_lock_term_set (nsl_game_inv Init) vset -∗
  {{{ True }}}
    do_init_loop c vset skI (TKey Seal skR)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #aencI #s_skI #s_skR #set".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ by iApply "IH" => //. }
wp_pures. wp_apply wp_recv => //.
iIntros (pkR') "#p_pkR'".
wp_pures. wp_apply wp_init => //. iIntros "%ts tsP".
case: ts=> [sk|] => /=; wp_pures; last by iApply "Hpost".
iDestruct "tsP" as "(%skR' & %si & -> & -> & _ & token & #s_sk)".
iPoseProof (@nsl_game_inv_fresh skI skR' Init with "token")
  as "fresh" => //; try solve_ndisj.
wp_apply (wp_add_fresh_lock_term_set with "[$]"). iIntros "_".
wp_eq_term e; wp_pures; last by iApply "Hpost".
case: e => <- {skR'}.
wp_apply wp_check_key_secrecy => //.
{ iIntros "!> #fail".
  iPoseProof ("s_sk" with "fail") as "{fail} fail".
  iModIntro. by iDestruct "fail" as "[fail|fail]";
  [iApply "s_skI"|iApply "s_skR"]. }
iIntros "_". wp_pures. by iApply "Hpost".
Qed.

Lemma wp_do_init c skI skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  aenc_key skI -∗
  □ (compromised_key skI → ▷ False) -∗
  □ (compromised_key skR → ▷ False) -∗
  {{{ True }}}
    do_init c skI (TKey Seal skR)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #aencI #s_skI #s_skR %Φ _ !> post".
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
   if: eq_term "pkI" "pkI'" then check_key_secrecy "c" "sk"
   else #());;
  #().

Definition do_resp : val := λ: "c" "skR" "pkI",
  let: "set" := new_lock_term_set #() in
  do_resp_loop "c" "set" "skR" "pkI".

Lemma wp_do_resp_loop c set skI skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  aenc_key skR -∗
  □ (compromised_key skR → ▷ False) -∗
  □ (compromised_key skI → ▷ False) -∗
  is_lock_term_set (nsl_game_inv Resp) set -∗
  {{{ True }}}
    do_resp_loop c set skR (TKey Seal skI)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #aencR #s_skR #s_skI #set".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ iApply "IH" => //. }
wp_pures. wp_apply wp_resp => //.
iIntros "%res res".
case: res => [[ekI' sk]|]; wp_pures; last by iApply "Hpost".
iDestruct "res" as "(%skI' & %si & -> & -> & token & #res)".
iPoseProof (@nsl_game_inv_fresh skI' skR Resp with "token")
  as "fresh" => //; try solve_ndisj.
wp_apply (wp_add_fresh_lock_term_set with "[$]"). iIntros "_".
wp_eq_term e; wp_pures; last by iApply "Hpost".
case: e => <- {skI'}.
wp_apply wp_check_key_secrecy => //.
{ iIntros "!> #fail".
  iPoseProof ("res" with "fail") as "{fail} fail".
  iModIntro. by iDestruct "fail" as "[fail|fail]";
  [iApply "s_skI"|iApply "s_skR"]. }
iIntros "_". wp_pures. by iApply "Hpost".
Qed.

Lemma wp_do_resp c skI skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  aenc_key skR -∗
  □ (compromised_key skR → ▷ False) -∗
  □ (compromised_key skI → ▷ False) -∗
  {{{ True }}}
    do_resp c skR (TKey Seal skI)
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #? #? #? #? %Φ _ !> post".
wp_lam. wp_pures.
wp_apply (wp_new_lock_term_set (nsl_game_inv Resp)) => //.
iIntros "%set #set". wp_pures.
by wp_apply wp_do_resp_loop => //.
Qed.

Definition game : val := λ: <>,
  let: "c"   := init_network #() in
  let: "skI" := mkakey #() in
  let: "skR" := mkakey #() in
  let: "pkI" := pkey "skI" in
  let: "pkR" := pkey "skR" in
  send "c" "pkI";;
  send "c" "pkR";;
  Fork (do_init "c" "skI" "pkR");;
  Fork (do_resp "c" "skR" "pkI").

Lemma wp_game :
  cryptis_ctx -∗
  seal_pred_token ⊤ -∗
  key_pred_token (⊤ ∖ ↑nroot.@"keys") -∗
  WP game #() {{ _, True }}.
Proof.
iIntros "#ctx enc_tok key_tok"; rewrite /game; wp_pures.
wp_apply wp_init_network => //. iIntros "%c #cP".
wp_pures. wp_apply (wp_mkakey with "[]"); eauto.
iIntros "%skI #p_pkI #aencI secI tokenI".
wp_pures. wp_apply (wp_mkakey with "[]"); eauto.
iIntros "%skR #p_pkR #aencR secR tokenR".
wp_pures. wp_apply wp_pkey. wp_pures. wp_apply wp_pkey. wp_pures.
set pkI := TKey Seal skI.
set pkR := TKey Seal skR.
iMod (aenc_freeze_secret with "secI [//]") as "#?".
iMod (aenc_freeze_secret with "secR [//]") as "#?".
wp_pures; wp_bind (send _ _); iApply wp_send => //.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
wp_pures.
iMod (nsl_alloc with "enc_tok") as "[#nsl_ctx _]" => //.
wp_apply wp_fork.
{ wp_apply wp_do_init => //. }
wp_pures. wp_apply wp_fork => //.
wp_apply wp_do_resp => //.
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
by iApply (wp_game with "ctx [enc_tok] [key_tok]").
Qed.
