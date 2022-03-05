From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term cryptis primitives tactics role nown.
From cryptis Require Import pk_auth.
From cryptis Require Import session.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NSL.

Context `{heap : !heapGS Σ, cryptis : !cryptisG Σ, sess : !session.sessionG Σ}.
Notation iProp := (iProp Σ).
Implicit Types t kI kR nI nR : term.

Variable N : namespace.

Definition nsl_gen_keys : val := λ: <>,
  let: "n" := mknonce #() in
  ("n", "n").

Definition nsl_mk_sess_key : val := λ: "nI" <>, "nI".

Definition nsl_init : expr :=
  pk_auth_init N nsl_gen_keys nsl_mk_sess_key.

Definition nsl_resp : expr :=
  pk_auth_resp N nsl_gen_keys nsl_mk_sess_key.

Definition nsl_ctx : iProp :=
  session.session_ctx (@nonce_meta _ _) N
    (λ rl nI nR (_ : term * term), True)%I.

Definition nsl_resp_accepted kI kR sI sR : iProp :=
  session.session (@nonce_meta _ heap) N Resp sI sR (kI, kR).

Definition nsl_init_finished sR : iProp := □ ∀ kI kR sI,
  session.session (@nonce_meta _ _) N Resp sI sR (kI, kR) →
  secret_of sI kI kR ∧
  session.session (@nonce_meta _ _) N Init sI sR (kI, kR).

Program Instance PK_NSL : PK N := {
  inv := nsl_ctx;

  init_waiting kI kR nI sI := (
    ⌜sI = nI⌝ ∧ nonce_meta_token nI (↑N)
  )%I;

  resp_accepted := nsl_resp_accepted;

  resp_waiting kI kR sI nR sR := (
    ⌜sR = nR⌝ ∧
    waiting_for_peer (@nonce_meta _ heap)
                     N (λ _ _ _ _, True)%I Resp sI nR (kI, kR)
  )%I;

  init_finished := nsl_init_finished;

  session rl kI kR kS := True%I;

  init_gen_keys := nsl_gen_keys;
  init_mk_sess_key := nsl_mk_sess_key;
  resp_gen_keys := nsl_gen_keys;
  resp_mk_sess_key := nsl_mk_sess_key;
  
}.

Next Obligation.
iIntros "%E %kI %kR % #? !> %Ψ _ post". rewrite /nsl_gen_keys.
wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce _ (λ _, corruption kI kR) (λ _, True)%I).
iIntros "%nI #s_nI #p_nI _ token".
rewrite (term_meta_token_difference _ (↑N)) //.
iDestruct "token" as "[token _]".
wp_pures. iModIntro. iApply "post". do !iSplit; eauto.
by rewrite /secret_of bi.intuitionistic_intuitionistically.
Qed.

Next Obligation.
iIntros "%E %kI %kR %nI %sI %sR % #ctx #s_nI _ #p_nI #s_sR #p_sR".
iIntros "[#fail|#sessR] %Ψ !> (-> & token) post".
  rewrite /nsl_mk_sess_key. wp_pures. iModIntro. iApply "post".
  by do !iSplit; eauto.
iMod (session_begin _ Init _ sR (kI, kR) with "ctx [//] token")
  as "[#sessI end]" => //.
(* This condition should be more interesting eventually *)
iMod ("end" with "[//] sessR") as "end".
rewrite /nsl_mk_sess_key. wp_pures. iModIntro. iApply "post".
do !iSplit; eauto. iRight.
iIntros "!> %kI' %kR' %nI' #sessR'".
iPoseProof (session_agree with "sessR' sessR") as "%e" => //.
case: e => -> -> ->. by eauto.
Qed.

Next Obligation.
iIntros "%E %kI %kR %nI % #ctx #s_nI _ !> %Ψ _ post".
rewrite /nsl_gen_keys. wp_pures. wp_bind (mknonce _).
iApply (wp_mknonce _ (λ _, corruption kI kR) (λ _, True)%I).
iIntros "%nR #s_nR #p_nR _ token".
rewrite bi.intuitionistic_intuitionistically.
rewrite (term_meta_token_difference _ (↑N)) //.
iDestruct "token" as "[token _]". wp_pures.
iApply "post".
iMod (session_begin _ Resp nI nR (kI, kR) with "ctx [//] token")
  as "[#sessR waiting]" => //.
by iModIntro; do 5!iSplit => //.
Qed.

Next Obligation.
iIntros "%E %kI %kR %sI %nR %sR % #ctx #s_sI #p_sI #s_nR #s_sR #p_sR".
iIntros "#accepted #finishedI !> %Ψ [-> waiting] post".
rewrite /nsl_mk_sess_key. wp_pures.
iDestruct "finishedI" as "[fail|#finishedI]".
  iModIntro. iApply "post". do!iSplit; eauto.
  iModIntro. iSplit; eauto.
  iIntros "_". by iApply "p_sI".
iPoseProof ("finishedI" with "accepted") as "{p_sI} [p_sI finished]".
(* This step should be more interesting eventually *)
iMod ("waiting" with "[//] finished") as "finishedR".
iModIntro. iApply "post". by eauto.
Qed.

End NSL.
