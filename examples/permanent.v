From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import numbers.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.

(* This example demonstrates a simple use of digital signatures to guarantee
integrity properties: a server uses a signature to inform the client that some
part of its state will never change.  *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (l : loc) (k t : term).

Definition server : val := rec: "loop" "c" "l" "sk" :=
  (* Receive request from the network *)
  let: <> := recv "c" in
  (* Sign message *)
  let: "reply" := sign nroot "sk" (! "l") in
  send "c" "reply";;
  "loop" "c" "l" "sk".

Definition client : val := λ: "c" "vk",
  do_until (λ: <>,
    (* Send out request *)
    let: "request" := tag (nroot.@"get") (tint #0) in
    send "c" "request" ;;
    (* Wait for response *)
    let: "reply" := recv "c" in
    (* Check signature *)
    bind: "value" := verify nroot "vk" "reply" in
    SOME "value"
  ).

Definition sig_pred l k t : iProp :=
  l ↦□ (t : val).

Lemma wp_server c l k t :
  cryptis_ctx -∗
  channel c -∗
  seal_pred nroot (sig_pred l) -∗
  minted (TKey Seal k) -∗
  l ↦□ (t : val) -∗
  public t -∗
  WP server c #l k {{ _, True }}.
Proof.
iIntros "#ctx #chan_c #sig_pred #s_sk #Hl #p_t".
(* Unfold the definition of the server *)
iLöb as "IH". wp_rec. wp_pures.
(* Receive request from the network *)
wp_bind (recv _). iApply wp_recv => //. iIntros "%request _". wp_pures.
(* Load contents and sign message *)
wp_load. wp_apply wp_sign. wp_pures.
(* Send message. Prove that it is well formed. *)
wp_bind (send _ _). iApply wp_send => //.
{ iModIntro. by iApply public_TSealIS; eauto. }
(* Loop *)
by wp_pures.
Qed.

Lemma wp_client T n c l k φ :
  TKey Seal k ∈ T →
  cryptis_ctx -∗
  channel c -∗
  seal_pred nroot (sig_pred l) -∗
  public (TKey Open k) -∗
  honest n T -∗
  ●Ph□ n -∗
  (∀ t : term, l ↦□ (t : val) -∗ φ (t : val)) -∗
  WP client c (TKey Open k) {{ v, φ v }}.
Proof.
iIntros "%hon_sk #ctx #chan_c #sig_pred #p_vk #hon #phase post".
(* Unfold definition of client *)
rewrite /client. wp_pures.
iRevert "post". iApply wp_do_until. iIntros "!> post". wp_pures.
(* Construct request *)
wp_bind (tint _). iApply wp_tint. wp_tag. wp_pures.
(* Send message. Prove it is well formed. *)
wp_bind (send _ _). iApply wp_send => //.
{ by rewrite public_tag public_TInt. }
(* Wait for response. *)
wp_pures. wp_bind (recv _). iApply wp_recv => //.
iIntros "%reply #p_reply". wp_pures.
(* Verify the signature *)
wp_verify reply; last by wp_pures; eauto.
iPoseProof (public_TSealE with "p_reply sig_pred")
  as "[[#p_sk _]|(#replyP & #s_reply & _)]".
{ (* The signature could have been forged if the key was compromised, but we
     have ruled out this possibility.  *)
  iPoseProof (secret_atI _ hon_sk with "hon") as "#sec".
  iMod (honest_public with "[] sec phase p_sk") as "#contra" => //; eauto.
  wp_pures. by iDestruct "contra" as ">[]". }
(* Therefore, the invariant must hold. *)
wp_pures. iModIntro. iRight. iExists reply. iSplit => //.
by iApply "post".
Qed.

(* Security game: ensure that the response that the client gets matches the
state of the server. *)

Definition game : val := λ: "mkchan",
  (* Initialize attacker (network) *)
  let: "c"   := "mkchan" #() in

  (* Generate signature keys and publicize verification key *)
  let: "k"   := mksigkey #() in
  let: "vk"  := vkey "k" in
  send "c" "vk" ;;

  (* Initialize server state *)
  let: "t" := recv "c" in
  let: "l" := ref "t" in

  (* Run server *)
  Fork (server "c" "l" "k");;

  (* Run client *)
  let: "t'" := client "c" "vk" in

  (* Check if client's value agrees with the server state *)
  eq_term (!"l") "t'".

Lemma wp_game (mkchan : val) :
  {{{ True }}} mkchan #() {{{ v, RET v; channel v }}} -∗
  cryptis_ctx ∗
  seal_pred_token ⊤ ∗
  honest 0 ∅ ∗
  ●Ph 0 -∗
  WP game mkchan {{ v, ⌜v = #true⌝ }}.
Proof.
iIntros "#wp_mkchan (#ctx & enc_tok & #hon & phase)".
rewrite /game. wp_pures.
(* Setup attacker *)
wp_bind (mkchan _); iApply "wp_mkchan" => //.
iIntros "!> %c #cP". wp_pures.
(* Generate server key. Keep the signing key secret. *)
wp_bind (mksigkey _). iApply (wp_mksigkey_phase with "[//] hon phase") => //.
iIntros (k) "#p_vk #hon' phase".
wp_pures.
wp_apply wp_vkey. wp_pures.
iMod (phase_auth_discard with "phase") as "#phase".
(* Publicize verification key. *)
wp_pures. wp_bind (send _ _). iApply wp_send => //. wp_pures.
(* Attacker chooses value stored by the server. *)
wp_bind (recv _). iApply wp_recv => //. iIntros "%t #p_t". wp_pures.
wp_alloc l as "Hl".
(* Promise that the stored value will not change. *)
iMod (pointsto_persist with "Hl") as "#Hl".
(* Initialize signature invariant *)
iMod (seal_pred_set nroot (sig_pred l) with "enc_tok") as "[#? _]" => //.
(* Run server in a loop in parallel. *)
wp_pures. wp_bind (Fork _). iApply wp_fork.
{ iApply wp_server => //.
  iPoseProof (public_minted with "p_vk") as "s_vk".
  by rewrite !minted_TKey. }
iModIntro.
(* Let client contact server *)
wp_pures. wp_bind (client _ _). iApply wp_client => //.
{ set_solver. }
iIntros (t') "#Hl'".
(* Now the client knows which value is stored in the server. *)
iPoseProof (pointsto_agree with "Hl' Hl") as "->". wp_pures. wp_load.
iApply wp_eq_term. by rewrite bool_decide_true.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ].

(* The same result, but without using the Cryptis logic. *)
Lemma game_secure (mkchan : val) σ₁ σ₂ (v : val) ts :
  (∀ `{!heapGS Σ, !cryptisGS Σ},
     ⊢ {{{ True }}} mkchan #() {{{ c, RET c; channel c}}}) →
  rtc erased_step ([game mkchan], σ₁) (Val v :: ts, σ₂) →
  v = #true.
Proof.
have ? : heapGpreS F by apply _.
move=> wp_mkchan.
apply (adequate_result NotStuck _ _ (λ v _, v = #true)).
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisGS_alloc _) as (?) "(#ctx & enc_tok & key_tok & hash_tok & hon)".
iApply (wp_game) => //; try by iFrame.
iApply wp_mkchan.
Qed.
