From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import numbers.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis.primitives Require Import attacker.

(* This example demonstrates a simple use of digital signatures to guarantee
integrity properties: a server uses a signature to inform the client that some
part of its state will never change.  *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Monotone counter *)
Class mcounterG Σ := MCounterG { mcounter_inG : inG Σ (authR max_natUR) }.
Local Existing Instance mcounter_inG.

Definition mcounterΣ : gFunctors := #[GFunctor (authR max_natUR)].

Global Instance subG_mcounterΣ {Σ} : subG mcounterΣ Σ → mcounterG Σ.
Proof. solve_inG. Qed.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !mcounterG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (γ : gname) (l : loc) (k t : term).

Definition newcounter : val := λ: <>, ref #0.
Definition incr : val := rec: "incr" "l" :=
    let: "n" := !"l" in
    if: CAS "l" "n" (#1 + "n") then #() else "incr" "l".
Definition read : val := λ: "l", !"l".

Definition server : val := rec: "loop" "c" "l" "sk" :=
  (* Receive request from the network *)
  let: "m" := recv "c" in
  if: eq_term "m" (tint #0) then
    (* Increment local state *)
    incr "l"
  else (
    (* Retrieve value *)
    let: "reply" := sign nroot "sk" (tint (! "l")) in
    send "c" "reply"
  ) ;;
  "loop" "c" "l" "sk".

Definition client : val := λ: "c" "vk",
  do_until (λ: <>,
    (* Send out request *)
    let: "request" := (tint #1) in
    send "c" "request" ;;
    (* Wait for response *)
    let: "reply" := recv "c" in
    (* Check signature *)
    bind: "value" := verify nroot "vk" "reply" in
    to_int "value"
  ).

Definition sig_pred γ k t : iProp :=
  ∃ n : nat, ⌜t = TInt n⌝ ∗ own γ (◯ MaxNat n).

Definition server_inv γ l : iProp :=
  inv nroot (∃ n : nat, l ↦ #n ∗ own γ (● MaxNat n) ∗ own γ (◯ MaxNat n)).

Lemma wp_newcounter φ :
  seal_pred_token ⊤ -∗
  (∀ γ l, seal_pred nroot (sig_pred γ) -∗ server_inv γ l -∗ φ #l) -∗
  WP newcounter #() {{ v, φ v }}.
Proof.
iIntros "tok post". rewrite /newcounter. wp_pures.
wp_alloc l as "Hl".
iMod (own_alloc (● MaxNat 0 ⋅ ◯ MaxNat 0)) as "(%γ & own & #ownf)".
{ by apply auth_both_valid. }
iMod (seal_pred_set nroot (sig_pred γ) with "tok") as "[#pred _]" => //.
iMod (inv_alloc nroot _
  (∃ n : nat, l ↦ #n ∗ own γ (● MaxNat n) ∗ own γ (◯ MaxNat n))
  with "[Hl own]") as "#inv".
{ iModIntro. iExists 0. by iFrame. }
iModIntro. by iApply "post".
Qed.

Lemma wp_incr γ l :
  server_inv γ l -∗
  WP incr #l {{ _, True }}.
Proof.
iIntros "#inv". iLöb as "IH". wp_rec.
wp_bind (! _)%E. iInv "inv" as (n) ">(Hl & Hγ & #Hγf1)".
wp_load. iModIntro. iSplitL "Hl Hγ"; [iNext; iExists n; by iFrame|].
wp_pures. wp_bind (CmpXchg _ _ _).
iInv "inv" as (n') ">(Hl & Hγ & #Hγf2)".
destruct (decide (n' = n)) as [->|].
- iDestruct (own_valid_2 with "Hγ Hγf2")
    as %[?%max_nat_included _]%auth_both_valid_discrete.
  iMod (own_update_2 with "Hγ Hγf2") as "[Hγ Hγf3]".
  { apply auth_update, (max_nat_local_update _ _ (MaxNat (S n))). simpl. auto. }
  wp_cmpxchg_suc. iPoseProof "Hγf3" as "#Hγf3". iModIntro. iSplitL "Hl Hγ".
  { iNext. iExists (S n). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
  wp_pures. eauto.
- wp_cmpxchg_fail; first (by intros [= ?%Nat2Z.inj]). iModIntro.
  iSplitL "Hl Hγ"; [iNext; iExists n'; by iFrame|].
  wp_pures. iApply "IH".
Qed.

Lemma wp_server c γ l k t :
  cryptis_ctx -∗
  channel c -∗
  seal_pred nroot (sig_pred γ) -∗
  minted (TKey Seal k) -∗
  server_inv γ l -∗
  public t -∗
  WP server c #l k {{ _, True }}.
Proof.
iIntros "#ctx #chan_c #sig_pred #s_sk #inv #p_t".
(* Unfold the definition of the server *)
iLöb as "IH". wp_rec. wp_pures.
(* Receive request from the network *)
wp_bind (recv _). iApply wp_recv => //. iIntros "%request _". wp_pures.
(* Check request *)
wp_bind (tint _). iApply wp_tint. wp_eq_term e.
{ (* Increment *)
  wp_pures. iApply wp_incr. by eauto. }
(* Read contents *)
wp_pures. wp_bind (! _)%E.
iInv "inv" as ">(%n & Hl & own & #ownf)". wp_load.
iModIntro. iSplitL "Hl own"; first by iExists n; iFrame.
wp_bind (tint _). iApply wp_tint. wp_apply wp_sign. wp_pures.
wp_bind (send _ _). iApply wp_send => //.
{ iApply public_TSealIS => //.
  - iModIntro. iExists n. by eauto.
  - by rewrite minted_TInt.
  - iIntros "!> !> _". by rewrite public_TInt. }
(* Loop *)
wp_pures. iApply "IH".
Qed.

Lemma wp_client T n c γ l k φ :
  TKey Seal k ∈ T →
  cryptis_ctx -∗
  channel c -∗
  seal_pred nroot (sig_pred γ) -∗
  public (TKey Open k) -∗
  honest n T -∗
  ●Ph□ n -∗
  (∀ n : nat, own γ (◯ MaxNat n) -∗ φ #n) -∗
  WP client c (TKey Open k) {{ v, φ v }}.
Proof.
iIntros "%hon_sk #ctx #chan_c #sig_pred #p_vk #hon #phase post".
(* Unfold definition of client *)
rewrite /client. wp_pures.
iRevert "post". iApply wp_do_until. iIntros "!> post". wp_pures.
(* Construct request *)
wp_bind (tint _). iApply wp_tint.  wp_pures.
(* Send message. Prove it is well formed. *)
wp_bind (send _ _). iApply wp_send => //.
{ by rewrite public_TInt. }
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
iDestruct "replyP" as (n') ">[-> #ownf]".
wp_pures. iApply wp_to_int.
iRight. iExists #n'. iSplit => //. by iApply "post".
Qed.

(* Security game: ensure that the response that the client gets matches the
state of the server. *)

Definition game : val := λ: <>,
  (* Initialize attacker (network) *)
  let: "c"   := init_network #() in

  (* Generate signature keys and publicize verification key *)
  let: "k"   := mksigkey #() in
  let: "vk"  := vkey "k" in
  send "c" "vk" ;;

  (* Initialize server state *)
  let: "l" := newcounter #() in

  (* Run server *)
  Fork (server "c" "l" "k");;

  (* Run client *)
  let: "n'" := client "c" "vk" in

  (* Check if client's value agrees with the server state *)
  ("n'" ≤ !"l").

Lemma wp_game :
  cryptis_ctx ∗
  seal_pred_token ⊤ ∗
  honest 0 ∅ ∗
  ●Ph 0 -∗
  WP game #() {{ v, ⌜v = #true⌝ }}.
Proof.
iIntros "(#ctx & seal_tok & #hon & phase)".
rewrite /game. wp_pures.
(* Setup attacker *)
wp_apply wp_init_network => //. iIntros "%c #cP". wp_pures.
(* Generate server key. Keep the signing key secret. *)
wp_bind (mksigkey _). iApply (wp_mksigkey_phase with "[//] hon phase") => //.
iIntros (k) "#p_vk #hon' phase". wp_pures.
wp_apply wp_vkey. wp_pures.
iMod (phase_auth_discard with "phase") as "#phase".
(* Publicize verification key. *)
wp_pures. wp_bind (send _ _). iApply wp_send => //. wp_pures.
wp_bind (newcounter _). iApply (wp_newcounter with "seal_tok").
iIntros "%γ %l #? #inv".
(* Run server in a loop in parallel. *)
wp_pures. wp_bind (Fork _). iApply wp_fork.
{ iApply wp_server => //.
  iPoseProof (public_minted with "p_vk") as "s_vk".
  by rewrite !minted_TKey. }
iModIntro.
(* Let client contact server *)
wp_pures. wp_bind (client _ _). iApply wp_client => //.
{ set_solver. }
iIntros (n') "#ownf".
(* Now the client knows a lower bound of which value is stored in the server. *)
wp_pures.
wp_bind (! _)%E.
iInv "inv" as ">(%n & Hl & own & #?)".
iDestruct (own_valid_2 with "own ownf")
  as %[?%max_nat_included _]%auth_both_valid_discrete.
wp_load. iModIntro. iSplitL "Hl own".
{ iExists n. iFrame; eauto. }
wp_pures. rewrite bool_decide_true //. simpl in H. lia.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; mcounterΣ].

(* The same result, but without using the Cryptis logic. *)
Lemma game_secure σ₁ σ₂ (v : val) ts :
  rtc erased_step ([game #()], σ₁) (Val v :: ts, σ₂) →
  v = #true.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_result NotStuck _ _ (λ v _, v = #true)).
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisGS_alloc _) as (?) "(#ctx & seal_tok & key_tok & hash_tok & hon)".
by iApply (wp_game) => //; try by iFrame.
Qed.
