From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import numbers reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par assert ticket_lock.
From cryptis Require Import lib cryptis primitives tactics role adequacy.
From cryptis.examples Require Import hmqv.
From cryptis.lib Require Import term_set hmqv.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Existing Instance ticket_lock.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !tlockG Σ, !hmqvGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types (p_a p_b : nonce).
Implicit Types rl : role.

Definition gameN := nroot.@"game".

Definition compromise_long_term_keys : val :=
  λ: "c" "compromised" "p_a" "p_b",
    "compromised" <- #true;;
    send "c" "p_a";;
    send "c" "p_b".

Definition wait_for_compromise : val :=
  rec: "loop" "compromised" :=
    if: !"compromised" then #()
    else "loop" "compromised".

(* The attacker picks, when the game starts, which keys it may learn: with
   [leak_eph], every ephemeral is sent to it after its session and the
   long-term keys never leak; otherwise the long-term keys leak when it asks
   and the ephemerals never do.  The key must stay unguessable either way. *)
Definition check_key_secrecy : val :=
  λ: "c" "leak_eph" "compromised" "sk",
    if: "leak_eph" then
      let: "guess" := recv "c" in
      assert: (~ eq_term "sk" "guess")
    else if: ~ !"compromised" then
      wait_for_compromise "compromised";;
      let: "guess" := recv "c" in
      assert: (~ eq_term "sk" "guess")
    else #().
Definition game_inv lcomp p_a p_b : iProp :=
  ∃ compromised : bool,
    lcomp ↦ #compromised ∗
    if compromised then public p_a ∗ public p_b
    else secret p_a ∗ secret p_b.

Lemma wp_compromise_long_term_keys c lcomp p_a p_b :
  {{{ cryptis_ctx ∗
      channel c ∗
      inv gameN (game_inv lcomp p_a p_b) }}}
    compromise_long_term_keys c #lcomp p_a p_b
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ (#? & #? & #?) post".
wp_lam. wp_pure _ credit:"c1". wp_pures.
wp_bind (_ <- _)%E. iInv gameN as "(%bcomp & >lcomp & inv)". wp_store.
iAssert (|==> (public p_a ∗ public p_b))%I
  with "[inv]" as ">#[p_pa p_pb]".
{ case: bcomp => //.
  iDestruct "inv" as "[s_pa s_pb]".
  iMod (secret_public with "s_pa") as "#?".
  iMod (secret_public with "s_pb") as "#?".
  by eauto. }
iModIntro. iSplitL "lcomp"; first by iFrame; eauto.
wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_send => //.
by iApply "post".
Qed.

Lemma wp_wait_for_compromise lcomp p_a p_b :
  {{{ cryptis_ctx ∗
      inv gameN (game_inv lcomp p_a p_b) }}}
    wait_for_compromise #lcomp
  {{{ RET #(); public p_a ∗ public p_b }}}.
Proof.
iLöb as "IH". iIntros "%Φ (#? & #?) post".
wp_rec. wp_bind (!_)%E. iInv gameN as "(%bcomp & lcomp & inv)".
wp_load. iModIntro.
iAssert (□ if bcomp then public p_a ∗ public p_b
           else True)%I as "#?".
{ case: bcomp => //. iPoseProof "inv" as "#inv". by eauto. }
 iSplitL "lcomp inv"; first by iFrame.
case: bcomp; wp_pures; first by iApply "post".
by wp_apply "IH"; eauto.
Qed.

(* The mode the game runs in, recorded on the initiator's public key. *)
Definition mode p_a (leak_eph : bool) : iProp :=
  term_meta (TExp g p_a) (gameN.@"mode") leak_eph.

(* What a party receives from its peer: nothing when ephemerals leak,
   otherwise the promise that the peer's ephemeral stays secret. *)
Definition game_pred p_a p_b si rl : iProp :=
  mode p_a true ∨ exp_frozen g (si_share_of (swap_role rl) si).

(* What a party keeps of its own ephemeral: the secret, to leak it later, or
   the promise that it stays secret. *)
Definition keep (leak_eph : bool) (x : nonce) : iProp :=
  (if leak_eph then secret x else □ (public x ↔ ▷ False))%I.

Definition key_secrecy (leak_eph : bool) lcomp p_a p_b : iProp :=
  (if leak_eph then □ (public p_a ↔ ▷ False) ∗ □ (public p_b ↔ ▷ False)
   else inv gameN (game_inv lcomp p_a p_b))%I.


#[global] Instance key_secrecy_persistent leak_eph lcomp p_a p_b :
  Persistent (key_secrecy leak_eph lcomp p_a p_b).
Proof. by case: leak_eph; apply _. Qed.

Lemma wp_check_key_secrecy leak_eph c lcomp p_a p_b rl si :
  {{{ cryptis_ctx ∗
      channel c ∗
      mode p_a leak_eph ∗
      key_secrecy leak_eph lcomp p_a p_b ∗
      session rl p_a p_b si ∗
      □ (¬ released_session si) ∗
      (if leak_eph then True
       else exp_frozen g (si_share_of rl si) ∗
            (public (si_key si) ∨ game_pred p_a p_b si rl)) }}}
    check_key_secrecy c #leak_eph #lcomp (si_key si)
  {{{ RET #(); True }}}.
Proof.
iIntros "%Φ (#? & #? & #mode & #ks & #s_sk & #un & frozen) post".
rewrite /check_key_secrecy. wp_pures.
case: leak_eph.
{ iDestruct "ks" as "[s_pa s_pb]".

  iAssert (□ (public (si_key si) → ▷ False))%I as "#sec".
  { iIntros "!> #p_k".
    iDestruct "s_sk" as "(%e1 & %e2 & _ & _ & [#comp|#s_k])".
    - iDestruct (compromised_static with "comp") as "[c|c]".
      + iEval (rewrite -e1) in "c". by iApply "s_pa".
      + iEval (rewrite -e2) in "c". by iApply "s_pb".
    - iDestruct ("s_k" with "p_k") as "[#rel|[[#c _]|[#c _]]]".
      + iNext. by iApply "un".
      + iEval (rewrite -e1) in "c". by iApply "s_pa".
      + iEval (rewrite -e2) in "c". by iApply "s_pb". }

  wp_pures. wp_apply wp_recv => //.
  iIntros "%guess #p_guess". wp_pures.
  wp_apply wp_assert. wp_eq_term e.
  { subst guess. iDestruct ("sec" with "p_guess") as ">[]". }
  wp_pures. iModIntro. iSplit => //. by iApply "post". }
iDestruct "frozen" as "[#frozen_own gift]".
iPoseProof "s_sk" as "(%e1 & %e2 & _)".
wp_pures. wp_bind (!_)%E.

iInv gameN as "(%bcomp & >Hcomp & inv)".
wp_load. case: bcomp.
{ iModIntro. iSplitR "post"; first by iExists true; eauto.
  wp_pures. by iApply "post". }
iDestruct "inv" as "[s_pa s_pb]".
iAssert (|={⊤ ∖ ↑gameN}=> secret p_a ∗ secret p_b ∗
                          □ (public (si_key si) → ▷ False))%I
  with "[s_pa s_pb gift]" as "{s_sk} >(s_pa & s_pb & #s_sk)".
{ iPoseProof (secret_session with "s_pa s_pb [//]")
    as "{s_sk} #>#s_sk".
  iDestruct "gift" as "[#p_k|[#m|#frozen_peer]]".
  - iDestruct ("s_sk" with "p_k") as "[#rel|[[#c _]|[#c _]]]".
    + iAssert (▷ False)%I as ">[]". iNext. by iApply "un".
    + iEval (rewrite -e1) in "c".
      by iDestruct (secret_not_public with "s_pa c") as ">[]".
    + iEval (rewrite -e2) in "c".
      by iDestruct (secret_not_public with "s_pb c") as ">[]".

  - by iPoseProof (term_meta_agree with "mode m") as "%".
  - iAssert (exp_frozen g (si_init_share si) ∗
             exp_frozen g (si_resp_share si))%I as "#[frozen_a frozen_b]".
    { case: rl; by iSplit. }
    iFrame. iIntros "!>".
    by iApply (frozen_key_secrecy with "un frozen_a frozen_b s_sk"). }

iModIntro. iSplitR "post".
{ iExists false; iFrame. }
wp_pures. wp_apply wp_wait_for_compromise; eauto.
iIntros "#[p_pa p_pb]". wp_pures. wp_apply wp_recv => //.
iIntros "%guess #p_guess". wp_pures.
wp_apply wp_assert. wp_eq_term e.
{ subst guess. iDestruct ("s_sk" with "p_guess") as ">[]". }
wp_pures. iModIntro. iSplit => //. by iApply "post".
Qed.

Definition leak_ephemeral : val := λ: "c" "leak_eph" "x",
  if: "leak_eph" then send "c" "x" else #().

Lemma wp_leak_ephemeral leak_eph c (x : nonce) :
  {{{ cryptis_ctx ∗ channel c ∗ keep leak_eph x }}}
    leak_ephemeral c #leak_eph x
  {{{ RET #(); if leak_eph then True else exp_frozen g (TExp g x) }}}.
Proof.
iIntros "%Φ (#? & #? & keep) post". wp_lam. wp_pures.
case: leak_eph; rewrite /keep.
- iMod (secret_public with "keep") as "#p_x". wp_pures.
  wp_apply wp_send => //. by iApply "post".
- wp_pures. iApply "post". by iApply (exp_frozen_intro _ gNm gNi).
Qed.

(* Both honest parties only ever confirm sessions with each other, as a DH
   public key received off the network carries nothing else to check; every
   completed session is therefore tested for secrecy. *)
Definition do_init_loop : val :=
  rec: "loop" "c" "leak_eph" "compromised" "set" "p_a" "P_a" "P_b" :=
    Fork ("loop" "c" "leak_eph" "compromised" "set" "p_a" "P_a" "P_b");;
    (bind: "r" := initiator "c" "p_a" "P_a" "P_b" (Tag gameN) in
     let: "sk" := Fst "r" in
     let: "x_a" := Snd "r" in
     add_fresh_lock_term_set "sk" "set";;
     leak_ephemeral "c" "leak_eph" "x_a";;
     check_key_secrecy "c" "leak_eph" "compromised" "sk");;
    #().

Definition do_init : val :=
  λ: "c" "leak_eph" "compromised" "p_a" "P_a" "P_b",
  let: "set" := new_lock_term_set #() in
  do_init_loop "c" "leak_eph" "compromised" "set" "p_a" "P_a" "P_b".

Definition hmqv_game_inv rl x : iProp := ∃ si,
  ⌜(si_key si : term) = x⌝ ∧
  ⌜session_of rl si⌝ ∧
  term_meta (si_share_of rl si) (gameN.@"fresh") ().

Lemma hmqv_game_fresh rl si E :
  session_of rl si →
  ↑gameN.@"fresh" ⊆ E →
  term_token (si_share_of rl si) E -∗
  fresh_term (hmqv_game_inv rl) (si_key si) ∗
  term_token (si_share_of rl si) (E ∖ ↑gameN.@"fresh").
Proof.
iIntros "%ss % token".
iPoseProof (term_token_difference _ (↑gameN.@"fresh") with "token")
  as "[token ?]" => //; iFrame. iSplit.
- iIntros "# (%si' & %e & %ss' & #meta)".
  move/term_of_senc_key_inj in e.
  rewrite (session_of_key_inj ss' ss e).
  by iDestruct (term_meta_token with "token meta") as "[]".
- iMod (term_meta_set (gameN.@"fresh") () with "token") as "#meta" => //.
  iIntros "!> !>". iExists si. by eauto.
Qed.

Lemma wp_do_init_loop leak_eph c lcomp vset p_a p_b :
  channel c -∗
  cryptis_ctx -∗
  hmqv_ctx -∗
  hmqv_pred gameN game_pred -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  mode p_a leak_eph -∗
  key_secrecy leak_eph lcomp p_a p_b -∗
  is_lock_term_set (hmqv_game_inv Init) vset -∗
  {{{ True }}}
    do_init_loop c #leak_eph #lcomp vset p_a (TExp g p_a) (TExp g p_b)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #? #key_a #key_b #mode #inv #set".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ by iApply "IH" => //. }
wp_pures.
wp_smart_apply (wp_initiator _ _ _ _ _ (keep leak_eph)) as "%ts [->|tsP]" => //.
- by iFrame "#".
- iIntros "%x_a %X_b s _". rewrite /keep /game_pred /=.
  case: leak_eph.
  + iModIntro. iFrame "s". by iLeft.
  + iMod (freeze_secret with "s") as "#s". iModIntro.
    iSplit => //. iRight. by iApply (exp_frozen_intro _ gNm gNi).
- wp_pures. by iApply "Hpost".
wp_pures.
iDestruct "tsP" as "(%x_a & %X_b & -> & #s_k & rel & token & keep & res)".
set si := init_si p_a x_a p_b X_b.
have ss : init_session si by exists p_a, x_a, p_b, X_b.
iPoseProof (hmqv_game_fresh (rl := Init) ss with "token")
  as "[fresh token]"; first solve_ndisj.
iMod (unrelease Init with "rel") as "#un".
wp_pures.
wp_apply (wp_add_fresh_lock_term_set with "[$]"). iIntros "_".
wp_pures. wp_apply (wp_leak_ephemeral with "[$]"). iIntros "frozen".
wp_pures.
wp_apply (wp_check_key_secrecy leak_eph _ lcomp _ _ Init si
            with "[frozen res]").
{ iFrame "#". case: leak_eph; first by [].
  iSplitL "frozen"; first by iExact "frozen".
  by iFrame. }
iIntros "_". wp_pures.
by iApply "Hpost".
Qed.

Lemma wp_do_init leak_eph c lcomp p_a p_b :
  channel c -∗
  cryptis_ctx -∗
  hmqv_ctx -∗
  hmqv_pred gameN game_pred -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  mode p_a leak_eph -∗
  key_secrecy leak_eph lcomp p_a p_b -∗
  {{{ True }}}
    do_init c #leak_eph #lcomp p_a (TExp g p_a) (TExp g p_b)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #? #? #? #? #? %Φ _ !> post".
wp_lam. wp_pures.
wp_apply (wp_new_lock_term_set (hmqv_game_inv Init)) => //.
iIntros "%set #set". wp_pures.
wp_apply wp_do_init_loop => //.
Qed.

Definition do_resp_loop : val :=
  rec: "loop" "c" "leak_eph" "compromised" "set" "p_b" "P_b" "P_a" :=
    Fork ("loop" "c" "leak_eph" "compromised" "set" "p_b" "P_b" "P_a");;
    let: "res" := responder_listen "c" in
    let: "X_a" := Fst "res" in
    let: "P_a'" := Snd "res" in
    (guard: eq_term "P_a" "P_a'" in
     bind: "r" := responder_confirm "c" "p_b" "P_b" "X_a" "P_a'" (Tag gameN) in
     let: "sk" := Fst "r" in
     let: "x_b" := Snd "r" in

     add_fresh_lock_term_set "sk" "set";;
     leak_ephemeral "c" "leak_eph" "x_b";;
     check_key_secrecy "c" "leak_eph" "compromised" "sk");;
    #().

Definition do_resp : val :=
  λ: "c" "leak_eph" "compromised" "p_b" "P_b" "P_a",
  let: "set" := new_lock_term_set #() in
  do_resp_loop "c" "leak_eph" "compromised" "set" "p_b" "P_b" "P_a".

Lemma wp_do_resp_loop leak_eph c lcomp set p_a p_b :
  channel c -∗
  cryptis_ctx -∗
  hmqv_ctx -∗
  hmqv_pred gameN game_pred -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  mode p_a leak_eph -∗
  key_secrecy leak_eph lcomp p_a p_b -∗
  is_lock_term_set (hmqv_game_inv Resp) set -∗
  {{{ True }}}
    do_resp_loop c #leak_eph #lcomp set p_b (TExp g p_b) (TExp g p_a)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #? #key_a #key_b #mode #inv #set".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ iApply "IH" => //. }
wp_pures. wp_apply wp_responder_listen; first by iSplit.
iIntros "%X_a %P_a' [#p_Xa #p_Pa']".
wp_pures. wp_eq_term e; wp_pures; last by iApply "Hpost".
subst P_a'.
wp_apply (wp_responder_confirm _ _ _ _ _ _ (keep leak_eph)).
{ do !iSplit => //. iIntros "%x_b s _". rewrite /keep /game_pred /=.
  case: leak_eph.
  + iModIntro. iFrame "s". by iLeft.
  + iMod (freeze_secret with "s") as "#s". iModIntro.
    iSplit => //. iRight. by iApply (exp_frozen_intro _ gNm gNi). }
iIntros "%r [->|Hr]"; wp_pures; first by iApply "Hpost".
iDestruct "Hr" as "(%x_b & -> & #s_k & rel & token & keep & res)".
set si := resp_si p_a X_a p_b x_b.
have ss : resp_session si by exists p_a, X_a, p_b, x_b.
wp_pures.
iPoseProof (hmqv_game_fresh (rl := Resp) ss with "token")
  as "[fresh token]"; first solve_ndisj.
iMod (unrelease Resp with "rel") as "#un".
wp_apply (wp_add_fresh_lock_term_set with "[$]"). iIntros "_".
wp_pures. wp_apply (wp_leak_ephemeral with "[$]"). iIntros "frozen".
wp_pures.
wp_apply (wp_check_key_secrecy leak_eph _ lcomp _ _ Resp si
            with "[frozen res]").
{ iFrame "#". case: leak_eph; first by [].
  iSplitL "frozen"; first by iExact "frozen".
  by iFrame. }
iIntros "_". wp_pures. by iApply "Hpost".
Qed.

Lemma wp_do_resp leak_eph c lcomp p_a p_b :
  channel c -∗
  cryptis_ctx -∗
  hmqv_ctx -∗
  hmqv_pred gameN game_pred -∗
  hmqv_key p_a -∗
  hmqv_key p_b -∗
  mode p_a leak_eph -∗
  key_secrecy leak_eph lcomp p_a p_b -∗
  {{{ True }}}
    do_resp c #leak_eph #lcomp p_b (TExp g p_b) (TExp g p_a)
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #? #? #? #? #? #? %Φ _ !> post".
wp_lam. wp_pures.
wp_apply (wp_new_lock_term_set (hmqv_game_inv Resp)) => //.
iIntros "%set #set". wp_pures.
by wp_apply wp_do_resp_loop => //.
Qed.

Definition game : val := λ: "c",
  let: "k_a" := mk_lt_key #() in
  let: "k_b" := mk_lt_key #() in
  let: "p_a" := Fst "k_a" in
  let: "P_a" := Snd "k_a" in
  let: "p_b" := Fst "k_b" in
  let: "P_b" := Snd "k_b" in
  let: "compromised" := ref #false in
  send "c" "P_a";;
  send "c" "P_b";;
  let: "leak_eph" := eq_term (recv "c") (TInt 1) in
  Fork (do_init "c" "leak_eph" "compromised" "p_a" "P_a" "P_b");;
  Fork (do_resp "c" "leak_eph" "compromised" "p_b" "P_b" "P_a");;
  if: "leak_eph" then #()
  else Fork (compromise_long_term_keys "c" "compromised" "p_a" "p_b").

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  hmqv_ctx -∗
  hmqv_pred gameN game_pred -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #? #? #?"; rewrite /game; wp_pures.
wp_apply wp_mk_lt_key => //.
iIntros "%p_a (#key_a & s_pa & #p_Pa & tok_Pa)". wp_pures.
wp_apply wp_mk_lt_key => //.
iIntros "%p_b (#key_b & s_pb & #p_Pb & _)". wp_pures.
wp_alloc lcomp as "lcomp".
wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_send => //.
wp_pures. wp_apply wp_recv => //. iIntros "%m _".
wp_eq_term e; wp_pures.
- iMod (term_meta_set (gameN.@"mode") true with "tok_Pa") as "#mode";
    first solve_ndisj.
  iMod (freeze_secret with "s_pa") as "#s_pa".
  iMod (freeze_secret with "s_pb") as "#s_pb".
  iAssert (key_secrecy true lcomp p_a p_b) as "#ks"; first by iSplit.
  wp_apply wp_fork; first by wp_apply (wp_do_init true). wp_pures.
  wp_apply wp_fork; first by wp_apply (wp_do_resp true). by wp_pures.
- iMod (term_meta_set (gameN.@"mode") false with "tok_Pa") as "#mode";
    first solve_ndisj.
  iMod (inv_alloc gameN _ (game_inv lcomp p_a p_b)
    with "[s_pa s_pb lcomp]") as "#inv".
  { iFrame. }
  iAssert (key_secrecy false lcomp p_a p_b) as "#ks"; first by [].
  wp_apply wp_fork; first by wp_apply (wp_do_init false). wp_pures.
  wp_apply wp_fork; first by wp_apply (wp_do_resp false). wp_pures.
  by wp_apply wp_fork; first wp_apply wp_compromise_long_term_keys; eauto.
Qed.
End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; tlockΣ; hmqvΣ].

Lemma hmqv_secure σ₁ σ₂ (v : val) t₂ e₂ :
  rtc erased_step ([run_network game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: cryptis_adequacy.
iIntros (? ? c) "#ctx #chan (_ & _ & _ & hash)".
iMod (hmqvGS_alloc with "hash") as (?) "(#? & tok & _)"; eauto.
iMod (hmqv_pred_set gameN game_pred with "tok")
  as "[#? ?]"; eauto.
by iApply (wp_game with "ctx [//]") => //.
Qed.
