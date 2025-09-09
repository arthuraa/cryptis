From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap reservation_map.
From iris.base_logic.lib Require Import invariants saved_prop.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import nondet_bool ticket_lock.
From cryptis Require Import term cryptis.
From cryptis.primitives
  Require Import notations pre_term comp simple with_cryptis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition add_int : val := λ: "c",
  let: "n" := nondet_int #() in
  send "c" (tint "n").

Definition add_pair : val := λ: "c",
  let: "t1" := recv "c" in
  let: "t2" := recv "c" in
  send "c" (tuple "t1" "t2").

Definition add_proj : val := λ: "c",
  let: "t" := recv "c" in
  match: untuple "t" with
    NONE => #()
  | SOME "v" => send "c" (Fst "v");; send "c" (Snd "v")
  end.

Definition add_nonce : val := λ: "c",
  send "c" (mk_nonce #()).

Definition add_keys : val := λ: "c",
  let: "t" := recv "c" in
  send "c" (key AEnc "t");;
  send "c" (key ADec "t");;
  send "c" (key Sign "t");;
  send "c" (key Verify "t");;
  send "c" (key SEnc "t");;
  send "c" (pkey "t").

Definition add_seal : val := λ: "c",
  let: "t1" := recv "c" in
  let: "t2" := recv "c" in
  send "c" (seal "t1" "t2").

Definition add_open : val := λ: "c",
  let: "t1" := recv "c" in
  let: "t2" := recv "c" in
  match: open "t1" "t2" with
    NONE => #()
  | SOME "t" => send "c" "t"
  end.

Definition add_hash : val := λ: "c",
  let: "t" := recv "c" in
  send "c" (hash "t").

Definition add_exp : val := λ: "c",
  let: "t1" := recv "c" in
  let: "t2" := recv "c" in
  send "c" (texp "t1" "t2").

Definition init_attacker : val := rec: "loop" "c" :=
  Fork (
    add_int "c";;
    add_pair "c";;
    add_proj "c";;
    add_nonce "c";;
    add_keys "c";;
    add_seal "c";;
    add_open "c";;
    add_hash "c";;
    add_exp "c";;
    "loop" "c").

Definition init_network : val := λ: <>,
  let: "c" := mk_channel #() in
  init_attacker "c";;
  "c".

Definition run_network : val := λ: "f",
  "f" (init_network #()).

Section Proofs.

Context `{!heapGS Σ, !cryptisGS Σ}.

Lemma wp_add_int c :
  {{{ channel c }}} add_int c {{{ RET #(); True }}}.
Proof.
iIntros "%Ψ #c post".
wp_lam. wp_apply wp_nondet_int. iIntros "%n". wp_pures.
wp_apply wp_tint. wp_apply wp_send => //.
  by rewrite public_TInt.
by iApply "post".
Qed.

Lemma wp_add_pair c :
  {{{ channel c }}} add_pair c {{{ RET #(); True }}}.
Proof.
iIntros "%Ψ #c post". wp_lam.
wp_apply wp_recv => //. iIntros "%t1 #p_t1". wp_pures.
wp_apply wp_recv => //. iIntros "%t2 #p_t2". wp_pures.
wp_apply wp_tuple. wp_apply wp_send => //.
- by iApply public_TPair; eauto.
- by iApply "post".
Qed.

Lemma wp_add_proj c :
  {{{ channel c }}} add_proj c {{{ RET #(); True }}}.
Proof.
iIntros "%Ψ #c post". wp_lam.
wp_apply wp_recv => //. iIntros "%t #p_t". wp_pures.
wp_apply wp_untuple.
case: t => *; wp_pures; try by iApply "post".
rewrite public_TPair. iDestruct "p_t" as "[??]".
wp_apply wp_send => //. wp_pures.
wp_apply wp_send => //. by iApply "post".
Qed.

Lemma wp_add_nonce c :
  {{{ cryptis_ctx ∗ channel c }}} add_nonce c {{{ RET #(); True }}}.
Proof.
iIntros "%Ψ [#? #c] post". wp_lam.
wp_apply (wp_mk_nonce (λ _, True)%I (λ _, True)%I) => //.
iIntros "%t _ _ #p_t _ _".
wp_apply wp_send => //.
- by iApply "p_t".
- by iApply "post".
Qed.

Lemma wp_add_keys c :
  {{{ channel c }}} add_keys c {{{ RET #(); True }}}.
Proof.
iIntros "%Ψ #c post". wp_lam.
wp_apply wp_recv => //. iIntros "%t #p_t". wp_pures.
wp_apply wp_key => //.
wp_apply wp_send => //; first by iApply public_TKey; eauto.
wp_pures. wp_apply wp_key => //.
wp_apply wp_send => //; first by iApply public_TKey; eauto.
wp_pures. wp_apply wp_key => //.
wp_apply wp_send => //; first by iApply public_TKey; eauto.
wp_pures. wp_apply wp_key => //.
wp_apply wp_send => //; first by iApply public_TKey; eauto.
wp_pures. wp_apply wp_key.
wp_apply wp_send => //; first by iApply public_TKey; eauto.
wp_pures. wp_apply wp_pkey. wp_apply wp_send => //.
  iApply public_pkey => //.
by iApply "post".
Qed.

Lemma wp_add_seal c :
  {{{ channel c }}} add_seal c {{{ RET #(); True }}}.
Proof.
iIntros "%Ψ #c post". wp_lam.
wp_apply wp_recv => //. iIntros "%t1 #p_t1". wp_pures.
wp_apply wp_recv => //. iIntros "%t2 #p_t2". wp_pures.
wp_apply wp_seal. wp_apply wp_send => //.
- by iApply public_TSeal; eauto.
- by iApply "post".
Qed.

Lemma wp_add_open c :
  {{{ channel c }}} add_open c {{{ RET #(); True }}}.
Proof.
iIntros "%Ψ #c post". wp_lam.
wp_apply wp_recv => //. iIntros "%t1 #p_t1". wp_pures.
wp_apply wp_recv => //. iIntros "%t2 #p_t2". wp_pures.
wp_apply wp_open.
case e: Spec.open => [t|]; wp_pures; last by iApply "post".
wp_apply wp_send => //; last by iApply "post".
by iApply public_open; eauto.
Qed.

Lemma wp_add_hash c :
  {{{ channel c }}} add_hash c {{{ RET #(); True }}}.
Proof.
iIntros "%Ψ #c post". wp_lam.
wp_apply wp_recv => //. iIntros "%t #p_t". wp_pures.
wp_apply wp_hash.
wp_apply wp_send => //; last by iApply "post".
by rewrite public_THash; eauto.
Qed.

Lemma wp_add_exp c :
  {{{ channel c }}} add_exp c {{{ RET #(); True }}}.
Proof.
iIntros "%Ψ #c post". wp_lam.
wp_apply wp_recv => //. iIntros "%t1 #p_t1". wp_pures.
wp_apply wp_recv => //. iIntros "%t2 #p_t2". wp_pures.
wp_apply wp_texp. wp_apply wp_send => //; last by iApply "post".
by iApply public_TExp.
Qed.

Lemma wp_init_attacker c :
  {{{ cryptis_ctx ∗ channel c }}} init_attacker c {{{ RET #(); True }}}.
Proof.
iLöb as "IH".
iIntros "%Ψ [#? #?] post".
wp_rec. wp_apply wp_fork; last by iApply "post".
wp_apply wp_add_int => //. iIntros "_". wp_pures.
wp_apply wp_add_pair => //. iIntros "_". wp_pures.
wp_apply wp_add_proj => //. iIntros "_". wp_pures.
wp_apply wp_add_nonce => //; eauto. iIntros "_". wp_pures.
wp_apply wp_add_keys => //. iIntros "_". wp_pures.
wp_apply wp_add_seal => //. iIntros "_". wp_pures.
wp_apply wp_add_open => //. iIntros "_". wp_pures.
wp_apply wp_add_hash => //. iIntros "_". wp_pures.
wp_apply wp_add_exp => //. iIntros "_". wp_pures.
by wp_apply "IH"; eauto.
Qed.

Lemma wp_init_network :
  {{{ cryptis_ctx }}} init_network #() {{{ c, RET c; channel c }}}.
Proof.
iIntros "%Ψ #ctx post".
wp_lam. wp_apply wp_mk_channel. iIntros "%c #cP". wp_pures.
wp_apply wp_init_attacker; eauto. iIntros "_". wp_pures.
by iApply "post".
Qed.

Lemma wp_run_network (f : val) φ :
  (∀ c, cryptis_ctx -∗ channel c -∗ WP f c {{ φ }}) -∗
  cryptis_ctx -∗ WP run_network f {{ φ }}.
Proof.
iIntros "wp #ctx". wp_lam. wp_apply wp_init_network => //.
iIntros "%c #?". by iApply "wp".
Qed.

End Proofs.
