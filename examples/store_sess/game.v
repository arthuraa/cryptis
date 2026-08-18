From cryptis Require Import lib.
From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import numbers reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par assert ticket_lock.
From cryptis Require Import cryptis primitives tactics gmeta role adequacy.
From cryptis.primitives Require Import attacker.
From cryptis.examples Require Import iso_dh sess gen_conn.
From cryptis.examples.sess.proofs Require base.
From cryptis.examples.store_sess Require Import impl proofs.
From cryptis.examples.store_sess.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ}.
Context `{!cryptis.examples.sess.proofs.base.sessG Σ, !storeGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types rl : role.
Implicit Types skI skR : sign_key.

Definition gameN := nroot.@"game".

Definition server_loop : val := rec: "loop" "c" "server" :=
  Server.listen "c" "server";;
  "loop" "c" "server".

Definition start_server : val := λ: "c" "skR",
  let: "server" := Server.start "skR" in
  server_loop "c" "server".

Definition game : val := λ: "c",

  let: "skI" := mk_sign_key #() in
  let: "skR" := mk_sign_key #() in
  let: "pkI" := pkey "skI" in
  let: "pkR" := pkey "skR" in
  send "c" "pkI";; send "c" "pkR";;

  Fork (start_server "c" "skR");;

  let: "conn" := Client.connect "c" "skI" "pkR" in

  let: "k" := recv "c" in
  let: "v" := recv "c" in
  Client.create "conn" "k" "v";;
  Client.close "conn";;

  send "c" (GenConn.session_key "conn");;

  let: "conn" := Client.connect "c" "skI" "pkR" in

  send "c" "skI";;
  send "c" "skR";;

  let: "v'" := Client.load "conn" "k" in
  assert: eq_term "v" "v'".

Lemma wp_server_loop c ss :
  {{{ cryptis_ctx ∗ channel c ∗ store_ctx ∗
      server ss }}}
    server_loop c (repr ss)
  {{{ RET #(); True }}}.
Proof.
iLöb as "IH". iIntros "%Ψ (#? & #? & #? & server) post".
wp_rec. wp_pures.
wp_apply (wp_server_listen with "[$server]"); eauto.
iIntros "server". wp_pures.
by iApply ("IH" with "[$server]"); eauto.
Qed.

Lemma wp_start_server c skR :
  {{{ cryptis_ctx ∗ channel c ∗ store_ctx ∗
      minted skR ∗
      term_token skR ⊤ }}}
    start_server c skR
  {{{ RET #(); True }}}.
Proof.
iIntros "%Ψ (#? & #? & #? & #? & token) post".
wp_lam. wp_pures.
wp_apply (wp_server_start with "[$token]") => //; eauto.
iIntros "%ss server". wp_pures.
wp_apply (wp_server_loop with "[$server]"); eauto.
Qed.

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  store_ctx -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #chan #store_ctx"; rewrite /game; wp_pures.
wp_apply (wp_mk_sign_key with "[]"); eauto.
iIntros "%skI #m_skI s_skI tokenI". wp_pures.
wp_pures. wp_apply (wp_mk_sign_key with "[]"); eauto.
iIntros "%skR #m_skR s_skR tokenR". wp_pures.
wp_apply wp_pkey. wp_pures.
wp_apply wp_pkey. wp_pures.
wp_apply wp_send => //. { by iApply public_verify_key. } wp_pures.
wp_apply wp_send => //. { by iApply public_verify_key. } wp_pures.
wp_apply (wp_fork with "[tokenR]").
{ iModIntro. wp_apply (wp_start_server with "[$tokenR]"); eauto. }
wp_pures.
have sub : ↑dbN.@"client".@(skR : term) ⊆ (⊤ : coPset) by solve_ndisj.
iMod (client_alloc skI sub with "tokenI")
  as "(client & free & token)".
wp_apply (wp_client_connect with "[] [] [] [] [] client"); eauto.
iIntros "%cs client". wp_pure _ credit:"c". wp_pures.
iPoseProof (db_connected_ok with "client s_skI s_skR") as "#>ok".
wp_apply wp_recv => //. iIntros "%k #p_k". wp_pures.
wp_apply wp_recv => //. iIntros "%v #p_v". wp_pures.
have subk : ({[k]} : coGset.coGset term) ⊆ ⊤ by set_solver.
rewrite (db_free_at_diff skI skR subk).
iDestruct "free" as "[free_k free]".
wp_apply (wp_client_create with "[] [] [] [] [$client $free_k]") => //.
iIntros "[client k_v]". wp_pures.
wp_apply (wp_client_close with "[//] [] [$client]") => //.
iIntros "[client #p_sk]".
wp_pures.
wp_apply GenConn.wp_session_key => //. iIntros "_".
wp_apply (wp_send with "[//]") => //. wp_pures.
wp_apply (wp_client_connect with "[] [] [] [] [] client"); eauto.
iIntros "%cs' client". wp_pure _ credit:"c'". wp_pures.
iPoseProof (db_connected_ok with "client s_skI s_skR") as "#>#ok'".
iMod (secret_public with "s_skI") as "#p_skI".
iMod (secret_public with "s_skR") as "#p_skR".
wp_apply wp_send => //. wp_pures.
wp_apply wp_send => //. wp_pures.
wp_apply (wp_client_load with "[] [] [] [$client $k_v]") => //.
iIntros "%v' (client & k_v & _ & [fail|->])".
{ iPoseProof (db_connected_ok_compromised with "client ok' fail") as ">[]". }
wp_pures. wp_apply wp_assert. wp_apply wp_eq_term.
by rewrite bool_decide_eq_true_2.
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; tlockΣ; iso_dhΣ; GenConn.connΣ;
    cryptis.examples.sess.proofs.base.sessΣ; storeΣ].

Lemma store_sess_secure σ₁ σ₂ t₂ e₂ :
  rtc erased_step ([run_network game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: cryptis_adequacy.
iIntros (? ? c) "#ctx #chan (_ & sign_tok & senc_tok & _)".
iMod (iso_dhGS_alloc with "sign_tok") as (?) "(#iso & iso_tok & sign_tok)" => //.
iMod (GenConn.base_ctx_alloc with "senc_tok") as "(#conn & senc_tok)" => //.
iMod (store_ctx_alloc with "conn iso iso_tok") as "(#sctx & iso_tok)";
  first solve_ndisj.
by iApply (wp_game with "ctx chan sctx") => //.
Qed.
