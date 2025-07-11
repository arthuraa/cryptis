From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import numbers.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role session challenge_response dh tls13.
From cryptis.pk_auth Require Import pk_auth dh.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisGS Σ, !heapGS Σ, !spawnG Σ, !sessionGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types rl : role.
Implicit Types skI skR : sign_key.

Definition nslN := nroot.@"nsldh".
Definition crN := nroot.@"cr".
Definition tlsN := nroot.@"tls".

Definition loop : val := λ: "f",
  rec: "loop" <> := "f" #();; "loop" #().

Lemma wp_loop e :
  □ WP e {{ _, True }} -∗
  {{{ True }}} loop (λ: <>, e)%V #() {{{ v, RET v; True }}}.
Proof.
iIntros "#eP %Φ !> _ _"; rewrite /loop.
wp_lam; wp_pure (Rec _ _ _).
iLöb as "IH"; wp_pures.
wp_bind e; iApply wp_wand; first by iApply "eP".
by iIntros "%v' _"; wp_seq.
Qed.

Definition fork_loop (e : expr) : expr := Fork (loop (λ: <>, e)%E #()).

Lemma fork_loopE (e : expr) :
  fork_loop e = Fork (loop (λ: <>, e)%E #()).
Proof. by []. Qed.

Lemma wp_fork_loop e :
  □ WP e {{ _, True }} -∗
  {{{ True }}} fork_loop e {{{ RET #(); True }}}.
Proof.
iIntros "#eP %Φ !> _ post"; rewrite /fork_loop.
iApply wp_fork; last by iApply "post".
by iModIntro; wp_pures; iApply wp_loop.
Qed.

Definition tls_server_loop : val := λ: "c" "psk" "skR" "params",
  (rec: "loop" "psk" :=
     bind: "res" := tls_server tlsN "c" "psk" Spec.zero "skR" "params" in
     let: "psk" := SShare.I.session_key_of "res" in
     "loop" "psk") "psk".

Lemma wp_tls_server_loop c psk skR params :
  channel c -∗
  tls_ctx tlsN -∗
  minted psk -∗
  minted skR  -∗
  public params -∗
  {{{ cryptis_ctx }}} tls_server_loop c psk skR params {{{ v, RET v; True }}}.
Proof.
iIntros "#? #ctx #psk #sign_skR #p_params !> %Φ #? post".
rewrite /tls_server_loop; wp_lam; wp_let; wp_let; wp_let.
wp_pure (Rec _ _ _).
iLöb as "IH" forall (psk) "psk".
wp_pures.
wp_bind (tls_server _ _ _ _ _ _).
iApply wp_tls_server => //; eauto.
- by rewrite public_TInt.
iIntros (res) "res".
case: res => [res|]; wp_pures; last by iApply "post".
wp_bind (SShare.I.session_key_of _); iApply SShare.wp_session_key_of.
wp_let. iDestruct "res" as "(_ & _ & #psk' & _)".
iApply ("IH" with "post").
by rewrite minted_senc.
Qed.

Definition environment : val := λ: "c" "skI1" "skI2" "skR1" "skR2" "psk",
  send "c" "skI1";;
  send "c" "skI2";;
  send "c" "skR1";;
  send "c" "skR2";;
  let: "pkI1" := pkey "skI1" in
  let: "pkI2" := pkey "skI2" in
  let: "pkR1" := pkey "skR1" in
  let: "pkR2" := pkey "skR2" in
  fork_loop (
    let: "pkR'" := recv "c" in
    guard: is_aenc_key "pkR'" in
    pk_dh_init nslN "c" "skI1" "pkR'");;
  fork_loop (pk_dh_resp nslN "c" "skR1");;
  fork_loop (cr_init crN "c" "skI2" "pkR2");;
  fork_loop (cr_resp crN "c" "skR2");;
  let: "server_params" := recv "c" in
  Fork (tls_server_loop "c" "psk" "skR2" "server_params").

Lemma wp_environment c (skI1 skR1 : aenc_key) (skI2 skR2 : sign_key) (psk : term) :
  cryptis_ctx -∗
  channel c -∗
  pk_dh_ctx nslN (λ _ _ _ _, True)%I -∗
  cr_ctx crN (λ _ _ _ _ _, True)%I -∗
  tls_ctx tlsN -∗
  public skI1 -∗
  public skR1 -∗
  public skI2 -∗
  public skR2 -∗
  minted psk -∗
  honest 0 ∅ -∗
  ●Ph□ 0 -∗
  {{{ True }}} environment c skI1 skI2 skR1 skR2 psk {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #? #? #? #? #? #? #? #? #hon #phase %Φ !> _ post".
rewrite /environment; wp_pures.
wp_bind (send _ _); iApply wp_send => //; wp_pures.
wp_bind (send _ _); iApply wp_send => //; wp_pures.
wp_bind (send _ _); iApply wp_send => //; wp_pures.
wp_bind (send _ _); iApply wp_send => //; wp_pures.
wp_apply wp_pkey. wp_pures. wp_apply wp_pkey. wp_pures.
wp_apply wp_pkey. wp_pures. wp_apply wp_pkey. wp_pures.
wp_bind (fork_loop _); iApply wp_fork_loop; eauto.
  iModIntro.
  wp_bind (recv _); iApply wp_recv => //.
  iIntros "%pkR' #?"; wp_pures.
  wp_apply wp_is_aenc_key; first by iApply public_minted.
  iSplit; last by wp_pures; eauto.
  iIntros "%skR' -> #m_skR'".
  wp_pures. wp_apply (wp_pk_dh_init _ (λ _ _ _ _, True)%I); eauto.
iIntros "!> _"; wp_pures; wp_bind (fork_loop _); iApply wp_fork_loop => //.
  iModIntro.
  by iApply (wp_pk_dh_resp _ (λ _ _ _ _, True)%I); eauto.
iIntros "!> _"; wp_pures; wp_bind (fork_loop _); iApply wp_fork_loop => //.
  iModIntro; iApply (wp_cr_init); eauto.
iIntros "!> _"; wp_pures; wp_bind (fork_loop _); iApply wp_fork_loop => //.
  by iModIntro; iApply (wp_cr_resp); eauto.
iIntros "!> _"; wp_pures.
wp_bind (recv _); iApply wp_recv => //.
iIntros "%params #p_params"; wp_pures.
iApply wp_fork; last by iApply "post".
iModIntro; iApply wp_tls_server_loop => //.
by iApply public_minted.
Qed.

Definition tls_client_loop : val := λ: "c" "psk",
  (rec: "loop" "psk" :=
    let: "params" := recv "c" in
    let: "m" := Meth.I.PskDh "psk" Spec.zero in
    bind: "res" := tls_client tlsN "c" "m" "params" in
    let: "psk'" := Snd "res" in
    let: "continue" := recv "c" in
    if: eq_term "continue" Spec.zero then
      "loop" "psk'"
    else SOME "psk'") "psk".

Lemma wp_tls_client_loop c psk :
  channel c -∗
  cryptis_ctx -∗
  tls_ctx tlsN -∗
  minted psk -∗
  {{{ public psk → ▷ False }}}
    tls_client_loop c psk
  {{{ (res : option term), RET (repr res);
      match res with
      | Some psk' => public psk' → ▷ False
      | None => True
      end }}}.
Proof.
iIntros "#? #? #? #t_psk !> %Φ s_psk post".
rewrite /tls_client_loop.
wp_lam; wp_let; wp_pure (Rec _ _ _).
iLöb as "IH" forall (psk) "t_psk".
wp_pure _ credit:"c".
wp_pures; wp_bind (recv _); iApply wp_recv => //.
iIntros "%params #p_params"; wp_pures.
wp_bind (Meth.I.PskDh _ _); iApply Meth.wp_PskDh => //.
iIntros "!> % ->"; rewrite [Meth.PskDh]lock; wp_pures.
wp_bind (tls_client _ _ _ _).
iApply wp_tls_client; rewrite -?lock; eauto.
  by rewrite /= public_TInt; eauto.
iIntros (res) "Hres"; case: res => [res|]; wp_pures; last first.
  by iApply ("post" $! None).
case: res => [] [] [] pk cn sn sk /=.
iDestruct "Hres" as (?) "(-> & _ & _ & _ & #t_sk & _ & Hres)".
iMod (lc_fupd_elim_later with "c Hres") as "Hres".
iDestruct "Hres" as "[[_ contra]|[_ #s_psk']]".
  by iDestruct ("s_psk" with "contra") as ">[]".
wp_bind (recv _); iApply wp_recv => //.
iIntros "%continue _"; wp_pures.
wp_eq_term e.
  wp_if.
  iApply ("IH" with "[] post [//]").
  iIntros "#contra". iSpecialize ("s_psk'" with "contra").
  by iDestruct "s_psk'" as ">[]".
wp_pures.
iApply ("post" $! (Some (sk : term))).
iModIntro.
iIntros "#contra". iSpecialize ("s_psk'" with "contra").
by iDestruct "s_psk'" as ">[]".
Qed.

Definition game : val := λ: <>,
  let: "c"   := init_network #() in
  let: "skI1" := mk_aenc_key #() in
  let: "skI2" := mk_sign_key #() in
  let: "skR1" := mk_aenc_key #() in
  let: "skR2" := mk_sign_key #() in
  let: "psk" := mk_nonce #() in
  environment "c" "skI1" "skI2" "skR1" "skR2" "psk";;
  bind: "sk" := tls_client_loop "c" "psk" in
  let: "m" := recv "c" in
  SOME (~ eq_term "m" "sk").

Lemma wp_game :
  cryptis_ctx ∗
  session_token ⊤ ∗
  seal_pred_token AENC ⊤ ∗
  seal_pred_token SIGN ⊤ ∗
  seal_pred_token SENC ⊤ ∗
  hash_pred_token ⊤ ∗
  honest 0 ∅ ∗
  ●Ph 0 -∗
  WP game #() {{ v, ⌜v = NONEV ∨ v = SOMEV #true⌝ }}.
Proof.
iIntros "(#ctx & sess_tok & aenc_tok & sign_tok & senc_tok & hash_tok & #hon & phase)".
iMod (phase_auth_discard with "phase") as "#phase".
rewrite /game; wp_pures.
iMod (pk_dh_alloc nslN (λ _ _ _ _, True)%I with "sess_tok aenc_tok")
  as "(#pk_dh_ctx & sess_tok & aenc_tok)" => //; try solve_ndisj.
iMod (cr_alloc crN (λ _ _ _ _ _, True)%I with "sess_tok sign_tok")
  as "(#cr_ctx & sess_tok & sign_tok)"; try solve_ndisj.
iMod (tls_ctx_alloc tlsN with "sess_tok senc_tok sign_tok hash_tok")
  as "(#tls_ctx & sess_tok & senc_tok & sign_tok & hash_tok)"; try solve_ndisj.
wp_apply wp_init_network => //. iIntros "%c #cP". wp_pures.
wp_apply wp_mk_aenc_key => //. iIntros "%skI1 #? s_skI1 _".
iMod (secret_public with "s_skI1") as "#?". wp_pures.
wp_apply wp_mk_sign_key => //. iIntros "%skI2 #? s_skI2 _".
iMod (secret_public with "s_skI2") as "#?". wp_pures.
wp_apply wp_mk_aenc_key => //. iIntros "%skR1 #? s_skR1 _".
iMod (secret_public with "s_skR1") as "#?". wp_pures.
wp_apply wp_mk_sign_key => //. iIntros "%skR2 #? s_skR2 _".
iMod (secret_public with "s_skR2") as "#?". wp_pures.
wp_apply (wp_mk_nonce (λ psk, term_meta psk (nroot.@"pub") ())%I (λ _, False%I)) => //.
iIntros (psk) "_ #t_psk #p_psk _ tok_psk". wp_pures.
wp_apply wp_environment; eauto.
iIntros "_"; wp_pures.
wp_bind (tls_client_loop _ _).
iApply (wp_tls_client_loop with "[] [] [] [] [tok_psk]")=> //.
  iIntros "#p_psk'".
  iSpecialize ("p_psk" with "p_psk'").
  iModIntro.
  iDestruct "p_psk" as "#p_psk".
  by iApply (term_meta_token with "tok_psk p_psk").
iIntros "!> %res H1".
case: res => [sk|]; wp_pures; last by eauto.
wp_bind (recv _); iApply wp_recv => //.
iIntros (m) "#p_m"; wp_let.
wp_bind (eq_term _ _); iApply wp_eq_term.
case: bool_decide_reflect => [->|?]; last by wp_pures; eauto.
by iDestruct ("H1" with "p_m") as ">[]".
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; sessionΣ].

Lemma composite_secure σ₁ σ₂ (v : val) ts :
  rtc erased_step ([game #()], σ₁) (Val v :: ts, σ₂) →
  v = NONEV ∨ v = SOMEV #true.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_result NotStuck _ _ (λ v _, v = NONEV ∨ v = SOMEV #true)).
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisGS_alloc _) as (?) "(#ctx & seal_tok & key_tok & hash_tok & hon)".
iMod (sessionGS_alloc _) as (?) "sess_tok".
by iApply (wp_game) => //; try by iFrame.
Qed.
