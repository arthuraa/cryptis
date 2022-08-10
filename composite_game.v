From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import numbers.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import nown role session challenge_response.
From cryptis Require Import pk_auth dh pk_dh tls13.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisG Σ, !heapGS Σ, !spawnG Σ, !sessionG Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types rl : role.

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

Definition tls_server_loop : val := λ: "c" "psk" "nR" "params",
  (rec: "loop" "psk" :=
     bind: "res" := tls_server tlsN "c" "psk" Spec.zero "nR" "params" in
     let: "psk" := Fst (mkkey (SShare.I.session_key_of tlsN "res")) in
     "loop" "psk") "psk".

Lemma wp_tls_server_loop c psk nR params :
  channel c -∗
  tls_ctx tlsN -∗
  sterm psk -∗
  pterm nR  -∗
  pterm params -∗
  {{{ True }}} tls_server_loop c psk nR params {{{ v, RET v; True }}}.
Proof.
iIntros "#? #ctx #psk #nR #p_params !> %Φ _ post".
rewrite /tls_server_loop; wp_lam; wp_let; wp_let; wp_let.
wp_pure (Rec _ _ _).
iLöb as "IH" forall (psk) "psk".
wp_pures.
wp_bind (tls_server _ _ _ _ _ _).
iApply wp_tls_server => //.
- by rewrite pterm_TInt.
- by rewrite sterm_TKey; iApply pterm_sterm.
- by rewrite pterm_TKey; eauto.
iIntros (res) "res".
case: res => [res|]; wp_pures; last by iApply "post".
wp_bind (SShare.I.session_key_of _ _); iApply SShare.wp_session_key_of.
wp_bind (mkkey _); iApply wp_mkkey; wp_pure (Fst _); wp_let.
iDestruct "res" as "(_ & _ & #psk' & _)".
iApply ("IH" with "post").
by rewrite sterm_TKey.
Qed.

Definition environment : val := λ: "c" "nI" "nR" "psk",
  let: "kI" := mkkey "nI" in
  let: "kR" := mkkey "nR" in
  let: "ekI" := Fst "kI" in
  let: "dkI" := Snd "kI" in
  let: "ekR" := Fst "kR" in
  let: "dkR" := Snd "kR" in
  send "c" "ekI";;
  send "c" "ekR";;
  send "c" "dkI";;
  send "c" "dkR";;
  fork_loop (
    let: "pkR'" := recv "c" in
    bind: "pkR'" := to_ek "pkR'" in
    pk_dh_init nslN "c" "dkI" "ekI" "pkR'");;
  fork_loop (pk_dh_resp nslN "c" "dkR" "ekR");;
  fork_loop (cr_init crN "c" "ekI" "dkI" "dkR");;
  fork_loop (cr_resp crN "c" "ekR" "dkR");;
  let: "server_params" := recv "c" in
  Fork (tls_server_loop "c" "psk" "nR" "server_params").

Lemma wp_environment c nI nR psk :
  channel c -∗
  pk_dh_ctx nslN (λ _ _ _ _, True)%I -∗
  cr_ctx crN (λ _ _ _ _ _, True)%I -∗
  tls_ctx tlsN -∗
  pterm nI -∗
  pterm nR -∗
  sterm psk -∗
  {{{ True }}} environment c nI nR psk {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #? #? #? #? #? %Φ !> _ post".
rewrite /environment; wp_pures.
wp_bind (mkkey _); iApply wp_mkkey; wp_pures.
wp_bind (mkkey _); iApply wp_mkkey; wp_pures.
rewrite -!fork_loopE.
iAssert (pterm (TKey Enc nI)) as "#?".
  by rewrite pterm_TKey; eauto.
iAssert (pterm (TKey Dec nI)) as "#?".
  by rewrite [pterm (TKey Dec _)]pterm_TKey; eauto.
iAssert (pterm (TKey Enc nR)) as "#?".
  by rewrite [pterm (TKey Enc nR)]pterm_TKey; eauto.
iAssert (pterm (TKey Dec nR)) as "#?".
  by rewrite [pterm (TKey Dec nR)]pterm_TKey; eauto.
wp_bind (send _ _); iApply wp_send => //; wp_pures.
wp_bind (send _ _); iApply wp_send => //; wp_pures.
wp_bind (send _ _); iApply wp_send => //; wp_pures.
wp_bind (send _ _); iApply wp_send => //; wp_pures.
wp_bind (fork_loop _); iApply wp_fork_loop; eauto.
  iModIntro.
  wp_bind (recv _); iApply wp_recv => //.
  iIntros "%pkR' #?"; wp_pures.
  wp_bind (to_ek _); iApply wp_to_ek.
  case: Spec.to_ekP => [? ->|_]; wp_pures => //.
  by iApply (wp_pk_dh_init _ (λ _ _ _ _, True)%I); eauto.
iIntros "!> _"; wp_pures; wp_bind (fork_loop _); iApply wp_fork_loop => //.
  iModIntro.
  by iApply (wp_pk_dh_resp _ (λ _ _ _ _, True)%I); eauto.
iIntros "!> _"; wp_pures; wp_bind (fork_loop _); iApply wp_fork_loop => //.
  by iModIntro; iApply (wp_cr_init); eauto.
iIntros "!> _"; wp_pures; wp_bind (fork_loop _); iApply wp_fork_loop => //.
  by iModIntro; iApply (wp_cr_resp); eauto.
iIntros "!> _"; wp_pures.
wp_bind (recv _); iApply wp_recv => //.
iIntros "%params #p_params"; wp_pures.
iApply wp_fork; last by iApply "post".
by iModIntro; iApply wp_tls_server_loop => //.
Qed.

Definition tls_client_loop : val := λ: "c" "psk",
  (rec: "loop" "psk" :=
    let: "params" := recv "c" in
    let: "m" := Meth.I.PskDh "psk" Spec.zero in
    bind: "res" := tls_client tlsN "c" "m" "params" in
    let: "psk'" := Fst (mkkey (Snd "res")) in
    let: "continue" := recv "c" in
    if: eq_term "continue" Spec.zero then
      "loop" "psk'"
    else SOME "psk'") "psk".

Lemma wp_tls_client_loop c psk :
  channel c -∗
  tls_ctx tlsN -∗
  sterm psk -∗
  {{{ pterm psk → ▷ False }}}
    tls_client_loop c psk
  {{{ (res : option term), RET (repr res);
      match res with
      | Some psk' => pterm psk' → ▷ False
      | None => True
      end }}}.
Proof.
iIntros "#? #? #t_psk !> %Φ s_psk post".
rewrite /tls_client_loop.
wp_lam; wp_let; wp_pure (Rec _ _ _).
iLöb as "IH" forall (psk) "t_psk".
wp_pures; wp_bind (recv _); iApply wp_recv => //.
iIntros "%params #p_params"; wp_pures.
wp_bind (Meth.I.PskDh _ _); iApply Meth.wp_PskDh => //.
iIntros "!> % ->"; rewrite [Meth.PskDh]lock; wp_pures.
wp_bind (tls_client _ _ _ _).
iApply wp_tls_client; rewrite -?lock; eauto.
  by rewrite /= pterm_TInt; eauto.
iIntros (res) "Hres"; case: res => [res|]; wp_pures; last first.
  by iApply ("post" $! None).
case: res => [] [] [] vkey cn sn sk /=.
iDestruct "Hres" as (?) "(-> & _ & _ & _ & #t_sk & _ & Hres)".
wp_bind (mkkey _); iApply wp_mkkey; wp_pures.
iDestruct "Hres" as "[[_ contra]|[_ #s_psk']]".
  by iDestruct ("s_psk" with "contra") as ">[]".
wp_bind (recv _); iApply wp_recv => //.
iIntros "%continue _"; wp_pures.
wp_eq_term e.
  wp_if.
  iApply ("IH" with "[] post []").
  - iIntros "#contra". iSpecialize ("s_psk'" with "contra").
    by iDestruct "s_psk'" as ">[]".
  - by rewrite sterm_TKey.
wp_pures.
iApply ("post" $! (Some (TKey Enc sk))).
iModIntro.
iIntros "#contra". iSpecialize ("s_psk'" with "contra").
by iDestruct "s_psk'" as ">[]".
Qed.

Definition game : val := λ: "mkchan",
  let: "c"   := "mkchan" #() in
  let: "nI"  := tag (nroot.@"key") (mknonce #()) in
  let: "nR"  := tag (nroot.@"key") (mknonce #()) in
  let: "psk" := mknonce #() in
  let: "kI"  := mkkey "nI" in
  let: "ekI" := Fst "kI" in
  let: "dkI" := Snd "kI" in
  environment "c" "nR" "nI" "psk";;
  bind: "sk" := tls_client_loop "c" "psk" in
  let: "m" := recv "c" in
  SOME (~ eq_term "m" "sk").

Lemma wp_game (mkchan : val) :
  {{{ True }}} mkchan #() {{{ v, RET v; channel v }}} -∗
  nown_token session_name ⊤ -∗
  enc_pred_token ⊤ -∗
  hash_pred_token ⊤ -∗
  key_pred_token (⊤ ∖ ↑nroot.@"keys") -∗
  WP game mkchan {{ v, ⌜v = NONEV ∨ v = SOMEV #true⌝ }}.
Proof.
iIntros "wp_mkchan sess_tok enc_tok hash_tok key_tok"; rewrite /game; wp_pures.
iMod (pk_dh_alloc nslN (λ _ _ _ _, True)%I with "sess_tok enc_tok")
  as "(#pk_dh_ctx & sess_tok & enc_tok)" => //; try solve_ndisj.
iMod (cr_alloc crN (λ _ _ _ _ _, True)%I with "sess_tok enc_tok")
  as "(#cr_ctx & sess_tok & enc_tok)"; try solve_ndisj.
iMod (tls_ctx_alloc tlsN with "sess_tok enc_tok hash_tok key_tok")
  as "(#tls_ctx & sess_tok & enc_tok & hash_tok & key_tok)"; try solve_ndisj.
iMod (key_pred_set (nroot.@"key") (λ kt _, ⌜kt = Enc⌝)%I with "key_tok")
  as "[#? key_tok]"; try solve_ndisj.
wp_bind (mkchan _); iApply "wp_mkchan" => //.
iIntros "!> %c #cP".
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce (λ _, True)%I (λ _, False%I)).
iIntros (nI) "#t_nI #p_nI _ tok_nI".
wp_tag.
iAssert (pterm (Spec.tag (nroot.@"key") nI)) as "{p_nI} p_nI".
  by rewrite pterm_tag; iApply "p_nI".
wp_pures.
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce (λ _, True)%I (λ _, False%I)).
iIntros (nR) "#t_nR #p_nR _ tok_nR".
wp_tag.
iAssert (pterm (Spec.tag (nroot.@"key") nR)) as "{p_nR} p_nR".
  by iApply pterm_tag; iApply "p_nR".
wp_pures.
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce (λ psk, nonce_meta psk (nroot.@"pub") ())%I (λ _, False%I)).
iIntros (psk) "#t_psk #p_psk _ tok_psk".
wp_pures; wp_bind (mkkey _); iApply wp_mkkey.
set ekI := TKey Enc _.
set dkI := TKey Dec _.
wp_pures; wp_bind (environment _ _ _ _).
iApply wp_environment; eauto.
iIntros "!> _"; wp_pures.
wp_bind (tls_client_loop _ _).
iApply (wp_tls_client_loop with "[] [] [] [tok_psk]")=> //.
  iIntros "#p_psk'".
  iSpecialize ("p_psk" with "p_psk'").
  iModIntro.
  iDestruct "p_psk" as "#p_psk".
  by iApply (term_meta_meta_token with "tok_psk p_psk").
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

Lemma nsl_dh_secure (mkchan : val) σ₁ σ₂ (v : val) ts :
  (∀ `{!heapGS Σ, !cryptisG Σ},
     ⊢ {{{ True }}} mkchan #() {{{ c, RET c; channel c}}}) →
  rtc erased_step ([game mkchan], σ₁) (Val v :: ts, σ₂) →
  v = NONEV ∨ v = SOMEV #true.
Proof.
have ? : heapGpreS F by apply _.
move=> wp_mkchan.
apply (adequate_result NotStuck _ _ (λ v _, v = NONEV ∨ v = SOMEV #true)).
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisG_alloc _) as (?) "(_ & enc_tok & key_tok & hash_tok & _)".
iMod (sessionG_alloc _) as (?) "sess_tok".
iApply (wp_game with "[] [sess_tok] [enc_tok] [hash_tok] [key_tok]") => //.
iApply wp_mkchan.
Qed.
