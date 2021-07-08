From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl namespace_map frac.
From iris.algebra Require Import numbers.
From iris.base_logic.lib Require Import auth.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import session challenge_response nsl dh nsl_dh tls13.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Game.

Context `{!cryptisG Σ, !heapG Σ, !spawnG Σ, !sessionG Σ}.
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

Definition environment : val := λ: "c" "ekI" "dkI" "ekR" "dkR",
  fork_loop (
    let: "pkR'" := recv "c" in
    bind: "pkR'" := to_ek "pkR'" in
    nsl_dh_init nslN "c" Spec.zero "dkI" "ekI" "pkR'");;
  fork_loop (nsl_dh_resp nslN "c" Spec.zero "dkR" "ekR");;
  fork_loop (cr_init crN "c" "ekI" "dkI" "dkR");;
  fork_loop (cr_resp crN "c" "ekR" "dkR").

Lemma wp_environment c γnsl γcr kI kR :
  channel c -∗
  nsl_dh_ctx nslN (λ _ _ _ _ _, True)%I Spec.zero γnsl -∗
  cr_ctx crN (λ _ _ _ _ _, True)%I γcr -∗
  pterm kI -∗
  pterm kR -∗
  {{{ True }}}
    environment c (TKey Enc kI) (TKey Dec kI) (TKey Enc kR) (TKey Dec kR)
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #? #? #? %Φ !> _ post".
rewrite /environment; wp_pures; rewrite -!fork_loopE.
iAssert (pterm (TKey Enc kI)) as "#?".
  by rewrite pterm_TKey; eauto.
iAssert (pterm (TKey Dec kI)) as "#?".
  by rewrite [pterm (TKey Dec _)]pterm_TKey; eauto.
iAssert (pterm (TKey Enc kR)) as "#?".
  by rewrite [pterm (TKey Enc kR)]pterm_TKey; eauto.
iAssert (pterm (TKey Dec kR)) as "#?".
  by rewrite [pterm (TKey Dec kR)]pterm_TKey; eauto.
wp_bind (fork_loop _); iApply wp_fork_loop; eauto.
  iModIntro.
  wp_bind (recv _); iApply wp_recv => //.
  iIntros "%pkR' #?"; wp_pures.
  wp_bind (to_ek _); iApply wp_to_ek.
  case: Spec.to_ekP => [? ->|_]; wp_pures => //.
  iApply (wp_nsl_dh_init _ (λ _ _ _ _ _, True)%I); eauto.
  by rewrite sterm_TInt.
iIntros "!> _"; wp_pures; wp_bind (fork_loop _); iApply wp_fork_loop => //.
  iModIntro.
  iApply (wp_nsl_dh_resp _ (λ _ _ _ _ _, True)%I); eauto.
  by rewrite sterm_TInt.
iIntros "!> _"; wp_pures; wp_bind (fork_loop _); iApply wp_fork_loop => //.
  by iModIntro; iApply (wp_cr_init); eauto.
iIntros "!> _"; wp_pures; iApply wp_fork_loop => //.
by iModIntro; iApply (wp_cr_resp); eauto.
Qed.

Definition game : val := λ: "mkchan",
  let: "c"    := "mkchan" #() in
  let: "nI"   := mknonce #() in
  let: "nR"   := mknonce #() in
  let: "psk" := mknonce #() in
  let: "kI" := mkkey (tag (nroot.@"key") "nI") in
  let: "kR" := mkkey (tag (nroot.@"key") "nR") in
  let: "ekI" := Fst "kI" in
  let: "dkI" := Snd "kI" in
  let: "ekR" := Fst "kR" in
  let: "dkR" := Snd "kR" in
  send "c" "ekI";;
  send "c" "ekR";;
  send "c" "dkI";;
  send "c" "dkR";;
  environment "c" "ekI" "dkI" "ekR" "dkR";;
  let: "param_client" := recv "c" in
  let: "param_server" := recv "c" in
  let: "m" := Meth.I.PskDh "psk" Spec.zero in
  let: "res" := tls_client tlsN "c" "m" "param_client" |||
                tls_server tlsN "c" "psk" Spec.zero "nR" "param_server" in
  bind: "resI" := Fst "res" in
  bind: "resR" := Snd "res" in
  let: "skI"   := Fst (mkkey (Snd "resI")) in
  let: "m" := recv "c" in
  SOME (~ eq_term "m" "skI").

Lemma wp_game (mkchan : val) :
  {{{ True }}} mkchan #() {{{ v, RET v; channel v }}} -∗
  enc_pred_token ⊤ -∗
  hash_pred_token ⊤ -∗
  key_pred_token ⊤ -∗
  WP game mkchan {{ v, ⌜v = NONEV ∨ v = SOMEV #true⌝ }}.
Proof.
iIntros "wp_mkchan enc_tok hash_tok key_tok"; rewrite /game; wp_pures.
rewrite (enc_pred_token_difference (↑nslN)) //.
iDestruct "enc_tok" as "[nsl_tok enc_tok]".
iMod (nsl_dh_alloc nslN (λ _ _ _ _ _, True)%I Spec.zero with "nsl_tok")
  as (γnsl) "#nsl_ctx" => //.
rewrite (enc_pred_token_difference (↑crN)); last solve_ndisj.
iDestruct "enc_tok" as "[cr_tok enc_tok]".
iMod (cr_alloc crN (λ _ _ _ _ _, True)%I with "cr_tok")
  as (γcr) "#cr_ctx"; eauto.
rewrite (enc_pred_token_difference (↑tlsN)); last solve_ndisj.
iDestruct "enc_tok" as "[tls_enc_tok _]".
rewrite (key_pred_token_difference (↑tlsN)); last solve_ndisj.
iDestruct "key_tok" as "[tls_key_tok key_tok]".
rewrite (hash_pred_token_difference (↑tlsN)); last solve_ndisj.
iDestruct "hash_tok" as "[tls_hash_tok _]".
iMod (tls_ctx_alloc tlsN with "tls_enc_tok tls_hash_tok tls_key_tok")
  as (γtls) "#tls_ctx"; eauto.
iMod (key_pred_set (nroot.@"key") (λ kt _, ⌜kt = Enc⌝)%I with "key_tok")
  as "#?"; try solve_ndisj.
wp_bind (mkchan _); iApply "wp_mkchan" => //.
iIntros "!> %c #cP".
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (λ _, True)%I (λ _, False%I)).
iIntros (kI) "#t_kI #p_kI _ tok_kI".
iAssert (pterm kI) as "{p_kI} p_kI"; first by iApply "p_kI".
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (λ _, True)%I (λ _, False%I)).
iIntros (kR) "#t_kR #p_kR _ tok_kR".
iAssert (pterm kR) as "{p_kR} p_kR"; first by iApply "p_kR".
wp_pures; wp_bind (mknonce _).
iApply (wp_mknonce _ (λ psk, nonce_meta psk (nroot.@"pub") ())%I (λ _, False%I)).
iIntros (psk) "#t_psk #p_psk _ tok_psk".
wp_pures; wp_tag; wp_bind (mkkey _); iApply wp_mkkey.
set ekI := TKey Enc _.
set dkI := TKey Dec _.
wp_pures; wp_tag; wp_bind (mkkey _); iApply wp_mkkey.
set ekR := TKey Enc _.
set dkR := TKey Dec _.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by rewrite pterm_TKey pterm_tag; eauto.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by rewrite pterm_TKey pterm_tag; eauto.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by rewrite pterm_TKey pterm_tag; eauto.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by rewrite pterm_TKey pterm_tag; eauto.
wp_pures; wp_bind (environment _ _ _ _ _).
iApply wp_environment; eauto.
- by rewrite pterm_tag.
- by rewrite pterm_tag.
iIntros "!> _"; wp_pures.
wp_bind (recv _); iApply wp_recv => //.
iIntros "%param_client #p_pc"; wp_pures.
wp_bind (recv _); iApply wp_recv => //.
iIntros "%param_server #p_ps"; wp_pures.
wp_pures; wp_bind (Meth.I.PskDh _ _).
iApply Meth.wp_PskDh => //.
iIntros "!> % ->"; wp_pures.
wp_bind (par _ _).
iApply (wp_par (λ v, ∃ a : option (term * term * term * term), ⌜v = repr a⌝ ∗ _)%I
               (λ v, ∃ a : option SShare.t, ⌜v = repr (SShare.term_of <$> a)⌝ ∗ _)%I
          with "[] []").
- iApply (wp_tls_client c _ (Meth.PskDh psk Spec.zero)) => //.
    rewrite /= pterm_TInt; iSplit => //.
  iIntros (res) "H"; iExists res; iSplit; first done.
  iApply "H".
- iApply (wp_tls_server c) => //.
  + by rewrite pterm_TInt.
  + by rewrite sterm_TKey.
  + by rewrite pterm_TKey; eauto.
  + iIntros (res) "H"; iExists res; iSplit; first done.
    iApply "H".
iAssert ((pterm psk → ▷ False) ∧ |==> pterm psk)%I
  with "[tok_psk]" as "{p_psk} p_psk"; first iSplit.
- iIntros "#p_psk'".
  iSpecialize ("p_psk" with "p_psk'").
  iModIntro.
  iDestruct "p_psk" as "#p_psk".
  by iApply (term_meta_meta_token with "tok_psk p_psk").
- iMod (term_meta_set _ _ () (nroot.@"pub") with "tok_psk") as "#?" => //.
  by iModIntro; iApply "p_psk"; eauto.
iIntros (v1 v2) "[H1 H2]".
iDestruct "H1" as (res1) "[-> H1]".
iDestruct "H2" as (res2) "[-> H2]".
iModIntro; wp_pures.
case: res1 => [res1|]; wp_pures; last by eauto.
case: res2 => [res2|]; wp_pures; last by eauto.
case: res1 => [] [] [] vkey cn sn sk /=.
iDestruct "H1" as (vk) "(-> & _ & _ & _ & _ & #sessII & H1)".
iDestruct "H2" as "(_ & _ & #sessRR & H2)".
wp_bind (mkkey _); iApply wp_mkkey; wp_pures.
wp_bind (recv _); iApply wp_recv => //.
iIntros (m) "#p_m"; wp_let.
iDestruct "H1" as "[[_ contra]|[_ #H1]]".
  iDestruct "p_psk" as "[p_psk _]".
  by iDestruct ("p_psk" with "contra") as ">[]".
wp_bind (eq_term _ _); iApply wp_eq_term.
case: bool_decide_reflect => [->|?]; last by wp_pures; eauto.
by iDestruct ("H1" with "p_m") as ">[]".
Qed.

End Game.

Definition F : gFunctors :=
  #[heapΣ; spawnΣ; cryptisΣ; sessionΣ].

Lemma nsl_dh_secure (mkchan : val) σ₁ σ₂ (v : val) ts :
  (∀ `{!heapG Σ, !cryptisG Σ},
     ⊢ {{{ True }}} mkchan #() {{{ c, RET c; channel c}}}) →
  rtc erased_step ([game mkchan], σ₁) (Val v :: ts, σ₂) →
  v = NONEV ∨ v = SOMEV #true.
Proof.
have ? : heapPreG F by apply _.
move=> wp_mkchan.
apply (adequate_result NotStuck _ _ (λ v _, v = NONEV ∨ v = SOMEV #true)).
apply: heap_adequacy.
iIntros (?) "?".
iMod (cryptisG_alloc _) as (?) "(enc_tok & key_tok & hash_tok)".
iApply (wp_game with "[] [enc_tok] [hash_tok] [key_tok]") => //.
iApply wp_mkchan.
Qed.
