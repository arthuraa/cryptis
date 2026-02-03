From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par ticket_lock assert.
From cryptis Require Import lib cryptis primitives tactics role adequacy.
From cryptis.lib Require Import term_set.
From cryptis.examples.nsl Require Import impl proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Section NSL.

Context `{!heapGS Σ, !cryptisGS Σ, !tlockG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (rl : role) (t nI nR sI sR kS : term).
Implicit Types (skI skR : aenc_key).

Definition check_key_secrecy : val := λ: "c" "sk",
  let: "guess" := recv "c" in
  assert: (~ eq_term "sk" "guess").

Definition do_init_loop : val := rec: "loop" "c" "set" "skI" "pkR" :=
  Fork ("loop" "c" "set" "skI" "pkR");;
  let: "pkR'" := recv "c" in
  (guard: is_aenc_key "pkR'" in
   bind: "sk" := init "c" "skI" "pkR'" in
   add_fresh_lock_term_set "sk" "set";;
   if: eq_term "pkR" "pkR'" then check_key_secrecy "c" "sk"
   else #());;
   #().

Definition do_init : val := λ: "c" "skI" "pkR",
  let: "set" := new_lock_term_set #() in
  do_init_loop "c" "set" "skI" "pkR".

Definition si_share_of rl :=
  if rl is Init then si_init_share else si_resp_share.

Definition nsl_game_inv rl t : iProp := ∃ si,
  ⌜t = si_key si⌝ ∧
  term_meta (si_share_of rl si) (nroot.@"fresh") ().

Lemma nsl_game_inv_fresh rl si E :
  ↑nroot.@"fresh" ⊆ E →
  term_token (si_share_of rl si) E -∗
  fresh_term (nsl_game_inv rl) (si_key si).
Proof.
iIntros "%sub token". iSplit.
- iIntros "(%si' & %e & #meta)".
  move/term_of_senc_key_inj/nsl_session_agree: e => <-.
  by iApply (term_meta_token with "token meta").
- iMod (term_meta_set (nroot.@"fresh") () with "token") as "#?" => //.
  iIntros "!> !>". iExists si. by eauto.
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
  minted skI -∗
  □ (public skI ↔ ▷ False) -∗
  □ (public skR ↔ ▷ False) -∗
  is_lock_term_set (nsl_game_inv Init) vset -∗
  {{{ True }}}
    do_init_loop c vset skI (Spec.pkey skR)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #m_skI #s_skI #s_skR #set".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ by iApply "IH" => //. }
wp_pures. wp_apply wp_recv => //.
iIntros (pkR') "#p_pkR'".
wp_pures. wp_apply wp_is_aenc_key => //.
{ by iApply public_minted. }
iSplit; last by wp_pures; iApply "Hpost".
iIntros "%skR' -> #m_skR'". wp_pures.
wp_apply wp_init as "%ts tsP" => //; first iFrame "#".
case: ts=> [sk|] => /=; wp_pures; last by iApply "Hpost".
iDestruct "tsP" as "[%|(%si & %e_sk & #s_sk & token)]" => //.
case: e_sk => ->.
iPoseProof (@nsl_game_inv_fresh Init with "token")
  as "fresh" => //; try solve_ndisj.
wp_apply (wp_add_fresh_lock_term_set with "[$]"). iIntros "_".
wp_eq_term e; wp_pures; last by iApply "Hpost".
move: e => /Spec.aenc_pkey_inj <- {skR'}.
wp_apply wp_check_key_secrecy => //.
{ iIntros "!> #fail".
  iDestruct "s_sk" as "(_ & _ & _ & #s_sk)".
  iPoseProof ("s_sk" with "fail") as "{fail} fail".
  iModIntro. by iDestruct "fail" as "[fail|fail]";
  [iApply "s_skI"|iApply "s_skR"]. }
iIntros "_". wp_pures. by iApply "Hpost".
Qed.

Lemma wp_do_init c skI skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  minted skI -∗
  □ (public skI ↔ ▷ False) -∗
  □ (public skR ↔ ▷ False) -∗
  {{{ True }}}
    do_init c skI (Spec.pkey skR)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #m_skI #s_skI #s_skR %Φ _ !> post".
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
  minted skR -∗
  □ (public skR ↔ ▷ False) -∗
  □ (public skI ↔ ▷ False) -∗
  is_lock_term_set (nsl_game_inv Resp) set -∗
  {{{ True }}}
    do_resp_loop c set skR (Spec.pkey skI)
  {{{ RET #(); True }}}.
Proof.
iIntros "#chan #? #? #m_skR #s_skR #s_skI #set".
iLöb as "IH". iIntros "!> %Φ _ Hpost".
wp_rec; wp_pures; wp_apply wp_fork.
{ iApply "IH" => //. }
wp_smart_apply wp_resp as "%res res" => //; first iFrame "#".
case: res => [[ekI' sk]|]; wp_pures; last by iApply "Hpost".
iDestruct "res" as "[%|(%skI' & %si & %e & #res & token)]" => //.
case: e => -> -> {ekI' sk}.
iPoseProof (@nsl_game_inv_fresh Resp with "token")
  as "fresh" => //; try solve_ndisj.
wp_apply (wp_add_fresh_lock_term_set with "[$]"). iIntros "_".
wp_eq_term e; wp_pures; last by iApply "Hpost".
move: e => /Spec.aenc_pkey_inj <- {skI'}.
wp_apply wp_check_key_secrecy => //.
{ iIntros "!> #fail".
  iDestruct "res" as "(_ & _ & _ & #s_sk)".
  iPoseProof ("s_sk" with "fail") as "{fail} fail".
  iModIntro. by iDestruct "fail" as "[fail|fail]";
  [iApply "s_skI"|iApply "s_skR"]. }
iIntros "_". wp_pures. by iApply "Hpost".
Qed.

Lemma wp_do_resp c skI skR :
  channel c -∗
  cryptis_ctx -∗
  nsl_ctx -∗
  minted skR -∗
  □ (public skR ↔ ▷ False) -∗
  □ (public skI ↔ ▷ False) -∗
  {{{ True }}}
    do_resp c skR (Spec.pkey skI)
  {{{ RET #(); True }}}.
Proof.
iIntros "#? #? #? #? #? #? %Φ _ !> post".
wp_lam. wp_pures.
wp_apply (wp_new_lock_term_set (nsl_game_inv Resp)) => //.
iIntros "%set #set". wp_pures.
by wp_apply wp_do_resp_loop => //.
Qed.

Definition game : val := λ: "c",
  let: "skI" := mk_aenc_key #() in
  let: "skR" := mk_aenc_key #() in
  let: "pkI" := pkey "skI" in
  let: "pkR" := pkey "skR" in
  send "c" "pkI";;
  send "c" "pkR";;
  Fork (do_init "c" "skI" "pkR");;
  Fork (do_resp "c" "skR" "pkI").

Lemma wp_game c :
  cryptis_ctx -∗
  channel c -∗
  seal_pred_token AENC ⊤ -∗
  WP game c {{ _, True }}.
Proof.
iIntros "#ctx #chan enc_tok"; rewrite /game; wp_pures.
wp_pures. wp_apply (wp_mk_aenc_key with "[]"); eauto.
iIntros "%skI #m_skI secI tokenI".
wp_pures. wp_apply (wp_mk_aenc_key with "[]"); eauto.
iIntros "%skR #m_skR secR tokenR".
wp_pures. wp_apply wp_pkey. wp_pures. wp_apply wp_pkey. wp_pures.
iMod (freeze_secret with "secI") as "#?".
iMod (freeze_secret with "secR") as "#?".
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by iApply public_aenc_key.
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by iApply public_aenc_key.
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
  rtc erased_step ([run_network game], σ₁) (t₂, σ₂) →
  e₂ ∈ t₂ →
  not_stuck e₂ σ₂.
Proof.
have ? : heapGpreS F by apply _.
apply (adequate_not_stuck NotStuck _ _ (λ v _, True)) => //.
apply: cryptis_adequacy.
iIntros (? ? c) "#ctx #chan (aenc & _)".
by iApply (wp_game with "ctx chan [aenc]").
Qed.
