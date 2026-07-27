(* TLS 1.3 handshake — CShare (client share) proofs.

   WP specs for the [CShare.I] constructors, the [CShare_wf] well-formedness
   invariant and its public-encoding lemma, plus [wp_CShare_new] and the
   [CShare_check_Some] soundness lemma.  Depends on impl + base + meth. *)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.lib Require Import dh.
From cryptis.examples.tls13 Require Import impl.
From cryptis.examples.tls13.proofs Require Import base meth.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import CShare.

Section Proofs.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

Lemma wp_CShare_case ke (f_psk f_dh f_pskdh : val) E Φ :
  match ke with
  | Psk psk cn => WP f_psk psk cn @ E {{ Φ }}
  | Dh g cn x => WP f_dh g cn x @ E {{ Φ }}
  | PskDh psk g cn x => WP f_pskdh psk g cn x @ E {{ Φ }}
  end -∗
  WP I.case (term_of ke) f_psk f_dh f_pskdh @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.case.
wp_untag_eq psk e_psk.
  case: ke e_psk => [??|???|????] /= /Spec.tag_inj []; try set_solver.
  move=> _ <-; wp_pures; do !rewrite subst_list_match /=.
  wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
  move/Spec.of_list_inj: e_l => {l} <-.
  by wp_list_match => // _ _ [<- <-].
wp_untag_eq args e_dh.
  case: ke e_psk e_dh => [??|g cn x|????] /= e_psk /Spec.tag_inj []; try set_solver.
  move=> _ <- {e_psk args}; wp_pures; do !rewrite subst_list_match /=.
  wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
  move/Spec.of_list_inj: e_l => {l} <-.
  by wp_list_match => // _ _ _ [<- <- <-].
wp_untag_eq args e_pskdh; last first.
  by case: ke e_psk e_dh e_pskdh =>> /=; rewrite Spec.tagK.
case: ke e_psk e_dh e_pskdh
  => [??|???|psk g cn x] /= e_psk e_dh /Spec.tag_inj []; try set_solver.
move=> _ <- {e_psk e_dh args}; wp_pures; do !rewrite subst_list_match /=.
wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
move/Spec.of_list_inj: e_l => {l} <-.
by wp_list_match => // _ _ _ _ [<- <- <- <-].
Qed.

Lemma wp_CShare_encode N ke E Φ :
  Φ (term_of (encode N ke)) -∗
  WP I.encode N (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.encode; wp_pures.
iApply wp_CShare_case.
case: ke => [psk c_nonce|g cn x|psk g cn x] /=; wp_pures.
- by wp_list; wp_tag; wp_hash; wp_list; wp_term_of_list; wp_tag.
- wp_bind (texp _ _); iApply wp_texp; wp_pures.
  wp_list; wp_term_of_list.
  by iApply wp_tag.
- wp_bind (texp _ _); iApply wp_texp; wp_pures.
  wp_list; wp_tag; wp_hash; wp_list; wp_term_of_list.
  by iApply wp_tag.
Qed.

Lemma wp_CShare_psk ke E Φ :
  Φ (psk ke) -∗
  WP I.psk (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.psk; wp_pures.
iApply wp_CShare_case.
by case: ke => [psk ?|? ? ?|psk ? ? ?]; wp_pures.
Qed.

Lemma wp_CShare_of_term ke E Φ :
  Φ (repr (term_of <$> of_term ke)) -∗
  WP I.of_term ke @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /term_of /of_term.
rewrite /I.of_term /=; wp_pures.
wp_untag_eq args e; wp_pures.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq args' e; wp_pures; last by rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [?? -> {args'} | neq]; wp_finish; last first.
    by rewrite prod_of_list_neq.
  by rewrite unlock /=; wp_pures.
rewrite {}e.
wp_untag_eq args e; wp_pures.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq args' e; wp_pures; last by rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [??? -> {args'} | neq]; wp_finish; last first.
    by rewrite prod_of_list_neq.
  by rewrite unlock /=; wp_pures.
rewrite {}e.
wp_untag_eq args e; wp_pures.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq args' e; wp_pures; last by rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [???? -> {args'} | neq]; wp_finish; last first.
    by rewrite prod_of_list_neq.
  by rewrite unlock /=; wp_pures.
by rewrite {}e.
Qed.

Lemma wp_CShare_check N psk g ke E Φ :
  Φ (repr (term_of <$> check N psk g ke)) -∗
  WP I.check N psk g (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.check; wp_pures.
iApply wp_CShare_case.
case: ke => [psk' cn|g' cn gx|psk' g' cn gx] //=; wp_pures => //.
- wp_tag; wp_hash; wp_eq_term e; wp_pures; try by rewrite decide_False.
  wp_list; wp_term_of_list; wp_tag; wp_pures.
  by rewrite decide_True //=.
- wp_eq_term e; wp_pures; try by rewrite decide_False.
  wp_list; wp_term_of_list; wp_tag; wp_pures.
  by rewrite e decide_True.
- wp_tag; wp_hash; wp_eq_term e; wp_pures; last first.
    rewrite decide_False //; intuition congruence.
  rewrite {}e; wp_eq_term e; wp_pures; last first.
    rewrite decide_False //; intuition congruence.
  wp_list; wp_term_of_list; wp_tag; wp_pures.
  by rewrite decide_True //=.
Qed.

Definition CShare_wf ke : iProp :=
  match ke with
  | Psk psk cn =>
    minted psk ∧ public cn
  | Dh g cn x  =>
    ⌜¬ is_exp g⌝ ∧ public g ∧ public cn ∧ dh_seed (λ _, True)%I x
  | PskDh psk g cn x =>
    minted psk ∧
    ⌜¬ is_exp g⌝ ∧ public g ∧ public cn ∧ dh_seed (λ _, True)%I x
  end.

#[global]
Instance CShare_Persistent_wf ke : Persistent (CShare_wf ke).
Proof. case: ke => *; apply _. Qed.

Lemma CShare_wf_psk ke : CShare_wf ke -∗ minted (psk ke).
Proof.
case: ke => [psk ?|???|psk ???] /=.
- by iIntros "(? & ?)".
- by iIntros "_"; rewrite minted_TInt.
- by iIntros "(? & ? & ? & ?)".
Qed.

Lemma CShare_wf_encode N ke :
  Keys.ctx N -∗
  CShare_wf ke -∗
  public (term_of (encode N ke)).
Proof.
iIntros "#hash #wf".
case: ke => [psk cn|g cn x|psk g cn x] //=.
- iDestruct "wf" as "[??]".
  rewrite public_tag public_of_list /=; do !iSplit => //.
  rewrite public_THash minted_tag; iRight; iSplit => //.
  by iExists _, _, _; eauto.
- iDestruct "wf" as "(% & ? & ? & ?)".
  rewrite public_tag public_of_list /=.
  do !iSplit => //.
  by iApply dh_public_TExp; eauto.
- iDestruct "wf" as "(? & % & ? & ? & ?)".
  rewrite public_tag public_of_list /=.
  do !iSplit => //.
    rewrite public_THash minted_tag; iRight; iSplit => //.
    by iExists _, _, _; eauto.
  by iApply dh_public_TExp; eauto.
Qed.

Lemma wp_CShare_new ke Φ :
  cryptis_ctx -∗
  Meth_wf ke -∗
  (∀ ke', ⌜ke = meth_of ke'⌝ -∗
          CShare_wf ke' -∗
          term_token (cnonce ke') ⊤ -∗
          Φ (term_of ke')) -∗
  WP I.new ke {{ Φ }}.
Proof.
iIntros "#? #p_ke post"; rewrite /I.new; wp_pures.
iApply wp_Meth_case; case: ke => [psk|g|psk g]; wp_pures.
- wp_bind (mk_nonce _); iApply (wp_mk_nonce (λ _, True)%I (λ _, True)%I) => //.
  iIntros (cn) "_ #p_cn _ _ token"; wp_list; wp_term_of_list.
  wp_tag.
  iApply ("post" $! (Psk psk cn) with "[] [] token") => //=.
  do !iSplit => //.
  by iApply "p_cn".
- iDestruct "p_ke" as "[% p_ke]".
  wp_bind (mk_dh _); iApply (wp_mk_dh (λ _, True)%I ∅ _) => //.
  + by iApply public_minted.
  + by iIntros "!> %"; rewrite elem_of_empty; iIntros ([]).
  iIntros (a) "_ #p_a _ _ _"; wp_list.
  wp_bind (mk_nonce _); iApply (wp_mk_nonce (λ _, True)%I (λ _, True)%I) => //.
  iIntros (cn) "_ #p_cn _ _ token"; wp_list; wp_term_of_list.
  wp_tag.
  rewrite (term_token_difference _ ⊤); try set_solver.
  iDestruct "token" as "[token _]".
  iApply ("post" $! (Dh g cn a)) => //=.
  do !iSplit => //.
  by iApply "p_cn".
- iDestruct "p_ke" as "(? & % & ?)".
  wp_bind (mk_dh _); iApply (wp_mk_dh (λ _, True)%I ∅ _) => //.
  + by iApply public_minted.
  + iIntros "!> %"; rewrite elem_of_empty; iIntros "[]".
  iIntros (a) "_ #p_a _ _ _"; wp_list.
  wp_bind (mk_nonce _); iApply (wp_mk_nonce (λ _, True)%I (λ _, True)%I) => //.
  iIntros (cn) "_ #p_cn _ _ token"; wp_list; wp_term_of_list.
  wp_tag.
  iApply ("post" $! (PskDh psk g cn a)) => //=.
  do !iSplit => //.
  by iApply "p_cn".
Qed.

Lemma CShare_check_Some N psk g ke ke' :
  check N psk g ke = Some ke' →
  ke = encode' N ke' ∧
  Meth.compatible psk g (meth_of ke').
Proof.
case: ke =>> /=.
- by case: decide => [->|//] [<-].
- by case: decide => [->|//] [<-].
- by case: decide => [[-> ->]|//] [<-].
Qed.

End Proofs.

#[global]
Existing Instance CShare_Persistent_wf.
