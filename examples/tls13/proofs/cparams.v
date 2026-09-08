(* TLS 1.3 handshake — CParams (client parameters / ClientHello) proofs.

   WP specs for [CParams.I.hello] / [CParams.I.check], the [CParams_wf]
   invariant, the binder-hash context ([CParams_ctx] / [CParams_ctx_alloc])
   and the [CParams_public_checkE] soundness lemma.  Depends on
   impl + base + meth + cshare. *)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.lib Require Import dh.
From cryptis.examples.tls13 Require Import impl.
From cryptis.examples.tls13.proofs Require Import base meth cshare.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import CParams.

Section Proofs.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

Lemma wp_CParams_hello N cp E Φ :
  Φ (hello N cp) -∗
  WP I.hello N (term_of cp) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.hello; wp_pures.
wp_list_of_term_eq t e; last by rewrite Spec.of_listK in e.
move/Spec.of_list_inj: e => <-.
wp_list_match => // _ _ [] <- <-.
wp_list; wp_bind (CShare.I.encode _ _); iApply wp_CShare_encode.
wp_list; wp_term_of_list; wp_pures.
wp_bind (CShare.I.psk _); iApply wp_CShare_psk.
wp_pures; wp_list; wp_term_of_list; wp_tag; wp_hash.
by wp_pures; wp_list; iApply wp_term_of_list.
Qed.

Lemma wp_CParams_check N psk g other ch E Φ :
  Φ (repr (CShare.term_of <$> check N psk g other ch)) -∗
  WP I.check N psk g other ch @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /check /I.check.
wp_pures.
wp_list_of_term_eq l e; wp_pures; last by rewrite e.
rewrite {}e Spec.of_listK /=.
wp_list_match => [ch' mac -> {l}|ne]; wp_finish; last first.
  by rewrite prod_of_list_neq.
rewrite [in prod_of_list _ [ch'; mac]]unlock /=.
wp_list_of_term_eq l e; wp_pures; last by rewrite e.
rewrite {}e Spec.of_listK /=.
wp_list_match => [ke other' -> {l}|neq]; wp_finish; last first.
  by rewrite prod_of_list_neq.
rewrite [in prod_of_list _ [ke; other']]unlock /=.
wp_bind (CShare.I.of_term _); iApply wp_CShare_of_term.
case e: CShare.of_term => [ke'|] //=; wp_pures => //.
wp_bind (CShare.I.check _ _ _ _); iApply wp_CShare_check.
case: CShare.check => [c_ke|] /=; wp_pures => //.
wp_bind (CShare.I.psk _); iApply wp_CShare_psk; wp_pures.
wp_list; wp_term_of_list; wp_tag; wp_hash.
wp_eq_term e'; wp_pures; last first.
  rewrite decide_False //; intuition congruence.
rewrite {}e' {other'}.
wp_eq_term e'; wp_pures; last first.
  rewrite decide_False //; intuition congruence.
by rewrite {}e' decide_True //.
Qed.

Definition CParams_wf N cp : iProp :=
  CShare_wf (share cp) ∧
  term_meta (CShare.cnonce (share cp)) (N.@"binder") (other cp) ∧
  public (other cp).

#[global]
Instance CParams_wf_persistent N cp : Persistent (CParams_wf N cp).
Proof. apply _. Qed.

Lemma CParams_wf_set N cp :
  CShare_wf (share cp) -∗
  term_token (CShare.cnonce (share cp)) (↑N.@"binder") -∗
  public (other cp) ==∗
  CParams_wf N cp.
Proof.
iIntros "#? token #?".
iMod (term_meta_set _ (other cp) with "token") as "meta"; eauto.
by iModIntro; do !iSplit.
Qed.

Definition CParams_binder_inv N m : iProp :=
  ∃ cp, ⌜m = Spec.of_list [CShare.psk (share cp);
                           hello_pub N cp]⌝ ∧
        ⌜CShare.has_psk (share cp)⌝ ∧
        CParams_wf N cp.

Definition CParams_ctx N : iProp :=
  Keys.ctx N ∧
  hash_pred (N.@"binder") (CParams_binder_inv N).

#[global]
Instance CParams_ctx_persistent N : Persistent (CParams_ctx N).
Proof. apply _. Qed.

Lemma CParams_ctx_alloc N E E' :
  ↑N.@"binder" ⊆ E →
  Keys.ctx N -∗
  hash_pred_token E ={E'}=∗
  CParams_ctx N ∗
  hash_pred_token (E ∖ ↑N.@"binder").
Proof.
iIntros (?) "#? token".
iMod (hash_pred_set (N.@"binder") (CParams_binder_inv N) with "token") as "[??]"; eauto.
iFrame. by iModIntro.
Qed.

Lemma CParams_public_hello N cp : CParams_ctx N -∗ CParams_wf N cp -∗ public (hello N cp).
Proof.
iIntros "#[ctx binder] # (wf_cp & meta & p_cp)".
iAssert (public (hello_pub N cp)) as "p_pub".
  rewrite public_of_list /=; do !iSplit => //.
  by iApply CShare_wf_encode.
rewrite [public (hello _ _)]public_of_list /=; do ![iSplit => //].
case e: (CShare.has_psk (share cp)); last first.
  rewrite public_THash; iLeft; rewrite public_tag public_of_list /=.
  do ![iSplit => //].
  case: (share cp) e => //= > _; by rewrite public_TInt.
rewrite public_THash; iRight; rewrite minted_tag minted_of_list /=.
do !iSplit; eauto; first by iApply CShare_wf_psk.
iExists _, _, _; do !iSplit => //; eauto.
iExists cp; iModIntro; do !iSplit => //.
by rewrite e.
Qed.

Lemma CParams_public_checkE N psk g other ch ke :
  check N psk g other ch = Some ke →
  CParams_ctx N -∗
  public ch -∗
  ⌜Meth.compatible psk g (CShare.meth_of ke)⌝ ∧
  public (CShare.encode' N ke) ∧
  ▷ (public (CShare.psk ke) ∨
     ⌜CShare.has_psk ke⌝ ∧
     ∃ ke', ⌜CShare.encode' N ke = CShare.encode N ke'⌝ ∧
            CShare_wf ke' ∧
            term_meta (CShare.cnonce ke') (N.@"binder") other).
Proof.
rewrite /check.
case: Spec.to_listP=> //= {}ch.
elim/(list_len_rect 2): ch => [ch mac|ch neq]; last first.
  by rewrite prod_of_list_neq.
rewrite [in prod_of_list _ _]unlock /=.
case: Spec.to_listP=> //= {}ch.
elim/(list_len_rect 2): ch => [ke' other'|ch neq]; last first.
  by rewrite prod_of_list_neq.
rewrite unlock /=.
case e_of_term: CShare.of_term => [ke''|] //=.
move: ke'' e_of_term => {}ke' /CShare.of_termK ->.
case e_check: CShare.check => [c_ke|] //= e.
move: c_ke e_check => {}ke' /CShare_check_Some [-> comp] in e *.
case: decide e => [[-> <-]|//] /= [<-].
iIntros "#(_ & binder_ctx) #p_ch"; iSplit => //.
do ![rewrite public_of_list /=]; rewrite public_THash public_tag.
iDestruct "p_ch" as  "((p_ke' & _) & p_ch & _)"; iSplit => //.
iDestruct "p_ch" as "[fail|succ]".
  do ![rewrite public_of_list /=].
  by iDestruct "fail" as "(fail & _ & _)"; eauto.
iDestruct "succ" as "[s_binder wf]".
iDestruct (wf_hash_elim with "wf binder_ctx") as "{wf} #wf".
iModIntro; iRight.
iDestruct "wf" as (cp) "(%e & psk & wf)".
case/Spec.of_list_inj: e => e_psk /Spec.of_list_inj [e_encode ->].
move/CShare.term_of_inj in e_encode.
iSplit; first by case: (ke') e_encode =>>; case: (share cp).
iExists (share cp); iSplit=> //.
by iDestruct "wf" as "(? & ? & ?)"; eauto.
Qed.

End Proofs.

#[global]
Existing Instance CParams_wf_persistent.
#[global]
Existing Instance CParams_ctx_persistent.
