(* TLS 1.3 handshake — SShare (server share) proofs.

   WP specs for the [SShare.I] constructors, the [SShare_wf] invariant, the
   session-key/cnonce/snonce/public lemmas and the [SShare_public_checkE]
   soundness lemma.  Uses [TExp2_TExpN] from cryptis.lib.dh.  Depends on
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

Import SShare.

Section Proofs.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

Lemma wp_SShare_case ke (f_psk f_dh f_pskdh : val) E Φ :
  match ke with
  | Psk psk c_nonce s_nonce => WP f_psk psk c_nonce s_nonce @ E {{ Φ }}
  | Dh g cn sn x y => WP f_dh g cn sn x y @ E {{ Φ }}
  | PskDh psk g cn sn x y => WP f_pskdh psk g cn sn x y @ E {{ Φ }}
  end -∗
  WP I.case (term_of ke) f_psk f_dh f_pskdh @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.case.
wp_untag_eq psk e_psk.
  case: ke e_psk => [???|?????|??????] /= /Spec.tag_inj []; try set_solver.
  move=> _ <-; wp_pures; do !rewrite subst_list_match /=.
  wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
  move/Spec.of_list_inj: e_l => {l} <-.
  by wp_list_match => // _ _ _ [<- <- <-].
wp_untag_eq args e_dh.
  case: ke e_psk e_dh => [???|g cn sn x y|??????] /= e_psk /Spec.tag_inj [];
    try set_solver.
  move=> _ <- {e_psk args}; wp_pures; do !rewrite subst_list_match /=.
  wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
  move/Spec.of_list_inj: e_l => {l} <-.
  by wp_list_match => // _ _ _ _ _ [<- <- <- <- <-].
wp_untag_eq args e_pskdh; last first.
  by case: ke e_psk e_dh e_pskdh =>> /=; rewrite Spec.tagK.
case: ke e_psk e_dh e_pskdh
  => [???|?????|psk g cn sn x y] /= e_psk e_dh /Spec.tag_inj []; try set_solver.
move=> _ <- {e_psk e_dh args}; wp_pures; do !rewrite subst_list_match /=.
wp_list_of_term_eq l e_l; last by rewrite Spec.of_listK in e_l.
move/Spec.of_list_inj: e_l => {l} <-.
by wp_list_match => // _ _ _ _ _ _ [<- <- <- <- <- <-].
Qed.

Lemma wp_SShare_cnonce ke E Φ :
  Φ (cnonce ke) -∗
  WP I.cnonce (term_of ke) @ E {{ Φ }}.
Proof.
rewrite /I.cnonce; iIntros "post"; wp_pures.
by iApply wp_SShare_case; case: ke =>>; wp_pures.
Qed.

Lemma wp_SShare_snonce ke E Φ :
  Φ (snonce ke) -∗
  WP I.snonce (term_of ke) @ E {{ Φ }}.
Proof.
rewrite /I.snonce; iIntros "post"; wp_pures.
by iApply wp_SShare_case; case: ke =>>; wp_pures.
Qed.

Lemma wp_SShare_encode N ke E Φ :
  Φ (term_of (encode N ke)) -∗
  WP I.encode N (term_of ke) @ E {{ Φ }}.
Proof.
iIntros "post"; rewrite /I.encode; wp_pures.
iApply wp_SShare_case.
case: ke => [psk c_nonce s_nonce|g cn sn gx y|psk g cn sn gx y] /=; wp_pures.
- wp_tag; wp_hash.
  by wp_list; wp_term_of_list; wp_tag.
- wp_bind (texp _ _); iApply wp_texp; wp_pures.
  wp_list; wp_term_of_list.
  by iApply wp_tag.
- wp_tag; wp_hash; wp_pures.
  wp_bind (texp _ _); iApply wp_texp; wp_pures.
  wp_list; wp_term_of_list.
  by iApply wp_tag.
Qed.

Lemma wp_SShare_session_key_of ke Φ :
  Φ (session_key_of ke) -∗
  WP I.session_key_of (term_of ke) {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.session_key_of; wp_pures.
iApply wp_SShare_case.
case: ke => [???|?????|??????]; wp_pures.
- by wp_list; wp_term_of_list; wp_apply wp_derive_senc_key.
- by wp_bind (texp _ _); iApply wp_texp; wp_apply wp_derive_senc_key.
- wp_list; wp_bind (texp _ _); iApply wp_texp; wp_list; wp_term_of_list.
  by wp_apply wp_derive_senc_key.
Qed.

Lemma wp_SShare_session_key_of' ke Φ :
  Φ (session_key_of' ke) -∗
  WP I.session_key_of' (term_of ke) {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.session_key_of'; wp_pures.
iApply wp_SShare_case.
case: ke => [???|?????|??????]; wp_pures.
- by wp_list; wp_term_of_list; wp_apply wp_derive_senc_key.
- by wp_bind (texp _ _); iApply wp_texp; wp_apply wp_derive_senc_key.
- wp_list; wp_bind (texp _ _); iApply wp_texp; wp_list; wp_term_of_list.
  by wp_apply wp_derive_senc_key.
Qed.

Lemma wp_SShare_check N c_kex s_kex E Φ :
  Φ (repr (term_of <$> check N c_kex s_kex)) -∗
  WP I.check N (CShare.term_of c_kex) s_kex @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.check; wp_pures.
iApply wp_CShare_case.
case: c_kex => [psk c_nonce|g cn x|psk g cn x] /=; wp_pures.
- wp_untag_eq s_kex' e; last by wp_pures; rewrite e.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq l e; last by wp_pures; rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [psk' c_nonce' s_nonce ->|ne] //=; wp_finish; last first.
    by rewrite prod_of_list_neq //=.
  rewrite unlock /=.
  wp_tag; wp_hash; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite e decide_True //; wp_pures.
  wp_list; wp_term_of_list; wp_pures.
  wp_tag.
  by wp_list; wp_pures.
- wp_untag_eq s_kex' e; last by wp_pures; rewrite e.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq l e; last by wp_pures; rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [g' cn' sn gx gy ->|ne] //=; wp_finish; last first.
    by rewrite prod_of_list_neq //=.
  rewrite [in prod_of_list _ _]unlock /=.
  wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_pures.
  wp_bind (texp _ _); iApply wp_texp.
  wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite e decide_True //; wp_pures.
  wp_list; wp_term_of_list.
  wp_tag; wp_pures.
  by iModIntro.
- wp_untag_eq s_kex' e; last by wp_pures; rewrite e.
  rewrite {}e Spec.tagK /=.
  wp_list_of_term_eq l e; last by wp_pures; rewrite e.
  rewrite {}e Spec.of_listK /=.
  wp_list_match => [psk' g' cn' sn gx gy ->|ne] //=; wp_finish; last first.
    by rewrite prod_of_list_neq //=.
  rewrite [in prod_of_list _ _]unlock /=.
  wp_tag; wp_hash; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite {}e; wp_pures.
  wp_bind (texp _ _); iApply wp_texp.
  wp_eq_term e; last first.
    rewrite decide_False; try by intuition congruence.
    by wp_pures.
  rewrite e decide_True //; wp_pures.
  wp_list; wp_term_of_list.
  wp_tag; wp_pures.
  by iModIntro.
Qed.

Definition SShare_wf ke : iProp :=
  match ke with
  | Psk psk c_nonce s_nonce =>
    minted psk ∧ public c_nonce ∧ public s_nonce
  | Dh g cn sn gx y =>
    ⌜negb (is_exp g)⌝ ∧ public g ∧ public cn ∧ public sn ∧ public gx ∧
    ⌜∀ x, subterm x gx → y ≠ x ∧ y ≠ TInv x⌝ ∧
    dh_seed (λ _, True)%I y
  | PskDh psk g cn sn gx y =>
    minted psk ∧
    ⌜negb (is_exp g)⌝ ∧ public g ∧ public cn ∧ public sn ∧
    public gx ∧
    ⌜∀ x, subterm x gx → y ≠ x ∧ y ≠ TInv x⌝ ∧
    dh_seed (λ _, True)%I y
  end.

#[global]
Instance SShare_Persistent_wf ke : Persistent (SShare_wf ke).
Proof. case: ke => *; apply _. Qed.

Lemma wp_SShare_new N psk g (ke : CShare.t) Φ :
  negb (is_exp g) →
  Meth.compatible psk g (CShare.meth_of ke) →
  cryptis_ctx -∗
  minted psk -∗
  public g -∗
  public (CShare.encode' N ke) -∗
  (∀ ke',
      ⌜ke = cshare_of ke'⌝ -∗
      SShare_wf ke' -∗
      term_token (snonce ke') ⊤ -∗
      Φ (term_of ke')) -∗
  WP I.new ke {{ Φ }}.
Proof.
iIntros (gXN e_check) "#? #s_psk #p_g #p_ke post"; rewrite /I.new; wp_pures.
iApply wp_CShare_case.
case: ke => [psk' cn|g' cn gx|psk' g' cn gx] /= in e_check *; wp_pures.
- subst psk.
  wp_bind (mk_nonce _); iApply (wp_mk_nonce (λ _, True)%I (λ _, True)%I) => //.
  iIntros (a) "_ #pred_a _ _ token"; wp_list; wp_term_of_list.
  wp_tag; iModIntro.
  iApply ("post" $! (Psk _ _ a)) => //=.
  rewrite public_tag public_of_list /=.
  iDestruct "p_ke" as "(_ & p_cn & _)".
  do !iSplit => //.
  by iApply "pred_a".
- subst g'.
  wp_bind (mk_dh _); iApply (wp_mk_dh (λ _, True)%I {[gx]} _) => //.
  + by iApply public_minted.
  + iIntros "!> %t"; iIntros (->%elem_of_singleton); rewrite !public_minted.
    rewrite minted_tag minted_of_list /=.
    by iDestruct "p_ke" as "(_ & _ & ? & _)".
  iIntros (a) "_ #pred_a _ _ %fresh_a"; wp_list.
  have {}fresh_a: ∀ t, subterm t gx → a ≠ t ∧ a ≠ TInv t.
    by move=> t; apply: fresh_a; set_solver.
  wp_bind (mk_nonce _); iApply (wp_mk_nonce (λ _, True)%I (λ _, True)%I) => //.
  iIntros (sn) "_ #p_sn _ _ token"; wp_list; wp_term_of_list.
  wp_tag; iModIntro.
  iApply ("post" $! (Dh g cn sn gx a)) => //=.
  rewrite !public_tag !public_of_list /=.
  iDestruct "p_ke" as "(? & ? & ? & _)".
  do !iSplit => //.
  by iApply "p_sn".
- case: e_check=> -> ->.
  wp_bind (mk_dh _); iApply (wp_mk_dh (λ _, True)%I {[gx]} _) => //.
  + by iApply public_minted.
  + iIntros "!> %t"; iIntros (->%elem_of_singleton); rewrite !public_minted.
    rewrite minted_tag minted_of_list /=.
    by iDestruct "p_ke" as "(_ & _ & _ & ? & _)".
  iIntros (a) "_ #pred_a _ _ %fresh_a"; wp_list.
  have {}fresh_a: ∀ t, subterm t gx → a ≠ t ∧ a ≠ TInv t.
    by move=> t; apply: fresh_a; set_solver.
  wp_bind (mk_nonce _); iApply (wp_mk_nonce (λ _, True)%I (λ _, True)%I) => //.
  iIntros (sn) "_ #p_sn _ _ token"; wp_list; wp_term_of_list.
  wp_tag; iModIntro.
  iApply ("post" $! (PskDh _ g cn sn gx a)) => //.
  rewrite !public_tag !public_of_list /=.
  iDestruct "p_ke" as "(? & ? & ? & ? & _)".
  do !iSplit => //.
  by iApply "p_sn".
Qed.

Lemma SShare_public_checkE N c_kex ke ke' :
  check N c_kex ke = Some ke' →
  c_kex = cshare_of ke' ∧ ke = term_of (encode' N ke').
Proof.
case: c_kex => [psk cn|g cn x|psk g cn x] /=.
- case: Spec.untagP => //= {}ke ->.
  case: Spec.to_listP=> //= {}ke.
  elim/(@list_len_rect 3): ke => [psk' cn' sn|ke neq]; last first.
    by rewrite prod_of_list_neq.
  rewrite unlock /=; case: decide => //= - [] {psk' cn'} -> -> [] {ke'} <-.
  by split => //.
- case: Spec.untagP => //= {}ke ->.
  case: Spec.to_listP => //= {}ke.
  elim/(@list_len_rect 5): ke => [g' cn' sn gx gy|ke neq]; last first.
    by rewrite prod_of_list_neq.
  rewrite [in prod_of_list _ _]unlock /=; case: decide => //= - [] -> [] -> ->.
  case=> [] {ke'} <-.
  by split => //.
- case: Spec.untagP => //= {}ke ->.
  case: Spec.to_listP => //= {}ke.
  elim/(@list_len_rect 6): ke => [psk' g' cn' sn gx gy|ke neq]; last first.
    by rewrite prod_of_list_neq.
  rewrite [in prod_of_list _ _]unlock /=.
  case: decide => //= - [] -> [] -> [] -> -> [] {ke'} <-.
  by split.
Qed.

Lemma SShare_public_cnonce ke : public (term_of ke) -∗ public (cnonce ke).
Proof.
case: ke=> * /=; rewrite public_tag public_of_list /=.
- by iIntros "(? & ? & ?)".
- by iIntros "(? & ? & ?)".
- by iIntros "(? & ? & ? & ?)".
Qed.

Lemma SShare_public_snonce ke : public (term_of ke) -∗ public (snonce ke).
Proof.
case: ke=> * /=; rewrite public_tag public_of_list /=.
- by iIntros "(? & ? & ? & ?)".
- by iIntros "(? & ? & ? & ?)".
- by iIntros "(? & ? & ? & ? & ?)".
Qed.

Lemma SShare_public_encode N ke :
  Keys.ctx N -∗
  SShare_wf ke -∗
  public (term_of (encode N ke)).
Proof.
iIntros "#?".
case: ke=>> /=.
- iIntros "#(s_psk & p_cn & p_sn)".
  rewrite public_tag public_of_list /=.
  do !iSplit => //.
  rewrite public_THash; iRight.
  rewrite minted_tag; iSplit => //.
  by iExists _, _, _; eauto.
- iIntros "#(% & p_g & p_cn & p_sn & p_gx & _ & seed_y)".
  rewrite public_tag public_of_list /=.
  do !iSplit => //.
  by iApply dh_public_TExp; eauto.
- iIntros "#(p_psk & % & p_g & p_cn & p_sn & p_gx & _ & seed_y)".
  rewrite public_tag public_of_list /=.
  do !iSplit => //.
  + rewrite public_THash; iRight.
    rewrite minted_tag; iSplit => //.
    by iExists _, _, _; eauto.
  + by iApply dh_public_TExp; eauto.
Qed.

Lemma SShare_minted_session_key_of ke : SShare_wf ke -∗ minted (session_key_of ke).
Proof.
case: ke=>> /=.
- iIntros "#(?&?&?)".
  rewrite minted_senc minted_of_list /=; do !iSplit; eauto.
- iIntros "#(%&?&?&?&?&_&seed)".
  rewrite minted_senc; iApply all_minted_TExp; eauto.
  iDestruct "seed" as "(?&_)".
  by iSplit => //; iApply public_minted.
- iIntros "#(?&%&?&?&?&?&_&seed)".
  rewrite minted_senc minted_of_list /=; do !iSplit => //.
  iApply all_minted_TExp; eauto.
  iDestruct "seed" as "(?&_)".
  by iSplit => //; iApply public_minted.
Qed.

Lemma SShare_public_session_key_of' ke :
  public (SShare.session_key_of' ke) -∗
  ◇ public (SShare.psk ke).
Proof.
case: ke => [psk| |psk] > /=; rewrite public_senc_key;
rewrite ?public_of_list /=.
- by iIntros "(? & _)".
- by iIntros "_"; rewrite public_TInt.
- by iIntros "(? & _)".
Qed.

Lemma SShare_public_session_key_ofW kex :
  SShare_wf kex -∗
  public (session_key_of kex) -∗
  ◇ public (psk kex).
Proof.
rewrite public_senc_key.
case: kex => [psk cn sn|g cn sn gx y|psk g cn sn gx y] /=.
- iIntros "#(s_psk & p_cn & p_sn)".
  rewrite public_of_list /=. iIntros "(?&?&?)". by eauto.
- by rewrite public_TInt /=; eauto.
- iIntros "#(_ & _ & _ & _ & p_gx & dh_y)".
  rewrite public_of_list /=. iIntros "(? & ? & _)". by eauto.
Qed.

Lemma SShare_public_session_key_of N c_kex s_kex :
  encode' N c_kex = encode N s_kex →
  CShare_wf (cshare_of c_kex) -∗
  SShare_wf s_kex -∗
  public (session_key_of s_kex) -∗
  ◇ if has_dh c_kex then False else public (psk c_kex).
Proof.
iIntros (e) "#wf1 #wf2 #p_k". rewrite public_senc_key.
case: c_kex e => [psk cn sn|g cn sn x gy|psk g cn sn x gy] /=.
- case: s_kex => //= _ _ _ [] /Spec.tag_inj [_ <-] <- <-.
  by rewrite public_of_list /=; iDestruct "p_k" as "(?&?&?&_)"; eauto.
- case: s_kex => //= _ ? ? gx y [] <- _ _ <- e2.
  iDestruct "wf1" as "#(%gXN & _ & _ & dh_x)".
  iPoseProof "dh_x" as "#dh_x2". iDestruct "dh_x2" as "(_ & %Nm_x & _)".
  move/negb_True: (gXN) => ?.
  iDestruct "wf2" as "#(_ & _ & _ & _ & p_gx & %fresh_y & dh_y)".
  have [??]: y ≠ x ∧ y ≠ TInv x.
    apply: fresh_y. rewrite (_ : TExp g x = TExpN g [x]); last by rewrite /TExpN TMulN1.
    apply: STExp2; eauto.
    - exact: invs_canceled1 Nm_x.
    - set_solver.
  iEval (rewrite TExp2_TExpN) in "p_k".
  by iMod (dh_seed_elim2 with "dh_y dh_x p_k") as "[]".
- case: s_kex => //= _ ? ? ? gx y [] /Spec.tag_inj [_ <-].
  move=> <- _ _ <- e2.
  iDestruct "wf1" as "#(_ & %gXN & _ & _ & dh_x)".
  iPoseProof "dh_x" as "#dh_x2". iDestruct "dh_x2" as "(_ & %Nm_x & _)".
  move/negb_True: (gXN) => ?.
  iDestruct "wf2" as "#(_ & _ & _ & _ & _ & p_gx & %fresh_y & dh_y)".
  have [??]: y ≠ x ∧ y ≠ TInv x.
    apply: fresh_y. rewrite (_ : TExp g x = TExpN g [x]); last by rewrite /TExpN TMulN1.
    apply: STExp2; eauto.
    - exact: invs_canceled1 Nm_x.
    - set_solver.
  rewrite public_of_list /=. iDestruct "p_k" as "(_ & p_k & _)".
  iEval (rewrite TExp2_TExpN) in "p_k".
  by iMod (dh_seed_elim2 with "dh_y dh_x p_k") as "[]".
Qed.

End Proofs.

#[global]
Existing Instance SShare_Persistent_wf.
