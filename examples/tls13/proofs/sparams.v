(* TLS 1.3 handshake — SParams (server parameters / ServerHello) proofs.

   WP specs for [SParams.I.hello] / [SParams.I.check] / [SParams.I.verify], the
   ServerHello seal/sign predicates and context ([SParams_ctx] /
   [SParams_ctx_alloc]), the [SParams_wf] invariant and the [SParams_public_hello]
   / [SParams_public_checkE] lemmas.  This section carries its own [Variable N]
   and payload predicate [Variable P].  Depends on impl + base + meth + sshare
   + cparams. *)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.lib Require Import dh.
From cryptis.examples.tls13 Require Import impl.
From cryptis.examples.tls13.proofs Require Import base meth sshare cparams.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import SParams.

Section Proofs.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

Lemma wp_SParams_case sp (f : val) E Φ :
  WP f (share sp)
       (verif_key sp)
       (other sp) @ E {{ Φ }} -∗
  WP I.case (term_of sp) f @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.case; wp_pures.
wp_list_of_term_eq l e; last by rewrite Spec.of_listK in e.
move/Spec.of_list_inj: e => {l} <-.
by wp_list_match => // _ _ _ [] <- <- <-.
Qed.

Lemma wp_SParams_hello_pub N sp E Φ :
  Φ (hello_pub N sp) -∗
  WP I.hello_pub N (term_of sp) @ E {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.hello_pub; wp_pures.
iApply wp_SParams_case; wp_pures.
wp_list.
wp_bind (SShare.I.encode _ _); iApply wp_SShare_encode.
by wp_list; wp_term_of_list.
Qed.

Lemma wp_SParams_hello N sp Φ :
  Φ (hello N sp) -∗
  WP I.hello N (term_of sp) {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.hello; wp_pures.
iApply wp_SParams_case; wp_pures.
wp_bind (I.hello_pub _ _); iApply wp_SParams_hello_pub; wp_pures.
wp_hash. wp_pures. rewrite /sign. wp_pures. wp_apply wp_enc.
wp_list. wp_apply wp_pkey.
wp_list; wp_term_of_list; wp_pures.
wp_bind (SShare.I.session_key_of _); iApply wp_SShare_session_key_of.
wp_pures. wp_apply wp_senc'. wp_pures. wp_list. by wp_term_of_list.
Qed.

Lemma wp_SParams_verify N k x sig Φ :
  Φ #(verify k N x sig) -∗
  WP I.verify k N x sig {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.verify; wp_pures.
rewrite /simple.verify. wp_pures. wp_apply wp_dec.
rewrite /verify; case e: Spec.dec => [y|]; wp_pures => //.
by wp_hash; iApply wp_eq_term.
Qed.

Lemma wp_SParams_check N cp sh Φ :
  Φ (repr ((λ '(t, kex), (t, SShare.term_of kex)) <$> check N cp sh)) -∗
  WP I.check N cp sh {{ Φ }}.
Proof.
iIntros "?"; rewrite /I.check /check; wp_pures.
wp_list_of_term_eq l e; last by rewrite Spec.of_listK in e.
move/Spec.of_list_inj: e => <- {l}; wp_pures.
wp_list_match => // _ _ [] <- <-; wp_finish.
wp_list_of_term_eq l e; last by rewrite e; wp_pures.
rewrite {}e Spec.of_listK /=; wp_pures.
wp_list_match => [pub sig -> {l}|ne]; last first.
  by rewrite prod_of_list_neq //=; wp_finish.
rewrite [in prod_of_list 2 [pub; sig]]unlock /=.
wp_list_of_term_eq pub' e; last by rewrite e; wp_pures.
rewrite {}e Spec.of_listK {pub} /=.
wp_list_match => [s_kex s_other -> {pub'}|ne]; last first.
  by rewrite prod_of_list_neq //=; wp_finish.
rewrite [in prod_of_list 2 [s_kex; s_other]]unlock /=.
wp_bind (SShare.I.check _ _ _); iApply wp_SShare_check.
case: SShare.check => [res|]; wp_pures => //=.
wp_bind (SShare.I.session_key_of' _); iApply wp_SShare_session_key_of'.
wp_pures. wp_apply wp_sdec'. iSplit; last by iIntros "-> /="; wp_pures.
iIntros "%dec_sig -> ->". wp_pures. rewrite /=.
wp_list_of_term_eq l e; wp_pures; last by rewrite e.
rewrite {}e Spec.of_listK {dec_sig} /=.
wp_list_match=> [verif_key sig' -> {l}|ne]; wp_finish; last first.
  by rewrite prod_of_list_neq //=.
rewrite [in prod_of_list 2 [verif_key; sig']]unlock /=.
rewrite /is_verify_key. wp_pures. wp_apply (wp_has_key_type Verify).
case: Spec.has_key_type; wp_pures; last by eauto.
wp_eq_term e; wp_pures; last by rewrite decide_False.
rewrite {}e decide_True //= {s_other}.
wp_bind (I.verify _ _ _ _); iApply wp_SParams_verify.
by case: verify; wp_pures => //=.
Qed.

Variable (N : namespace) (P : role → term → term → Meth.t * senc_key * term → iProp).

Definition SParams_hello_pred (k : senc_key) (t : term) : iProp := ∃ sp,
  let ss := share sp in
  ⌜t = hello_priv N sp⌝ ∧
  SShare_wf ss ∧
  tls_ready N P Resp (SShare.cnonce ss) (SShare.snonce ss)
              (SShare.meth_of ss, SShare.session_key_of ss, other sp).

Definition SParams_hello_sig_pred (k : sign_key) (t : term) : iProp := ∃ kex other,
  ⌜t = THash (Spec.of_list [SShare.term_of (SShare.encode N kex); other])⌝ ∧
  SShare_wf kex ∧
  tls_ready N P Resp (SShare.cnonce kex) (SShare.snonce kex)
              (SShare.meth_of kex, SShare.session_key_of kex, other).

Definition SParams_ctx : iProp :=
  Keys.ctx N ∧
  senc_pred (N.@"server_hello") SParams_hello_pred ∧
  sign_pred (N.@"server_hello_sig") SParams_hello_sig_pred.

Lemma SParams_ctx_alloc (E1 E2 E' : coPset) :
  ↑N.@"server_hello" ⊆ E1 →
  ↑N.@"server_hello_sig" ⊆ E2 →
  Keys.ctx N -∗
  seal_pred_token SENC E1 -∗
  seal_pred_token SIGN E2 ={E'}=∗
  SParams_ctx ∗
  seal_pred_token SENC (E1 ∖ ↑N.@"server_hello") ∗
  seal_pred_token SIGN (E2 ∖ ↑N.@"server_hello_sig").
Proof.
iIntros "% % #ctx tok1 tok2".
iMod (senc_pred_set (N := N.@"server_hello") SParams_hello_pred with "tok1")
  as "[#? tok1]"; eauto. iFrame.
iMod (sign_pred_set (N := N.@"server_hello_sig") SParams_hello_sig_pred with "tok2")
  as "[#? tok2]"; try solve_ndisj. iFrame.
iModIntro; do !iSplit => //.
Qed.

Definition SParams_wf sp : iProp :=
  SShare_wf (share sp) ∧
  minted (verif_key sp) ∧
  public (other sp).

#[global]
Instance SParams_wf_persistent sp : Persistent (SParams_wf sp).
Proof. apply _. Qed.

Lemma SParams_public_hello E sp :
  ↑N ⊆ E →
  let ss := share sp in
  SParams_ctx -∗
  SParams_wf sp -∗
  P Resp (SShare.cnonce ss) (SShare.snonce ss)
    (SShare.meth_of ss, SShare.session_key_of ss, other sp) ={E}=∗
  public (hello N sp) ∗
  tls_ready N P Resp (SShare.cnonce ss) (SShare.snonce ss)
              (SShare.meth_of ss, SShare.session_key_of ss, other sp).
Proof.
iIntros (?) "%ss #(keys & hello_ctx & sig_ctx)".
iIntros "#(wf_share & #m_pk & p_other) r".
iMod (tls_ready_alloc N P Resp _ _ _ with "r") as "#sess".
iModIntro; iFrame "sess".
rewrite public_of_list /=; do !iSplit=> //.
  rewrite public_of_list /=; do !iSplit => //.
  by iApply SShare_public_encode; eauto.
iApply (public_sencIS (SEncKey _)); eauto.
- by iApply SShare_minted_session_key_of.
- rewrite minted_of_list /= minted_TSeal minted_tag minted_THash minted_of_list /=.
  rewrite !minted_pkey.
  do !iSplit; eauto.
  iApply public_minted. by iApply SShare_public_encode.
- by iModIntro; iExists sp; eauto.
iIntros "!> #fail"; rewrite public_of_list /= public_verify_key.
do !iSplit => //.
iApply public_signIS; eauto.
- rewrite public_THash; iLeft.
  rewrite public_of_list /=; do !iSplit => //.
  by iApply SShare_public_encode.
- iModIntro. iExists (share sp), (other sp); by do !iSplit => //.
Qed.

(* TODO: Clean this statement *)
Lemma SParams_public_checkE cp sh pkey s_ke :
  check N cp sh = Some (pkey, s_ke) →
  SParams_ctx -∗
  public sh -∗
  ∃ k : sign_key,
       ⌜pkey = Spec.pkey k⌝ ∧
       ⌜CParams.share cp = SShare.cshare_of s_ke⌝ ∧
       minted k ∧
       public (SShare.cnonce s_ke) ∧
       public (SShare.snonce s_ke) ∧
       minted (SShare.session_key_of' s_ke) ∧
       ⌜∀ sp, sh = hello N sp →
              SShare.cnonce (share sp) = SShare.cnonce s_ke ∧
              SShare.snonce (share sp) = SShare.snonce s_ke ∧
              SShare.session_key_of (share sp) = SShare.session_key_of' s_ke ∧
              verif_key sp = k ∧
              SShare.encode' N s_ke = SShare.encode N (share sp) ∧
              SShare.meth_of s_ke = SShare.meth_of (share sp) ∧
              other sp = CParams.other cp⌝ ∧
       ▷ (public k ∧ public (SShare.session_key_of' s_ke) ∨
          ∃ sp, ⌜sh = hello N sp⌝ ∧
                SShare_wf (share sp) ∧
                tls_ready N P Resp
                            (SShare.cnonce s_ke)
                            (SShare.snonce s_ke)
                            (SShare.meth_of s_ke,
                             SShare.session_key_of' s_ke, CParams.other cp)).
Proof.
rewrite /check; case: Spec.to_listP => //= {}sh.
elim/(@list_len_rect 2): sh => [pub sig|sh ne]; last first.
  by rewrite prod_of_list_neq.
rewrite [in prod_of_list _ _]unlock /=; case: Spec.to_listP => //= {}pub.
elim/(@list_len_rect 2): pub => [kex other'|pub ne]; last first.
  by rewrite prod_of_list_neq.
rewrite [in prod_of_list _ _]unlock /=.
case e_check: SShare.check => [kex'|] //=.
move/SShare_public_checkE: e_check; move: kex' => {}kex [e_cp ->].
case e_dec: Spec.dec => [res|] //=.
have {sig e_dec} -> := Spec.decK (Spec.open_key_senc _) e_dec.
case: Spec.to_listP => //= {}res.
elim/(@list_len_rect 2): res => [pk sig|res neq]; last first.
  by rewrite prod_of_list_neq.
rewrite [in prod_of_list _ _]unlock /=.
case e: Spec.has_key_type => //.
have [sk -> {pk e}] : ∃ sk : sign_key, pk = Spec.pkey sk.
  case: pk e => // - [] // sk _; by exists (SignKey sk); rewrite keysE.
case: decide => [-> {other'}|//] /=.
rewrite /verify /Spec.dec /Spec.open.
case: sig => //= k sig.
case: decide => [/Spec.open_key_signK -> {k}|//] /=.
case: Spec.untagP=> [ {}sig ->|//=].
rewrite bool_decide_decide; case: decide => [->|//] [] {s_ke pkey} <- <-.
do !rewrite public_of_list /=.
iIntros "#(? & ctx1 & ctx2)".
iDestruct 1 as "# ((p_kex & p_cp & _) & p_sig & _)".
iPoseProof (public_minted with "p_sig") as "s_sig".
iExists sk; do 3!iSplit => //.
  rewrite minted_TSeal minted_tag minted_of_list /= !minted_pkey.
  by iDestruct "s_sig" as "[_ [??]]".
iSplit.
  by rewrite -(SShare.cnonce_encode' N); iApply SShare_public_cnonce.
iSplit.
  by rewrite -(SShare.snonce_encode' N); iApply SShare_public_snonce.
iSplit.
  rewrite minted_TSeal.
  by iDestruct "s_sig" as "[??] {p_sig}".
iSplit.
  iPureIntro.
  move=> sp /Spec.of_list_inj [].
  case/Spec.of_list_inj=> /SShare.term_of_inj.
  case/SShare.encode_eq=> [] -> [] -> [] -> [] _ [] _ ? -> ?.
  case/Spec.tag_inj=> _ /Spec.of_list_inj [/Spec.sign_pkey_inj -> _].
  case/Spec.tag_inj=> _ [] /Spec.of_list_inj [/SShare.term_of_inj ->].
  by eauto.
iClear "s_sig".
iPoseProof (public_sencE with "p_sig ctx1") as "(m_sig & inv & #pub)".
iDestruct "inv" as "[psk_fail|#hello]".
- iSpecialize ("pub" with "psk_fail"). rewrite public_of_list /=.
  iDestruct "pub" as "{p_sig} (p_pkey & p_sig & _)".
  iPoseProof (public_signE with "p_sig ctx2") as "(s_sig & inv)".
  iDestruct "inv" as "[?|#hello]"; eauto.
  iModIntro.
  iDestruct "hello" as (kex' other') "(%e_hash & wf & hello)".
  case: e_hash => /Spec.of_list_inj [/SShare.term_of_inj e_kex <- {other'}].
  iRight.
  iExists (Params kex' sk (CParams.other cp)); iSplit.
    iPureIntro.
    rewrite e_kex; by case/SShare.encode_eq: e_kex => [_ [] _ [] ->].
  iSplit => //.
  by case/SShare.encode_eq: e_kex => [-> [] -> [] -> [] _ [] _ ->]; eauto.
- iModIntro.
  iDestruct "hello" as (sp) "(%e & wf & hello)".
  case/Spec.of_list_inj: e => /Spec.sign_pkey_inj -> _ /Spec.tag_inj [] _ [].
  case/Spec.of_list_inj=> [/SShare.term_of_inj e_ke ->].
  iRight.
  iExists sp; iSplit.
    iPureIntro.
    by rewrite e_ke; case/SShare.encode_eq: e_ke => [_ [] _ [] ->].
  by case/SShare.encode_eq: e_ke => -> [] -> [] -> [] _ [] _ ->; eauto.
Qed.

End Proofs.
