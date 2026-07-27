(* TLS 1.3 handshake — the top-level protocol.

   The [tls_client] / [tls_server] programs, the protocol invariant [tls_ctx]
   (bundling every component context) and its allocation, and the two WP
   specifications.  [P] is the (currently vacuous) session-agreement payload.
   Depends on impl + base + every component proof file. *)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.lib Require Import dh.
From cryptis.examples.tls13 Require Import impl.
From cryptis.examples.tls13.proofs Require Import base meth cshare sshare cparams sparams.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Protocol.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).
Variable N : namespace.

Implicit Types t : term.
Implicit Types rl : role.
Implicit Types Φ : val → iProp.

Definition P rl t1 t2 (x : Meth.t * senc_key * term) : iProp := True.

Definition tls_client : val := λ: "c" "kex" "other",
  let: "kex" := CShare.I.new "kex" in
  let: "cp"  := term_of_list ["kex"; "other"] in
  let: "ch"  := CParams.I.hello N "cp" in
  send "c" "ch";;
  let: "sh" := recv "c" in
  bind: "res" := SParams.I.check N "cp" "sh" in
  let: "pkey" := Fst "res" in
  let: "kex" := Snd "res" in
  let: "session_key" := SShare.I.session_key_of' "kex" in
  let: "ack" := senc "session_key" (Tag $ N.@"ack") "sh" in
  send "c" "ack" ;;
  SOME ("pkey", SShare.I.cnonce "kex", SShare.I.snonce "kex", "session_key").

Definition ack_pred (k t : term) : iProp :=
  ∀ sp, ⌜t = SParams.hello N sp⌝ →
  let ss := SParams.share sp in
  let m  := SShare.meth_of ss in
  let sk := SShare.session_key_of ss in
  tls_ready N P Init
              (SShare.cnonce ss) (SShare.snonce ss) (m, sk, SParams.other sp) ∧
  ∃ ke, ⌜SShare.encode' N ke = SShare.encode N ss⌝ ∧
        CShare_wf (SShare.cshare_of ke).

Definition tls_ctx : iProp :=
  Keys.ctx N ∧
  CParams_ctx N ∧
  SParams_ctx N P ∧
  senc_pred (N.@"ack") ack_pred.

Lemma tls_ctx_alloc E1 E2 E3 E' :
  ↑N ⊆ E1 →
  ↑N ⊆ E2 →
  ↑N ⊆ E3 →
  seal_pred_token SENC E1 -∗
  seal_pred_token SIGN E2 -∗
  hash_pred_token E3 ={E'}=∗
  tls_ctx ∗
  seal_pred_token SENC (E1 ∖ ↑N) ∗
  seal_pred_token SIGN (E2 ∖ ↑N) ∗
  hash_pred_token (E3 ∖ ↑N).
Proof.
iIntros (???) "senc_tok sign_tok hash_tok".
iMod (Keys.ctx_alloc with "hash_tok")
  as "(#kctx & hash_tok)"; try solve_ndisj.
iMod (CParams_ctx_alloc with "kctx hash_tok")
  as "[#cctx hash_tok]"; first solve_ndisj.
iMod (SParams_ctx_alloc with "kctx senc_tok sign_tok")
  as "(#? & senc_tok & sign_tok)"; try solve_ndisj.
iMod (senc_pred_set (N := N.@"ack") ack_pred with "senc_tok")
  as "[#? senc_tok]"; try solve_ndisj.
iModIntro.
iSplit.
  do !iSplit => //.
iSplitL "senc_tok".
  iApply seal_pred_token_drop; last eauto; solve_ndisj.
iSplitL "sign_tok".
  iApply seal_pred_token_drop; last eauto; solve_ndisj.
iApply hash_pred_token_drop; last eauto; solve_ndisj.
Qed.

Lemma wp_tls_client c ke other Φ :
  channel c -∗
  cryptis_ctx -∗
  tls_ctx -∗
  Meth_wf ke -∗
  public other -∗
  (∀ res : option (term * term * term * senc_key),
      match res with
      | Some (pkey, cn, sn, sk) =>
        ∃ sk', ⌜pkey = Spec.pkey sk'⌝ ∧
             minted sk' ∧
             public cn ∧
             public sn ∧
             minted sk ∧
             tls_ready N P Init cn sn (ke, sk, other) ∧
             ▷ (public sk ∧ public (Meth.psk ke) ∨
                tls_ready N P Resp cn sn (ke, sk, other) ∧
                □ (public sk -∗
                ◇ if Meth.has_dh ke then False else public (Meth.psk ke)))
      | None => True
      end -∗
      Φ (repr res)) -∗
  WP tls_client c ke other {{ Φ }}.
Proof.
iIntros "#? #? #(k_ctx & c_ctx & s_ctx & ackP) #p_ke #p_other post".
rewrite /tls_client; wp_pures.
wp_bind (CShare.I.new _); iApply (wp_CShare_new _) => //.
iIntros (ke' e) "#p_ke' token"; wp_pures.
rewrite (term_token_difference _ (↑N.@"binder")); try set_solver.
iDestruct "token" as "[binder token]".
pose cp := {| CParams.share := ke'; CParams.other := other |}.
iMod (CParams_wf_set _ cp with "p_ke' binder p_other") as "#wf_cp".
rewrite (term_token_difference _ (↑N.@"sess")); try solve_ndisj.
iDestruct "token" as "[sess token]".
wp_list; wp_term_of_list.
wp_pures; wp_bind (CParams.I.hello _ _).
iApply (wp_CParams_hello N cp).
wp_pures; wp_bind (send _ _); iApply wp_send => //.
  by iModIntro; iApply CParams_public_hello.
wp_pures; wp_bind (recv _); iApply wp_recv => //.
iIntros (sh) "#p_sh"; wp_pures.
wp_bind (SParams.I.check _ _ _); iApply (wp_SParams_check N cp).
case e_check: SParams.check => [res|]; wp_pures; last by iApply ("post" $! None).
case: res=> pkey ke'' in e_check *.
iDestruct (SParams_public_checkE with "s_ctx p_sh") as (k) "Hk"; eauto.
iDestruct "Hk" as "/= (%e_k & %e_share & #s_k & #p_cn & #p_sn &
                       #s_sk & %e_hello & rest)".
subst ke' pkey; rewrite SShare.cnonce_cshare_of.
iMod (tls_ready_alloc N P Init (SShare.cnonce ke'') (SShare.snonce ke'')
                    (SShare.meth_of ke'', SShare.session_key_of' ke'',
                     CParams.other cp)
        with "[]") as "#ready"; first done.
wp_bind (SShare.I.session_key_of' _); iApply wp_SShare_session_key_of'; wp_pures.
wp_apply wp_senc'. wp_pures.
iDestruct "rest" as "[[fail_vsk fail_psk]|succ]".
  iPoseProof (SShare_public_session_key_of' with "fail_psk") as ">fail".
  wp_bind (send _ _); iApply wp_send => //.
    iModIntro. iApply public_sencIS; eauto.
    iIntros "!> %sp %e_sh".
    by case: (e_hello _ e_sh) => [] -> [] -> [] -> [] _ [] e_enc [] <- ->; eauto.
  wp_pures; wp_bind (SShare.I.snonce _); iApply wp_SShare_snonce.
  wp_pures; wp_bind (SShare.I.cnonce _); iApply wp_SShare_cnonce.
  wp_pures.
  iApply ("post" $! (Some (_, _, _, _))).
  rewrite e CShare.psk_meth_of.
  by iModIntro; iExists _; do 6!iSplit => //; eauto.
wp_bind (send _ _); iApply wp_send => //.
  iModIntro.
  iApply public_sencIS; eauto.
  iIntros "!> %sp %e_sp".
  by case: (e_hello _ e_sp) => -> [] -> [] -> [] _ [] e_enc [] <- ->; eauto.
iDestruct "succ" as (sp) "(-> & wf & succ)".
wp_pures; wp_bind (SShare.I.snonce _); iApply wp_SShare_snonce.
wp_pures; wp_bind (SShare.I.cnonce _); iApply wp_SShare_cnonce.
wp_pures.
iApply ("post" $! (Some (_, _, _, _))) => //.
rewrite e.
iModIntro; iExists _; do 6!iSplit => //.
case: (e_hello _ eq_refl) => ? [] ? [] e_sk [] ? [] ? [] ? ?.
iModIntro; iRight; iSplit => //.
rewrite -e_sk. iModIntro. iApply SShare_public_session_key_of => //.
Qed.

Definition tls_server : val := λ: "c" "psk" "g" "verif_key" "other",
  let: "ch" := recv "c" in
  bind: "ke" := CParams.I.check N "psk" "g" "other" "ch" in
  let: "ke'" := SShare.I.new "ke" in
  let: "sp"  := term_of_list ["ke'"; "verif_key"; "other"] in
  let: "sh"  := SParams.I.hello N "sp" in
  send "c" "sh" ;;
  let: "session_key" := SShare.I.session_key_of "ke'" in
  let: "ack" := recv "c" in
  bind: "ack" := sdec "session_key" (Tag $ N.@"ack") "ack" in
  guard: eq_term "ack" "sh" in
  SOME "ke'".

Lemma wp_tls_server c psk g (verif_key : sign_key) other Φ :
  ¬ is_exp g →
  channel c -∗
  cryptis_ctx -∗
  tls_ctx -∗
  minted psk -∗
  public g -∗
  minted verif_key -∗
  public other -∗
  (∀ ke : option SShare.t,
      match ke with
      | Some ke =>
        public (SShare.cnonce ke) ∧
        public (SShare.snonce ke) ∧
        minted (SShare.session_key_of ke) ∧
        tls_ready N P Resp (SShare.cnonce ke) (SShare.snonce ke)
                    (SShare.meth_of ke, SShare.session_key_of ke, other) ∧
        ▷ (public (SShare.psk ke) ∨
           tls_ready N P Init (SShare.cnonce ke) (SShare.snonce ke)
                       (SShare.meth_of ke, SShare.session_key_of ke, other) ∧
           □ (public (SShare.session_key_of ke) -∗
           ◇ if SShare.has_dh ke then False else public (SShare.psk ke)))
      | None => True
      end -∗ Φ (repr (SShare.term_of <$> ke))) -∗
  WP tls_server c psk g verif_key other {{ Φ }}.
Proof.
iIntros "% #? #? #(k_ctx & c_ctx & s_ctx & ?)".
iIntros "#s_psk #p_g #sign_key #p_other post".
rewrite /tls_server; wp_pures.
wp_bind (recv _); iApply wp_recv => //.
iIntros (ch) "#p_ch"; wp_pures.
wp_bind (CParams.I.check _ _ _ _ _).
iApply wp_CParams_check.
case e: CParams.check => [ke|] //=; wp_pures; last first.
  by iApply ("post" $! None).
iDestruct (CParams_public_checkE e with "c_ctx p_ch")
  as "{p_ch} (%compat & p_ke & p_ch)".
wp_bind (SShare.I.new _); iApply wp_SShare_new; eauto.
iIntros (ke') "-> #p_ke' token"; wp_pures.
wp_list; wp_term_of_list.
pose sp := SParams.Params ke' verif_key other.
iAssert (SParams_wf sp) as "wf_sp"; first by do !iSplit => //.
wp_pures.
wp_bind (SParams.I.hello _ _); iApply (wp_SParams_hello _ sp).
rewrite (term_token_difference _ (↑N.@"sess")); eauto.
iDestruct "token" as "[token _]".
iMod (SParams_public_hello with "s_ctx wf_sp []")
  as "(#p_hello & #sess)" => //.
wp_pures; wp_bind (send _ _); iApply wp_send; eauto.
wp_pures.
wp_bind (SShare.I.session_key_of _); iApply wp_SShare_session_key_of.
wp_pures.
wp_bind (recv _); iApply wp_recv => //; iIntros (ack) "#p_ack"; wp_pures.
wp_apply (wp_sdec' _ (SEncKey _)) => //.
iSplit; last by iIntros "_"; wp_pures; iApply ("post" $! None).
iIntros "%ack' -> ?".
wp_eq_term e_ack; last by wp_pures; iApply ("post" $! None).
rewrite {}e_ack; wp_pures; iApply ("post" $! (Some ke')).
iModIntro; iSplit.
  rewrite -(SShare.cnonce_encode N).
  iApply SShare_public_cnonce.
  by iApply SShare_public_encode => //.
iSplit.
  rewrite -(SShare.snonce_encode N).
  iApply SShare_public_snonce.
  by iApply SShare_public_encode => //.
iSplit; eauto.
  iPoseProof (public_minted with "p_ack") as "{p_ack} ack".
  by rewrite minted_TSeal !minted_senc; iDestruct "ack" as "[sk _]".
iDestruct "p_ch" as "[p_ch|p_ch]"; first by eauto.
iDestruct (public_sencE with "p_ack [//]")
  as "{p_ack} (m_hello & p_ack & #dec)".
iSplit => //.
iDestruct "p_ack" as "[fail|succ]".
  iMod (SShare_public_session_key_ofW with "p_ke' fail") as "?".
  by eauto.
rewrite /=.
iDestruct ("succ" $! sp with "[//]") as "{succ} [sess' succ]".
iRight; iSplitL => //. iModIntro.
iDestruct "succ" as (ke) "[%e_enc wf]".
iIntros "!> #p_sk".
iPoseProof (SShare_public_session_key_of e_enc with "[] p_ke' p_sk")
  as "?" => //.
by case/SShare.encode_eq: e_enc => _ [] _ [] _ [] -> [] -> ?.
Qed.

End Protocol.

Arguments tls_ctx_alloc {Σ _ _} N E1 E2 E3 E'.
