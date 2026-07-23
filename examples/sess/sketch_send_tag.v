From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn.
From cryptis.examples.sess Require impl.
From cryptis.examples.sess.proofs Require Import base.
From actris.channel Require Import proto_model proto.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SketchSendTag.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ, !sessG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).

Lemma sess_send_msg skI skR si rl (m : iMsg Σ term) t p ts_send ts_recv :
  sess_own skI skR si rl (<!> m) -∗
  iMsg_car m t (Next p) -∗
  ▷ GenConn.chan_inv_for sess_ctx skI skR si rl ts_send ts_recv
  ={⊤ ∖ ↑GenConn.connN, ∅}=∗ |={∅}▷=>^(S (length ts_recv)) |={∅, ⊤ ∖ ↑GenConn.connN}=>
    GenConn.chan_inv_for sess_ctx skI skR si rl (ts_send ++ [t]) ts_recv ∗
    sess_own skI skR si rl p.
Proof.
iIntros "(%γs & #Hγs & own) Hm (%γs' & >#Hγs' & ctx)".
iPoseProof (session_names_agree with "Hγs Hγs'") as "<-".
iClear "Hγs'". case: rl => /=.
- iApply fupd_mask_intro; first set_solver.
  iIntros "close !> !>".
  iMod (iProto_send with "ctx own Hm") as "[ctx own]".
  iApply step_fupdN_intro => //.
  iIntros "!> !>". iMod "close" as "_".
  iModIntro. by iFrame; eauto.
- rewrite iProto_ctx_sym.
  iApply fupd_mask_intro; first set_solver.
  iIntros "close !> !>".
  iMod (iProto_send with "ctx own Hm") as "[ctx own]".
  iApply step_fupdN_intro => //.
  iIntros "!> !>". iMod "close" as "_".
  iModIntro. rewrite iProto_ctx_sym. by iFrame; eauto.
Qed.

Lemma wp_send_msg skI skR rl cs (m : iMsg Σ term) t p :
  {{{ connected skI skR rl cs (<!> m) ∗
      public t ∗
      (public (si_key cs) ∨ iMsg_car m t (Next p)) }}}
    impl.send (repr cs) t
  {{{ RET #(); connected skI skR rl cs p }}}.
Proof.
iIntros (Φ) "((c & own) & #p_t & Hdisj) post". wp_lam; wp_pures.
wp_apply (GenConn.wp_send_fupdN (λ skI skR si, sess_own skI skR si rl p)
           with " [//] [$c own Hdisj]").
{ iDestruct "own" as "[#fail|own]"; eauto.
  iDestruct "Hdisj" as "[#fail|Hm]"; eauto.
  iRight. iIntros (ts_send ts_recv) "inv".
  iMod (sess_send_msg with "own Hm inv") as "upd". by iIntros "!>". }
iIntros "[??]"; iApply "post". by iFrame.
Qed.

Lemma iMsg_tag_intro (ms : gmap namespace (iMsg Σ term)) N m t' pp :
  ms !! N = Some m →
  iMsg_car m t' pp -∗ iMsg_car (iMsg_tag ms) (Spec.tag (Tag N) t') pp.
Proof.
move=> HN. rewrite iMsg_tag_eq. iIntros "H".
iExists N, t', m. iFrame. by iPureIntro.
Qed.

Lemma wp_send_tag {TT : tele} skI skR rl cs
    (ms : gmap namespace (iMsg Σ term)) N
    (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) (x : TT) :
  ms !! N = Some (∃.. y, MSG t y {{ P y }}; p y)%msg →
  {{{ connected skI skR rl cs (iProto_tag Send ms) ∗
      public (t x) ∗
      (public (si_key cs) ∨ P x) }}}
    impl.send (repr cs) (Spec.tag (Tag N) (t x))
  {{{ RET #(); connected skI skR rl cs (p x) }}}.
Proof.
move=> HN. iIntros (Φ) "(conn & #p_t & Hdisj) post".
iApply (wp_send_msg _ _ _ _ (iMsg_tag ms) _ (p x) with "[conn Hdisj] post").
iSplitL "conn"; first by rewrite /iProto_tag.
iSplitR; first by rewrite public_tag.
iDestruct "Hdisj" as "[#fail|HP]"; first by iLeft.
iRight. iApply (iMsg_tag_intro _ _ HN).
rewrite iMsg_texist_exist bi_texist_exist. iExists x.
rewrite iMsg_base_eq /=.
iSplit; first done.
iFrame "HP".
auto.
Qed.

Lemma iMsg_map_tag (f : iProto Σ term → iProto Σ term)
    (ms : gmap namespace (iMsg Σ term)) :
  iMsg_map f (iMsg_tag ms) ≡ iMsg_tag ((λ m, iMsg_map f m) <$> ms).
Proof.
rewrite iMsg_tag_unseal. intros v lp; simpl. iSplit.
- iDestruct 1 as (p1) "[H Heq]".
  iDestruct "H" as (N t' m0 [HN ->]) "Hm".
  iExists N, t', (iMsg_map f m0).
  iSplit; first by iPureIntro; rewrite lookup_fmap HN.
  simpl. iExists p1. iFrame.
- iDestruct 1 as (N t' m0 [HN ->]) "Hm".
  move: HN; rewrite lookup_fmap.
  case E: (ms !! N) => [m1|] //= => -[<-].
  iDestruct "Hm" as (p1) "[Hm Heq]".
  iExists p1. iFrame "Heq".
  iExists N, t', m1. iFrame. by iPureIntro.
Qed.

Lemma iMsg_dual_tag (ms : gmap namespace (iMsg Σ term)) :
  iMsg_dual (iMsg_tag ms) ≡ iMsg_tag (iMsg_dual <$> ms).
Proof. apply iMsg_map_tag. Qed.

Lemma iMsg_app_tag (ms : gmap namespace (iMsg Σ term)) (q : iProto Σ term) :
  (iMsg_tag ms <++> q)%msg ≡ iMsg_tag ((λ m, (m <++> q)%msg) <$> ms).
Proof. apply iMsg_map_tag. Qed.

Lemma iProto_dual_tag (a : action) (ms : gmap namespace (iMsg Σ term)) :
  iProto_dual (iProto_tag a ms)
  ≡ iProto_tag (action_dual a) (iMsg_dual <$> ms).
Proof. by rewrite /iProto_tag iProto_dual_message iMsg_dual_tag. Qed.

Lemma iProto_app_tag (a : action) (ms : gmap namespace (iMsg Σ term))
    (q : iProto Σ term) :
  (iProto_tag a ms <++> q)%proto
  ≡ iProto_tag a ((λ m, (m <++> q)%msg) <$> ms).
Proof. by rewrite /iProto_tag iProto_app_message iMsg_app_tag. Qed.

Lemma iMsg_tag_proper :
  Proper ((≡) ==> (≡)) (iMsg_tag (Σ:=Σ)).
Proof.
rewrite iMsg_tag_unseal.
intros ms1 ms2 Hms v lp; simpl. iSplit.
- iDestruct 1 as (N t' m0 [HN ->]) "Hm".
  move: (Hms N); rewrite HN.
  case E: (ms2 !! N) => [m2|] Hopt; last by inversion Hopt.
  inversion Hopt as [?? He|]; subst.
  iExists N, t', m2.
  iSplit; first by iPureIntro.
  iApply (bi.equiv_entails_1_1 _ _ (He t' lp)). iExact "Hm".
- iDestruct 1 as (N t' m0 [HN ->]) "Hm".
  move: (Hms N); rewrite HN.
  case E: (ms1 !! N) => [m2|] Hopt; last by inversion Hopt.
  inversion Hopt as [?? He|]; subst.
  iExists N, t', m2.
  iSplit; first by iPureIntro.
  iApply (bi.equiv_entails_1_2 _ _ (He t' lp)). iExact "Hm".
Qed.

End SketchSendTag.
