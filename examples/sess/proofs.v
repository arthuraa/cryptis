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

Section Proofs.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ, !sessG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Notation sessN := (iso_dhN.@"res".@"sess").

Lemma wp_connect P N p c skI skR :
  channel c -∗
  cryptis_ctx -∗
  ctx N p -∗
  minted skI -∗
  minted skR -∗
  {{{ GenConn.failure skI skR ∨ P }}}
    impl.connect c skI (Spec.pkey skR) (Tag N)
  {{{ cs, RET (repr cs);
      connected skI skR Init cs p ∗
      release_token (si_init_share cs) ∗
      (public (si_key cs) ∨ P) }}}.
Proof.
iIntros "#? #? #? #? #? % !> P post".
wp_lam; wp_pures. iApply wp_fupd.
wp_apply (GenConn.wp_connect with "[] [P]"); eauto 10.
iIntros "%cs (connected & P & own & rel & token)".
iApply ("post" $! cs).
by iFrame.
Qed.

Lemma wp_listen c :
  channel c -∗
  cryptis_ctx -∗
  {{{ True }}}
    impl.listen c
  {{{ ga skI, RET (ga, Spec.pkey skI)%V;
      public ga ∗ minted skI }}}.
Proof.
iIntros "#? #? % !> _ post".
wp_lam. by iApply GenConn.wp_listen.
Qed.

Lemma wp_confirm P N p c skI skR ga :
  channel c -∗
  cryptis_ctx -∗
  ctx N p -∗
  {{{ public ga ∗ minted skI ∗ minted skR ∗
      (GenConn.failure skI skR ∨ P) }}}
    impl.confirm c skR (Tag N) (ga, Spec.pkey skI)%V
  {{{ cs, RET (repr cs);
      connected skI skR Resp cs (iProto_dual p) ∗
      (public (si_key cs) ∨ P) }}}.
Proof.
iIntros "#? #ctx1 #? !> %Φ (#p_ga & #m_skI & #m_skR & P) post".
wp_lam; wp_pures. iApply wp_fupd.
wp_apply (GenConn.wp_confirm P with "[] [$P]").
- eauto.
- eauto.
- do 3!iSplit => //.
  iIntros "!> %b tok".
  iMod (iProto_init p) as (γl γr) "(ctx & ownI & ownR)".
  iMod (term_meta_set (sessN.@"names") (γl, γr) with "tok") as "#meta".
  { solve_ndisj. }
  iModIntro. iSplitL "ownI".
  { iExists (γl, γr). iFrame. by eauto. }
  iSplitL "ownR".
  { iExists (γl, γr). iFrame. by eauto. }
  iExists (γl, γr). iFrame. by eauto.
iIntros "%cs (conn & dis & proto & rel & token)".
iApply "post". by iFrame.
Qed.

Lemma wp_send skI skR rl cs (t : term) p :
  (* ctx N p0 ∗  *)public t -∗
  {{{ connected skI skR rl cs (<!> MSG t; p) }}}
    impl.send (repr cs) t
  {{{ RET #(); connected skI skR rl cs p }}}.
Proof.
iIntros "#p_t !>"; iIntros (Φ) "[c own] post". wp_lam; wp_pures.
wp_apply (GenConn.wp_send_fupdN (λ skI skR si, sess_own skI skR si rl p)
           with " [//] [$c own]").
{ iDestruct "own" as "[#fail|own]"; eauto.
  iRight. iIntros (ts_send ts_recv) "inv".
  iMod (sess_send with "own inv") as "upd". by iIntros "!>". }
iIntros "[??]"; iApply "post". by iFrame.
Qed.

Lemma wp_recv {TT : tele} skI skR rl cs
  (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) :
  (* ctx N p0 -∗ *)
  {{{ connected skI skR rl cs (<?.. x> MSG t x {{ P x }}; p x) }}}
    impl.recv (repr cs)
  {{{ t', RET (repr t'); public t' ∗ (public (si_key cs) ∨
      ∃.. x, ⌜t' = t x⌝ ∗ connected skI skR rl cs (p x) ∗ P x) }}}.
Proof.
iIntros ""; iIntros (Φ) "[c own] post".
rewrite /impl.recv. wp_pure _ credit:"c1". wp_pure _ credit:"c2".
wp_pures.
wp_apply (GenConn.wp_recv (λ skI skR si (t' : term),
                           ∃.. x, ⌜t' = t x⌝ ∗
                                  sess_own skI skR si rl (p x) ∗ P x)%I
           with " [$c c1 c2 own]").
{ iDestruct "own" as "[#fail|own]"; eauto.
  iRight. iIntros (t' ts_send ts_recv) "inv".
  iMod (sess_recv with "[$c1 $c2] own inv") as "[??]".
  iModIntro. by iFrame. }
iIntros "%t' (conn & #p_t' & inv)". iApply "post".
iSplit => //. iDestruct "inv" as "[#fail|inv]"; eauto. iRight.
iDestruct "inv" as (x) "(-> & own & Px)". iExists x. iFrame.
by eauto.
Qed.

End Proofs.
