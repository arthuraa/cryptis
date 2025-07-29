From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn.
From cryptis.examples.conn.proofs Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation connN := (nroot.@"conn").

Section Proofs.

Context `{!cryptisGS Σ, !heapGS Σ, !GenConn.connGS Σ, !iso_dhGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types kS t : term.
Implicit Types skI skR : sign_key.
Implicit Types n m : nat.
Implicit Types γ : gname.
Implicit Types v : val.
Implicit Types (N : namespace).

Lemma wp_connect P c skI skR N ps :
  channel c ∗
  cryptis_ctx ∗
  ctx N ps ∗
  minted skI ∗
  minted skR -∗
  {{{ GenConn.failure skI skR ∨ P }}}
    impl.connect c skI (Spec.pkey skR) (Tag N)
  {{{ cs, RET (repr cs);
      connected ps skI skR Init cs ∗
      (public (si_key cs) ∨ P) ∗
      release_token (si_init_share cs) ∗
      term_token (si_init_share cs) (⊤ ∖ ↑iso_dhN ∖ ↑connN) }}}.
Proof. exact: GenConn.wp_connect. Qed.

Lemma wp_listen c N ps :
  channel c -∗
  cryptis_ctx -∗
  ctx N ps -∗
  {{{ True }}}
    impl.listen c
  {{{ ga skI, RET (ga, Spec.pkey skI)%V;
      public ga ∗ minted skI }}}.
Proof. exact: GenConn.wp_listen. Qed.

Lemma wp_confirm P ps c skI skR ga N :
  channel c ∗
  cryptis_ctx ∗
  ctx N ps -∗
  {{{ public ga ∗ minted skI ∗ minted skR ∗
      (GenConn.failure skI skR ∨ P) }}}
    impl.confirm c skR (Tag N) (ga, Spec.pkey skI)%V
  {{{ cs, RET (repr cs);
      connected ps skI skR Resp cs ∗
      (public (si_key cs) ∨ P) ∗
      release_token (si_resp_share cs) ∗
      term_token (si_resp_share cs) (⊤ ∖ ↑iso_dhN ∖ ↑connN) }}}.
Proof.
iIntros "#? !> %Φ (#p_ga & #p_pkA & #sign_skB & P) post".
wp_apply (GenConn.wp_confirm P with "[//] [$P]") => //.
do !iSplit => //=. by eauto.
Qed.

Lemma wp_send skI skR rl cs t N ps :
  ctx N ps -∗
  public t -∗
  {{{ connected ps skI skR rl cs ∗
      (public (si_key cs) ∨ msg_inv ps skI skR cs rl t) }}}
    impl.send (repr cs) t
  {{{ RET #(); connected ps skI skR rl cs }}}.
Proof.
iIntros "#ctx #p_t !> %Φ (conn & inv) post".
wp_apply (GenConn.wp_send with "[//] [//] [$conn inv]") => //.
iDestruct "inv" as "[fail|inv]"; auto.
iRight. iIntros "% % [inv1 inv2]".
by case: rl; iFrame; eauto.
Qed.

Lemma wp_recv skI skR rl cs N ps :
  ctx N ps -∗
  {{{ connected ps skI skR rl cs }}}
    impl.recv (repr cs)
  {{{ t, RET (repr t);
      connected ps skI skR rl cs ∗
      public t ∗
      (public (si_key cs) ∨ msg_inv ps skI skR cs (swap_role rl) t) }}}.
Proof.
iIntros "#ctx !> %Φ conn post".
wp_apply (GenConn.wp_recv with "[//] [$conn]") => //.
iRight. iIntros "% % % [inv1 inv2]". rewrite/=.
case: rl => /=; iFrame.
- iDestruct "inv2" as "[??]". by iFrame.
- iDestruct "inv1" as "[??]". by iFrame.
Qed.

Lemma wp_free ps kI kR rl cs :
  {{{ connected ps kI kR rl cs }}}
    impl.free (repr cs)
  {{{ RET #(); True }}}.
Proof. exact: GenConn.wp_free. Qed.

End Proofs.
