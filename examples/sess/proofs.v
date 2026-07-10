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
  {{{ connected skI skR rl cs (<!> MSG t; p) ∗ public t}}}
    impl.send (repr cs) t
  {{{ RET #(); connected skI skR rl cs p }}}.
Proof.
iIntros (Φ) "([c own] & #p_t) post". wp_lam; wp_pures.
wp_apply (GenConn.wp_send_fupdN (λ skI skR si, sess_own skI skR si rl p)
           with " [//] [$c own]").
{ iDestruct "own" as "[#fail|own]"; eauto.
  iRight. iIntros (ts_send ts_recv) "inv".
  iMod (sess_send with "own inv") as "upd". by iIntros "!>". }
iIntros "[??]"; iApply "post". by iFrame.
Qed.

Lemma wp_send_tele {TT : tele} skI skR rl cs (tt : TT)
    (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) :
  {{{ connected skI skR rl cs (<!.. x> MSG t x {{ P x }}; p x) ∗
      public (t tt) ∗ P tt }}}
    impl.send (repr cs) (t tt)
  {{{ RET #(); connected skI skR rl cs (p tt) }}}.
Proof.
iIntros (Φ) "(Hc & #pt & HP) HΦ".
iDestruct (connected_le _ _ _ _ _ (<!> MSG t tt; p tt)%proto with "Hc [HP]")
  as "Hc".
{ iIntros "!>".
  iApply iProto_le_trans.
  iApply iProto_le_texist_intro_l.
  by iFrame "HP". }
by iApply (wp_send with "[$Hc]").
Qed.

(* Todo *)
Lemma wp_send' skI skR rl cs (t : term) p :
  public t -∗
  □ (∀Φ, (connected skI skR rl cs (<!> MSG t; p)) -∗
  (▷ (connected skI skR rl cs p -∗ Φ #())) -∗
  (WP impl.send (repr cs) t {{ Φ }})).
Proof.
iIntros "#p_t !>"; iIntros (Φ) "[c own] post". wp_lam; wp_pures.
wp_apply (GenConn.wp_send_fupdN (λ skI skR si, sess_own skI skR si rl p)
           with " [//] [$c own]").
{ iDestruct "own" as "[#fail|own]"; eauto.
  iRight. iIntros (ts_send ts_recv) "inv".
  iMod (sess_send with "own inv") as "upd". by iIntros "!>". }
iIntros "[??]"; iApply "post". by iFrame.
Qed.

Lemma wp_recv skI skR rl cs (m : iMsg Σ term) :
  {{{ connected skI skR rl cs (<?> m) }}}
    impl.recv (repr cs)
  {{{ t' p, RET (repr t');
      public t' ∗
      connected skI skR rl cs p ∗
      (public (si_key cs) ∨ iMsg_car m t' (Next p)) }}}.
Proof.
iIntros ""; iIntros (Φ) "[c own] post".
rewrite /impl.recv. wp_pure _ credit:"c1". wp_pure _ credit:"c2".
wp_pure _ credit:"c3". wp_apply wp_fupd.
wp_apply (GenConn.wp_recv (λ skI skR si (t' : term),
                           ∃ p, sess_own skI skR cs rl p ∗
                                iMsg_car m t' (Next p))%I
           with " [$c c1 c2 own]").
{ iDestruct "own" as "[#fail|own]"; eauto.
  iRight. iIntros (t' ts_send ts_recv) "inv".
  iMod (sess_recv with "[$c1] own inv") as "[$ $]"; eauto. }
iIntros "%t' (conn & #p_t' & inv)".
iDestruct "inv" as "[#fail|(%p & own & inv)]"; eauto.
{ iApply ("post" $! _ inhabitant). iFrame. by iFrame "#". }
by iApply "post"; iFrame; eauto.
Qed.

Lemma wp_recv_tele {TT : tele} skI skR rl cs
  (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) :
  {{{ connected skI skR rl cs (<?.. x> MSG t x {{ ▷ P x }}; p x) }}}
    impl.recv (repr cs)
  {{{ t', RET (repr t'); public t' ∗ (public (si_key cs) ∨
      ∃.. x, ⌜t' = t x⌝ ∗ connected skI skR rl cs (p x) ∗ P x) }}}.
Proof.
iIntros ""; iIntros (Φ) "[c own] post".
rewrite /impl.recv. wp_pure _ credit:"c1". wp_pure _ credit:"c2".
wp_pure _ credit:"c3". wp_apply wp_fupd.
wp_apply (GenConn.wp_recv (λ skI skR si (t' : term),
                           ∃.. x, ⌜t' = t x⌝ ∗
                                  sess_own skI skR si rl (p x) ∗ ▷ P x)%I
           with " [$c c1 c2 own]").
{ iDestruct "own" as "[#fail|own]"; eauto.
  iRight. iIntros (t' ts_send ts_recv) "inv".
  iMod (sess_recv_tele with "[$c1 $c2] own inv") as "[??]".
  iModIntro. by iFrame. }
iIntros "%t' (conn & #p_t' & inv)". iApply "post". iFrame "#".
iDestruct "inv" as "[#fail|inv]"; eauto. iRight.
iDestruct "inv" as (x) "(-> & own & Px)". iExists x. iFrame.
iMod (lc_fupd_elim_later with "c3 Px") as "?".
by eauto.
Qed.

Lemma wp_recv_inhabited {TT : tele} `{Inhabited TT} skI skR rl cs
  (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) :
  {{{ connected skI skR rl cs (<?.. x> MSG t x {{ ▷ P x }}; p x) }}}
    impl.recv (repr cs)
  {{{ t' x, RET (repr t');
      public t' ∗
      connected skI skR rl cs (p x) ∗
      (public (si_key cs) ∨ ⌜t' = t x⌝ ∗ P x) }}}.
Proof.
iIntros ""; iIntros (Φ) "[c own] post".
rewrite /impl.recv. wp_pure _ credit:"c1". wp_pure _ credit:"c2".
wp_pure _ credit:"c3". wp_apply wp_fupd.
wp_apply (GenConn.wp_recv (λ skI skR si (t' : term),
                           ∃.. x, ⌜t' = t x⌝ ∗
                                  sess_own skI skR si rl (p x) ∗ ▷ P x)%I
           with " [$c c1 c2 own]").
{ iDestruct "own" as "[#fail|own]"; eauto.
  iRight. iIntros (t' ts_send ts_recv) "inv".
  iMod (sess_recv_tele with "[$c1 $c2] own inv") as "[??]".
  iModIntro. by iFrame. }
iIntros "%t' (conn & #p_t' & [#fail|inv])".
{ iApply ("post" $! t' inhabitant) . iFrame. by iFrame "#". }
iDestruct "inv" as (x) "(-> & own & Px)". iApply ("post" $! (t x) x).
iMod (lc_fupd_elim_later with "c3 Px") as "?".
iFrame. by eauto.
Qed.

Lemma wp_recv_term skI skR rl cs (P : term → iProp) (p : term → iProto Σ term) :
  {{{ connected skI skR rl cs (<? t> MSG t {{ ▷ P t }}; p t) }}}
    impl.recv (repr cs)
  {{{ t, RET (repr t); public t ∗
      connected skI skR rl cs (p t) ∗
      (public (si_key cs) ∨ P t) }}}.
Proof.
iIntros ""; iIntros (Φ) "[c own] post".
rewrite /impl.recv. wp_pure _ credit:"c1". wp_pure _ credit:"c2".
wp_pure _ credit:"c3". wp_apply wp_fupd.
wp_apply (GenConn.wp_recv (λ skI skR si (t : term),
              sess_own skI skR si rl (p t) ∗ ▷ P t)%I
           with " [$c c1 c2 own]").
{ iDestruct "own" as "[#fail|own]"; eauto.
  iRight. iIntros (t ts_send ts_recv) "inv".
  pose TT : tele := TeleS (λ t : term, TeleO).
  iAssert (sess_own skI skR cs rl
             (<?.. x> MSG @tele_app TT _ (λ t, t) x {{ ▷ @tele_app TT _ (λ t, P t) x }};
                   @tele_app TT _ (λ t, p t) x)) with "[own]" as "own".
  { iApply (sess_own_le with "own"). rewrite /=. iModIntro. eauto. }
  iMod (sess_recv_tele with "[$c1 $c2] own inv") as "[? H]".
  iModIntro. iFrame. iModIntro.
  iDestruct "H" as (x) "(-> & own & H)". rewrite /=. by iFrame. }
iIntros "%t (conn & #p_t & [#fail|inv])".
{ iApply ("post" $! t) . iFrame. by iFrame "#". }
iDestruct "inv" as "(own & Px)". iApply ("post" $! t).
iMod (lc_fupd_elim_later with "c3 Px") as "?".
iFrame. by eauto.
Qed.

(** ** Select and Branch (untrusted setting)

The choice operator [iProto_choice_term] (defined in [proofs/base.v]) is the
Cryptis analogue of Actris's [iProto_choice], binary-choice protocol over a
boolean encoded as [TInt 0]/[TInt 1].  In the untrusted setting the
adversary may have compromised the session, so [wp_select] requires either
the protocol's payload [P1]/[P2] OR the session key being public, and
[wp_branch] returns either the payload OR public-key evidence in its
postcondition.

[wp_branch] uses plan.org's term-binder design: the postcondition binds
the actual received term [t] and derives [b := bool_decide (t = TInt 1)].
This is needed because in the compromised case the adversary controls
[t] so it may not be a [TInt 0/1]. *)

Local Instance bool_tele_inhabited :
  Inhabited (tele_arg (TeleS (λ _ : bool, TeleO))) :=
  populate (TeleArgCons false tt).

Lemma wp_select skI skR rl cs (b : bool) (P1 P2 : iProp)
    (p1 p2 : iProto Σ term) :
  {{{ connected skI skR rl cs
        (iProto_choice_term Send P1 P2 p1 p2) ∗
      (public (si_key cs) ∨ if b then P1 else P2) }}}
    impl.send (repr cs) (TInt (if b then 1 else 0))
  {{{ RET #(); connected skI skR rl cs (if b then p1 else p2) }}}.
Proof.
iIntros (Φ) "[tc HP_or] post".
iDestruct "HP_or" as "[#pub | HP]".
- iApply (wp_send _ _ _ _ (TInt (if b then 1 else 0))
                       (if b then p1 else p2) with "[tc]").
  + iSplitL.
    * iDestruct "tc" as "[gc _]".
      iSplitL "gc"; first iExact "gc".
      iLeft. iExact "pub".
    * by rewrite public_TInt.
  + iIntros "!> tc". by iApply "post".
- iApply (wp_send _ _ _ _ (TInt (if b then 1 else 0))
                       (if b then p1 else p2) with "[tc HP]").
  + iSplitL.
    * iApply (connected_le with "tc"). iNext.
      rewrite /iProto_choice_term.
      iApply iProto_le_trans.
      { iApply (iProto_le_exist_intro_l _ b). }
      by iApply iProto_le_payload_intro_l.
    * by rewrite public_TInt.
  + iIntros "!> tc". by iApply "post".
Qed.

Lemma wp_branch skI skR rl cs (P1 P2 : iProp)
    (p1 p2 : iProto Σ term) :
  {{{ connected skI skR rl cs
        (iProto_choice_term Recv P1 P2 p1 p2) }}}
    impl.recv (repr cs)
  {{{ t, RET (repr t);
      let b := bool_decide (t = TInt 1) in
      connected skI skR rl cs (if b then p1 else p2) ∗
      (public (si_key cs) ∨ if b then P1 else P2) }}}.
Proof.
iIntros (Φ) "tc post".
iApply (wp_recv_inhabited
          (TT := TeleS (λ _ : bool, TeleO))
          skI skR rl cs
          (tele_app (TT := TeleS (λ _ : bool, TeleO))
                    (λ b : bool, TInt (if b then 1 else 0)))
          (tele_app (TT := TeleS (λ _ : bool, TeleO))
                    (λ b : bool, if b then P1 else P2))
          (tele_app (TT := TeleS (λ _ : bool, TeleO))
                    (λ b : bool, if b then p1 else p2))
          with "[tc]").
- iApply (connected_le with "tc"). iNext.
  rewrite /iProto_choice_term.
  iApply iProto_le_exist_elim_l_inhabited.
  iIntros (b).
  iApply (iProto_le_payload_elim_l Recv).
  iIntros "HP".
  iApply (iProto_le_trans _
           (<?> MSG (TInt (if b then 1 else 0))
                  {{ ▷ (if b then P1 else P2) }};
                if b then p1 else p2)
           with "[HP]").
  + iApply (iProto_le_payload_intro_r _ (▷ (if b then P1 else P2))).
    iNext. iExact "HP".
  + iApply (iProto_le_texist_intro_r (TT := TeleS (λ _ : bool, TeleO))
             _ (TeleArgCons b tt)).
- iIntros "!> %t' %x (#p_t & tc' & disj)".
  destruct x as [b []].
  iDestruct "disj" as "[#fail | (-> & HP)]".
  + iApply ("post" $! t').
    iDestruct "tc'" as "[gc _]".
    iSplitL "gc".
    { iSplitL "gc"; first iExact "gc". iLeft. iExact "fail". }
    iLeft. iExact "fail".
  + iApply ("post" $! (TInt (if b then 1 else 0))).
    destruct b => /=.
    * iFrame "tc'". iRight. iExact "HP".
    * iFrame "tc'". iRight. iExact "HP".
  Unshelve. apply _.
Qed.

End Proofs.
