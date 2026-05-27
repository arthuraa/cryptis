From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta cryptis primitives tactics role.
From cryptis.examples Require Import iso_dh gen_conn sess.
From cryptis.examples.sess.proofs Require Import base.
From actris.channel Require Import proto_model proto.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Trusted.

Context `{!cryptisGS Σ, !heapGS Σ, !iso_dhGS Σ, !GenConn.connGS Σ, !Sess.sessG Σ}.
Notation iProp := (iProp Σ).

Implicit Types (cs : GenConn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types v : val.

(** * Trusted connected

A wrapper around [Sess.connected] that additionally asserts that the session
key can never become public.  When both parties are permanently honest (i.e.,
their signing keys satisfy [□ (public sk → ▷ False)]), the session key inherits
this property via the iso-DH handshake.  The honesty hypothesis uses [False]
(not [▷ False]) so that the adversary branch can be eliminated in any context,
not just under a WP.  The [▷] from the key secrecy chain is consumed inside the
(admitted) connect/confirm proofs, which run in WP context. *)

Definition trusted_connected skI skR rl cs p : iProp :=
  Sess.connected skI skR rl cs p ∗
  □ (public (si_key cs) →  ▷ False).

Global Instance trusted_connected_proper skI skR rl cs :
  Proper ((≡) ==> (≡)) (trusted_connected skI skR rl cs).
Proof. solve_proper. Qed.

Lemma trusted_connected_connected skI skR rl cs p :
  trusted_connected skI skR rl cs p -∗
  Sess.connected skI skR rl cs p.
Proof. rewrite /trusted_connected. by iIntros "[$ _]". Qed.

Lemma trusted_connected_honest skI skR rl cs p :
  trusted_connected skI skR rl cs p -∗
  □ (public (si_key cs) →  ▷  False).
Proof. rewrite /trusted_connected. by iIntros "[_ #$]". Qed.

Lemma trusted_connected_le skI skR rl cs p1 p2 :
  trusted_connected skI skR rl cs p1 ⊢
  ▷ (p1 ⊑ p2) -∗ trusted_connected skI skR rl cs p2.
Proof.
rewrite /trusted_connected.
iIntros "[conn #hon] le".
iFrame "hon". by iApply (Sess.connected_le with "conn le").
Qed.

(** ** Send *)

Lemma trusted_wp_send skI skR rl cs (t : term) p :
  {{{ trusted_connected skI skR rl cs (<!> MSG t; p) ∗ public t }}}
    Sess.send (repr cs) t
  {{{ RET #(); trusted_connected skI skR rl cs p }}}.
Proof.
iIntros (Φ) "[tc #p_t] post".
iDestruct "tc" as "[conn #hon]".
iApply (Sess.wp_send with "[$conn $p_t]").
iIntros "!> conn". iApply "post".
rewrite /trusted_connected. iFrame "conn hon".
Qed.

Lemma trusted_wp_send_tele {TT : tele} skI skR rl cs (tt : TT)
    (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) :
  {{{ trusted_connected skI skR rl cs (<!.. x> MSG t x {{ P x }}; p x) ∗
      public (t tt) ∗ P tt }}}
    Sess.send (repr cs) (t tt)
  {{{ RET #(); trusted_connected skI skR rl cs (p tt) }}}.
Proof.
iIntros (Φ) "(tc & #p_t & HP) post".
iDestruct "tc" as "[conn #hon]".
iApply (Sess.wp_send_tele with "[$conn $p_t $HP]").
iIntros "!> conn". iApply "post".
rewrite /trusted_connected. iFrame "conn hon".
Qed.

(** ** Recv

The key advantage: no disjunction in the postcondition.  The adversary branch
is eliminated by the honesty hypothesis carried in [trusted_connected]. *)

Lemma trusted_wp_recv {TT : tele} skI skR rl cs
  (t : TT → term) (P : TT → iProp) (p : TT → iProto Σ term) :
  {{{ trusted_connected skI skR rl cs (<?.. x> MSG t x {{ ▷ P x }}; p x) }}}
    Sess.recv (repr cs) 
  {{{ x , RET (repr (t x)); public (t x) ∗
     trusted_connected skI skR rl cs (p x) ∗ P x }}}.
Proof.
iIntros (Φ) "tc post".
iDestruct "tc" as "[conn #hon]".
(* wp_pure _ credit: "c". *)
(* wp_pures. *)
iApply (wp_fupd).
iApply (Sess.wp_recv with "conn").
iIntros "!> %t' (p_t' & [fail | inv])".
- iMod ("hon" with "fail") as "[]". 
-
  iDestruct "inv" as (x) "(-> & conn & Px)".
  iApply "post". iFrame "p_t'".
  iFrame "Px".
  (* iSplit => //. *)
  rewrite /trusted_connected. iFrame "conn hon".
  auto.
Qed.

(** ** Recv (fixed-message, no existential)

For protocols of the form [<?> MSG t; p] — no existential quantifier, resource
[True] — the [trusted_wp_recv] tele version is reached via a two-step subtyping
chain: inject [▷ True] with [iProto_le_payload_intro_r], then lift to the tele
form with [iProto_le_texist_intro_r (TT := TeleO)]. *)

Lemma trusted_wp_recv_base skI skR rl cs (t : term) (p : iProto Σ term) :
  {{{ trusted_connected skI skR rl cs (<?> MSG t; p) }}}
    Sess.recv (repr cs)
  {{{ RET (repr t); public t ∗ trusted_connected skI skR rl cs p }}}.
Proof.
iIntros (Φ) "tc post".
iApply (trusted_wp_recv (TT := TeleO) with "[tc]").
- iApply (trusted_connected_le with "tc"). iNext.
  iApply iProto_le_trans.
  { iApply (iProto_le_payload_intro_r _ (▷ True)). iNext. done. }
  iApply (iProto_le_texist_intro_r (TT := TeleO) (fun _ => iMsg_base t (▷ True) p) tt).
- iIntros "!> % (p_t & tc2 & _)". iApply "post". iFrame "p_t tc2".
Qed.

(** ** Connect and confirm

The hypothesis [□ (public skI → ▷ False)] for both keys flows to
[□ (public (si_key cs) → False)] through the iso-DH key secrecy chain:
  1. [freeze_secret] gives [□ (public sk ↔ ▷ False)] from [secret sk]
  2. [secret_session] gives [session_ok si] from both keys being secret
  3. [unreleased_key_secrecy] gives [□ (public (si_key si) ↔ ▷ False)]
     from [session_ok si] and [□ (¬ released_session si)]
The [▷] is eliminated using a later credit from the WP context of the
connect/confirm operations themselves. *)

Lemma trusted_wp_connect N p c skI skR :
  channel c -∗
  cryptis_ctx -∗
  Sess.ctx N p -∗
  minted skI -∗
  minted skR -∗
  □ (public skI → ▷ False) -∗
  □ (public skR → ▷ False) -∗
  {{{ True }}}
    Sess.connect c skI (Spec.pkey skR) (Tag N)
  {{{ cs, RET (repr cs);
      trusted_connected skI skR Init cs p }}}.
Proof.
iIntros "#chan #ctx #sess #m_skI #m_skR #hon_I #hon_R".
iIntros "%Φ !> pre post".
iApply wp_fupd.
iApply (Sess.wp_connect True with "chan ctx sess m_skI m_skR [pre]").
eauto.
(* { iDestruct "pre" as "[fail|_]"; eauto. } *)
iIntros "!> %cs (conn & rel & disj)".
iDestruct "conn" as "[gconn pub_or_own]".
iDestruct "gconn" as "(#e1 & #e2 & #e3 & #base & #chan2 & (#minted_key & #sess_cs) & rest)".
iAssert (GenConn.connected base.sess_ctx skI skR Init cs) with "[rest]" as "gconn".
{ iFrame "#". iExact "rest". }
iDestruct (session_session_ok with "sess_cs") as "[comp | #ok]".
- iDestruct "comp" as "[p_si | p_sr]".
  + iDestruct "e1" as %<-. iMod ("hon_I" with "p_si") as "[]".
  + iDestruct "e2" as %<-. iMod ("hon_R" with "p_sr") as "[]".
- iMod (unrelease Init cs with "rel") as "#un".
  iDestruct (unreleased_key_secrecy with "un ok") as "#sec".
  iApply "post".
  rewrite /trusted_connected /Sess.connected.
  iSplitL "gconn pub_or_own".
  { iModIntro. iFrame "gconn pub_or_own". }
  iModIntro. iIntros "!> #pub". by iApply "sec".
Qed.

Lemma trusted_wp_confirm N p c skI skR ga :
  channel c -∗
  cryptis_ctx -∗
  Sess.ctx N p -∗
  minted skI -∗
  minted skR -∗
  □ (public skI → ▷ False) -∗
  □ (public skR → ▷ False) -∗
  {{{ public ga ∗ minted skI ∗ minted skR 
       }}}
    Sess.confirm c skR (Tag N) (ga, Spec.pkey skI)%V
  {{{ cs, RET (repr cs);
      trusted_connected skI skR Resp cs (iProto_dual p) }}}.
Proof.
iIntros "#chan #ctx #sess #m_skI #m_skR #hon_I #hon_R".
iIntros "%Φ !> (#p_ga & #m_skI' & #m_skR') post".
rewrite /Sess.confirm.
wp_lam; wp_pures. iApply wp_fupd.
wp_apply (GenConn.wp_confirm True with "[]").
- eauto.
- iFrame "#". iSplit; last iRight => //. iIntros "!> %b tok".
  iMod (iProto_init p) as (γl γr) "(proto_ctx & ownI & ownR)".
  iMod (term_meta_set (sessN.@"names") (γl, γr) with "tok") as "#meta".
  { solve_ndisj. }
  iModIntro. iSplitL "ownI". { iExists (γl, γr). iFrame. by eauto. }
  iSplitL "ownR". { iExists (γl, γr). iFrame. by eauto. }
  iExists (γl, γr). iFrame. by eauto.
iIntros "%cs (gconn & disj & proto & rel & token)".
iDestruct "gconn" as "(#e1 & #e2 & #e3 & #base2 & #chan3 & (#minted_key & #sess_cs) & rest)".
iAssert (gen_conn.proofs.base.connected (base.chan_inv (Sess.sess_params p)) skI skR Resp cs)
  with "[rest]" as "gconn".
{ iFrame "#". iExact "rest". }
iDestruct (session_session_ok with "sess_cs") as "[comp | #ok]".
- iDestruct "comp" as "[p_si | p_sr]".
  + iDestruct "e1" as %<-. iMod ("hon_I" with "p_si") as "[]".
  + iDestruct "e2" as %<-. iMod ("hon_R" with "p_sr") as "[]".
- iMod (unrelease Resp (base.cs_si cs) with "rel") as "#un".
  iDestruct (unreleased_key_secrecy with "un ok") as "#sec".
  iApply "post".
  rewrite /trusted_connected /Sess.connected.
  iSplitL "gconn proto".
  { iModIntro. iFrame "gconn".
    iDestruct "proto" as "[#pub | own]".
    - iLeft. iExact "pub".
    - iRight. iExact "own". }
  iModIntro. iIntros "!> #pub". by iApply "sec".
Qed.

(** **Select and branch *)
Lemma trusted_wp_select skI skR rl cs (b : bool) (P1 P2 : iProp) (p1 p2 : iProto Σ term) :
{{{ trusted_connected skI skR rl cs 
(iProto_choice_term Send P1 P2 p1 p2) ∗
(if b then P1 else P2) }}}
Sess.send (repr cs) (TInt (if b then 1 else 0))
{{{ RET #(); trusted_connected skI skR rl cs (if b then p1 else p2) }}}.
Proof.
 iIntros (ϕ) "[tc Hp] post".
 iApply (trusted_wp_send _ _ _ _ (TInt (if b then 1 else 0)) (if b then p1 else p2) with "[tc Hp]").
 - iSplitL. 
 + iApply (trusted_connected_le with "tc"). iNext.
 rewrite /iProto_choice_term.
 iApply iProto_le_trans.
 { iApply (iProto_le_exist_intro_l _ b). }
 by iApply iProto_le_payload_intro_l.
 + by rewrite public_TInt.
 - iFrame.
 Qed.

Lemma trusted_wp_branch skI skR rl cs (P1 P2 : iProp) (p1 p2 : iProto Σ term) :
{{{ trusted_connected skI skR rl cs 
(iProto_choice_term Recv P1 P2 p1 p2)}}}
Sess.recv (repr cs) 
{{{ (b : bool), RET (repr (TInt (if b then 1 else 0))); trusted_connected skI skR rl cs (if b then p1 else p2) ∗
(if b then P1 else P2)}}}.
Proof.
iIntros (Φ) "tc Post".
iApply (trusted_wp_recv
(TT := TeleS ( λ _ : bool, TeleO))
skI skR rl cs
(tele_app (TT := TeleS ( λ _ : bool, TeleO))
( λ b : bool, TInt (if b then 1 else 0)))
(tele_app (TT := TeleS (λ _ : bool, TeleO))
(λ b : bool, if b then P1 else P2))
(tele_app (TT := TeleS (λ _ : bool, TeleO))
(λ b : bool, if b then p1 else p2))
with "[tc]").
- iApply (trusted_connected_le with "tc"). iNext.
  rewrite /iProto_choice_term.
  iApply iProto_le_exist_elim_l_inhabited.
  iIntros (b).
  iApply (iProto_le_payload_elim_l Recv).
  iIntros "HP". 
  iApply (iProto_le_trans _
  (<?> MSG (TInt (if b then 1 else 0))
  {{▷(if b then P1 else P2)}};
  if b then p1 else p2)
  with "[HP]").
+ iApply (iProto_le_payload_intro_r _ (▷(if b then P1 else P2))).
iNext. iExact "HP".
+ iApply (iProto_le_texist_intro_r (TT := TeleS (λ _ : bool, TeleO)) _ (TeleArgCons b tt)).
- iIntros ([b []]) "!> /= (#p_t & tc & HP)".
  iApply ("Post" $! b). by iFrame.
  Unshelve. apply _.
Qed.
End Trusted.
