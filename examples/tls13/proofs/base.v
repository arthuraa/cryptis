(* TLS 1.3 handshake — shared proof infrastructure.

   The PSK-namespace context ([Module Keys]) and the session-readiness predicate
   ([tls_ready] / [tls_ready_alloc]).  Imported by every proofs/<component>.v.
   Dependency-order neighbour: just above impl.v; below all component proofs. *)

From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib cryptis primitives tactics role.
From cryptis.lib Require Import dh.
From cryptis.examples.tls13 Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Keys.

Section Keys.

Context `{!heapGS Σ, cryptisGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types t : term.
Implicit Types Φ : val → iProp.

Definition ctx N : iProp :=
  hash_pred (N.@"psk") (λ _, True)%I.

Global Instance ctx_persistent N : Persistent (ctx N).
Proof. apply _. Qed.

Lemma ctx_alloc N E E' :
  ↑N.@"psk" ⊆ E →
  hash_pred_token E ={E'}=∗
  ctx N ∗
  hash_pred_token (E ∖ ↑N.@"psk").
Proof.
iIntros (?) "tok".
iMod (hash_pred_set (N.@"psk") (λ _, True)%I with "tok")
  as "[? ?]"; eauto.
Qed.

End Keys.

End Keys.

#[global]
Existing Instance Keys.ctx_persistent.

Section TlsLib.

Context `{!heapGS Σ, !cryptisGS Σ}.
Notation iProp := (iProp Σ).

Definition tls_ready N (P : role → term → term → (Meth.t * senc_key * term) → iProp)
    rl cn sn (x : Meth.t * senc_key * term) : iProp :=
  escrow nroot
    (term_token (if rl is Init then sn else cn) (↑N.@"sess"))
    (P rl cn sn x).

Lemma tls_ready_alloc N P rl cn sn (x : Meth.t * senc_key * term) E :
  P rl cn sn x ={E}=∗
  tls_ready N P rl cn sn x.
Proof.
iIntros "P_inv".
iApply (escrowI nroot with "P_inv []").
by iApply (term_token_switch (if rl is Init then sn else cn) (N.@"sess")).
Qed.

End TlsLib.

Arguments tls_ready {Σ _ _} N P rl cn sn x.
Arguments tls_ready_alloc {Σ _ _} N P rl cn sn x E.
