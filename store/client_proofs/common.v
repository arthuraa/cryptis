From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term cryptis primitives tactics.
From cryptis Require Import role session pk_auth pk_dh.
From cryptis.store Require Import impl shared db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Local Instance STORE : PK := PK_DH (λ _ _ _ _, True)%I.

Implicit Types (cs : cst).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_get_timestamp E cs (n : nat) :
  {{{ cst_ts cs ↦ #n }}}
    Client.get_timestamp (repr cs) @ E
  {{{ RET #n; cst_ts cs ↦ #n }}}.
Proof.
rewrite /Client.get_timestamp.
iIntros "%Φ Hn post".
wp_pures. wp_load. iApply "post". iModIntro. by iFrame.
Qed.

Lemma wp_client_incr_timestamp E cs (n : nat) :
  {{{ cst_ts cs ↦ #n }}}
    Client.incr_timestamp (repr cs) @ E
  {{{ RET #(); cst_ts cs ↦ #(S n) }}}.
Proof.
iIntros "%Ψ Hn post".
rewrite /Client.incr_timestamp; wp_pures; wp_load; wp_store.
iApply "post"; iFrame.
rewrite (_ : (n + 1)%Z = (S n)%nat :> Z); last by lia.
by iFrame.
Qed.

Lemma wp_client_get_session_key E cs :
  {{{ True }}}
    Client.get_session_key (repr cs) @ E
  {{{ RET (repr (Spec.mkskey (cst_key cs))); True }}}.
Proof.
rewrite /Client.get_session_key.
iIntros "%Φ ? post". wp_pures. by iApply "post".
Qed.

End Verif.
