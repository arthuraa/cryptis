From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta nown cryptis.
From cryptis Require Import primitives tactics role iso_dh conn.
From cryptis.store Require Import impl shared db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types (cs : Conn.state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_close c kI kR cs :
  channel c -∗
  store_ctx N -∗
  {{{ db_connected N kI kR cs }}}
    Client.close N c (repr cs)
  {{{ RET #(); db_disconnected N kI kR }}}.
Proof.
iIntros "#chan_c (_ & _ & _ & _ & _ & _ & #?)".
iIntros "!> %Φ client post".
iDestruct "client" as "(%n & client & conn & token)".
wp_lam. wp_pures.
wp_apply (Conn.wp_close with "[//] [//] [$]").
iIntros "%failed [#failed dis]". iApply "post".
by iFrame.
Qed.

End Verif.
