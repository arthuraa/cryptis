From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.algebra Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib version term gmeta nown.
From cryptis Require Import cryptis primitives tactics.
From cryptis Require Import role iso_dh.
From cryptis.store Require Import impl shared db connection_proofs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !sessionGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types (cs : conn_state).
Implicit Types kI kR kS t : term.
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Variable N : namespace.

Lemma wp_client_connect c kI kR :
  channel c -∗
  cryptis_ctx -∗
  store_ctx N -∗
  sign_key kI -∗
  public (TKey Open kR) -∗
  {{{ db_disconnected kI kR }}}
    Client.connect N c kI (TKey Open kR)
  {{{ cs, RET (repr cs);
      db_connected kI kR cs }}}.
Proof.
iIntros "#chan_c #ctx #ctx'".
iIntros "#p_ekI #p_ekR".
iIntros "!> %Φ client post".
iDestruct "client" as "(%n & %failed & db & dis)".
wp_lam. wp_pures.
iApply (wp_connection_connect with "[//] [//] [//] [//] [//] [$]") => //.
iIntros "!> %cs (conn & token)".
iApply "post".
by iFrame.
Qed.

End Verif.
