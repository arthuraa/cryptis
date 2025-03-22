From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.algebra Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis primitives tactics.
From cryptis Require Import role conn rpc.
From cryptis.store Require Import impl shared db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types (cs : Conn.state).
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
  {{{ db_disconnected N kI kR }}}
    Client.connect N c kI (TKey Open kR)
  {{{ cs, RET (repr cs);
      db_connected N kI kR cs }}}.
Proof.
iIntros "#chan_c #ctx #ctx'".
iPoseProof (store_ctx_rpc_ctx with "ctx'") as "?".
iIntros "#p_ekI #p_ekR".
iIntros "!> %Φ client post".
iDestruct "client" as "(%n & %db & dis & version & #db_at & state)".
wp_lam. wp_pures.
iApply (RPC.wp_connect True%I with "[//] [//] [//] [//] [//] [$]") => //.
iIntros "!> %cs (conn & _)".
iApply "post".
by iFrame.
Qed.

End Verif.
