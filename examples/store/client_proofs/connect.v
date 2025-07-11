From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.algebra Require Import dfrac_agree.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib term gmeta nown.
From cryptis Require Import cryptis primitives tactics role.
From cryptis.examples Require Import conn rpc.
From cryptis.examples.store Require Import impl shared db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Verif.

Context `{!cryptisGS Σ, !heapGS Σ, !Conn.connGS Σ, !RPC.rpcGS Σ, !storeGS Σ}.
Notation iProp := (iProp Σ).

Context `{!storeG Σ}.

Implicit Types (cs : Conn.state).
Implicit Types (skI skR : sign_key) (kS t : term).
Implicit Types n : nat.
Implicit Types γ : gname.
Implicit Types v : val.

Lemma wp_client_connect c skI skR :
  channel c -∗
  cryptis_ctx -∗
  store_ctx -∗
  minted skI -∗
  minted skR -∗
  {{{ db_disconnected skI skR }}}
    Client.connect c skI (Spec.pkey skR)
  {{{ cs, RET (repr cs);
      db_connected skI skR cs }}}.
Proof.
iIntros "#chan_c #ctx #ctx'".
iPoseProof (store_ctx_rpc_ctx with "ctx'") as "?".
iIntros "#p_ekI #p_ekR".
iIntros "!> %Φ client post".
iDestruct "client" as "(%db & ready & state)".
wp_lam. wp_pures.
iApply (RPC.wp_connect (db_client_ready skI skR db)
         with "[//] [//] [//] [] [] [$]") => //.
iIntros "!> %cs (conn & ready)".
iApply "post".
by iFrame.
Qed.

End Verif.
