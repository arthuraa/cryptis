From cryptis.examples Require Import iso_dh.
From cryptis.examples.rpc Require Import impl proofs.

Module RPC.

Include cryptis.examples.rpc.impl.
Include cryptis.examples.rpc.proofs.base.
Include cryptis.examples.rpc.proofs.

End RPC.

Existing Instance RPC.repr_handler.
Existing Instance RPC.persistent_wf_handler.
#[global] Typeclasses Opaque RPC.wf_handler.
