From cryptis Require Import iso_dh.
From cryptis.rpc Require Import props impl proofs.

Module RPC.

Include Props.
Include Impl.
Include Proofs.

End RPC.

Coercion RPC.cs_si : RPC.state >-> sess_info.
