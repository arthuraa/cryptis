From cryptis Require Import iso_dh.
From cryptis.conn Require Import props impl proofs.

Module Conn.

Include Props.
Include Impl.
Include Proofs.

End Conn.

Coercion Conn.cs_si : Conn.state >-> sess_info.
Existing Instance Conn.repr_handler.
Existing Instance Conn.persistent_wf_handler.
#[global] Typeclasses Opaque Conn.wf_handler.
