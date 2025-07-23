From cryptis.examples Require Import iso_dh.
From cryptis.examples.conn Require Import impl proofs.

Module Conn.
Include cryptis.examples.conn.impl.
Include cryptis.examples.conn.proofs.base.
Include cryptis.examples.conn.proofs.
End Conn.

Coercion Conn.cs_si : Conn.state >-> sess_info.
