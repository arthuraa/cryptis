From cryptis.examples Require Import iso_dh.
From cryptis.examples.gen_conn Require Import impl proofs.

Module GenConn.
Include cryptis.examples.gen_conn.impl.
Include cryptis.examples.gen_conn.proofs.base.
Include cryptis.examples.gen_conn.proofs.
End GenConn.

Coercion GenConn.cs_si : GenConn.state >-> sess_info.
