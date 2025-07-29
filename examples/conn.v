From cryptis.examples Require Import iso_dh.
From cryptis.examples.gen_conn Require impl.
From cryptis.examples.conn Require Import proofs.

Module Conn.
Include cryptis.examples.gen_conn.impl.
Include cryptis.examples.conn.proofs.base.
Include cryptis.examples.conn.proofs.
End Conn.
