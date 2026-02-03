From cryptis.examples.iso_dh Require Export impl proofs.
From cryptis.examples.iso_dh.proofs Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*

A --> B: g^a; pkA
B --> A: {g^a; g^b; pkA}@skB
A --> B: {g^a; g^b; pkB}@skA

Key: [g^a; g^b; g^ab]

*)
