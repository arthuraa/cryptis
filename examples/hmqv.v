From cryptis.examples.hmqv Require Export impl proofs.
From cryptis.examples.hmqv.proofs Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

HMQV-C, three messages.  Each party has a long-term key pair [p, g^p]; the
public keys stand in for the identities.

A --> B: g^a; P_A
B --> A: g^b; H(σ, N)
A --> B: H'(σ, N)

σ is the HMQV element, H and H' its two tagged hashes (the authenticators).
Ephemeral private keys are resources of their owners, who may leak them.

Key: derive_key (H''(σ)), returned with the party's ephemeral private key


*)
