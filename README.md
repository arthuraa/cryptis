# Cryptis: Composition and Separation for Cryptographic Protocols

Cryptis is known to compile with the following dependencies in the OPAM Coq
repository:

- Coq 8.14
- coq-iris v3.5
- coq-mathcomp-ssreflect v1.12
- coq-deriving v0.1.0

## Core Library

- `mathcomp_compat`: Compatibility with the Mathematical Components library
- `lib`: General additions to Iris and MathComp.  List manipulation programs for
  HeapLang.
- `pre_term`, `term`: Cryptographic terms manipulated by protocols in Cryptis.
- `cryptis`: Definitions of the main predicates of the Cryptis logic on top of
  Iris.  In particular, this includes tag invariants for encrypted terms, keys
  and hashes.
- `primitives/*`, `primitives`: HeapLang functions for manipulating
  cryptographic terms.
- `tactics`: Ltac tactics for symbolically executing the main HeapLang functions
  on terms.
- `session`: Predicates and invariants for agreeing on session parameters. Note
  that, although this file is used in the development, it is more general than
  what is needed to derive the examples in the paper.
- `dh`: Additional lemmas for deriving forward secrecy properties with
  Diffie-Hellman key exchange.
- `attacker`: Type system for writing attacker code.

## Case studies

- `challenge_response`: Authentication based on digital signatures.
- `nsl`, `nsl_dh`, `nsl_dh_game`: NSL with Diffie-Hellman key exchange. Includes
  a generalized version of the NSL protocol, and the game-based proof of forward
  secrecy for NSL+DH.
- `tls13`: The model of the TLS 1.3 handshake.
- `composite_game`: A game-based security proof for TLS 1.3 when all previous
  three protocols are running together.
  
