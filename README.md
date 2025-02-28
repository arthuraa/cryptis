# Cryptis: Cryptographic Reasoning in Separation Logic

Cryptis is known to compile with the following dependencies:

- Coq v8.18
- coq-iris v4.2
- coq-mathcomp-ssreflect v1.18.0
- coq-deriving v0.1.1

If you use Nix, the accompanying flake file should be enough to install all the
required dependencies.  To compile and check all proofs, simply type `make`.

The material covered in the paper can be found in the following files:

## Core Library

- `mathcomp_compat`: Compatibility with the Mathematical Components library
- `lib`: General additions to Iris and MathComp.  List manipulation programs for
  HeapLang.
- `core/*`, `cryptis`: Definitions of cryptographic terms and of the `public`
  predicate.
- `cryptis`: Definitions of the main predicates of the Cryptis logic on top of
  Iris.  In particular, this includes tag invariants for encrypted terms, keys
  and hashes.
- `primitives/*`, `primitives`: HeapLang functions for manipulating
  cryptographic terms.  Definition of the attacker.
- `tactics`: Ltac tactics for symbolically executing the main HeapLang functions
  on terms.

## Case studies

- `examples/nsl.v`: NSL protocol, including game.
- `iso_dh/*`, `iso_dh`: ISO protocol with DH key exchange and digital signatures
  (game is in its own file).
- `conn/*`, `conn`: Authenticated connections
- `store/*`, `store`: Authenticated key-value store (game is in its own file).
  
