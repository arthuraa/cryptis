# Cryptis: Cryptographic Reasoning in Separation Logic

The material covered in the paper can be found in the following files:

## Core Library

In the `cryptis` directory you will find:

- `lib/*, lib`: General additions to Iris and MathComp.  List manipulation programs for
  HeapLang.
- `core/*`, `cryptis`: Core Cryptis components: cryptographic terms, the
  `public` predicate, encryption predicates, and term metadata.
- `primitives/*`, `primitives`: HeapLang functions for manipulating
  cryptographic terms.  Definition of the attacker.
- `tactics`: Ltac tactics for symbolically executing the main HeapLang functions
  on terms.

## Case studies

In the `examples` you will find our case studies:

- `nsl`: NSL protocol, including game.
- `iso_dh`: ISO protocol with DH key exchange and digital signatures (game is in
  its own file).
- `conn`: Authenticated connections
- `rpc`: Remote procedure calls
- `store`: Authenticated key-value store (game is in its own file).
  
## Building

Cryptis is known to compile with the following dependencies:

- rocq-prover v9.0.0
- rocq-mathcomp-ssreflect v2.4.0
- coq-deriving v0.2.2
- coq-iris v4.4.0
- coq-iris-heap-lang v4.4.0

### Nix

If you use Nix, the accompanying flake file should be enough to install all the
required dependencies.  To compile and check all proofs, simply type `make`.

### opam

Make sure to add the Rocq opam repository to your switch:

```opam repo add rocq-released https://rocq-prover.org/opam/released```

Afterwards, Cryptis can be installed with:

```opam install .```

Alternatively, run `make builddep` to produce and install a dummy package that
installs the correct dependencies and run `make`.
