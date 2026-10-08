# Cryptis: Cryptographic Reasoning in Separation Logic

The material covered in the paper can be found in the following files:

## Core Library

In the `cryptis` directory you will find:

- `lib/*, lib`: General additions to Iris, MathComp, and stdpp; Diffie–Hellman and
  ghost-state helpers; list-manipulation programs for HeapLang.
- `core/*`, `cryptis`: Core Cryptis components: cryptographic terms, the
  `public` predicate, encryption predicates, and term metadata.
- `primitives/*`, `primitives`: HeapLang functions for manipulating
  cryptographic terms.  Definition of the attacker.
- `tactics`: Ltac tactics for symbolically executing the main HeapLang functions
  on terms.

## Case studies

In the `examples` directory you will find our case studies:

- `nsl`: Needham–Schroeder–Lowe public-key protocol, including game (`nsl_secr.v`
  and `nsl_auth.v` are standalone single-file variants for secrecy / agreement).
- `nsl_dh`: NSL with Diffie–Hellman key exchange, including game.
- `iso_dh`: ISO protocol with DH key exchange and digital signatures (game is in
  its own file).
- `gen_conn`, `conn`: Generic and authenticated secure-connection layers.
- `rpc`: Remote procedure calls (built on `conn`).
- `store`: Authenticated key-value store built on `rpc` (game is in its own file);
  `alist` is a supporting association-list module.
- `opaque`: OPAQUE-style password-authenticated key exchange with HMQV,
  including game and ISO-DH-style authentication (resource exchange, tokens
  on the session key).
- `tls13`: TLS 1.3 handshake (partial; `impl.v` + per-component `proofs/`).
- `challenge_response`, `composite_game`, `permanent`, `counter`: smaller
  single-file examples plus a composite security game.

## Session types

In the `session` directory (Rocq namespace `cryptis.sess`) you will find
Actris-style session types for authenticated channels built on `iso_dh` and
`gen_conn`: `impl`, `proofs`, `proofs/base` (aggregated by `sess`), the
tagged-message layer `tag`, the `trusted` wrapper for honest parties, and
`proofmode` tactics.  Its case studies live in `session/examples`:

- `basic`: small protocols (send-42, vote, key-value database).
- `store`: authenticated key-value store over session types (game is in its
  own file).

## Building

Cryptis is known to compile with the following dependencies:

- rocq-prover
- rocq-core v9.2.0
- rocq-mathcomp-ssreflect v2.6.0
- coq-deriving v0.2.3
- rocq-iris v4.5.0
- rocq-iris-heap-lang v4.5.0
- rocq-actris fa66960 (Nix)/367149a (opam)

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
