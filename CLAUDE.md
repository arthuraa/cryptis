# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**Cryptis** is a formal verification framework for cryptographic protocols, built on top of [Iris](https://iris-project.org/) (a separation logic framework) and [HeapLang](https://plv.mpi-sws.org/iris/). It provides tools for proving security properties of cryptographic protocol implementations in the [Rocq](https://rocq-prover.org/) (formerly Coq) proof assistant.

The framework allows reasoning about protocols using a Dolev-Yao–style symbolic attacker model within a separation logic setting.

## Build Commands

```bash
# Build everything (generates RocqMakefile from _CoqProject then runs it)
make

# Install build dependencies via opam
make builddep

# Build a single file (e.g., to check just one proof)
make cryptis/core/public.vo

# Clean all build artifacts
make clean
```

Building is slow — individual `.vo` files can be large (e.g., `lib.vo` ~600MB). Use targeted builds when working on a specific file.

## Setup

**Via Nix (preferred):** Use the provided `flake.nix`.

**Via opam:**
```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install . # or: make builddep && make
```

Key dependencies: Rocq 9.1.0, rocq-mathcomp-ssreflect 2.5.0, coq-iris 4.4.0, coq-iris-heap-lang 4.4.0, coq-deriving 0.2.2.

## Code Architecture

### Directory Structure

- **`cryptis/`** — Core library (Rocq namespace `cryptis`)
  - `lib/` — Utilities: session management, adequacy, Diffie-Hellman helpers, ghost state helpers
  - `core/` — Foundation: term definitions, public predicate, term metadata
  - `primitives/` — HeapLang implementations of cryptographic operations
  - `tactics.v` — Ltac2 automation for symbolic execution of HeapLang programs
  - `cryptis.v` — Top-level integration; defines `cryptisGpreS`/`cryptisGS` typeclasses
  - `adequacy.v` — Soundness/adequacy theorems

- **`examples/`** — Case studies (Rocq namespace `cryptis.examples`)

### Core Concepts

**Cryptographic Terms** (`core/term/`): The main inductive type `term` represents symbolic cryptographic values:
- `TNonce a` — nonces
- `TKey kt k` — keys (key types: `Enc`, `Sign`, `Sym`)
- `TEnc t1 t2`, `TSEnc t1 t2`, `TSign t1 t2` — asymmetric/symmetric encryption, signatures
- `THash t` — hashes
- `TTuple ts` — tuples

**The Public Predicate** (`core/public.v`): Central to the framework. `public t` (an Iris proposition) holds when term `t` is known to the attacker. Protocol proofs establish invariants about which terms are and are not public.

**Encryption Predicates** (`core/public.v`): Per-protocol specifications registered via namespaces:
- `aenc_pred N Φ` — asymmetric encryption invariant
- `sign_pred N Φ` — signing invariant
- `senc_pred N Φ` — symmetric encryption invariant

**HeapLang Primitives** (`primitives/`): Concrete implementations of `aenc`, `adec`, `sign`, `verify`, `senc`, `sdec`, `hash`, `pkey`, `send`, `recv`, etc., with associated Hoare triple specifications.

**Tactics** (`tactics.v`): Custom tactics (`tac_wp_hash`, `tac_wp_list_match`, etc.) for stepping through HeapLang programs that manipulate cryptographic terms.

### Module Dependency Order

```
examples/*
  → cryptis + primitives + tactics
    → cryptis.v (integration)
      → core/public.v, core/term_meta.v, core/minted.v
        → core/term/, core/pre_term/
          → lib/
            → mathcomp, iris, iris.heap_lang
```

The `_CoqProject` file specifies the exact file ordering for compilation.

### Case Studies

Each protocol in `examples/` follows the pattern:
- `impl.v` — HeapLang implementation
- `proofs/` — Iris proof of security properties
- `game.v` — Security game definition and final theorem

Protocols included: NSL, ISO-DH, generic authenticated connections, RPC, authenticated key-value store, public-key authentication (generalized NSL), TLS 1.3 (partial).
