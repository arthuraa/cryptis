# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**Cryptis** is a formal verification framework for cryptographic protocols, built on top of [Iris](https://iris-project.org/) (a separation logic framework) and [HeapLang](https://plv.mpi-sws.org/iris/). It provides tools for proving security properties of cryptographic protocol implementations in the [Rocq](https://rocq-prover.org/) (formerly Coq) proof assistant.

The framework allows reasoning about protocols using a Dolev-Yao–style symbolic attacker model within a separation logic setting.

## Keeping documentation in sync

When you change code, check in the **same pass** whether the change invalidates any documentation, and update it. Docs that drift from the code are worse than no docs — a wrong `term` datatype or stale version misleads both human maintainers and future agent sessions. In particular:

- **This file (`CLAUDE.md`)** — the `term` datatype and smart-constructor list, the encryption-predicate and primitive names, the dependency versions, the module dependency order, and the case-study list.
- **`README.md`** — the case-study list and dependency versions. Keep both files consistent with `rocq-cryptis.opam`, which is the single source of truth for versions.
- **File header comments** that state a module's purpose, invariants, or dependency position.

Cheap check: after renaming or removing an identifier, `grep` it across `*.md` (and file headers) before considering the change done. Adding a case study / primitive, or changing the term representation, requires updating `CLAUDE.md` and `README.md`.

## Build Commands

Rocq and its dependencies are not on the default PATH. Always wrap build/check commands in the project's `ai` dev shell, which provides `coq-lsp` plus `rocq-mcp`:

```bash
nix develop .#ai --command make                                # build everything
nix develop .#ai --command make cryptis/core/public.vo         # build one file
nix develop .#ai --command make clean                          # clean artifacts
```

Other useful commands inside the shell: `make builddep` (install build deps via opam, only needed outside Nix), `rocq compile <file.v>` (compile a single `.v` file directly).

Building is slow (Iris typechecking dominates). Foundational files — the `core/term/` layer (especially `base.v` and `algebra.v`), `core/public.v`, `cryptis.v` — cascade a rebuild through much of the tree, so an edit there costs minutes, not seconds. Prefer targeted builds (`make path/to/file.vo`) while iterating, and run the full `make` only to verify everything compiles. `make -k -j<N>` keeps going past the first error and surfaces every root failure at once (dependents of a failed file are silently skipped, so re-run after each fix).

## Interactive Proof Tooling (rocq-mcp)

The project ships an MCP server in `.mcp.json` (`rocq`, launched via `nix develop .#ai --command rocq-mcp`). It exposes `mcp__rocq__*` tools for interactive proof work. The schemas are surfaced as **deferred tools** — load them on demand with `ToolSearch query="select:mcp__rocq__rocq_start,mcp__rocq__rocq_check,..."` before calling.

When to use which:

- **Interactive proof development** (stepping through tactics, inspecting goals, exploring lemmas): prefer the MCP tools. `rocq_start` opens a file/theorem and returns a state id + current goals; `rocq_check` advances by running tactics (imports are cached, so iteration is fast); `rocq_step_multi` tries several tactics at once without committing; `rocq_query` runs `Search`/`Check`/`Print`/`About` without touching proof state; `rocq_toc` outlines a file; `rocq_assumptions` checks what a finished theorem depends on.
- **"Does the file still build?"** (after edits, or to confirm a full proof closes): prefer `nix develop .#ai --command make path/to/file.vo` via Bash. It exercises the real build, respects `_CoqProject`, and avoids loading large schemas into context.

Caveat: a `rocq_start` session reads the file at start time and does not track later edits. After modifying a `.v` file, restart the session (`rocq_start` again) before continuing — otherwise tactic results may be stale.

## Setup

**Via Nix (preferred):** Use the provided `flake.nix`. Two dev shells are exposed:

- `nix develop` (or `.#default`) — `coq-lsp` and the cryptis build inputs.
- `nix develop .#ai` — everything in the default shell plus `rocq-mcp`. **Use this shell for any work that compiles Rocq files or invokes proof tooling.**

**Via opam:**
```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install . # or: make builddep && make
```

Key dependencies (authoritative pins live in `rocq-cryptis.opam` — treat it as the single source of truth): rocq-core 9.1.1, rocq-mathcomp-ssreflect 2.5.0, rocq-iris 4.5.0, rocq-iris-heap-lang 4.5.0, coq-deriving 0.2.3. `README.md` and this file must agree with the opam file.

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

**Cryptographic Terms** (`core/term/base.v`): The main inductive type `term` is:
- `TInt (n : Z)` — integers/constants
- `TPair t1 t2` — pairs (n-ary tuples are nested pairs; see `Spec.of_list`)
- `TNonce (a : nonce)` — nonces
- `TKey (kt : key_type) t` — keys, where `key_type = AEnc | ADec | Sign | Verify | SEnc`
- `TSeal k t` — a single sealing constructor covering asymmetric encryption, signatures, and symmetric encryption (disambiguated by the key's `key_type`)
- `THash t` — hashes
- `TNonFree pt of PreTerm.wf_term pt & is_non_free pt` — the Diffie–Hellman fragment (inverse / exponentiation / product), represented indirectly by a well-formed `PreTerm.pre_term`

`TInv`, `TExp`, `TExpN`, `TMul`, `TMulN` are **smart constructors** (locked `Definition`s over `TNonFree`), *not* real constructors — so `case`/`elim` on them is not structural; use the custom induction principles (`term_ind`/`term_rect` in `core/term/base.v`, `term_lt_ind` in `core/term/tsize.v`). Typed key wrappers `aenc_key`/`sign_key`/`senc_key` sit on top of `TKey`, and the surface API lives in `Module Spec` (`core/term/spec.v`: `Spec.tag`, `Spec.of_list`, `Spec.pkey`, `Spec.to_list`, …).

The term layer is split across `core/term/` and aggregated by `core/term.v`: `base.v` (the `term` inductive, the `unfold`/`fold` ↔ `pre_term` conjugation, smart constructors, instances, destructor defs, the `count_factors_*` counting API, and the structural `term_rect`/`term_ind` eliminators), `algebra.v` (multiplicative-group + DH-exponentiation laws), `tsize.v` (the `tsize` measure, its termination lemmas, and the well-founded `term_lt_rect`/`term_lt_ind`), `repr.v` (`val_of_term`/`repr`), `nonces.v`, `subterms.v`, `spec.v`. Downstream imports `cryptis.core.term`, so the split is transparent — but **module-qualified references (`base.foo`) break when a lemma moves file**; prefer unqualified names. Each split file must re-declare the file-local `Implicit Types (t k : term) (ts : list term).` and `Set Implicit Arguments.` block (those do not cross a `Require` boundary).

**The Public Predicate** (`core/public.v`): Central to the framework. `public t` (an Iris proposition) holds when term `t` is known to the attacker. Protocol proofs establish invariants about which terms are and are not public.

**Encryption Predicates** (`core/public.v`): Per-protocol invariants attached to a namespace `N`, one per key usage:
- `aenc_pred N (Φ : aenc_key → term → iProp)` — asymmetric-encryption invariant
- `sign_pred N (Φ : sign_key → term → iProp)` — signing invariant
- `senc_pred N (Φ : senc_key → term → iProp)` — symmetric-encryption invariant

These are thin wrappers over the generic `seal_pred F N Φ` (with `F : functionality = AENC | SIGN | SENC`); predicates are allocated against a `seal_pred_token F E`.

**HeapLang Primitives** (`primitives/`): Concrete implementations with associated Hoare-triple specs — sealing (`aenc`/`adec`, `sign`/`verify`, `senc`/`sdec`), `hash`, key handling (`pkey`, `mk_nonce`, `mk_aenc_key`, `mk_sign_key`, `derive_senc_key`, `is_aenc_key`), Diffie–Hellman (`tint`, `texp`), the generic `open`, and channel I/O (`send`, `recv`).

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

**mathcomp ↔ stdpp boundary:** `core/pre_term/` is implemented in mathcomp (`seq`, `%O` order, `~~`, `sort <=%O`, bigops) and exposes a stdpp-facing API via `core/pre_term/normalize.v` (normal forms + the `wf`/`normalize` machinery), `laws.v` (the algebraic theory of the operations and destructors), and `with_stdpp.v`. Everything from `core/term/` upward is stdpp (`Forall`, `≡ₚ`, `∈`, `merge_sort`). The active boolean→Prop coercion above `pre_term` is stdpp's `Is_true`, **not** ssreflect's `is_true` (bridged by `is_trueP` in `lib/mathcomp_compat.v`); mixing the two silently breaks `rewrite`/`apply`.

### Case Studies

Directory-structured protocols use some of: `impl.v` (HeapLang implementation), a `proofs.v` / `proofs/` tree (Iris security proofs), and `game.v` (security game + final `*_secure` theorem via `cryptis_adequacy`). **The layout is not uniform** — proof decomposition and the name/location of the final theorem vary per protocol, so inspect a protocol's files rather than assuming the pattern.

- `nsl/` — Needham–Schroeder–Lowe public-key protocol (with game); `nsl_secr.v` / `nsl_auth.v` are standalone single-file variants (secrecy / agreement).
- `nsl_dh/` — NSL with Diffie–Hellman key exchange (with game).
- `iso_dh/` — ISO protocol with DH key exchange + digital signatures (game in `iso_dh/game.v`).
- `gen_conn/`, `conn/` — generic and authenticated secure-connection layers (building blocks).
- `rpc/` — remote procedure calls over `conn`.
- `store/` — authenticated key-value store over `rpc` (game in `store/game.v`); `alist/` is a supporting association-list module.
- `opaque/` — OPAQUE-style password-authenticated key exchange (partial: `impl.v` + `game.v`, no closed theorem yet).
- `tls13/` — TLS 1.3 handshake (partial; `impl.v` executable layer + per-component `proofs/` (meth, cshare, sshare, cparams, sparams) + `proofs/protocol.v`, no closed theorem yet).
- `challenge_response.v` — signature-based mutual authentication; `composite_game.v` runs several protocols together under one adequacy game.
- `permanent.v`, `counter.v` — small digital-signature demos (immutable state / monotone counter).

The `gen_conn → conn → rpc → store` chain is a real abstraction stack (reuse it), and the `nsl` / `iso_dh` / `store` `game.v` files share a consistent template worth following.
