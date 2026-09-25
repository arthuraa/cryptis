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

A second caveat, with a much worse symptom: the coq-lsp process behind the MCP caches loaded `.vo` libraries for its whole lifetime and does **not** invalidate them when you recompile underneath it. After a `make` mid-session, a later `Require` of anything that was rebuilt fails with `Compiled library X ... makes inconsistent assumptions over library Y` — and `rocq_start`/`rocq_query` swallow that into a bare "The reference … was not found in the current environment", which looks like a load-path problem and is not. Fix: `rocq_start` with `force_restart: true`. Rule of thumb: **any `make` invalidates every open MCP session** — restart after rebuilding, not just after editing. (Editor clients drive the same `coq-lsp` binary, so the same rebuild-then-everything-is-"not found" symptom appears there; restarting the LSP server clears it.)

## Setup

**Via Nix (preferred):** Use the provided `flake.nix`. Two dev shells are exposed:

- `nix develop` (or `.#default`) — `coq-lsp` and the cryptis build inputs.
- `nix develop .#ai` — everything in the default shell plus `rocq-mcp`. **Use this shell for any work that compiles Rocq files or invokes proof tooling.**

**Via opam:**
```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install . # or: make builddep && make
```

Key dependencies (authoritative pins live in `rocq-cryptis.opam` — treat it as the single source of truth): rocq-core 9.2.0, rocq-mathcomp-ssreflect 2.6.0, rocq-iris 4.5.0, rocq-iris-heap-lang 4.5.0, coq-deriving 0.2.3. `README.md` and this file must agree with the opam file.

nixpkgs has no Rocq 9.2 build of two of these, so `flake.nix` overrides them: `deriving` is
pinned to release 0.2.3 — which does support 9.2, nixpkgs' own compatibility table merely
stops at 9.1 — and `coq-lsp` is built from the upstream `v9.2` branch, since no 9.2 release is
tagged. Drop each override once nixpkgs catches up. `actris` is pinned to a fixed upstream
commit and must not be updated; it is intentionally absent from the opam file.

## Code Architecture

### Directory Structure

- **`cryptis/`** — Core library (Rocq namespace `cryptis`)
  - `lib/` — Utilities: session management, adequacy, Diffie-Hellman helpers, ghost state helpers. `dh.v` owns the protocol-independent DH reasoning, in two flavours: `dh_seed`/`dh_publ` for a seed that is never public and carries a protocol payload `P` (`dh_seed_elim*`, `dh_public_TExp`, `wp_mk_dh`), and the bare `dh_key_share` for a seed whose secrecy is conditional (`public_dh_share`, `public_dh_secret*`, used by `iso_dh` and `opaque`). Case studies instantiate these rather than re-deriving them.
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
- `TNonFree pt of PreTerm.wf pt & is_non_free pt` — the Diffie–Hellman fragment (the two inverses, the two products and exponentiation), represented indirectly by a well-formed `PreTerm.pre_term`

**Two multiplicative structures.** The DH group and the exponent ring are *separate* operations, and never mix:

| | group (base of `^`) | exponents |
| --- | --- | --- |
| product | `TGMulN` / `TGMul`, unit `TGMulN []` | `TMulN` / `TMul`, unit `TMulN []` |
| inverse | `TGInv` | `TInv` |
| factors / counting | `gfactors`, `gcount`, `ginvs_canceled` | `factors`, `count`, `invs_canceled` |
| recognisers | `is_gmul`, `is_ginv` | `is_mul`, `is_inv` |

`TExp : G → E → G` takes a group element and a scalar. The group validates `(a·b)^x = a^x·b^x`, `1^x = 1` and `(a⁻¹)^x = (a^x)⁻¹`; the exponents validate `(g^a)^b = g^(a·b)`, `g^1 = g` and `(g^a)^(a⁻¹) = g`. Both are abelian groups. The group product is what lets `examples/opaque/` express HMQV: an exponent *sum* is unavailable, but distributivity turns `Y^(x + c)` into `Y^x · Y^c`. **Identifying them is unsound**: with one carrier, those laws make `x ↦ (_^x)` a homomorphism `G → ℤ_n*`, whose image is trivial on any large prime-order subgroup — so exponentiation degenerates to the identity in any group where DLP is hard. A scalar product or scalar inverse in a *base* is therefore just an atom: `(a·b)^x` does **not** distribute.

A term heading neither exponent operation — `negb (is_enon_free t)`, where `is_enon_free := is_inv || is_mul` (`core/term/base.v`, the exponent-side sibling of `PreTerm.is_gnon_free`) — is its own single `factors` entry, so a signed `count` between two such terms is decided by plain disequality. `core/term/algebra.v` packages that as `TInv_Nenf_ne`, `count_Nenf_ne`, `elem_of_factors_cons` / `elem_of_factors_cons_weak` and `not_elem_of_factors_TMulN_Nenf`; a protocol that must locate one exponent inside a product of others (`examples/opaque/`) goes through them, with `Nenf_TNonce` / `Nenf_THash` discharging the side conditions.

Underneath, `PreTerm.pre_term` is an *arity-indexed* datatype: `PT0 o`, `PT1 o pt`, `PT2 o pt1 pt2` and `PTN o ts`, where the operations of each arity live in their own inductive (`term_op0`, `term_op1`, `term_op2`, `term_opN`) with its own derived `eqType`/`choiceType`/`countType`/`orderType`. `term_op1` has `O1Key | O1Hash | O1Inv | O1GInv` and `term_opN` has `ONMul | ONGMul`, with `PTInv`/`PTGInv`/`PTMul`/`PTGMul` as `Notation`s — so `match`es and `case` patterns keep naming each operation directly, and adding another one turns every operation-specific `match` into a non-exhaustiveness error rather than a silent wrong branch. Two habits follow: in `case`/`elim` intro patterns the op1 and n-ary branches destruct the operation (`case: pt => [o|[k| | |] t|o t1 t2|[|] ts]`, or `[|||[|] ts]` when the other branches need no names); and structural functions that ignore the operation (`height`, `PreTerm.tsize`, `nonces_of_pre_term`) match on `PT1 _`/`PTN _ ts`, while operation-specific ones (`is_mul`, `is_gmul`, `factors`, `gfactors`, `wf`, `normalize`) match on the notation. New constructors go **last**, so the `deriving`-generated order agrees with the tag order HeapLang's `leq_term_op1`/`leq_term_opN` compare. The HeapLang encoding mirrors the arities too: `(#TOpN_tag, (repr o, repr_list …))`, with `repr ONMul = #TMul_tag` and `repr ONGMul = #TGMul_tag`.

`TInv`, `TGInv`, `TExp`, `TExpN`, `TMul`, `TMulN`, `TGMul`, `TGMulN` are **smart constructors** (locked `Definition`s over `TNonFree`), *not* real constructors — so `case`/`elim` on them is not structural; use the custom induction principles (`term_ind`/`term_rect` in `core/term/base.v`, `term_lt_ind` in `core/term/tsize.v`). Typed key wrappers `aenc_key`/`sign_key`/`senc_key` sit on top of `TKey`, and the surface API lives in `Module Spec` (`core/term/spec.v`: `Spec.tag`, `Spec.of_list`, `Spec.pkey`, `Spec.to_list`, …).

Exponentiation is an endomorphism of the *group*: `(a·b)^x = a^x·b^x`, and hence also `1^x = 1` and `(a⁻¹)^x = (a^x)⁻¹`. `PreTerm.wf` therefore demands that the base of a normal-form exponential be a **group atom** — neither group product, nor group inverse, nor exponential (`negb (is_gnon_free b)`, the smaller sibling of the `is_non_free` that `TNonFree` uses); `PreTerm.exp` re-establishes this by spreading over `PreTerm.gfactors` (`exp b e := gmul ((λ t, exp_aux t e) <$> gfactors b)`, with `exp_aux` handling the `PTGInv` case and `mk_exp` the `e = 1` guard). Two consequences bite downstream: `TExp` is **not** injective in the exponent at the group unit, so `TExp_injr`, `base_TExp`, `expo_TExp`, `tsize_TExp`, `minted_TExp`, `public_TExpN` and friends carry `negb (is_gmul b)` / `negb (is_ginv b)` premises; and a protocol that exponentiates an attacker-supplied value must either reject the identity or reason factor-by-factor (`gfactors_TExp`, `public_TExp_gfactors`, `subterm_TExp_gfactors`). Note there is **no** `is_mul_base`/`is_inv_base`: only `is_gmul_base`/`is_ginv_base` hold, since `wf (PTExp (PTMul ts) e)` is legal.

The term layer is split across `core/term/` and aggregated by `core/term.v`: `base.v` (the `term` inductive, the `unfold`/`fold` ↔ `pre_term` conjugation, smart constructors, instances, destructor defs, the two counting APIs (`count`/`count_inj`/`count_TMulN`/`count_TInv` and `gcount`/`gcount_inj`/`gcount_TGMulN`/`gcount_TGInv`), and the structural `term_rect`/`term_ind` eliminators), `algebra.v` (both abelian-group theories + DH-exponentiation laws), `tsize.v` (the `tsize` measure, its termination lemmas, and the well-founded `term_lt_rect`/`term_lt_ind`), `repr.v` (`val_of_term`/`repr`), `nonces.v`, `subterms.v`, `spec.v`. Downstream imports `cryptis.core.term`, so the split is transparent — but **module-qualified references (`base.foo`) break when a lemma moves file**; prefer unqualified names. Each split file must re-declare the file-local `Implicit Types (t k : term) (ts : list term).` and `Set Implicit Arguments.` block (those do not cross a `Require` boundary).

**The Public Predicate** (`core/public.v`): Central to the framework. `public t` (an Iris proposition) holds when term `t` is known to the attacker. Protocol proofs establish invariants about which terms are and are not public.

**Encryption Predicates** (`core/public.v`): Per-protocol invariants attached to a namespace `N`, one per key usage:
- `aenc_pred N (Φ : aenc_key → term → iProp)` — asymmetric-encryption invariant
- `sign_pred N (Φ : sign_key → term → iProp)` — signing invariant
- `senc_pred N (Φ : senc_key → term → iProp)` — symmetric-encryption invariant

These are thin wrappers over the generic `seal_pred F N Φ` (with `F : functionality = AENC | SIGN | SENC`); predicates are allocated against a `seal_pred_token F E`.

**HeapLang Primitives** (`primitives/`): Concrete implementations with associated Hoare-triple specs — sealing (`aenc`/`adec`, `sign`/`verify`, `senc`/`sdec`), `hash`, key handling (`pkey`, `mk_nonce`, `mk_aenc_key`, `mk_sign_key`, `derive_senc_key`, `is_aenc_key`), Diffie–Hellman (`tint`, `texp`; group operations `tgmul`, `tginv`, `tgone`; exponent operations `tmul`, `tinv`, `tone`), the generic `open`, and channel I/O (`send`, `recv`).  `primitives/attacker.v` exposes every one of these to the symbolic attacker — omitting one would make it strictly weaker than a real attacker.

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

**mathcomp ↔ stdpp boundary:** `core/pre_term/base.v` is implemented in mathcomp (`seq`, `%O` order, `~~`, `sort <=%O`, bigops, `deriving`); `core/pre_term/normalize.v` (normal forms + the `wf`/`normalize` machinery) is already stdpp-only. `core/pre_term/with_stdpp.v` is *the* bridge, and is where any new mathcomp→stdpp translation belongs: it packages the deriving-generated order both as `pt_order` (a stdpp `relation` with `RelDecision`/`Transitive`/`Total`/`AntiSymm`) and as a global `Lexico PreTerm.pre_term` instance (with `StrictOrder`/`TrichotomyT`, which is what makes `bool_decide (x = y ∨ lexico x y)` decidable), and proves `pt_order_lexico`, `pt_order_N` (the derived order on `PTN o ts` *is* stdpp's `lexico` on `ts`) and `pt_orderE` (the structural comparison equation, stated with `bool_decide` and `op0_le`/`op1_le`/`op2_le`/`opN_le` instead of `<=%O`). Because of that bridge, `primitives/pre_term.v` — which implements the `normalize.v` operations in HeapLang — needs no mathcomp beyond `ssreflect`. Everything from `core/term/` upward is stdpp (`Forall`, `≡ₚ`, `∈`, `merge_sort`). The active boolean→Prop coercion above `pre_term` is stdpp's `Is_true`, **not** ssreflect's `is_true` (bridged by `is_trueP` in `lib/mathcomp_compat.v`); mixing the two silently breaks `rewrite`/`apply`.

### Case Studies

Directory-structured protocols use some of: `impl.v` (HeapLang implementation), a `proofs.v` / `proofs/` tree (Iris security proofs), and `game.v` (security game + final `*_secure` theorem via `cryptis_adequacy`). **The layout is not uniform** — proof decomposition and the name/location of the final theorem vary per protocol, so inspect a protocol's files rather than assuming the pattern.

- `nsl/` — Needham–Schroeder–Lowe public-key protocol (with game); `nsl_secr.v` / `nsl_auth.v` are standalone single-file variants (secrecy / agreement).
- `nsl_dh/` — NSL with Diffie–Hellman key exchange (with game).
- `iso_dh/` — ISO protocol with DH key exchange + digital signatures (game in `iso_dh/game.v`).
- `gen_conn/`, `conn/` — generic and authenticated secure-connection layers (building blocks).
- `rpc/` — remote procedure calls over `conn`.
- `store/` — authenticated key-value store over `rpc` (game in `store/game.v`); `alist/` is a supporting association-list module.
- `opaque/` — OPAQUE-style password-authenticated key exchange, with the paper's **HMQV** key exchange (partial: `impl.v`, `shared.v`, `client_proofs.v`, `server_proofs.v`, `game.v`; `game.v` stops at `wp_game`, no closed theorem yet). The key `(X_b · P_b^m_b)^(x_a + m_a·p_a)` needs an exponent sum the algebra does not have, so distributivity trades it for a group product: `(X_b · P_b^m_b)^x_a · (X_b · P_b^m_b)^(m_a·p_a)` (`hmqv_K` in `shared.v`; `hmqv_K_sym` says both roles compute the same element). Secrecy rests on the static-static group factor `g^(p_b·m_b·m_a·p_a)`, which survives whatever `X_b` the peer sends — that is HMQV's own argument, symbolically the occurs check `gcount_TExp_eq0` (`core/term/tsize.v`): the multiplier `m_b` is a hash of `X_b`, hence strictly bigger, so `X_b` cannot contain it. `hmqv_key_gfactors` packages what both roles need.
- `tls13/` — TLS 1.3 handshake (partial; `impl.v` executable layer + per-component `proofs/` (base, meth, cshare, sshare, cparams, sparams) + `proofs/protocol.v`, no closed theorem yet).
- `challenge_response.v` — signature-based mutual authentication; `composite_game.v` runs several protocols together under one adequacy game.
- `permanent.v`, `counter.v` — small digital-signature demos (immutable state / monotone counter).

The `gen_conn → conn → rpc → store` chain is a real abstraction stack (reuse it), and the `nsl` / `iso_dh` / `store` `game.v` files share a consistent template worth following.
