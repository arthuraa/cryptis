# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with
code in this repository.

## Project Overview

**Cryptis** is a formal verification framework for cryptographic protocols,
built on top of [Iris](https://iris-project.org/) and the
[Rocq](https://rocq-prover.org/) proof assistant. The framework allows reasoning
about protocols using a Dolev-Yao–style symbolic attacker model within a
separation logic setting.

## Keeping documentation in sync

When you change code, check in the **same pass** whether the change invalidates
any documentation, and update it. In particular:

- **This file (`CLAUDE.md`)**

- **`README.md`**: the case-study list and dependency versions. Keep both files
  consistent with the `*.opam` files, which are the ground truth for versions.
  
- **`CONTRIBUTING.md`**: General guidelines for contributing code.

- **File header comments** that state a module's purpose, invariants, or
  dependency position.

Cheap check: after renaming or removing an identifier, `grep` it across `*.md`
(and file headers) before considering the change done. Adding a case study /
primitive, or changing the term representation, requires updating `CLAUDE.md`
and `README.md`.

## Setup

**Via Nix (preferred):** The `ai` `devShell` in the project's flake provides all
of its dependencies plus `coq-lsp` and `rocq-mcp`.

**Via opam:**
```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install . # or: make builddep && make
```

The repository holds three opam packages: `rocq-cryptis` (`cryptis/`),
`rocq-cryptis-examples` (`examples/`) and `rocq-cryptis-session`
(`session/`). Each builds and installs only its own directory through
`./make-package <dir>`, assuming the packages it depends on are installed;
`make` alone builds all three.

## Useful Commands

```bash
nix develop .#ai --command make                                # build everything
nix develop .#ai --command make cryptis/core/public.vo         # build one file
nix develop .#ai --command make clean                          # clean artifacts
nix develop .#ai --command rocq-mcp                            # MCP server for Rocq
```

## Building times

Building is slow (Iris typechecking dominates). Foundational files — the
`core/term/` layer (especially `base.v` and `algebra.v`), `core/public.v`,
`cryptis.v` — cascade a rebuild through much of the tree, so an edit there costs
minutes.



## Interactive Proof Tooling (rocq-mcp)

The project ships an MCP server in `.mcp.json`. It exposes `mcp__rocq__*` tools
for interactive proof work. The schemas are surfaced as **deferred tools** —
load them on demand with `ToolSearch
query="select:mcp__rocq__rocq_start,mcp__rocq__rocq_check,..."` before calling.

When to use which:

- **Interactive proof development** (stepping through tactics, inspecting goals,
  exploring lemmas): prefer the MCP tools. `rocq_start` opens a file/theorem and
  returns a state id + current goals; `rocq_check` advances by running tactics
  (imports are cached, so iteration is fast); `rocq_step_multi` tries several
  tactics at once without committing; `rocq_query` runs
  `Search`/`Check`/`Print`/`About` without touching proof state; `rocq_toc`
  outlines a file; `rocq_assumptions` checks what a finished theorem depends on.
- **"Does the file still build?"** (after edits, or to confirm a full proof
  closes): prefer `nix develop .#ai --command make path/to/file.vo` via Bash. It
  exercises the real build, respects `_RocqProject`, and avoids loading large
  schemas into context.

Caveat: a `rocq_start` session reads the file at start time and does not track
later edits. After modifying a `.v` file, restart the session (`rocq_start`
again) before continuing — otherwise tactic results may be stale.

A second caveat: the coq-lsp process behind the MCP caches loaded `.vo`
libraries for its whole lifetime and does **not** invalidate them when you
recompile underneath it. After a `make` mid-session, a later `Require` of
anything that was rebuilt fails with `Compiled library X ... makes inconsistent
assumptions over library Y` — and `rocq_start`/`rocq_query` swallow that into a
bare "The reference … was not found in the current environment", which looks
like a load-path problem and is not. Fix: `rocq_start` with `force_restart:
true`. Rule of thumb: **any `make` invalidates every open MCP session** —
restart after rebuilding, not just after editing. (Editor clients drive the same
`coq-lsp` binary, so the same rebuild-then-everything-is-"not found" symptom
appears there; restarting the LSP server clears it.)

=
