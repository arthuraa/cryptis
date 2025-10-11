# Cryptis: Cryptographic Reasoning in Separation Logic

## Core Library

The file `cryptis` contains the main components of the Cryptis logic.  The parts
that are covered in the paper are summarized in the file
`summary/summary.v`. You should consult this file to see how the Rocq
development compares to the paper version.  The remaining files are structured
as follows:

- `lib/*, lib.v`: General additions to Iris and MathComp.  List manipulation
  programs for HeapLang.
- `core/*`, `cryptis.v`: Core Cryptis components: cryptographic terms, the
  `public` predicate, encryption predicates, and term metadata.
- `primitives/*`, `primitives.v`: HeapLang functions for manipulating
  cryptographic terms.  Definition of the attacker.
- `tactics.v`: Ltac tactics for symbolically executing the main HeapLang
  functions on terms.
  
### Notable differences with respect to the paper

#### Minted terms

On paper, we assume that the user can only refer to terms that contain nonces
and keys that have already been generated.  In Rocq, we cannot impose this
restriction, because the definition of the term datatype contains all terms,
whether they have been generated or not.  Instead, we add a special `minted t`
predicate to several lemmas, which holds precisely when the term `t` only
contains nonces that have already been generated.

#### Invariants and explicit channels

In Rocq, the `send` and `recv` functions must take an explicit channel parameter
`c`.  Functions that manipulate the network must assume that c is a valid
channel in their preconditions.  To run a program `f` from the initial state, we
must pass it to the `run_network` function, which allocates a new channel `c`,
initializes the attacker threads that control `c`, and then passes `c` to `f`
(cf. the `cryptis_adequacy` in `cryptis/summary.v`).  Moreover, most programs
require a special `cryptis_ctx` invariant to hold, which is also given by the
adequacy theorem.

#### Confidentiality of Diffie-Hellman terms

The Rocq development uses a more general definition of `public` for
Diffie-Hellman terms than the one in the paper.  The paper rules hold for any DH
private key that satisfies the `dh_key` predicate.  As shown by the
`wp_mk_nonce` specification in `cryptis/summary.v`, any nonce can be allocated
to satisfy this property.

#### Types for keys

Our Rocq development uses separate types `aenc_key`, `sign_key` and `senc_key`
to describe private keys for asymmetric encryption, signature keys, and
symmetric encryption keys.

#### Notation mapping

| Paper notation   | Rocq equivalent                         |
|------------------|-----------------------------------------|
| `t ^ t1 .. tn`   | `TExpN t [t1; ..; tn]`                  |
| `F, N ↦ φ`       | `seal_pred F N φ` (when `F` is generic) |
| `aenc, N ↦ φ`    | `aenc_pred N φ`                         |
| `sign, N ↦ φ`    | `sign_pred N φ`                         |
| `senc, N ↦ φ`    | `senc_pred N φ`                         |
| `token F E`      | `seal_pred_token F E`                   |
| `t, N ↦ x`       | `term_meta t N x`                       |
| `token t E`      | `term_token t E`                        |
| `t ↦db ot'`      | `db_mapsto` or `db_free`                |

## Case studies

In `examples` you will find the code for our case studies in separate
directories:

- `nsl`: NSL protocol.
- `iso_dh`: ISO protocol with DH key exchange and digital signatures.
- `conn`: Authenticated connections.
- `rpc`: Remote procedure calls.
- `store`: Authenticated key-value store.

Each case study is structured as follows:

- `impl.v`: Implementation in HeapLang.
- `proofs/*`, `proofs.v`: Proofs of correctness using the Cryptis logic.
- `game.v`: Security based on a symbolic game (for `nsl`, `iso_dh` and `store`).
- `README.md`: General comments and comparison with the paper presentation.

We list some noteworthy differences between the formalization of the case
studies and the paper presentation.

### ISO

Our implementation of ISO includes the three extensions described in the end of
Section 5: the decomposed responder and the ability to compromise a session
before or after the handshake is completed.  The specifications for this more
general functionality are given in `wp_initiator`
(`examples/iso_dh/proofs/initiator.v`) and `wp_responder_listen` and
`wp_responder_accept` (`examples/iso_dh/proofs/responder.v`).  For ease of
reference, the specifications of Theorem 5.1 are also proved
(`wp_initiator_weak` and `wp_responder_weak`).

Because the weak specifications are proved with the strong ones, the signature
predicates that we use (`examples/iso_dh/proofs/base.v`) are a bit different
from what appears in Fig. 10.

### Reliable connections

The implementation of the `recv` function is a bit different from what is shown
in Figure 13: it is based on a more general `select` function that allows an
agent to invoke a different handler depending on the type of message that it
received.  The reason for having `select` as a primitive instead of `recv` is
that it simplifies the server logic of the RPC functionality: we just need to
specify how each type of call is handled.

### Remote procedure calls

The specifications of `call` and `close` are the same as those on paper, except
for some auxiliary definitions that were inlined in the paper for space reasons.
The development also has the specifications for the server functions, which were
omitted from the paper.  In particular, the `wp_server` function says that a
connected server can initiate a loop where it awaits for calls from the client
on the other end of the connection, provided that the server has correct
handlers for all the calls it wants to respond to.

### Key-value store

The paper uses a single points-to resource to describe the state of each key,
regardless of whether the key is present in the database or not.  In Rocq, this
notation corresponds to two resources: `db_mapsto skC skS t t'` says that the
key `t` is mapped to the value `t'`, and `db_free skC skS T` says that no term
`t ∈ T` is present in the database.

The game in Figure 4 is also a bit different: the paper version was split into
two functions to better fit the page.

## Dependencies

Cryptis is known to compile with the following dependencies:

- rocq-prover v9.0.0
- rocq-mathcomp-ssreflect v2.4.0
- coq-deriving v0.2.2
- coq-iris v4.4.0
- coq-iris-heap-lang v4.4.0

There are two recommended ways to install the dependencies: via Nix or opam.

### Nix

If you have Nix flakes enabled, the accompanying `flake.nix` file should be
enough to install all the required dependencies.  Simply run `nix develop`.

### opam

Make sure to add the Rocq opam repository to your switch:

```
opam repo add rocq-released https://rocq-prover.org/opam/released
```

Afterwards, Cryptis can be installed with:

```
opam install .
```

Alternatively, run `make builddep` to produce and install a dummy package that
installs the correct dependencies.

## Building and checking proofs

After setting up the required dependencies, simply run `make`.  We recommend
using `make -j` to enable parallel compilation.  If everything goes well, `make`
should run until completion, and the last file `cryptis/summary.v` should print
"Closed under the global context." three times, indicating that the security
results for the main case studies in the paper are free of axioms and
assumptions.

## Generating Statistics in Figure 17

Run the script `./stats.sh` in the working directory.  This will clean all the
object files generated by Rocq, then compile the code comprising each row of the
table.  The result will be output in `table.tex`.

## List of claims

For convenience, the following table maps each result claimed in the paper to
the corresponding Rocq files.

| Paper reference        | Development                          | Notes |
|------------------------|--------------------------------------|-------|
| Fig. 1 (Core logic)    | `summary/summary.v`                  |       |
| Fig. 3 (Client specs)  | `examples/store/proofs/client/*`     |       |
| Fig. 3 (Other rules)   | `examples/store/proofs/base.v`       |       |
| Fig. 4                 | `examples/store/impl.v`              |       |
| Fig. 5                 | `examples/nsl/impl.v`                |       |
| Theorem 4.1            | `examples/nsl/proofs.v`              |       |
| Fig. 6                 | `examples/nsl/proofs/base.v`         |       |
| Fig. 7                 | `examples/nsl/game.v`                |       |
| Fig. 8 (Lowe's attack) | ----                                 | (1)   |
| Fig. 9                 | `examples/iso_dh/impl.v`             |       |
| Fig. 10                | `examples/iso_dh/proofs/base.v`      | (2)   |
| Theorem 5.1 (Init)     | `examples/iso_dh/proofs/initiator.v` |       |
| Theorem 5.1 (Resp)     | `examples/iso_dh/proofs/responder.v` |       |
| Fig. 11                | `examples/iso_dh/game.v`             |       |
| Fig. 12                | `examples/iso_dh/proofs/base.v`      |       |
| Fig. 13                | `examples/conn/{impl.v,proofs.v}`    |       |
| Fig. 14                | `examples/conn/proofs/base.v`        |       |
| Fig. 15 (Definitions)  | `examples/rpc/proofs/base.v`         |       |
| Fig. 15 (Specs)        | `examples/rpc/proofs.v`              |       |
| Fig. 16 (Rules 5--8)   | `cryptis/lib/replica.v`              |       |
| Fig. 16 (Other parts)  | `examples/store/proofs/base.v`       |       |


Notes:

1. We didn't not model Lowe's attack in Cryptis, but our security proofs show
   that it cannot arise.
   
2. The signature predicates that we have formalized are for the stronger
   specifications of the ISO protocol.
