# NSL-DH Proof Notes

## Implementation Decomposition (`impl.v`)

Each protocol role is split into subroutines with at most one `send` and one
`recv` per subroutine (following the ISO-DH responder pattern).

### Initiator

The initiator has 2 sends and 1 recv, split into:

- **`initiator_send c skI pkR N`** (1 send, 1 recv):
  Creates nonce `a`, key share `ga = g^a`, encrypts and sends msg1
  `{ga; pkI}@pkR`, receives and decrypts msg2 `{ga'; gb; pkR'; N'}@pkI`,
  checks `ga = ga'`, `pkR = pkR'`, `N = N'`.
  Returns `SOME (a, ga, gb)`.

- **`initiator_confirm c skI pkR a ga gb`** (1 send, 0 recv):
  Computes `gab = g^(ab)`, secret, encrypts and sends msg3 `{gb; pkI}@pkR`.
  Returns `SOME (derive_senc_key secret)`.

- **`initiator c skI pkR N`**: orchestrates `initiator_send` then
  `initiator_confirm`.

### Responder

The responder has 1 send and 2 recvs, split into:

- **`responder_listen c skR`** (0 send, 1 recv):
  Receives and decrypts msg1 `{ga; pkI}@pkR`, checks `pkI` is an aenc key.
  Returns `SOME (ga, pkI)`.

- **`responder_confirm c skR ga pkI N`** (1 send, 1 recv):
  Creates nonce `b`, key share `gb = g^b`, encrypts and sends msg2
  `{ga; gb; pkR; N}@pkI`, receives and decrypts msg3 `{gb'; pkI'}@pkR`,
  checks `gb = gb'`, `pkI = pkI'`, computes `gab = g^(ab)`, secret.
  Returns `SOME (derive_senc_key secret)`.

- **`responder c skR N`**: orchestrates `responder_listen` then
  `responder_confirm`, returns `SOME (pkI, kS)`.

---

## Admitted Lemmas in `proofs/base.v` — Now Proved

There were three admitted lemmas, all related to DH reasoning. They are
analogues of the ISO-DH versions (`examples/iso_dh/proofs/base.v:342-390`)
but adapted for NSL-DH's key share predicate.

### Key Difference from ISO-DH

In ISO-DH, key shares (g^a, g^b) are sent in the clear, so they are always
public. The predicate `iso_dh_key_share t := ⌜length (exps t) = 1⌝` is
purely structural.

In NSL-DH, key shares are sent inside encrypted NSL messages. They are only
public when the encryption keys are compromised. Hence:

```
nsl_dh_key_share skI skR t := (public skI ∨ public skR) ∧ ⌜length (exps t) = 1⌝
```

This corruption guard `(public skI ∨ public skR)` is the source of all
differences from ISO-DH.

### Library Lemmas Used

- `public_TInt n : public (TInt n) ⊣⊢ True` — integers are always public
- `public_TExpN` — decompose `public (TExpN t ts)` into structural/DH cases
- `public_TExp_iff` — single-exponent case of `public_TExpN`
- `public_TExp2_iff` — two-exponent case: three disjuncts (left-public,
  right-public, or both-dh-pred)
- `minted_TExp`, `minted_TInt`, `minted_TExpN` — mintedness decomposition
- `exps_TExpN` — `exps (TExpN t ts) = ts` (for non-exp `t`)

### 1. `public_dh_share` (line 350) — Proved

```
minted a -∗
□ (∀ t, dh_pred a t ↔ ▷ □ nsl_dh_key_share skI skR t) -∗
(public skI ∨ public skR) -∗
public (TExp (TInt 0) a)
```

**Proof structure**: Same as ISO-DH but threads through the corruption
hypothesis.

1. `public_TExpN` decomposes the goal into left (public base ∧ public exp) or
   right (minted ∧ dh_pred).
2. Take right disjunct. Mintedness from `minted_TExp` + `minted_TInt` + `minted a`.
3. For `dh_pred a (TExp (TInt 0) a)`: apply `pred_a` backward.
4. Goal becomes `▷ □ nsl_dh_key_share skI skR (TExp (TInt 0) a)`.
5. Under `▷ □`, unfold to `(public skI ∨ public skR) ∧ ⌜length [a] = 1⌝`.
6. Split: corruption from hypothesis (persistent, survives under `▷ □`);
   length from `exps_TExpN`.

### 2. `public_dh_secret` (line 364) — Proved (statement modified)

**Original statement** (as admitted):
```
minted a -∗ minted b -∗
□ (∀ t, dh_pred a t ↔ ...) -∗ □ (∀ t, dh_pred b t ↔ ...) -∗
(public (TExpN (TInt 0) [a; b]) ↔ ◇ (public a ∨ public b))
```

**Issue**: The backward direction (`◇ (public a ∨ public b) → public (TExpN ...)`)
requires `public_dh_share` to construct `public (TExp (TInt 0) b)` from
`public a`. But `public_dh_share` needs `(public skI ∨ public skR)`, which
cannot be derived from the original hypotheses alone. In ISO-DH this wasn't
needed because `iso_dh_key_share` has no corruption guard.

**Fix**: Added `(public skI ∨ public skR)` as an additional hypothesis:
```
minted a -∗ minted b -∗
□ (∀ t, dh_pred a t ↔ ...) -∗ □ (∀ t, dh_pred b t ↔ ...) -∗
(public skI ∨ public skR) -∗
(public (TExpN (TInt 0) [a; b]) ↔ ◇ (public a ∨ public b))
```

This lemma is never used elsewhere, so the change has no downstream impact.

**Proof structure** (adapts ISO-DH):

Forward direction (three cases from `public_TExp2_iff`):
1. `public (TExpN (TInt 0) [a]) ∧ public b` → `◇ (... ∨ public b)` via right.
2. `public (TExpN (TInt 0) [b]) ∧ public a` → `◇ (public a ∨ ...)` via left.
3. `minted ∧ dh_pred a ∧ dh_pred b` → contradiction.
   Apply `pred_a` to get `▷ □ nsl_dh_key_share skI skR (TExpN (TInt 0) [a; b])`.
   Under `▷` then `□`, the key share predicate requires `⌜length [a; b] = 1⌝`
   but `length [a; b] = 2`, giving `▷ False`, hence `◇ P`.

   **Key tactic pattern** for the contradiction:
   ```
   iPoseProof ("pred_a" with "contra") as "#contra2".
   iAssert (▷ False)%I as ">[]".
   { iModIntro. iDestruct "contra2" as "[_ %contra]".
     by rewrite /nsl_dh_key_share exps_TExpN /= in contra. }
   ```
   - Introduce `contra2` as **persistent** (`#`) — necessary because
     `iModIntro` drops spatial hypotheses.
   - `iModIntro` strips `▷` from goal and hypotheses.
   - Under `▷`, `contra2 : □ (... ∧ ⌜2 = 1⌝)` — destruct to get pure
     contradiction.

Backward direction (three cases from `◇ = ▷ False ∨ _`):
1. `▷ False` → take third disjunct of `public_TExp2_iff`; establish `dh_pred`
   via `pred_a/pred_b` backward using `▷ False ⊢ ▷ Q`.
2. `public a` → take second disjunct; need `public_dh_share b` (uses corruption).
3. `public b` → take first disjunct; need `public_dh_share a` (uses corruption).

### 3. `public_dh_secret'` (line 390) — Proved

```
□ (public a ↔ P) -∗
□ (∀ t, dh_pred a t ↔ ▷ □ nsl_dh_key_share skI skR t) -∗
□ (public b ↔ P) -∗
□ (∀ t, dh_pred b t ↔ ▷ □ nsl_dh_key_share skI skR t) -∗
(public (TExpN (TInt 0) [a; b]) → ◇ P)
```

**Proof structure**: Identical to ISO-DH. Only the forward direction is needed.

Three cases from `public_TExp2_iff`:
1. `public b` → apply `s_b` to get `P`.
2. `public a` → apply `s_a` to get `P`.
3. `dh_pred a (...)` → same contradiction as `public_dh_secret`:
   `pred_a` gives `▷ □ (... ∧ ⌜2 = 1⌝)`, length check fails,
   gives `▷ False`, hence `◇ P`.

The corruption guard in `nsl_dh_key_share` doesn't affect this case because
the pure length check alone provides the contradiction (length 2 ≠ 1
regardless of corruption).

---

## DH Key Generation Refactoring

### `mk_dh_keys` (`impl.v`)

Combined `mk_nonce` and `mk_keyshare` into a single function:

```
mk_dh_keys () =
  let a  = mk_nonce () in
  let ga = texp (tint 0) a in
  (a, ga)
```

Both `initiator_send` and `responder_confirm` now call `mk_dh_keys` instead of
separate `mk_nonce` + `mk_keyshare` calls.

### `dh_key` Predicate (`proofs/base.v`)

Persistent predicate capturing the secrecy properties of a DH private key:

```
dh_key skI skR a :=
  minted a ∧
  □ (public a ↔ ▷ □ nonce_secrecy a) ∧
  □ (∀ t, dh_pred a t ↔ ▷ □ nsl_dh_key_share skI skR t)
```

Three components:
1. **Mintedness**: `a` was properly generated (from `mk_nonce`)
2. **Private key secrecy**: `public a` iff `nonce_secrecy a` holds (under later
   and persistence modalities). `nonce_secrecy` is a flexible predicate refined
   via term metadata: initially false (key is secret), later set to track
   whether the session failed or both shares were released.
3. **DH predicate**: controls what the attacker learns when combining `a` with
   other exponents. Tied to `nsl_dh_key_share`, ensuring that the shared secret
   `g^(ab)` is only public when both individual shares are.

### `nonce_secrecy` (moved from `initiator.v` to `base.v`)

```
nonce_secrecy a :=
  session_failed ga ∨
  ∃ gb, has_peer_share ga gb ∗ released ga ∗ released gb
```

where `ga = TExp (TInt 0) a`. This predicate is initially unsatisfiable (no
metadata set), making `public a ↔ ▷ False`. It is later refined:
- **Failed case**: `mark_failed ga` consumes `fail_token ga`, producing
  `session_failed ga`, making the private key effectively public.
- **Released case**: `set_peer_share ga gb` consumes `peer_share_token ga`,
  producing `has_peer_share ga gb`. Secrecy then becomes
  `released ga ∧ released gb`.

### `wp_mk_dh_keys` Spec (`proofs/base.v`)

```
wp_mk_dh_keys skI skR Ψ :
  cryptis_ctx -∗
  (∀ a, dh_key skI skR a -∗
        release_token ga -∗ fail_token ga -∗
        peer_share_token ga -∗ ready_token ga -∗
        res_token ga -∗ term_token ga (⊤ ∖ ↑nsl_dhN) -∗
        Ψ (repr (a, ga))) -∗
  WP mk_dh_keys #() {{ Ψ }}
```

**Proof**: Uses `wp_mk_nonce_freshN` with `P = nonce_secrecy` and
`Q = nsl_dh_key_share skI skR`, `T' = λ a, {[TExp (TInt 0) a]}`.
The token for `ga` is split via `dh_share_tokenI` into all five
sub-namespace tokens plus the remainder outside `nsl_dhN`.
The `dh_key` predicate is assembled from the properties provided by
`wp_mk_nonce_freshN`.

### Message Predicate Refactoring

**`msg1_pred`**: Now existentially quantifies over the private key `a` (not
just `ga`) and includes `dh_key skI skR a`:
```
msg1_pred skR m1 := ∃ a skI,
  ⌜m1 = Spec.of_list [TExp (TInt 0) a; Spec.pkey skI]⌝ ∧
  dh_key skI skR a ∧
  (public ga ↔ ▷ □ (public skI ∨ public skR))
```

The biconditional is kept explicitly because the forward direction
(`public ga → corruption`) cannot be derived from `dh_key` alone — it
requires knowledge of the metadata state (that `nonce_secrecy` is currently
unsatisfiable).

**`msg2_pred`**: Replaces the explicit `∀ t, dh_pred b t ↔ ...` with
`dh_key skI skR b`:
```
msg2_pred skI m2 := ∃ ga b skR N,
  ⌜m2 = ...⌝ ∧
  dh_key skI skR b ∧
  ((public skI ∨ public skR) ∨ (public b ↔ ▷ (released ga ∧ released gb))) ∧
  nsl_dh_ready N skI skR si
```

**`msg3_pred`**: Unchanged (no DH-specific properties).

---

## Token/Meta Encapsulation (`proofs/base.v`)

Raw `term_token`/`term_meta` under `nsl_dhN` are now wrapped in named
predicates, following the pattern established by `release_token`/`released`.

### Token Predicates

Each sub-namespace of `nsl_dhN` has a corresponding token predicate:

```
release_token share    := term_token share (↑nsl_dhN.@"released")
fail_token share       := term_token share (↑nsl_dhN.@"failed")
peer_share_token share := term_token share (↑nsl_dhN.@"peer_share")
ready_token share      := term_token share (↑nsl_dhN.@"ready")
res_token share        := term_token share (↑nsl_dhN.@"res")
```

### Meta Predicates

```
released share           := term_meta share (nsl_dhN.@"released") true
session_failed share     := term_meta share (nsl_dhN.@"failed") true
has_peer_share share gb  := term_meta share (nsl_dhN.@"peer_share") gb
```

With corresponding set/consume lemmas:
- `release : release_token share ==∗ released share`
- `mark_failed : fail_token share ==∗ session_failed share`
- `set_peer_share : peer_share_token share ==∗ has_peer_share share gb`
- `has_peer_share_agree : has_peer_share share gb1 -∗ has_peer_share share gb2 -∗ ⌜gb1 = gb2⌝`

### `dh_share_tokenI` (replaces `release_tokenI`)

```
dh_share_tokenI share E :
  ↑nsl_dhN ⊆ E →
  term_token share E -∗
  release_token share ∗ fail_token share ∗
  peer_share_token share ∗ ready_token share ∗
  res_token share ∗ term_token share (E ∖ ↑nsl_dhN)
```

Splits a term token into all five sub-namespace tokens plus the remainder
outside `nsl_dhN`. Used in `wp_mk_dh_keys` to distribute tokens from
`wp_mk_nonce_freshN`.

### Updated Definitions

**`nonce_secrecy`** now uses `session_failed` and `has_peer_share`:
```
nonce_secrecy a :=
  session_failed ga ∨
  ∃ gb, has_peer_share ga gb ∗ released ga ∗ released gb
```

**`nsl_dh_ready`** now uses `ready_token`:
```
nsl_dh_ready N skI skR si := ∀ φ,
  nsl_dh_pred N φ →
  ready_token (si_init_share si) ={⊤}=∗ ▷ φ skI skR si Init
```

**`wp_mk_dh_keys`** postcondition now returns all five individual tokens:
```
wp_mk_dh_keys skI skR Ψ :
  cryptis_ctx -∗
  (∀ a, dh_key skI skR a -∗
        release_token ga -∗ fail_token ga -∗
        peer_share_token ga -∗ ready_token ga -∗
        res_token ga -∗ term_token ga (⊤ ∖ ↑nsl_dhN) -∗
        Ψ (repr (a, ga))) -∗
  WP mk_dh_keys #() {{ Ψ }}
```

**Responder specs** use `res_token` instead of raw `term_token`.
