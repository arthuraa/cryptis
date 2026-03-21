# NSL-DH Proof Notes

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
