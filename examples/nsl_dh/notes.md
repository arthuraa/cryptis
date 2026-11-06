# NSL-DH Proof Notes

## Implementation (`impl.v`)

Each subroutine has at most one `send` and one `recv`.

- Initiator: `initiator_send_msg1` (mints `a`, sends `{g^a; pkI}@pkR`),
  `initiator_recv_msg2` (checks `g^a`, `pkR` and the usage tag `N`),
  `initiator_send_msg3` (sends `{g^b}@pkR`, derives the key); `initiator`
  chains them.
- Responder: `responder_recv_msg1` (= `responder_listen`),
  `responder_send_msg2` (mints `b`), `responder_recv_msg3` (checks `g^b`);
  `responder_confirm` chains the last two and `responder` runs everything.

The key is `derive_senc_key (H(nsl_dh.key, [pkI; pkR; g^a; g^b; g^ab]))`.

## Secrecy (`proofs/base.v`)

The shares travel encrypted and serve as the NSL challenges, so their secrecy
must not depend on the key's:

- `dh_key skI skR P a`: the exponent `a` is public iff `▷ □ P`, and its share
  `g^a` leaks only with `a` or with a long-term key (`nsl_dh_key_share`).  The
  responder's `P` is `False`; the initiator's is its `compromised` meta, set
  when it accepts a forged `m2`.

- `public_dh_secret`: `g^ab` leaks only with `a` or `b`.
- The key is a tagged hash, so it can be public while the shares are secret.
  Its hash predicate `key_pred` releases it when the usage's `ρ` holds; the
  usage is recorded on the responder's share (`usage gb N`).  Finding `ρ`
  through the usage's saved predicate costs a second later:
  `public k → ▷ ▷ □ ρ si`.

## Message predicates

- `msg1_pred`: `g^a` leaks with a long-term key.
- `msg2_pred`: the responder's exponent, its peer record
  (`resp_peer gb skI ga`), its usage, and the initiator's escrowed gift.
- `msg3_pred`: for the session the responder recorded on `g^b`, the initiator
  vouches for its honest exponent and escrows the responder's gift.  A forged
  `m3` makes `g^b` public, which only a leaked long-term key explains.

## Specs

`wp_initiator` and `wp_responder` follow the uniform shape of HMQV, ISO-DH and
OPAQUE: usage `nsl_dh_pred N φ ρ`, a hook that trades the share token for the
peer's gift and a local share `ψ si`, and the result `session ρ rl si ∗ ψ si ∗
(compromised rl si ∨ φ si rl)`.  `secret_session` and `session_ok` give key
secrecy when both long-term keys are secret.
