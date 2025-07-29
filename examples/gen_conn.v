(**

This module implements a reliable connection abstraction that allows agents to
exchange resources.  It is parameterized by a structure [ps : params Σ] which
groups two invariants:

  - [chan_inv ps skI skR si tsI tsR] is an invariant that pertains to the
    contents of the channel.  [tsI] is the sequence of messages sent by the
    initiator that have not yet been received by the responder. [tsR] means the
    same, but with the roles flipped.  The other parameters are: [skI] and [skR]
    (the identities of the two parties) and [si] (the key shares and secrets;
    cf. the iso_dh protocol).

  - [msg_inv ps skI skR si rl t] denotes the resource that an agent gets when
    they receive a message [t], assuming that that agent that sent the message
    had role [rl].

The protocol works as follows:

  1. The responder of the protocol uses the [listen] function to wait for a
  connection request.

  2. The initiator of the protocol uses [connect] to contact the responder.

  3. If the responder decides to accept the connection, it calls the [confirm]
  function.

  4. After the connection is established, both parties can use [send] and [recv]
  to communicate.

The specifications of [connect] and [confirm] allow agents to keep a long-term
resource that can be manipulated when communicating.  This resource, of the form
[failure skI skR ∨ P], says that either one of the agents was shown to be
compromised in the past, or the resource [P] is available.  When the handshake
completes, this resource is replaced by [public (si_key cs) ∨ P], where [cs] is
the connection object just created.  This allows agents to communicate without
proving any obligations when [public (si_key cs)] holds.  Moreover, the
responder of the protocol is required to initialize the channel invariant by
using the tokens associated with its key share.

To actually send and receive messages, the preconditions of the communication
functions assume that the agents are capable of updating the channel invariant
[chan_inv] when adding or removing a message.

To have an idea of how this could be used, look at the simpler [conn] module,
where the channel invariant is simply the conjunction of several invariants
pertaining to the individual messages.  This definition is simple enough that
the responder does not need to do anything special to initialize the channel
invariant (since initially the channels do not hold any messages).

*)

From cryptis.examples Require Import iso_dh.
From cryptis.examples.gen_conn Require Import impl proofs.

Module GenConn.
Include cryptis.examples.gen_conn.impl.
Include cryptis.examples.gen_conn.proofs.base.
Include cryptis.examples.gen_conn.proofs.
End GenConn.

Coercion GenConn.cs_si : GenConn.state >-> sess_info.
