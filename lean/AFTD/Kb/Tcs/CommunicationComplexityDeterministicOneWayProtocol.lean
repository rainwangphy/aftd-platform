import AFTD.Prelude

/-!
# CommunicationComplexity.Deterministic.OneWay.Protocol

Topic: communication   Node: e7e0d7dc197d

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.OneWay.Protocol`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

A one-way deterministic communication protocol for inputs $x \in X$, $y \in Y$, and
output type $\alpha$ is a structure consisting of a finite, nonempty \emph{message
codebook} \texttt{Message}, Alice's encoder $\mathtt{send} : X \to \mathtt{Message}$
that selects a codeword from the codebook based solely on her input, and Bob's decoder
$\mathtt{decode} : \mathtt{Message} \times Y \to \alpha$ that produces the final output
from the received message and his own input.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- A one-way deterministic communication protocol: Alice sends Bob a single message that is a function of her input only, and Bob outputs the answer as a function of that message and his own input. [Rou16, §1.7 Definition (one-way protocol)]. `Message` is the protocol's message codebook (language): the finite set of admissible full one-shot messages Alice may send. It is not the base symbol alphabet/signature (for example, bits), but whole message values (codewords). -/
structure CommunicationComplexity.Deterministic.OneWay.Protocol (X Y α : Type*) where
  /-- The message codebook/language: all admissible complete one-shot messages. -/
  Message : Type
  /-- Finiteness of the message codebook, needed to assign a bit cost. -/
  [instFintypeMessage : Fintype Message]
  /-- Nonemptiness of the codebook (mirrors existing finite-message conventions). -/
  [instNonemptyMessage : Nonempty Message]
  /-- Alice's encoder: picks a codeword/message from the protocol codebook. -/
  send : X → Message
  /-- Bob's local decoder from received message and Bob's input. -/
  decode : Message → Y → α

attribute [instance] CommunicationComplexity.Deterministic.OneWay.Protocol.instFintypeMessage CommunicationComplexity.Deterministic.OneWay.Protocol.instNonemptyMessage
