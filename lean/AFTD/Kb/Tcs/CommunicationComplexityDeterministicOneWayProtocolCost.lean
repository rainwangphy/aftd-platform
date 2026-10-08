import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocol

/-!
# CommunicationComplexity.Deterministic.OneWay.Protocol.cost

Topic: communication   Node: 111096138078

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.OneWay.Protocol.cost`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The communication cost of a one-way protocol $p$ is $\lceil \log_2 |\mathtt{Message}| \rceil$
bits, where $\mathtt{Message}$ is the protocol's codebook.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Protocol-level communication cost in bits: `⌈log₂ |Message|⌉`, where `Message` is the protocol codebook/language. [Rou16, §1.7 Definition (one-way protocol)]. Deviation: Roughgarden charges the length of Alice's message; here messages are abstract codewords and the cost is the length of a fixed-length binary encoding of the codebook. -/
def CommunicationComplexity.Deterministic.OneWay.Protocol.cost (p : Protocol X Y α) : ℕ :=
  Nat.clog 2 (Fintype.card p.Message)
