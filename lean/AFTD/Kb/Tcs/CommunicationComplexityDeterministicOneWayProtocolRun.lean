import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun

/-!
# CommunicationComplexity.Deterministic.OneWay.Protocol.run

Topic: communication   Node: ce44e9de9918

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.OneWay.Protocol.run`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a one-way protocol $p$ and inputs $x \in X$, $y \in Y$, executing the protocol
yields the output $p.\mathtt{decode}(p.\mathtt{send}(x),\, y) \in \alpha$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Execute a one-way protocol on input `(x, y)`. -/
def CommunicationComplexity.Deterministic.OneWay.Protocol.run (p : Protocol X Y α) (x : X) (y : Y) : α :=
  p.decode (p.send x) y
