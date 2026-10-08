import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolCost
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocol

/-!
# CommunicationComplexity.Deterministic.OneWay.communicationComplexity

Topic: communication   Node: 1c8f5c37f2a1

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.OneWay.communicationComplexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The one-way deterministic communication complexity of $f : X \to Y \to \alpha$ is the
infimum (in $\mathbb{N}_\infty$) of the bit costs $p.\mathtt{cost}$ over all one-way
protocols $p$ that compute $f$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- One-way deterministic communication complexity of `f`: the infimum, over one-way protocols computing `f`, of protocol bit cost. [Rou16, §1.7 Definition (one-way communication complexity)]. Deviation: defined as an `ENat` infimum, so it is `⊤` when no one-way protocol computes `f`. -/
noncomputable def CommunicationComplexity.Deterministic.OneWay.communicationComplexity (f : X → Y → α) : ENat :=
  ⨅ (p : Protocol X Y α) (_ : Protocol.Computes p f), (Protocol.cost p : ENat)
