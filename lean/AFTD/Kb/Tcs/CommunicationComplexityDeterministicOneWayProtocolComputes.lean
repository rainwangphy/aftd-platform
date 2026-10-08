import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun

/-!
# CommunicationComplexity.Deterministic.OneWay.Protocol.Computes

Topic: communication   Node: 7a57a54324a7

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.OneWay.Protocol.Computes`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A one-way protocol $p$ \emph{computes} a function $f : X \to Y \to \alpha$ if
$p.\mathtt{run}(x, y) = f(x, y)$ for every pair of inputs $(x, y)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- A one-way protocol computes `f` when its execution agrees with `f` everywhere. [Rou16, §1.7 Definition (one-way protocol)]. -/
def CommunicationComplexity.Deterministic.OneWay.Protocol.Computes (p : Protocol X Y α) (f : X → Y → α) : Prop :=
  p.run = f
