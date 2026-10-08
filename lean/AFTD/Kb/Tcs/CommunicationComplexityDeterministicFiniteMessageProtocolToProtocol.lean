import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolExists
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol

Topic: communication   Node: 4b10dbe0e5f2

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A noncomputable function that converts a finite-message protocol $p$ into a binary protocol
\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol} $p$ with the same run behavior and the same communication complexity,
encoding each $\beta$-valued message as $\lceil \log_2 |\beta| \rceil$ bits.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Convert a finite-message protocol to a binary protocol with the same run behavior and complexity, encoding each `β`-valued message as `⌈log₂ |β|⌉` bits. This is folklore (a `|β|`-ary message costs `⌈log₂ |β|⌉` bits); no textbook counterpart was located, so no citation is attached. The protocol is obtained noncomputably from the existence proof `toProtocol_exists`. -/
noncomputable def CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol (p : Protocol X Y α) : Deterministic.Protocol X Y α :=
  (toProtocol_exists p).choose
