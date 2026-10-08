import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolExists
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_complexity

Topic: communication   Node: fb97ee91c318

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_complexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Conversion to a binary protocol preserves complexity. Let $p$ be a finite-message deterministic two-party communication protocol over input
types $X$ (Alice) and $Y$ (Bob) with outputs in $\alpha$, in which each message is an
element of an arbitrary finite nonempty type. Its conversion into a binary protocol,
obtained by encoding every $\beta$-valued message as $\lceil \log_2 \abs{\beta} \rceil$
bits, has communication complexity equal to that of $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The binary protocol obtained from a finite-message protocol has the same complexity: encoding each `β`-valued message in binary costs exactly `⌈log₂ |β|⌉` bits. Folklore; no textbook counterpart was located, so no citation is attached. -/
@[simp]
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_complexity (p : Protocol X Y α) :
    (toProtocol p).complexity = p.complexity :=
  (toProtocol_exists p).choose_spec.2
