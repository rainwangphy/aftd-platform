import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity

/-!
# CommunicationComplexity.Deterministic.communicationComplexity

Topic: communication   Node: 8873396ec633

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.communicationComplexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetComplexity.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The deterministic communication complexity of $f : X \to Y \to \alpha$ is defined as
\[
  D(f) \;=\; \inf_{\substack{p \;:\; \mathrm{Protocol}\;X\;Y\;\alpha \\ p \text{ computes } f}}
              p.\mathrm{complexity} \;\in\; \mathbb{N}_\infty.
\]
The infimum is taken over all deterministic protocols $p$ that compute $f$, and the
result lives in $\mathrm{ENat}$ to accommodate the case where no finite protocol exists.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The deterministic communication complexity of `f : X → Y → α`: the minimum, over all protocols computing `f`, of the protocol's complexity (worst-case number of bits exchanged). [RY20, Ch. 1, Definition (computing a function, complexity, rounds)]. Deviation: defined as an `ENat` infimum over protocols, so it is `⊤` when no protocol computes `f`; for finite nonempty `X`, `Y` the value is finite (`UpperBounds.communicationComplexity_le_clog_card`). -/
noncomputable def CommunicationComplexity.Deterministic.communicationComplexity
    {X Y α : Type*} (f : X → Y → α) : ENat :=
  ⨅ (p : Protocol X Y α) (_ : p.Computes f),
    (p.complexity : ENat)
