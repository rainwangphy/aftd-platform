import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexityLeIff
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolComplexity

/-!
# CommunicationComplexity.Deterministic.communicationComplexity_le_of_finiteMessage_protocol

Topic: communication   Node: c363e90c84f4

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.communicationComplexity_le_of_finiteMessage_protocol`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/UpperBounds.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Upper bound witnessed by a finite-message protocol. Let $f : X \to Y \to \alpha$ and let $p$ be a finite-message protocol over $X$, $Y$,
$\alpha$ whose run function equals $f$. Then for every $c \in \mathbb{N} \cup \{\infty\}$
with $ FiniteMessage.Protocol.complexity\,(p) \le c$, the deterministic
communication complexity of $f$ satisfies $D(f) \le c$. Each of the three public bounds
above is a single application of this lemma to an explicit two-message protocol.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Any finite-message protocol `p` that computes `f` witnesses the upper bound `communicationComplexity f ≤ c` for every `c` dominating `p.complexity`. Each of the three public bounds in this file is a single application of this lemma to an explicit two-message protocol. -/
theorem CommunicationComplexity.Deterministic.communicationComplexity_le_of_finiteMessage_protocol
    {X Y α : Type} {f : X → Y → α} (p : FiniteMessage.Protocol X Y α)
    (hrun : p.run = f) {c : ℕ∞} (hc : (p.complexity : ℕ∞) ≤ c) :
    communicationComplexity f ≤ c :=
  -- Go through `p.toProtocol` directly (rather than `communicationComplexity_le_iff_finiteMessage`),
  -- which keeps the axiom footprint minimal (historically `ofProtocol_complexity` used
  -- `native_decide`; it no longer does, but the direct route is also the shorter one).
  ((communicationComplexity_le_iff f p.complexity).2
    ⟨p.toProtocol, (FiniteMessage.Protocol.toProtocol_run p).trans hrun,
      (FiniteMessage.Protocol.toProtocol_complexity p).le⟩).trans hc
