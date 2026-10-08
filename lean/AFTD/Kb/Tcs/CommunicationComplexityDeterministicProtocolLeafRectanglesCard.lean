import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxCard

/-!
# CommunicationComplexity.Deterministic.Protocol.leafRectangles_card

Topic: communication   Node: f24535b0741e

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.leafRectangles_card`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Leaf rectangle count is at most two to the complexity. Let $p$ be a deterministic two-party communication protocol over input types $X$ and $Y$
producing values in $\alpha$, and let $c$ be its communication complexity. Then the
number of leaf rectangles of $p$ is at most $2^{c}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- A protocol of communication complexity `c` has at most `2 ^ c` leaf rectangles [RY20, Lemma 1.2] (a protocol tree of depth `c` has at most `2 ^ c` leaves). -/
lemma CommunicationComplexity.Deterministic.Protocol.leafRectangles_card (p : Protocol X Y α) :
    Set.ncard (leafRectangles p) ≤ 2 ^ p.complexity :=
  aux_card p Set.univ Set.univ
