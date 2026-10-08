import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxFinite

/-!
# CommunicationComplexity.Deterministic.Protocol.leafRectangles_finite

Topic: communication   Node: e9b5ce6d7be9

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.leafRectangles_finite`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Finiteness of a protocol's leaf rectangles. For any deterministic two-party communication protocol $p$ over input types $X$ (Alice)
and $Y$ (Bob) producing values in $\alpha$, the collection of leaf rectangles of $p$ —
the input rectangles in $X \times Y$ induced by the leaves of $p$ over the full input
space — is finite.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The set of leaf rectangles of a protocol is finite. -/
lemma CommunicationComplexity.Deterministic.Protocol.leafRectangles_finite (p : Protocol X Y α) :
    (leafRectangles p).Finite :=
  aux_finite p Set.univ Set.univ
