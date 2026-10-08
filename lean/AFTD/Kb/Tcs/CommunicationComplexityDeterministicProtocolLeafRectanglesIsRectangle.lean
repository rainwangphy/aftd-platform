import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxIsRectangle
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle

/-!
# CommunicationComplexity.Deterministic.Protocol.leafRectangles_isRectangle

Topic: communication   Node: dd6702c9ab4f

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.leafRectangles_isRectangle`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Leaf rectangles are combinatorial rectangles. Let $p$ be a deterministic two-party communication protocol with Alice's inputs drawn
from $X$ and Bob's from $Y$, and let $R$ belong to the collection of leaf rectangles of
$p$ over the full input space $X \times Y$. Then $R$ is a rectangle: there exist subsets
$A \subseteq X$ and $B \subseteq Y$ with $R = A \times B$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Every leaf rectangle of a protocol is a combinatorial rectangle `A ×ˢ B` [RY20, Lemma 1.6] (also [Rou16, Lemma 4.1, Lemma 4.2]). -/
lemma CommunicationComplexity.Deterministic.Protocol.leafRectangles_isRectangle (p : Protocol X Y α)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : Rectangle.IsRectangle R :=
  aux_isRectangle p Set.univ Set.univ R hR
