import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxCover

/-!
# CommunicationComplexity.Deterministic.Protocol.leafRectangles_cover

Topic: communication   Node: 07e52d4ae58a

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.leafRectangles_cover`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Leaf rectangles cover the input space. Let $p$ be a deterministic communication protocol over input types $X$ (Alice) and $Y$
(Bob) producing a value of some type $\alpha$. Then the leaf rectangles of $p$ cover the
entire input space: the union of all rectangles in the collection of leaf rectangles of
$p$ equals $X \times Y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The leaf rectangles of a protocol cover the whole input space `X × Y` [RY20, Lemma 1.6] (also [Rou16, Lemma 4.1, Lemma 4.2]). -/
lemma CommunicationComplexity.Deterministic.Protocol.leafRectangles_cover (p : Protocol X Y α) :
    ⋃₀ leafRectangles p = Set.univ :=
  Set.eq_univ_of_univ_subset (by simpa [leafRectangles] using aux_cover p Set.univ Set.univ)
