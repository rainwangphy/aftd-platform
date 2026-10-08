import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesCover
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesDisjoint
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonoPartition
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesIsRectangle
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesMono
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonochromatic

/-!
# CommunicationComplexity.Deterministic.Protocol.leafRectangles_isMonoPartition

Topic: communication   Node: 06579717428b

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.leafRectangles_isMonoPartition`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Leaf rectangles of a protocol form a monochromatic partition. Let $p$ be a deterministic two-party communication protocol over input types $X$ and $Y$
producing outputs in $\alpha$, and let $g : X \to Y \to \alpha$. If $p$ computes $g$,
then the collection of leaf rectangles of $p$ is a monochromatic rectangle partition of
$X \times Y$ for $g$: every leaf rectangle is a rectangle and is monochromatic for $g$,
the leaf rectangles cover all of $X \times Y$, and any two distinct leaf rectangles are
disjoint.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- If `p` computes `g`, then the leaf rectangles of `p` form a monochromatic rectangle partition of `X × Y` for `g`: every member is a rectangle, `g` is constant on every member, the members cover `X × Y`, and distinct members are disjoint [RY20, Lemma 1.6] (also [Rou16, Lemma 4.1, Lemma 4.2]). -/
theorem CommunicationComplexity.Deterministic.Protocol.leafRectangles_isMonoPartition
    (p : Protocol X Y α) (g : X → Y → α)
    (h_comp : Computes p g) :
    Rectangle.IsMonoPartition (leafRectangles p) g :=
  ⟨fun R hR => leafRectangles_isRectangle p R hR,
   fun R hR => leafRectangles_mono p g h_comp R hR,
   leafRectangles_cover p,
   fun R S hR hS hne =>
     leafRectangles_disjoint p R S hR hS hne⟩
