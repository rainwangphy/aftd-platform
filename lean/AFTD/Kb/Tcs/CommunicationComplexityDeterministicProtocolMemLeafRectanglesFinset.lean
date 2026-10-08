import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesFinset
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.Deterministic.Protocol.mem_leafRectanglesFinset

Topic: communication   Node: 3a657c7838f6

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.mem_leafRectanglesFinset`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Membership in the finite set of leaf rectangles. Let $X \times Y$ carry the structure of a finite probability space, let $p$ be a
deterministic two-party communication protocol on inputs $X$ (Alice) and $Y$ (Bob) with
Boolean output, and let $R \subseteq X \times Y$. Then $R$ belongs to the finite set
enumerating the leaf rectangles of $p$ if and only if $R$ is a leaf rectangle of $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped BigOperators in
variable {X Y : Type*} in
/-- Membership in the finite enumeration of leaf rectangles is membership in the set of leaf rectangles. -/
lemma CommunicationComplexity.Deterministic.Protocol.mem_leafRectanglesFinset
    [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol X Y Bool) (R : Set (X × Y)) :
    R ∈ leafRectanglesFinset p ↔ R ∈ p.leafRectangles := by
  classical
  simpa [leafRectanglesFinset] using ((Set.toFinite p.leafRectangles).mem_toFinset (a := R))
