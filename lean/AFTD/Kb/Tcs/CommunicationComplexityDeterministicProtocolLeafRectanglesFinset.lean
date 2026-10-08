import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.Deterministic.Protocol.leafRectanglesFinset

Topic: communication   Node: 9107f109b1d1

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Protocol.leafRectanglesFinset`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a finite probability space $\mu$ on $X \times Y$ and a deterministic protocol $p$,
this is the canonical \texttt{Finset} enumerating the (finitely many) leaf rectangles of
$p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped BigOperators in
variable {X Y : Type*} in
/-- A finite enumeration of the leaf rectangles of a protocol. -/
noncomputable def CommunicationComplexity.Deterministic.Protocol.leafRectanglesFinset
    [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol X Y Bool) : Finset (Set (X × Y)) :=
  (Set.toFinite p.leafRectangles).toFinset
