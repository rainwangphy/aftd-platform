import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesAux

/-!
# CommunicationComplexity.Deterministic.Protocol.leafRectangles

Topic: communication   Node: 7c3612e66ea0

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Protocol.leafRectangles`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{leaf rectangles} of a protocol $p : \texttt{Protocol}\,X\,Y\,\alpha$ form the
collection $\texttt{leafRectangles}(p) = \texttt{leafRectanglesAux}(p, X, Y)$, i.e.\ the set
of input rectangles induced by the leaves of $p$ over the full input space $X \times Y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The set of leaf rectangles of a protocol: for each leaf `v`, the set `R_v` of inputs `(x, y)` on which the protocol reaches `v` [RY20, Lemma 1.6] (the rectangles `R_v` of the leaves). Deviation: this is a set of subsets of `X × Y` rather than a family indexed by the leaves, so leaves with identical input sets (for instance two unreachable leaves, both with empty input set) contribute a single element. -/
def CommunicationComplexity.Deterministic.Protocol.leafRectangles (p : Protocol X Y α) : Set (Set (X × Y)) :=
  leafRectanglesAux p Set.univ Set.univ
