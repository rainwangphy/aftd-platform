import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesAux

/-!
# CommunicationComplexity.Deterministic.Protocol.aux_finite

Topic: communication   Node: 013b101b7d74

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.aux_finite`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Finiteness of the auxiliary leaf rectangles. Let $X$, $Y$, and $\alpha$ be types, let $p$ be a deterministic two-party communication
protocol over inputs $X$ (Alice) and $Y$ (Bob) with outputs in $\alpha$, and let $A
\subseteq X$ and $B \subseteq Y$. Then the collection of leaf rectangles induced by $p$
when its reachable inputs are constrained to $A \times B$ is finite.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The set of leaf rectangles of `p` relative to `A ×ˢ B` is finite. -/
lemma CommunicationComplexity.Deterministic.Protocol.aux_finite (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    (leafRectanglesAux p A B).Finite := by
  induction p generalizing A B with
  | output _ =>
    simp [leafRectanglesAux]
  | alice f P ih =>
    simp only [leafRectanglesAux]
    exact (ih false _ _).union (ih true _ _)
  | bob f P ih =>
    simp only [leafRectanglesAux]
    exact (ih false _ _).union (ih true _ _)
