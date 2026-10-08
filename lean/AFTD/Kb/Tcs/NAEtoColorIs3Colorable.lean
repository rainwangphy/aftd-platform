import AFTD.Prelude

/-!
# NAEtoColor.Is3Colorable

Topic: np_completeness   Node: eb8f46780cce

Provenance: formalization of a published result. Source: TCSlib, `NAEtoColor.Is3Colorable`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A simple graph $G$ on vertex type $V'$ is \emph{3-colorable} if there exists
a proper coloring $G.\mathtt{Coloring}\;(\mathrm{Fin}\,3)$, i.e.\ a map
from vertices to $\{0,1,2\}$ such that no two adjacent vertices share the same
color.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A simple graph is 3-colorable if there exists a valid 3-coloring. Equivalently, a valid 3-coloring is equivalent to a graph homomorphism from the given simple graph to the 3-Clique. -/
def NAEtoColor.Is3Colorable {V' : Type} (G : SimpleGraph V') : Prop :=
  Nonempty (G.Coloring (Fin 3))
