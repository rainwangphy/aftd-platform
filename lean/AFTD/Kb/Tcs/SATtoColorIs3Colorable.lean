import AFTD.Prelude

/-!
# SATtoColor.Is3Colorable

Topic: np_completeness   Node: 447b644ab569

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.Is3Colorable`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A simple graph $G$ on vertex type $V'$ is \emph{3-colorable} if there exists a
proper graph coloring with colors $\mathrm{Fin}\,3$, i.e.\
$\mathrm{Nonempty}(G.\mathrm{Coloring}(\mathrm{Fin}\,3))$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A simple graph is 3-colorable if there exists a valid 3-coloring. -/
def SATtoColor.Is3Colorable {V' : Type} (G : SimpleGraph V') : Prop :=
  Nonempty (G.Coloring (Fin 3))
