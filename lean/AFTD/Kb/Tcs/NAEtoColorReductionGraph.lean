import AFTD.Prelude
import AFTD.Kb.Tcs.NAEtoColorEdgeRelation
import AFTD.Kb.Tcs.NAEtoColorNAESat3
import AFTD.Kb.Tcs.NAEtoColorOutputVertex
import AFTD.Kb.Tcs.V

/-!
# NAEtoColor.ReductionGraph

Topic: np_completeness   Node: b77943465a68

Provenance: formalization of a published result. Source: TCSlib, `NAEtoColor.ReductionGraph`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/NAESATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Given a NAE-SAT instance $f$, $\texttt{NAEtoColor.ReductionGraph}\;f$ is the
simple graph on $\texttt{NAEtoColor.OutputVertex}\;V$ whose adjacency is the
symmetrization of $\texttt{NAEtoColor.EdgeRelation}\;f$ restricted to distinct
pairs (no self-loops).
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Simple graph for reduction from NAE-SAT to 3-Coloring. We symmetrize EdgeRelation manually so proof of symmetry becomes trivial. A SimpleGraph also requires irreflexivity (no self-loops), enforced by `u ≠ v`, so we encode that in adjacency as well. -/
def NAEtoColor.ReductionGraph {V : Type} (f : NAESat3 V) : SimpleGraph (OutputVertex V) where
  Adj u v := u ≠ v ∧ (EdgeRelation f u v ∨ EdgeRelation f v u)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
