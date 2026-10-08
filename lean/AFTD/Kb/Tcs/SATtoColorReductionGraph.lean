import AFTD.Prelude
import AFTD.Kb.Tcs.SATtoColorEdgeRelation
import AFTD.Kb.Tcs.SATtoColorOutputVertex
import AFTD.Kb.Tcs.SATtoColorSat3

/-!
# SATtoColor.ReductionGraph

Topic: np_completeness   Node: 9c3e88a0b76d

Provenance: formalization of a published result. Source: TCSlib, `SATtoColor.ReductionGraph`. Lean proof by CS 294-268 course staff (UC Berkeley, Spring 2026), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean (Copyright (c) 2026 UC Berkeley CS 294. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Given a 3-SAT instance $f$ over variables $V$, the \emph{reduction graph}
$\mathrm{ReductionGraph}(f)$ is the \texttt{SimpleGraph} on
$\mathrm{OutputVertex}(V)$ whose adjacency relation is the symmetrisation of
$\mathrm{EdgeRelation}(f)$: two distinct vertices are adjacent iff
$\mathrm{EdgeRelation}(f, u, v)$ or $\mathrm{EdgeRelation}(f, v, u)$ holds.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Simple graph for reduction from 3-SAT to 3-Coloring. -/
def SATtoColor.ReductionGraph {V : Type} (f : Sat3 V) : SimpleGraph (OutputVertex V) where
  Adj u v := u ≠ v ∧ (EdgeRelation f u v ∨ EdgeRelation f v u)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
