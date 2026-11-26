import AFTD.Prelude
import AFTD.Kb.Tcs.IsPureStabilizerState

/-!
# stab_polytope

Topic: quantum   Node: 750b81f4f4b6

Provenance: formalization of a published result. Source: arXiv:2611.34872, line 196

The stabilizer polytope $\mathrm{STAB}_n$ is the convex hull of all pure $n$-qubit stabilizer states.
-/

/-- The stabilizer polytope STAB_n is the convex hull of all pure n-qubit stabilizer states. -/
def stab_polytope (n : ℕ) : Set (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := convexHull ℝ {ρ | is_pure_stabilizer_state ρ}
