import AFTD.Prelude
import AFTD.Kb.Tcs.IsLatticePolytope
import AFTD.Kb.Tcs.PolytopePolar

/-!
# is_reflexive_polytope

Topic: combinatorics   Node: 9efa2775be3c

Provenance: formalization of a published result. Source: arXiv:2611.08819 Section 1; Batyrev 1994

A subset P of ℝ^d is a reflexive polytope if P is a lattice polytope containing the origin in its interior and its polar polytope is also a lattice polytope.
-/

/-- A subset of ℝ^d is a reflexive polytope if it is a lattice polytope with 0 in its interior and its polar is a lattice polytope. -/
def is_reflexive_polytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop := is_lattice_polytope P ∧ (0 : Fin d → ℝ) ∈ interior P ∧ is_lattice_polytope (polytope_polar P)
