import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyProperty

/-!
# set_coloring_ramsey_number

Topic: combinatorics   Node: 04f0062b172b

Provenance: formalization of a published result. Source: scout/2611-15376-set-coloring-ramsey-numbers-with-multiple-intersections.md:147

Given a type V, a simple graph G on V, and natural numbers r, s, t, set_coloring_ramsey_number G r s t is the infimum in ℕ of the set of natural numbers N such that set_coloring_ramsey_property G r s t N holds.
-/

/-- The generalized set-coloring Ramsey number R(G; r, s, t). -/
noncomputable def set_coloring_ramsey_number {V : Type*} (G : SimpleGraph V) (r s t : ℕ) : ℕ :=
  sInf {N : ℕ | set_coloring_ramsey_property G r s t N}
