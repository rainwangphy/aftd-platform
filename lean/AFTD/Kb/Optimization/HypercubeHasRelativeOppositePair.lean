import AFTD.Prelude
import AFTD.Kb.Optimization.HypercubeRelativeOpposite

/-!
# hypercube_has_relative_opposite_pair

Topic: submodular   Node: 2494ff2b13fa

Provenance: formalization of a published result. Source: arXiv:2610.38287 Definition 1

A finite set X : Finset (Fin n → Bool) contains a relative opposite pair (hypercube_has_relative_opposite_pair X) if there exists d ∈ X such that the relative opposite vector hypercube_relative_opposite X d belongs to X.
-/

/-- A set of vertices of the unit hypercube contains a relative opposite pair if there exists an element whose relative opposite point also belongs to the set. -/
def hypercube_has_relative_opposite_pair {n : ℕ} (X : Finset (Fin n → Bool)) : Prop := ∃ d ∈ X, hypercube_relative_opposite X d ∈ X
