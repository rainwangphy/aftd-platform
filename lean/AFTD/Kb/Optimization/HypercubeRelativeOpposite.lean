import AFTD.Prelude
import AFTD.Kb.Optimization.HypercubeNonconstantCoords

/-!
# hypercube_relative_opposite

Topic: submodular   Node: ca85f37ae2bc

Provenance: formalization of a published result. Source: arXiv:2610.38287 Definition 1

Given a finite set X : Finset (Fin n → Bool) and a Boolean vector d : Fin n → Bool, hypercube_relative_opposite X d is the Boolean vector obtained by negating d i for all coordinates i in the Finset hypercube_nonconstant_coords X and keeping d i unchanged otherwise.
-/

/-- The relative opposite point of a Boolean vector d with respect to a set X. -/
def hypercube_relative_opposite {n : ℕ} (X : Finset (Fin n → Bool)) (d : Fin n → Bool) : Fin n → Bool := fun i => if i ∈ hypercube_nonconstant_coords X then !d i else d i
