import AFTD.Prelude

/-!
# hypercube_nonconstant_coords

Topic: submodular   Node: 22a828e7e54f

Provenance: formalization of a published result. Source: arXiv:2610.38287 Definition 1

Given a finite set X : Finset (Fin n → Bool), hypercube_nonconstant_coords X is the Finset (Fin n) of all coordinates i : Fin n for which there exist x, y ∈ X such that x i ≠ y i, defined by filtering Finset.univ.
-/

/-- The finite set of nonconstant coordinates of a subset of vertices of the unit hypercube. -/
def hypercube_nonconstant_coords {n : ℕ} (X : Finset (Fin n → Bool)) : Finset (Fin n) := Finset.univ.filter (fun i => ∃ x ∈ X, ∃ y ∈ X, x i ≠ y i)
