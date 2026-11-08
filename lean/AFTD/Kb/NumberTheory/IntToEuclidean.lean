import AFTD.Prelude

/-!
# int_to_euclidean

Topic: elementary_number_theory   Node: 1c0345cfad63

Provenance: original. Related work: folklore

The canonical embedding of an integer vector z ∈ ℤ^n into the Euclidean space ℝ^n.
-/

/-- Embed an integer vector into Euclidean space ℝ^n. -/
noncomputable def int_to_euclidean (n : ℕ) (z : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => (z i : ℝ))
