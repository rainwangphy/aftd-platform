import AFTD.Prelude

/-!
# view_obstruction_center

Topic: elementary_number_theory   Node: b9bef1ae8898

Provenance: formalization of a published result. Source: arXiv:2610.37711, Section 1.1

The center point c = (1/2, ..., 1/2) of the shifted lattice in Euclidean space ℝ^n.
-/

/-- The center point c = (1/2, ..., 1/2) in ℝ^n. -/
noncomputable def view_obstruction_center (n : ℕ) : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm (fun _ => (1 : ℝ) / 2)
