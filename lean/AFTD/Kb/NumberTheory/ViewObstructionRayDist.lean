import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntToEuclidean
import AFTD.Kb.NumberTheory.ViewObstructionCenter

/-!
# view_obstruction_ray_dist

Topic: elementary_number_theory   Node: ca96ad4ffa0a

Provenance: formalization of a published result. Source: arXiv:2610.37711, Equation (1.1)

The view-obstruction squared distance d_n(v) for an integer direction vector v, defined as the infimum over t ∈ ℝ of the squared distance from t*v to the shifted lattice (1/2, ..., 1/2) + ℤ^n.
-/

/-- The view-obstruction squared distance d_n(v) for an integer direction vector v. -/
noncomputable def view_obstruction_ray_dist (n : ℕ) (v : Fin n → ℤ) : ℝ := ⨅ (t : ℝ) (z : Fin n → ℤ), ‖t • int_to_euclidean n v - (view_obstruction_center n + int_to_euclidean n z)‖ ^ 2
