import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntToEuclidean
import AFTD.Kb.NumberTheory.ViewObstructionCenter

/-!
# view_obstruction_offset

Topic: elementary_number_theory   Node: 5534fe6f88e6

Provenance: formalization of a published result. Source: arXiv:2610.37711 Definition 3.1

The offset δ_U^2 of a linear subspace U in ℝ^n, defined as the infimum over integer vectors z ∈ ℤ^n of the squared norm of the orthogonal projection of c - z onto U (using Submodule.orthogonalProjectionOnto U), where c = (1/2, ..., 1/2).
-/

/-- The offset δ_U^2 of a linear subspace U ⊆ ℝ^n, the squared distance from c to U along integer points. -/
noncomputable def view_obstruction_offset (n : ℕ) (U : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : ℝ := ⨅ z : Fin n → ℤ, ‖Submodule.orthogonalProjectionOnto U (view_obstruction_center n - int_to_euclidean n z)‖ ^ 2
