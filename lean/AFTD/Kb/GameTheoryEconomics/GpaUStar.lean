import AFTD.Prelude

/-!
# gpa_uStar

Topic: mechanism_design   Node: 7dab0d3d5480

The principal's utility of arXiv:2209.01146, Section 5.3: u*(σ) = Σ_i max{σ_i - Σ_j e_{ij} σ_j, 0} for a 0/1 matrix e.
-/

open Finset in
/-- The principal's utility of arXiv:2209.01146, Section 5.3: `u*(σ) = Σ_i max{σ_i - Σ_j e_{ij} σ_j, 0}` for a 0/1 matrix `e`. -/
noncomputable def gpa_uStar {k : ℕ} (e : Fin k → Fin k → ℝ) (σ : Fin k → ℝ) : ℝ :=
  ∑ i, max (σ i - ∑ j, e i j * σ j) 0
