import AFTD.Prelude

/-!
# is_stationary_distribution

Topic: combinatorial_games   Node: f03d85c749a6

Provenance: formalization of a published result. Source: arXiv:2610.08949, Section 1

For a natural number n, a rational matrix P : Matrix (Fin n) (Fin n) ℚ, and a rational vector π : Fin n → ℚ, is_stationary_distribution P π asserts that Matrix.vecMul π P = π, each coordinate of π is nonnegative (0 ≤ π i for all i : Fin n), and the sum of π i over all i : Fin n equals 1.
-/

/-- A rational probability vector π is a stationary distribution for a rational matrix P if Matrix.vecMul π P = π. -/
def is_stationary_distribution {n : ℕ} (P : Matrix (Fin n) (Fin n) ℚ) (π : Fin n → ℚ) : Prop := Matrix.vecMul π P = π ∧ (∀ i, 0 ≤ π i) ∧ (∑ i, π i) = 1
