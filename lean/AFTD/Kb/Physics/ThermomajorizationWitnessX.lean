import AFTD.Prelude

/-!
# thermomajorization_witness_x

Topic: quantum_mechanics   Node: 916d8e727e8f

Provenance: formalization of a published result. Source: OP-2138

For dimension n and integers a < j < b ≤ n, the thermomajorization witness vector x is defined by x_i = d₁ * 1_{i < a} + d₂ * 1_{i < b} where d₁ = (b - j) / (j * (b - a)) and d₂ = (j - a) / (j * (b - a)).
-/

/-- Thermomajorization candidate witness vector x for parameters a < j < b <= n. -/
noncomputable def thermomajorization_witness_x (n : ℕ) (a j b : ℕ) : Fin n → ℝ :=
  let d₁ : ℝ := ((b : ℝ) - (j : ℝ)) / ((j : ℝ) * ((b : ℝ) - (a : ℝ)))
  let d₂ : ℝ := ((j : ℝ) - (a : ℝ)) / ((j : ℝ) * ((b : ℝ) - (a : ℝ)))
  fun i => (if (i : ℕ) < a then d₁ else 0) + (if (i : ℕ) < b then d₂ else 0)
