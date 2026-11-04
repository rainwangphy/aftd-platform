import AFTD.Prelude

/-!
# recurrence_ratio

Topic: combinatorics   Node: b3a5247e7404

Provenance: formalization of a published result. Source: arXiv:2611.01561 Sec. 6

For N : ℕ, b, c : Fin (N + 1) → ℝ, and i : Fin (N + 1), the ratio is c i / (b i + c i).
-/

/-- Ratio sequence r_i = c_i / (b_i + c_i) on Fin (N + 1). -/
noncomputable def recurrence_ratio (N : ℕ) (b c : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : ℝ := c i / (b i + c i)
