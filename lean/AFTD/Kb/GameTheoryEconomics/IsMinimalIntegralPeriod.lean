import AFTD.Prelude

/-!
# is_minimal_integral_period

Topic: combinatorial_games   Node: 70c5bc29ce8d

Provenance: formalization of a published result. Source: arXiv:2610.08949 line 211

For a natural number n, a rational vector π : Fin n → ℚ, and a natural number T, is_minimal_integral_period π T asserts that 0 < T, for all i : Fin n there exists z : ℤ with (T : ℚ) * π i = (z : ℚ), and for every natural number T' with 0 < T' and T' < T, it is not the case that for all i : Fin n there exists z : ℤ with (T' : ℚ) * π i = (z : ℚ).
-/

/-- The minimal period T such that T * π is an integer vector. -/
def is_minimal_integral_period {n : ℕ} (π : Fin n → ℚ) (T : ℕ) : Prop := 0 < T ∧ (∀ i, ∃ z : ℤ, (T : ℚ) * π i = (z : ℚ)) ∧ ∀ T', 0 < T' → T' < T → ¬ (∀ i, ∃ z : ℤ, (T' : ℚ) * π i = (z : ℚ))
