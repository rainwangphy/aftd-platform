import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HungerTransientTime
import AFTD.Kb.GameTheoryEconomics.HungerTransientTimeEqZeroOfMemBasin
import AFTD.Kb.GameTheoryEconomics.RationalMatrixMaxDenominator
import AFTD.Kb.GameTheoryEconomics.HungerRecurrentBasin
import AFTD.Kb.GameTheoryEconomics.HungerMaxNorm

/-!
# hunger_transient_polynomial_bound_of_mem_basin

Topic: combinatorial_games   Node: 26a56ddcd72a

Provenance: helper lemma. arXiv:2610.08949 after Thm 3.8

For a natural number n with [NeZero n], a rational matrix P : Matrix (Fin n) (Fin n) ℚ, a natural number T, and a rational vector h : Fin n → ℚ, if h belongs to hunger_recurrent_basin P T, then (hunger_transient_time P T h : ℚ) ≤ (1 : ℚ) * ((n : ℚ) + (T : ℚ) + hunger_max_norm h + (rational_matrix_max_denominator P : ℚ)) ^ 1.
-/

/-- The polynomial bound holds with C=1, d=1 for hunger vectors already in the recurrent basin. -/
theorem hunger_transient_polynomial_bound_of_mem_basin {n : ℕ} [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℚ) (T : ℕ) (h : Fin n → ℚ)
    (h_mem : h ∈ hunger_recurrent_basin P T) :
    (hunger_transient_time P T h : ℚ) ≤
      (1 : ℚ) * ((n : ℚ) + (T : ℚ) + hunger_max_norm h + (rational_matrix_max_denominator P : ℚ)) ^ 1 := by
  rw [hunger_transient_time_eq_zero_of_mem_basin P T h h_mem]
  simp only [Nat.cast_zero, one_mul, pow_one]
  have h_norm : 0 ≤ hunger_max_norm h := by
    dsimp [hunger_max_norm]
    rw [Finset.le_fold_max]
    left
    exact le_rfl
  have : 0 ≤ (n : ℚ) := Nat.cast_nonneg n
  have : 0 ≤ (T : ℚ) := Nat.cast_nonneg T
  have : 0 ≤ (rational_matrix_max_denominator P : ℚ) := Nat.cast_nonneg _
  linarith
