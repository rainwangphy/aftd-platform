import AFTD.Prelude
import AFTD.Kb.Tcs.CactusCycleEnvelope

/-!
# cactus_cycle_envelope_lt_three_halves

Topic: algorithms   Node: 8b48e80e17e4

Provenance: helper lemma. arXiv:2610.23032

For every natural number m satisfying 1 ≤ m, the cactus cycle envelope cactus_cycle_envelope m is strictly less than 3 / 2.
-/

/-- The cactus cycle envelope is strictly bounded above by 3 / 2 for all m ≥ 1. -/
theorem cactus_cycle_envelope_lt_three_halves (m : ℕ) (hm : 1 ≤ m) : cactus_cycle_envelope m < 3 / 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  simp only [cactus_cycle_envelope, Nat.add_sub_cancel]
  have h2 : (2:ℝ)^(n+1) = 2 * 2^n := by ring
  have hpos : (0:ℝ) < 2 ^ (n + 1) - 1 := by
    have h3 : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    rw [h2]; linarith
  rw [div_lt_iff₀ hpos, h2]
  linarith
