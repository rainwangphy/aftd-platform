import AFTD.Prelude
import AFTD.Kb.Tcs.IntervalR

/-!
# interval_r_doubling

Topic: learning   Node: 7d250e7e94c5

Provenance: formalization of a published result. Source: arXiv:2611.28727 Section 9, after Conjecture 31

For every positive natural number ℓ ≥ 1, the rational sequence interval_r satisfies interval_r (2 * ℓ) = interval_r ℓ + 1 - (1 : ℚ) / (2 ^ (2 * ℓ - 1) : ℚ).
-/

/-- Doubling recurrence for the sequence R: R(2ℓ) = R(ℓ) + 1 - 2^(1 - 2ℓ) for ℓ ≥ 1. -/
theorem interval_r_doubling (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    interval_r (2 * ℓ) = interval_r ℓ + 1 - (1 : ℚ) / (2 ^ (2 * ℓ - 1) : ℚ) := by
  have h2 : 2 * ℓ = (2 * (ℓ - 1)) + 2 := by omega
  rw [h2, interval_r]
  have h3 : 2 * (ℓ - 1) + 2 = 2 * ℓ := by omega
  rw [h3]
  have h4 : (2 * ℓ) / 2 = ℓ := by omega
  have h5 : (2 * ℓ + 1) / 2 = ℓ := by omega
  rw [h4, h5]
  ring
