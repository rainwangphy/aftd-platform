import AFTD.Prelude
import AFTD.Kb.Physics.DyadicSectorS

/-!
# dyadic_sector_S_knot

Topic: quantum_mechanics   Node: b6c0ae6ce635

Provenance: formalization of a published result. Source: arXiv:2611.07003; OP-1787

For every natural number s >= 1 with A = (2 : ℝ)^s and B = A^2, and for every integer j, dyadic_sector_S s (B ^ j / (B - 1)) = A ^ j / (A - 1).
-/

/-- Exact value of the dyadic sector function at knot points. -/
theorem dyadic_sector_S_knot (s : ℕ) (hs : 1 ≤ s) (j : ℤ) :
    let A : ℝ := (2 : ℝ) ^ s
    let B : ℝ := A ^ 2
    dyadic_sector_S s (B ^ j / (B - 1)) = A ^ j / (A - 1) := by
  intro A B
  have hA : 2 ≤ A := by
    dsimp [A]
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hs
    simpa using h
  have hB_gt : 1 < B := by
    dsimp [B]
    nlinarith
  have hB_sub : B - 1 ≠ 0 := by linarith
  have hlog : Real.log B ≠ 0 := by
    have : 0 < Real.log B := Real.log_pos hB_gt
    linarith
  change
    let j' : ℤ := ⌊Real.log ((B ^ j / (B - 1)) * (B - 1)) / Real.log B⌋
    A ^ j' / (A - 1) + (B ^ j / (B - 1) - B ^ j' / (B - 1)) * A ^ (-j') = A ^ j / (A - 1)
  have hj : ⌊Real.log ((B ^ j / (B - 1)) * (B - 1)) / Real.log B⌋ = j := by
    rw [div_mul_cancel₀ (B ^ j) hB_sub]
    rw [Real.log_zpow]
    rw [mul_div_cancel_right₀ (j : ℝ) hlog]
    rw [Int.floor_intCast]
  dsimp only
  rw [hj]
  ring
