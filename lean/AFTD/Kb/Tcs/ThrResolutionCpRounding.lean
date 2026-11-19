import AFTD.Prelude

/-!
# thr_resolution_cp_rounding

Topic: proof_complexity   Node: c651e83db265

Provenance: helper lemma. arXiv:2611.24548 Lemma 4.3 proof

Rounding the sum of translated resolution premises in Cutting Planes yields the original threshold: the ceiling of (2d - 1) / 2 equals d.
-/

/-- Rounding the sum of translated resolution premises in Cutting Planes yields the original threshold. -/
theorem thr_resolution_cp_rounding (d : ℤ) :
    ⌈((2 * (d : ℚ) - 1) / 2)⌉ = d := by
  rw [Int.ceil_eq_iff]
  constructor <;> linarith
