import AFTD.Prelude

/-!
# op826_envelope_at_two

Topic: fair_division   Node: e5d4dc289d6a

Provenance: helper lemma. arXiv:2610.34625

For value ratio R = 2, the discrete envelope min (1 / floor(sqrt 2)) (ceil(sqrt 2) / 2) equals 1.
-/

/-- Evaluation of the discrete EFX envelope at R = 2 yields 1. -/
theorem op826_envelope_at_two :
    min (1 / (⌊Real.sqrt (2 : ℝ)⌋ : ℝ)) ((⌈Real.sqrt (2 : ℝ)⌉ : ℝ) / (2 : ℝ)) = 1 := by
  rw [show ⌊Real.sqrt (2 : ℝ)⌋ = (1 : ℤ) by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num]
  rw [show ⌈Real.sqrt (2 : ℝ)⌉ = (2 : ℤ) by
    rw [Int.ceil_eq_iff]
    constructor
    · norm_num
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
      norm_num
    · norm_num]
  norm_num
