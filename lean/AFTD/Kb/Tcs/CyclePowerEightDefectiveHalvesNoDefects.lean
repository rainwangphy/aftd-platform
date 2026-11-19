import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerEightZeroPhaseHalfNoDefects
import AFTD.Kb.Tcs.CyclePowerEightHalfPhaseHalfNoDefects

/-!
# cycle_power_eight_defective_halves_no_defects

Topic: combinatorics   Node: e4f5811d9c7a

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635; the hnodefect hypothesis of cycle_power_dyadic_middle_bits_from_defective_halves at t = 3.

Exponent-three dyadic defective half models have no defects in either phase: with shift 0 or shift 2^(3-1) = 4, every defect bit is false.
-/

theorem cycle_power_eight_defective_halves_no_defects :
    ∀ (y : ℤ → ℕ → Bool) (e : ℤ → Bool) (shift : ℤ),
      (shift = 0 ∨ shift = (2 : ℤ)^(3-1)) → cycle_power_dyadic_defective_half_model 3 y e shift →
        ∀ v, e v = false := by
  intro y e shift hs hm
  rcases hs with rfl | rfl
  · exact cycle_power_eight_zero_phase_half_no_defects y e hm
  · exact cycle_power_eight_half_phase_half_no_defects y e (by norm_num at hm; exact hm)
