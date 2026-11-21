import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfNoDefects
import AFTD.Kb.Tcs.CyclePowerSixteenZeroPhaseHalfNoDefects

/-!
# cycle_power_sixteen_defective_halves_no_defects

Topic: combinatorics   Node: cdced4e1d6a1

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635; the hnodefect hypothesis of cycle_power_dyadic_middle_bits_from_defective_halves at t = 4.

Exponent-four dyadic defective half models have no defects in either phase: with shift 0 or shift 2^(4-1) = 8, every defect bit is false.
-/

theorem cycle_power_sixteen_defective_halves_no_defects :
    ∀ (y : ℤ → ℕ → Bool) (e : ℤ → Bool) (shift : ℤ),
      (shift = 0 ∨ shift = (2 : ℤ)^(4-1)) → cycle_power_dyadic_defective_half_model 4 y e shift →
        ∀ v, e v = false := by
  intro y e shift hs hm
  exact cycle_power_dyadic_defective_half_no_defects 4 (by norm_num) y e shift hs
    (fun y e h => cycle_power_sixteen_zero_phase_half_no_defects y e h) hm
