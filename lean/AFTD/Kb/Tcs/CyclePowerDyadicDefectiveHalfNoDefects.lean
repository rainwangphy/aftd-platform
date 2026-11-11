import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicReflectDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerRootedReflect

/-!
# cycle_power_dyadic_defective_half_no_defects

Topic: combinatorics   Node: 007860672bc0

Provenance: helper lemma. Reflection reduction of the two defect phases in RT-1.

If zero-phase defective half models have no defects, the same holds in either zero or half-span phase.
-/

theorem cycle_power_dyadic_defective_half_no_defects (t : ℕ) (ht : 2 ≤ t) (y : ℤ → ℕ → Bool) (e : ℤ → Bool) (shift : ℤ) (hshift : shift = 0 ∨ shift = (2 : ℤ)^(t-1)) (hzero : ∀ (y : ℤ → ℕ → Bool) (e : ℤ → Bool), cycle_power_dyadic_defective_half_model t y e 0 → ∀ v, e v = false) (hmodel : cycle_power_dyadic_defective_half_model t y e shift) : ∀ v : ℤ, e v = false := by
  rcases hshift with h | h
  · subst shift
    exact hzero y e hmodel
  · subst shift
    have hr := cycle_power_dyadic_reflect_defective_half_model t ht y e ((2 : ℤ)^(t-1)) hmodel
    simp only [sub_self] at hr
    intro v
    have hv := hzero _ _ hr (-v)
    simpa only [neg_neg] using hv
