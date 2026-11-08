import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEventualPeriod
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightDilate

/-!
# is_eventual_period_const

Topic: combinatorial_games   Node: 6ac89ff241d0

Provenance: helper lemma. folklore

Every constant sequence of Booleans has eventual period 1.
-/

/-- A constant binary sequence has eventual period 1. -/
theorem is_eventual_period_const (b : Bool) : is_eventual_period (fun _ => b) 1 := by first | exact cycle_power_dyadic_class_weight_dilate | (apply cycle_power_dyadic_class_weight_dilate <;> assumption) | (apply cycle_power_dyadic_class_weight_dilate <;> simp_all) | simpa using cycle_power_dyadic_class_weight_dilate | (simp only [is_eventual_period] at *; first | exact cycle_power_dyadic_class_weight_dilate | (apply cycle_power_dyadic_class_weight_dilate <;> assumption) | (apply cycle_power_dyadic_class_weight_dilate <;> simp_all) | simpa using cycle_power_dyadic_class_weight_dilate)
