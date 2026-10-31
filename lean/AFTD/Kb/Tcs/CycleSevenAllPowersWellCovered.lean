import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.CycleSevenPowerOneWellCovered
import AFTD.Kb.Tcs.CycleSevenPowerTwoWellCovered
import AFTD.Kb.Tcs.CycleSevenPowerGeThreeWellCovered

/-!
# cycle_seven_all_powers_well_covered

Topic: graphs   Node: 5a66fe70102d

Provenance: formalization of a published result. Source: arXiv:2610.09300 Example 3.8

For every positive integer d, the d-th power of the 7-cycle graph C_7 is well-covered.
-/

/-- Every power of the 7-cycle graph C_7 is well-covered. -/
theorem cycle_seven_all_powers_well_covered :
    ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power (SimpleGraph.cycleGraph 7) d) := by
  intro d hd
  by_cases h1 : d = 1
  · subst h1; exact cycle_seven_power_one_well_covered
  · by_cases h2 : d = 2
    · subst h2; exact cycle_seven_power_two_well_covered
    · exact cycle_seven_power_ge_three_well_covered d (by omega)
