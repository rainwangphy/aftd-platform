import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.SimpleGraphPowerOne

/-!
# cycle_seven_power_one_well_covered

Topic: graphs   Node: 3ac4bd56297c

Provenance: helper lemma. step towards cycle_seven_all_powers_well_covered

The first power (the graph itself) of the 7-cycle graph is well-covered.
-/

/-- The first power (the graph itself) of the 7-cycle graph is well-covered. -/
theorem cycle_seven_power_one_well_covered :
    simple_graph_is_well_covered (simple_graph_power (SimpleGraph.cycleGraph 7) 1) := by
  rw [simple_graph_power_one, simple_graph_is_well_covered]
  simp only [Maximal]
  decide
