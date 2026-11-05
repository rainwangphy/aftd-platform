import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasWellCoveredPowers
import AFTD.Kb.Tcs.CycleFiveAllPowersWellCovered

/-!
# cycle_five_has_well_covered_powers

Topic: graphs   Node: c5ad601c4af9

Provenance: helper lemma. arXiv:2611.03956 Theorem 4.1

The 5-cycle graph C_5 has the well-covered powers property.
-/

/-- The 5-cycle graph C_5 has the well-covered powers property. -/
theorem cycle_five_has_well_covered_powers :
    simple_graph_has_well_covered_powers (SimpleGraph.cycleGraph 5) := cycle_five_all_powers_well_covered
