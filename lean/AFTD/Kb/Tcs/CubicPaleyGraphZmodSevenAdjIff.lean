import AFTD.Prelude
import AFTD.Kb.Tcs.CubicPaleyGraph
import AFTD.Kb.Tcs.CubicPaleyGraphDecidableAdj

/-!
# cubic_paley_graph_zmod_seven_adj_iff

Topic: graphs   Node: 6dfb4f248750

Provenance: helper lemma. sanity lemma for cubic_paley_graph; serves OP-442

In F_7 the nonzero cubes are ±1, so G_3(7) is the 7-cycle.
-/

theorem cubic_paley_graph_zmod_seven_adj_iff (x y : ZMod 7) :
    (cubic_paley_graph (ZMod 7)).Adj x y ↔ x - y = 1 ∨ x - y = 6 := by
  revert x y; decide
