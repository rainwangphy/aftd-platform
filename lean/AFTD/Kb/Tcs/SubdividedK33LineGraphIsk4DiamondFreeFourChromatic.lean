import AFTD.Prelude
import AFTD.Kb.Tcs.HSubdividedK33
import AFTD.Kb.Tcs.HasInducedK4Subdivision
import AFTD.Kb.Tcs.IsDiamondFree
import AFTD.Kb.Tcs.K4ClawDiamondFreeHasNoInducedK4Subdivision
import AFTD.Kb.Tcs.SubdividedK33LineGraphNoK4ClawDiamond
import AFTD.Kb.Tcs.SubdividedK33LineGraphChromaticNumberEqFour
import AFTD.Kb.Tcs.IsClawFree

/-!
# subdivided_k33_line_graph_isk4_diamond_free_four_chromatic

Topic: graphs   Node: 50e3b0ad1a46

Provenance: formalization of a published result. Source: arXiv:2610.32404 Proposition 11.2, with H as constructed in Section 11.

Let H be the graph obtained from K3,3 by subdividing one edge exactly once, and let G be its line graph. Then G has no induced subdivision of K4, has no induced diamond, and has chromatic number exactly four.
-/

theorem subdivided_k33_line_graph_isk4_diamond_free_four_chromatic :
    (¬ has_induced_k4_subdivision h_subdivided_k33.lineGraph) ∧
    is_diamond_free h_subdivided_k33.lineGraph ∧
    h_subdivided_k33.lineGraph.chromaticNumber = 4 := by
  rcases subdivided_k33_line_graph_no_k4_claw_diamond with ⟨hK, hc, hd⟩
  exact ⟨k4_claw_diamond_free_has_no_induced_k4_subdivision _ hK hc hd, hd, subdivided_k33_line_graph_chromatic_number_eq_four⟩
