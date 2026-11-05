import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasWellCoveredPowers
import AFTD.Kb.Tcs.ForallPowerWellCoveredOfWellCoveredDiamLeTwo
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered

/-!
# op_1058_of_diam_le_two

Topic: graphs   Node: 275ec721e6de

Provenance: original. Related work: arXiv:2611.03956 Question 1.1

For any finite connected simple graphs G and H of diameter at most 2, if at least one of G and H is well-covered, then at least one of G and H has the well-covered powers property.
-/

/-- For graphs of diameter at most 2, if at least one factor is well-covered, then at least one factor has well-covered powers. -/
theorem op_1058_of_diam_le_two {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (hG : G.Connected) (hH : H.Connected)
    (hdG : G.diam ≤ 2) (hdH : H.diam ≤ 2)
    (hwc : simple_graph_is_well_covered G ∨ simple_graph_is_well_covered H) :
    simple_graph_has_well_covered_powers G ∨ simple_graph_has_well_covered_powers H := by
  cases hwc with
  | inl hG_wc =>
    left
    exact forall_power_well_covered_of_well_covered_diam_le_two G hG hdG hG_wc
  | inr hH_wc =>
    right
    exact forall_power_well_covered_of_well_covered_diam_le_two H hH hdH hH_wc
