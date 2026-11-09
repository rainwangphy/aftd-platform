import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy
import AFTD.Kb.Tcs.Op902SingleEdgeMaxDiscrepancy

/-!
# op_1106_forest_carpooling_single_edge_max_discrepancy

Topic: online_algorithms   Node: 5d6e11a23887

Provenance: helper lemma. arXiv:2611.00388: Online carpooling against an oblivious adversary; OP-1106

For any single edge on Fin n with distinct endpoints and any initial coin, randomized greedy carpooling produces a maximum discrepancy of at most 1.
-/

/-- On a single-edge carpooling instance with distinct endpoints, randomized greedy orientation achieves maximum discrepancy at most 1. -/
theorem op_1106_forest_carpooling_single_edge_max_discrepancy
    (n : ℕ) (e : Fin n × Fin n) (he : e.1 ≠ e.2) (c : Bool) :
    carpool_max_discrepancy n [e] (carpool_greedy_orientations n [e] [c]) ≤ 1 := by first | exact op_902_single_edge_max_discrepancy | (apply op_902_single_edge_max_discrepancy <;> assumption) | (apply op_902_single_edge_max_discrepancy <;> simp_all) | simpa using op_902_single_edge_max_discrepancy | (simp only [carpool_max_discrepancy, carpool_greedy_orientations] at *; first | exact op_902_single_edge_max_discrepancy | (apply op_902_single_edge_max_discrepancy <;> assumption) | (apply op_902_single_edge_max_discrepancy <;> simp_all) | simpa using op_902_single_edge_max_discrepancy)
