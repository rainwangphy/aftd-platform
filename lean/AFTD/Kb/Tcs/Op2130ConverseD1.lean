import AFTD.Prelude
import AFTD.Kb.Physics.InstDecidableRelPathGraph
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy

/-!
# op_2130_converse_d1

Topic: online_algorithms   Node: 8f074652cfc6

Provenance: helper lemma. arXiv:2611.00388; OP-2130

There exists an edge sequence of length at most 1^3 = 1 on the 2-vertex path graph SimpleGraph.pathGraph 2 such that the uniform probability over all fair coin assignments that randomized greedy carpooling achieves maximum prefix discrepancy at least 1 is at least 1.
-/

/-- The D = 1 base case of the OP-2130 converse: a single edge on the 2-vertex path achieves maximum prefix discrepancy at least 1 with probability 1. -/
theorem op_2130_converse_d1 :
    ∃ (edges : List (Fin 2 × Fin 2)),
      (∀ e ∈ edges, (SimpleGraph.pathGraph 2).Adj e.1 e.2) ∧
      edges.length ≤ 1 ^ 3 ∧
      let T := edges.length
      let high_discrepancy := Finset.univ.filter (fun r : Fin T → Bool =>
        1 ≤ carpool_max_discrepancy 2 edges
          (carpool_greedy_orientations 2 edges (List.ofFn r)))
      1 ≤ ((high_discrepancy.card : ℝ) / (2 ^ T : ℝ)) := by
  refine ⟨[(⟨0, by decide⟩, ⟨1, by decide⟩)], ?_, ?_, ?_⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    decide
  · decide
  · intro T high_discrepancy
    have hc : high_discrepancy.card = 2 := by decide
    change 1 ≤ (high_discrepancy.card : ℝ) / (2 ^ 1 : ℝ)
    rw [hc]
    norm_num
