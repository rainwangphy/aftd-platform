import AFTD.Prelude
import AFTD.Kb.Physics.InstDecidableRelPathGraph
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy

/-!
# op_2130_converse_d2

Topic: online_algorithms   Node: 3b11729310a9

Provenance: helper lemma. arXiv:2611.00388; OP-2130

There exists an edge sequence of length at most 2^3 on the 4-vertex path graph SimpleGraph.pathGraph 4 such that the uniform probability over all fair coin assignments that randomized greedy carpooling achieves maximum prefix discrepancy at least 2 is at least 1/2.
-/

/-- The D = 2 case of the OP-2130 converse: an oblivious sequence of 3 edges on the 4-vertex path graph achieves maximum prefix discrepancy at least 2 with probability at least 1/2. -/
theorem op_2130_converse_d2 :
    ∃ (edges : List (Fin 4 × Fin 4)),
      (∀ e ∈ edges, (SimpleGraph.pathGraph 4).Adj e.1 e.2) ∧
      edges.length ≤ 2 ^ 3 ∧
      let T := edges.length
      let high_discrepancy := Finset.univ.filter (fun r : Fin T → Bool =>
        2 ≤ carpool_max_discrepancy 4 edges
          (carpool_greedy_orientations 4 edges (List.ofFn r)))
      (1 / 2 : ℝ) ≤ ((high_discrepancy.card : ℝ) / (2 ^ T : ℝ)) := by
  refine ⟨[(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨2, by decide⟩, ⟨3, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩)], ?_, ?_, ?_⟩
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> decide
  · decide
  · intro T high_discrepancy
    have hc : high_discrepancy.card = 4 := by decide
    change (1 / 2 : ℝ) ≤ (high_discrepancy.card : ℝ) / (2 ^ 3 : ℝ)
    rw [hc]
    norm_num
