import AFTD.Prelude
import AFTD.Kb.Tcs.AlternatingPath
import AFTD.Kb.Tcs.AlternatingPathVertex

/-!
# alternating_path_two_adj_zero_one

Topic: graphs   Node: e57b722d69a6

Provenance: helper lemma. arXiv:2611.08375 "New results on cyclic and ordered Ramsey numbers", Section 1

In the alternating path AP_2 on Fin 2, vertices 0 and 1 are adjacent.
-/

/-- In the alternating path AP_2, vertex 0 and vertex 1 are adjacent. -/
theorem alternating_path_two_adj_zero_one :
    (alternating_path 2).Adj ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  unfold alternating_path
  rw [SimpleGraph.fromRel_adj]
  refine ⟨by decide, Or.inl ⟨0, by decide, rfl, rfl⟩⟩
