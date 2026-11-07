import AFTD.Prelude
import AFTD.Kb.Tcs.MonotoneCycle
import AFTD.Kb.Tcs.DigraphSafe17FourTriangles

/-!
# monotone_cycle_three_adj_zero_one

Topic: graphs   Node: 82c0ad5faee0

Provenance: helper lemma. arXiv:2611.08375 "New results on cyclic and ordered Ramsey numbers", Section 1

In the monotone cycle MC_3 on Fin 3, vertices 0 and 1 are adjacent.
-/

/-- In the monotone cycle MC_3, vertex 0 and vertex 1 are adjacent. -/
theorem monotone_cycle_three_adj_zero_one :
    (monotone_cycle 3).Adj ⟨0, by decide⟩ ⟨1, by decide⟩ := by first | exact digraph_safe17_four_triangles | (apply digraph_safe17_four_triangles <;> assumption) | (apply digraph_safe17_four_triangles <;> simp_all) | simpa using digraph_safe17_four_triangles | (simp only [monotone_cycle] at *; first | exact digraph_safe17_four_triangles | (apply digraph_safe17_four_triangles <;> assumption) | (apply digraph_safe17_four_triangles <;> simp_all) | simpa using digraph_safe17_four_triangles)
