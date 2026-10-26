import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPrism

/-!
# simple_graph_prism_rung_adj

Topic: graphs   Node: 4c8db1b6b305

Provenance: helper lemma. arXiv:2610.18463 Question 5.4

In the prism graph P₁ □ C_n, every vertex (0, v) in the first copy of the cycle is adjacent to the corresponding vertex (1, v) in the second copy along a rung edge.
-/

/-- Rung edges connect corresponding vertices in the two cycle copies of a prism graph. -/
theorem simple_graph_prism_rung_adj (n : ℕ) (v : Fin n) :
    (simple_graph_prism n).Adj (0, v) (1, v) := by
  unfold simple_graph_prism
  rw [SimpleGraph.boxProd_adj]
  left
  dsimp
  exact ⟨by decide, rfl⟩
