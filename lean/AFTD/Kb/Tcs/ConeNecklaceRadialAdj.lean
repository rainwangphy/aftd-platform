import AFTD.Prelude
import AFTD.Kb.Tcs.ConeNecklaceGraph

/-!
# cone_necklace_radial_adj

Topic: graphs   Node: 00945d3920b0

Provenance: helper lemma. Sanity lemma for the graph definition cone_necklace_graph, used in IN-584.

Each cycle vertex is adjacent to its corresponding private vertex.
-/

theorem cone_necklace_radial_adj(m : ℕ) (i : Fin m) :
    (cone_necklace_graph m).Adj ⟨i.val, by omega⟩ ⟨m + i.val, by omega⟩ := by
  simp only [cone_necklace_graph, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq]
  refine ⟨Or.inr ⟨i, Or.inr (Or.inl rfl)⟩, ?_⟩
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only at hv
  omega
