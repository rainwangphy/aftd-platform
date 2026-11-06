import AFTD.Prelude
import AFTD.Kb.Tcs.ConeNecklaceGraph

/-!
# cone_necklace_apex_adj

Topic: graphs   Node: fe78a6ad24c6

Provenance: helper lemma. Sanity lemma for the graph definition cone_necklace_graph, used in IN-584.

The apex is adjacent to every other vertex.
-/

theorem cone_necklace_apex_adj(m : ℕ) (v : Fin (2 * m + 1)) (h : v.val ≠ 2 * m) :
    (cone_necklace_graph m).Adj ⟨2 * m, by omega⟩ v := by
  have hv : v ≠ (⟨2 * m, by omega⟩ : Fin (2 * m + 1)) := by
    intro e
    apply h
    exact congrArg Fin.val e
  simp only [cone_necklace_graph, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq]
  exact ⟨Or.inl ⟨v, hv, rfl⟩, Ne.symm hv⟩
