import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphVertexDominated

/-!
# not_simple_graph_vertex_dominated_of_isolated

Topic: graphs   Node: 0a9db86cf24d

Provenance: helper lemma. scout/2611-14430-linear-size-graphs-at-every-strict-dismantling-level.md:237 (arXiv:2611.14430 Lemma 2.1)

An isolated vertex in a simple graph $H$ (a vertex with empty open neighbourhood) is not dominated by any vertex.
-/

/-- An isolated vertex in a simple graph is not dominated by any vertex. -/
theorem not_simple_graph_vertex_dominated_of_isolated {V : Type*} (H : SimpleGraph V) (u : V)
    (hu : H.neighborSet u = ∅) :
    ¬ simple_graph_vertex_dominated H u := by
  rintro ⟨t, htv, hsub⟩
  have hmem : u ∈ insert t (H.neighborSet t) := hsub (by simp)
  rw [Set.mem_insert_iff] at hmem
  rcases hmem with h | h
  · exact htv h.symm
  · rw [SimpleGraph.mem_neighborSet] at h
    have h' : t ∈ H.neighborSet u := by
      rw [SimpleGraph.mem_neighborSet]; exact SimpleGraph.Adj.symm h
    rw [hu] at h'
    exact h'
