import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsChainGraph

/-!
# simple_graph_is_chain_graph_complete_bipartite

Topic: graphs   Node: 5221fa39d7f8

Provenance: helper lemma. Sanity lemma for the definition of chain graphs, arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination).

The complete bipartite graph K_{a,b} is a chain graph (all vertices on one side have the same neighbourhood).
-/

theorem simple_graph_is_chain_graph_complete_bipartite (a b : ℕ) :
    simple_graph_is_chain_graph (completeBipartiteGraph (Fin a) (Fin b)) (Set.range Sum.inl) := by
  constructor
  · rintro (u | u) (v | v) h <;> simp_all
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    left
    intro w hw
    rcases w with w | w <;> simp_all
