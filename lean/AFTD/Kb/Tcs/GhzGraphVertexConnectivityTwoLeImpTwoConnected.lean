import AFTD.Prelude
import AFTD.Kb.Tcs.GhzGraphVertexConnectivity

/-!
# ghz_graph_vertex_connectivity_two_le_imp_two_connected

Topic: graphs   Node: 312da3596a8b

Provenance: helper lemma. step towards radius_independence_connectivity_hamiltonian_connectivity_two

A finite simple graph with vertex connectivity at least 2 is 2-connected: it is preconnected, and deleting any single vertex leaves it preconnected.
-/

/-- Vertex connectivity at least two implies 2-connectedness (no cut vertex, graph connected). -/
theorem ghz_graph_vertex_connectivity_two_le_imp_two_connected
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h : 2 ≤ ghz_graph_vertex_connectivity G) :
    G.Preconnected ∧ ∀ v : V, (G.induce ({v}ᶜ : Set V)).Preconnected := by
  unfold ghz_graph_vertex_connectivity at h
  by_cases htop : G = ⊤
  · subst htop
    refine ⟨SimpleGraph.preconnected_top, fun v => ?_⟩
    rw [SimpleGraph.induce_top]
    exact SimpleGraph.preconnected_top
  · rw [if_neg htop] at h
    constructor
    · by_contra hp
      have hmem : (0:ℕ) ∈ {n | ∃ T : Finset V, ¬(SimpleGraph.induce (↑T)ᶜ G).Preconnected ∧ n = T.card} := by
        refine ⟨∅, ?_, rfl⟩
        rw [Finset.coe_empty, Set.compl_empty]
        intro hc
        exact hp ((SimpleGraph.Iso.preconnected_iff (SimpleGraph.induceUnivIso G)).mp hc)
      have := Nat.sInf_le hmem
      omega
    · intro v
      by_contra hp
      have hmem : (1:ℕ) ∈ {n | ∃ T : Finset V, ¬(SimpleGraph.induce (↑T)ᶜ G).Preconnected ∧ n = T.card} := by
        refine ⟨{v}, ?_, by simp⟩
        rw [Finset.coe_singleton]
        simpa using hp
      have := Nat.sInf_le hmem
      omega
