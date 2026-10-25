import AFTD.Prelude
import AFTD.Kb.Tcs.SubcubicSubgraphThreeVerticesMaxDegreeLeOne

/-!
# subcubic_subgraph_three_vertices_max_degree_le_two

Topic: graphs   Node: ef3f4ef3a8dd

Provenance: original. Related work: arXiv:2610.21868 Sec. 4

If H is a subgraph of G, G has maximum degree at most 3, and every vertex of degree 3 in G has at most two degree 3 neighbours, then H also satisfies these two properties.
-/

/-- The property of being subcubic with Delta(G[V_3]) <= 2 is hereditary to subgraphs. -/
theorem subcubic_subgraph_three_vertices_max_degree_le_two {V : Type*}
    [Fintype V] [DecidableEq V] (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G)
    (hdeg : G.maxDegree ≤ 3)
    (h3 : ∀ v, G.degree v = 3 → ((G.neighborFinset v).filter (fun w => G.degree w = 3)).card ≤ 2) :
    H.maxDegree ≤ 3 ∧
    ∀ v, H.degree v = 3 → ((H.neighborFinset v).filter (fun w => H.degree w = 3)).card ≤ 2 := by
  have h_deg_le : ∀ u, H.degree u ≤ G.degree u := by
    intro u
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hHG hw
  have h_max : H.maxDegree ≤ 3 := (SimpleGraph.maxDegree_mono hHG).trans hdeg
  refine ⟨h_max, ?_⟩
  intro v hv
  have hGv : G.degree v = 3 := by
    apply le_antisymm
    · exact (G.degree_le_maxDegree v).trans hdeg
    · rw [← hv]
      exact h_deg_le v
  have h_sub : (H.neighborFinset v).filter (fun w => H.degree w = 3) ⊆
      (G.neighborFinset v).filter (fun w => G.degree w = 3) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset] at hw ⊢
      exact hHG hw.1
    · apply le_antisymm
      · exact (G.degree_le_maxDegree w).trans hdeg
      · rw [← hw.2]
        exact h_deg_le w
  exact (Finset.card_le_card h_sub).trans (h3 v hGv)
