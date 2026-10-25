import AFTD.Prelude

/-!
# subcubic_minDegree_two_cubic_vertex_has_degree_two_neighbor

Topic: graphs   Node: a1d827ea933f

Provenance: helper lemma. step towards subcubic_maxDegree_induce_V3_le_two_exists_rich_neighbor_five_coloring

Let G be a finite simple graph with minimum degree at least 2 and maximum degree at most 3 in which every degree-3 vertex has at most two degree-3 neighbours (the pointwise form of Delta(G[V_3]) <= 2). Then every vertex v with G.degree v = 3 has a neighbour w with G.degree w = 2.
-/

/-- Every degree-3 vertex of a subcubic graph with minimum degree >= 2 and at most two degree-3 neighbours has a neighbour of degree exactly 2. -/
theorem subcubic_minDegree_two_cubic_vertex_has_degree_two_neighbor {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) (hdeg : G.maxDegree ≤ 3)
    (h3 : ∀ v, G.degree v = 3 → ((G.neighborFinset v).filter (fun w => G.degree w = 3)).card ≤ 2)
    (v : V) (hv : G.degree v = 3) :
    ∃ w, G.Adj v w ∧ G.degree w = 2 := by
  classical
  have hcard : (G.neighborFinset v).card = 3 := by rw [G.card_neighborFinset_eq_degree, hv]
  have hlt : ((G.neighborFinset v).filter (fun w => G.degree w = 3)).card < (G.neighborFinset v).card := by
    have := h3 v hv; omega
  obtain ⟨w, hw, hwf⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_filter] at hwf
  have hadj : G.Adj v w := by simpa [G.mem_neighborFinset] using hw
  have hdegw : G.degree w ≠ 3 := fun h => hwf ⟨hw, h⟩
  have hle : G.degree w ≤ 3 := le_trans (G.degree_le_maxDegree w) hdeg
  have hge : 2 ≤ G.degree w := hmin w
  exact ⟨w, hadj, by omega⟩
