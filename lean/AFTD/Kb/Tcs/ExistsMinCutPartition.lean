import AFTD.Prelude
import AFTD.Kb.Tcs.GraphEdgeConnectivity
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# exists_min_cut_partition

Topic: graphs   Node: c28c32512092

Provenance: helper lemma. step towards edge_connectivity_ge_three_halves_min_degree_mul_lly_lower_bound_three

For every finite connected graph G on at least two vertices, there exists a non-trivial cut partition (X, X^c) with crossing edges at most the edge-connectivity κ'(G).
-/

/-- For every finite connected graph G on at least two vertices, there exists a partition of the vertices into two non-empty sets X and X^c such that the number of crossing edges is at most the edge-connectivity κ'(G). -/
theorem exists_min_cut_partition {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ (X : Finset V), X.Nonempty ∧ (Xᶜ : Finset V).Nonempty ∧
      (G.edgeFinset.filter (fun e => ∃ u ∈ X, ∃ v ∈ (Xᶜ : Finset V), e = s(u, v))).card ≤
        graph_edge_connectivity G := by
  classical
  -- `κ'(G)+1` exceeds the sSup, so `G` is not `(κ'(G)+1)`-edge-connected.
  have hnot : ¬ G.IsEdgeConnected (graph_edge_connectivity G + 1) := by
    intro h
    have hbound : graph_edge_connectivity G + 1 ≤ graph_edge_connectivity G := by
      dsimp [graph_edge_connectivity]
      apply le_csSup
      · obtain ⟨v⟩ : Nonempty V := inferInstance
        exact ⟨G.degree v, fun k hk ↦ hk.le_degree⟩
      · exact h
    omega
  rw [SimpleGraph.IsEdgeConnected] at hnot
  push_neg at hnot
  obtain ⟨u, v, huv⟩ := hnot
  rw [SimpleGraph.IsEdgeReachable] at huv
  push_neg at huv
  obtain ⟨s, hs, hreach⟩ := huv
  -- Work in `H = G` with the edge set `s` deleted, and take the component of `u`.
  let H := G.deleteEdges s
  let X : Finset V := Finset.univ.filter (fun x => H.Reachable u x)
  have huX : u ∈ X := by
    simp [X, SimpleGraph.Reachable.rfl]
  have hvX : v ∉ X := by
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hreach
  have hXne : X.Nonempty := ⟨u, huX⟩
  have hXcne : (Xᶜ : Finset V).Nonempty := ⟨v, by simp [hvX]⟩
  refine ⟨X, hXne, hXcne, ?_⟩
  -- Every edge crossing the cut `(X, Xᶜ)` must belong to `s`.
  have hsub : ((G.edgeFinset.filter (fun e => ∃ a ∈ X, ∃ b ∈ (Xᶜ : Finset V), e = s(a, b))) : Set (Sym2 V)) ⊆ s := by
    intro e he
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at he
    obtain ⟨heedge, a, haX, b, hbXc, rfl⟩ := he
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at haX
    simp only [Finset.mem_compl, X, Finset.mem_filter, Finset.mem_univ, true_and] at hbXc
    by_contra hmem
    have hadj : G.Adj a b := (SimpleGraph.mem_edgeSet G).mp ((SimpleGraph.mem_edgeFinset).mp heedge)
    have hHadj : H.Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hmem⟩
    exact hbXc (haX.trans hHadj.reachable)
  -- Since `s.encard < κ'(G)+1`, we have `s.encard ≤ κ'(G)`, bounding the cut size.
  have hleκ : s.encard ≤ (graph_edge_connectivity G : ℕ∞) := by
    have hs' : s.encard < (graph_edge_connectivity G : ℕ∞) + 1 := by
      simpa using hs
    exact (ENat.lt_add_one_iff (by simp)).mp hs'
  have hcardle : ((G.edgeFinset.filter (fun e => ∃ a ∈ X, ∃ b ∈ (Xᶜ : Finset V), e = s(a, b))) : Set (Sym2 V)).encard ≤ (graph_edge_connectivity G : ℕ∞) :=
    le_trans (Set.encard_le_encard hsub) hleκ
  rw [Set.encard_coe_eq_coe_finsetCard] at hcardle
  exact ENat.natCast_le_natCast.mp hcardle
