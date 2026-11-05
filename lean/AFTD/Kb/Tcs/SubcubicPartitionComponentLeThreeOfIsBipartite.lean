import AFTD.Prelude

/-!
# subcubic_partition_component_le_three_of_isBipartite

Topic: graphs   Node: 2b1d267aedc7

Provenance: helper lemma. arXiv:2611.05178 Section 5 -- Weighted Max Cut in Subcubic Graphs

Every bipartite finite simple graph admits a partition of its vertex set into an independent set L and a complement R = Lᶜ such that every connected component of the induced subgraph G[R] has order at most 3.
-/

lemma subcubic_partition_component_le_three_of_isBipartite_subsingleton {V : Type*}
    (G : SimpleGraph V) (K : Set V) (h : G.induce Kᶜ = ⊥)
    (C : G.ComponentCompl K) :
    Subsingleton C := by
  constructor
  intro ⟨x, hx⟩ ⟨y, hy⟩
  rw [Subtype.mk.injEq]
  rw [SimpleGraph.ComponentCompl.mem_supp_iff] at hx hy
  rcases hx with ⟨hxK, hxC⟩
  rcases hy with ⟨hyK, hyC⟩
  have h_eq : G.componentComplMk hxK = G.componentComplMk hyK := by
    rw [hxC, hyC]
  change (G.induce Kᶜ).connectedComponentMk ⟨x, hxK⟩ = (G.induce Kᶜ).connectedComponentMk ⟨y, hyK⟩ at h_eq
  rw [h] at h_eq
  rw [SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_bot] at h_eq
  exact Subtype.ext_iff.mp h_eq

/-- Every bipartite graph admits an independent set whose complement has all connected components of order at most 3 (in fact order at most 1). -/
theorem subcubic_partition_component_le_three_of_isBipartite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hbp : G.IsBipartite) :
    ∃ L : Finset V, G.induce (L : Set V) = ⊥ ∧
      ∀ C : (G.induce (Lᶜ : Set V)).ConnectedComponent,
        open scoped Classical in Fintype.card C ≤ 3 := by
  rcases hbp with ⟨c⟩
  let L : Finset V := Finset.filter (fun v => c v = 0) Finset.univ
  have hL : G.induce (L : Set V) = ⊥ := by
    ext ⟨u, hu⟩ ⟨v, hv⟩
    simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
    intro hadj
    have hu' : c u = 0 := by
      have : u ∈ L := hu
      rw [Finset.mem_filter] at this
      exact this.2
    have hv' : c v = 0 := by
      have : v ∈ L := hv
      rw [Finset.mem_filter] at this
      exact this.2
    have hne := c.valid hadj
    rw [hu', hv'] at hne
    exact hne rfl
  have hR : G.induce (Lᶜ : Set V) = ⊥ := by
    ext ⟨u, hu⟩ ⟨v, hv⟩
    simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
    intro hadj
    have hu' : c u = 1 := by
      have hu_not : u ∉ L := hu
      have : c u ≠ 0 := by
        intro h0
        apply hu_not
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ u, h0⟩
      omega
    have hv' : c v = 1 := by
      have hv_not : v ∉ L := hv
      have : c v ≠ 0 := by
        intro h0
        apply hv_not
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ v, h0⟩
      omega
    have hne := c.valid hadj
    rw [hu', hv'] at hne
    exact hne rfl
  refine ⟨L, hL, fun C => ?_⟩
  classical
  have : Subsingleton C := subcubic_partition_component_le_three_of_isBipartite_subsingleton G (L : Set V) hR C
  have : Fintype.card C ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr this
  omega
