import AFTD.Prelude

/-!
# simple_graph_card_commonNeighbors_add_two_le_degree

Topic: graphs   Node: 7c45c591809a

Provenance: helper lemma. step towards amply_regular_diameter_bound_conjecture

Let G be a graph on a finite vertex set that is regular of degree k. If u and v are two distinct common neighbours of a vertex w and u is not adjacent to v, then u and w have at most k - 2 common neighbours: |N(u) ∩ N(w)| + 2 ≤ k.
-/

/-- Counting lemma for regular graphs: two non-adjacent neighbours u, v of w cannot both lie in N(u) ∩ N(w), so N(u) ∩ N(w) misses the two distinct points u, v of N(w). -/
theorem simple_graph_card_commonNeighbors_add_two_le_degree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hreg : G.IsRegularOfDegree k) {u v w : V}
    (hne : u ≠ v) (huw : G.Adj u w) (hvw : G.Adj v w) (huv : ¬ G.Adj u v) :
    Fintype.card (G.commonNeighbors u w) + 2 ≤ k := by
  classical
  have hFk : (G.neighborFinset u).card = k := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hreg u
  have hWk : (G.neighborFinset w).card = k := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hreg w
  have hCeq : (G.commonNeighbors u w).toFinset = G.neighborFinset u ∩ G.neighborFinset w := by
    ext x; simp [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_commonNeighbors]
  have huW : u ∈ G.neighborFinset w := by rw [SimpleGraph.mem_neighborFinset]; exact huw.symm
  have hvW : v ∈ G.neighborFinset w := by rw [SimpleGraph.mem_neighborFinset]; exact hvw.symm
  have hvF : v ∉ G.neighborFinset u := by rw [SimpleGraph.mem_neighborFinset]; exact huv
  have huF : u ∉ G.neighborFinset u := by simp
  suffices h : (G.neighborFinset u ∩ G.neighborFinset w).card + 2 ≤ (G.neighborFinset u).card by
    rw [← Set.toFinset_card, hCeq]; omega
  by_contra hcon
  push Not at hcon
  have hCsub2 : G.neighborFinset u ∩ G.neighborFinset w ⊆ (G.neighborFinset w).erase u := by
    intro x hx
    rw [Finset.mem_inter] at hx
    exact Finset.mem_erase.mpr ⟨fun hh => huF (hh ▸ hx.1), hx.2⟩
  have hset2 : G.neighborFinset u ∩ G.neighborFinset w = (G.neighborFinset w).erase u :=
    Finset.eq_of_subset_of_card_le hCsub2 (by rw [Finset.card_erase_of_mem huW, hWk]; omega)
  have hv : v ∈ G.neighborFinset u ∩ G.neighborFinset w := by
    rw [hset2]; exact Finset.mem_erase.mpr ⟨hne.symm, hvW⟩
  exact hvF (Finset.mem_inter.mp hv).1
