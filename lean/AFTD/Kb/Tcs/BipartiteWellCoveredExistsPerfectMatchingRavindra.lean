import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteWellCoveredHasPerfectMatching
import AFTD.Kb.Tcs.BipartiteWellCoveredPerfectMatchingRavindra
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered

/-!
# bipartite_well_covered_exists_perfect_matching_ravindra

Topic: graphs   Node: 1c83d49d793e

Provenance: helper lemma. step towards bipartite_all_powers_well_covered_diameter_le_two

Every finite connected well-covered bipartite graph G with at least 2 vertices has a perfect matching M such that for every edge uv of M, every neighbor of u is adjacent to every neighbor of v (N(u) x N(v) are all edges).
-/

/-- Ravindra's theorem (1977): Every finite connected well-covered bipartite graph with at least 2 vertices has a perfect matching M whose edges have complete bipartite neighborhoods. -/
theorem bipartite_well_covered_exists_perfect_matching_ravindra {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (hbip : G.IsBipartite)
    (hcard : 2 ≤ Fintype.card V) (hwc : simple_graph_is_well_covered G) :
    ∃ M : SimpleGraph.Subgraph G, M.IsPerfectMatching ∧
      ∀ u v : V, M.Adj u v → ∀ x y : V, G.Adj u x → G.Adj v y → G.Adj x y := by
  obtain ⟨M, hM⟩ := bipartite_well_covered_has_perfect_matching G hconn hbip hcard hwc
  exact ⟨M, hM, fun u v huv x y hx hy =>
    bipartite_well_covered_perfect_matching_ravindra G hconn hbip hcard hwc M hM u v huv x y hx hy⟩
