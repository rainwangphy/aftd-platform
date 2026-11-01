import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# simple_graph_exists_geodesic_vertex_family

Topic: graphs   Node: 179238d0a8ac

Provenance: helper lemma. step towards amply_regular_diameter_bound_qpk

A shortest walk realises a geodesic: if x and y are reachable in G and dist x y = d, then there is a family of vertices (v_i)_{i ≤ d} with v_0 = x, v_d = y and dist (v i) (v j) = |i − j| (i.e. `Nat.dist i j`) for all i, j ≤ d.
-/

/-- A shortest walk yields a geodesic family of vertices indexed by 0, …, dist x y, whose pairwise distances are the index distances. -/
theorem simple_graph_exists_geodesic_vertex_family {V : Type*} (G : SimpleGraph V) {x y : V} {d : ℕ}
    (hd : G.dist x y = d) (hr : G.Reachable x y) :
    ∃ v : ℕ → V, v 0 = x ∧ v d = y ∧ ∀ i j : ℕ, i ≤ d → j ≤ d → G.dist (v i) (v j) = Nat.dist i j := by
  classical
  obtain ⟨p, -, hp⟩ := hr.exists_path_of_dist
  have hlen : p.length = d := hp.trans hd
  refine ⟨fun i => p.getVert i, p.getVert_zero, ?_, ?_⟩
  · rw [← hlen]; exact p.getVert_length
  · intro i j hi hj
    have hmain : ∀ a b : ℕ, a ≤ b → b ≤ d → G.dist (p.getVert a) (p.getVert b) = Nat.dist a b := by
      intro a b hab hb
      have hsub : ((p.drop a).take (b - a)).IsSubwalk p :=
        (SimpleGraph.Walk.isSubwalk_take _ _).trans (SimpleGraph.Walk.isSubwalk_drop _ _)
      have hq := SimpleGraph.length_eq_dist_of_subwalk hp hsub
      have htake : ((p.drop a).take (b - a)).length = b - a := by
        rw [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length, hlen]
        omega
      have hdist' : G.dist (p.getVert a) ((p.drop a).getVert (b - a)) = b - a := by
        rw [← hq, htake]
      have hget : (p.drop a).getVert (b - a) = p.getVert b := by
        rw [SimpleGraph.Walk.drop_getVert]
        congr 1
        omega
      have h2 : G.dist (p.getVert a) (p.getVert b) = b - a := hget ▸ hdist'
      rw [h2, Nat.dist_eq_sub_of_le hab]
    rcases le_total i j with h | h
    · exact hmain i j h hj
    · rw [SimpleGraph.dist_comm, Nat.dist_comm]
      exact hmain j i h hi
