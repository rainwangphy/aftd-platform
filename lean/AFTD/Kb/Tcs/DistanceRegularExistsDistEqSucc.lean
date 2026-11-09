import AFTD.Prelude
import AFTD.Kb.Tcs.IsDistanceRegularWith

/-!
# distance_regular_exists_dist_eq_succ

Topic: graphs   Node: 3dc6f2f9a509

Provenance: helper lemma. step towards op_1146_classification_realizable_intersection_array_k_geodetic

In any finite distance-regular graph G with parameters d, b, c, for every index i : Fin d, there exist vertices u, v at distance i + 1.
-/

/-- In any finite distance-regular graph with diameter d and parameters b, c, every distance 1 ≤ i + 1 ≤ d is attained by some pair of vertices. -/
theorem distance_regular_exists_dist_eq_succ {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (b c : Fin d → ℕ)
    (hG : is_distance_regular_with G d b c) (i : Fin d) :
    ∃ u v : V, G.dist u v = i.val + 1 := by
  obtain ⟨conn, hdiam, hb, hc⟩ := hG
  haveI hne : Nonempty V := conn.nonempty
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  rw [hdiam] at huv
  obtain ⟨p, hp⟩ := conn.exists_walk_length_eq_dist u v
  have hle : i.val + 1 ≤ p.length := by
    rw [hp, huv]; exact Nat.succ_le_of_lt i.isLt
  refine ⟨u, p.getVert (i.val + 1), ?_⟩
  have hsub := p.isSubwalk_take (i.val + 1)
  have hlen : (p.take (i.val + 1)).length = i.val + 1 := by
    rw [SimpleGraph.Walk.take_length, min_eq_left hle]
  have hdist := SimpleGraph.length_eq_dist_of_subwalk hp hsub
  rw [← hdist, hlen]
