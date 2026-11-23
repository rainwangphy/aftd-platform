import AFTD.Prelude
import AFTD.Kb.Tcs.CableSteinerOpt
import AFTD.Kb.Tcs.RatSegmentsUnion
import AFTD.Kb.Tcs.TwoPointNetworkLengthGe
import AFTD.Kb.Tcs.RatPlanePoint

/-!
# cable_steiner_opt_two_points

Topic: approximation   Node: bdee872e3da6

Provenance: helper lemma. Sanity check of cable_steiner_opt: two point cables are joined at cost their distance.

For two one-point cables p and q (degenerate segments), the cable Steiner optimum is the Euclidean distance between p and q.
-/

theorem cable_steiner_opt_two_points (p q : ℚ × ℚ) :
    cable_steiner_opt [[(p, p)], [(q, q)]] = dist (rat_plane_point p) (rat_plane_point q) := by
  have hU : (⋃ c ∈ [[(p, p)], [(q, q)]], rat_segments_union c) =
      ({rat_plane_point p, rat_plane_point q} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext x
    simp [rat_segments_union, or_comm]
  unfold cable_steiner_opt
  simp only [hU]
  have hmem : dist (rat_plane_point p) (rat_plane_point q) ∈
      {L : ℝ | ∃ T : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
        IsConnected (({rat_plane_point p, rat_plane_point q} : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ t ∈ T, segment ℝ t.1 t.2) ∧ L = ∑ t ∈ T, dist t.1 t.2} := by
    refine ⟨{(rat_plane_point p, rat_plane_point q)}, ?_, by simp⟩
    have he : ({rat_plane_point p, rat_plane_point q} : Set (EuclideanSpace ℝ (Fin 2))) ∪
        ⋃ t ∈ ({(rat_plane_point p, rat_plane_point q)} : Finset _), segment ℝ t.1 t.2 =
        segment ℝ (rat_plane_point p) (rat_plane_point q) := by
      simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
      exact Set.union_eq_right.mpr (Set.insert_subset_iff.mpr
        ⟨left_mem_segment ℝ _ _, Set.singleton_subset_iff.mpr (right_mem_segment ℝ _ _)⟩)
    rw [he]
    exact (convex_segment _ _).isConnected ⟨_, left_mem_segment ℝ _ _⟩
  apply le_antisymm
  · apply csInf_le _ hmem
    refine ⟨0, ?_⟩
    rintro L ⟨T, -, rfl⟩
    exact Finset.sum_nonneg fun t _ => dist_nonneg
  · apply le_csInf ⟨_, hmem⟩
    rintro L ⟨T, hT, rfl⟩
    exact two_point_network_length_ge _ _ T hT
