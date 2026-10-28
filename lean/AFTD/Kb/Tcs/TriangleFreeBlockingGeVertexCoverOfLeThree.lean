import AFTD.Prelude
import AFTD.Kb.Tcs.TriangleMidpointsExist
import AFTD.Kb.Tcs.SegmentCrossingOfMemOpenSegments
import AFTD.Kb.Tcs.NotCliqueFreeThreeOfCrossesCrossingPairTf
import AFTD.Kb.Tcs.TriangleFreeBlockingGeVertexCoverOfLeTwo
import AFTD.Kb.Tcs.SegmentsBlockPoints
import AFTD.Kb.Tcs.ExistsTriangleThroughThreePointsAvoiding
import AFTD.Kb.Tcs.VertexCoverThreeExtractsStarPairs
import AFTD.Kb.Tcs.CrossingPointsDistinctOfTriangleFree
import AFTD.Kb.Tcs.ThreeCrossingPointsOfVertexCoverThree
import AFTD.Kb.Tcs.BlockingCardThreeOfThreeCrossingPoints
import AFTD.Kb.Tcs.SegmentCrossingGraph

/-!
# triangle_free_blocking_ge_vertex_cover_of_le_three

Topic: combinatorics   Node: 8d5eeb9789f1

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover

For every finite family of line segments L whose crossing graph is triangle-free and has vertex cover number at most 3, there exists a point set P blocked by L with cardinality at least the vertex cover number.
-/

/-- For every finite family of line segments L whose crossing graph is triangle-free and has vertex cover number at most 3, there exists a point set P blocked by L with cardinality at least the vertex cover number. -/
theorem triangle_free_blocking_ge_vertex_cover_of_le_three
    (L : Finset (Sym2 (ℝ × ℝ)))
    (h_tf : (segment_crossing_graph L).CliqueFree 3)
    (h_vc : (segment_crossing_graph L).vertexCoverNum ≤ 3) :
    ∃ P : Finset (ℝ × ℝ), segments_block_points L P ∧
      (segment_crossing_graph L).vertexCoverNum ≤ P.card := by
  by_cases h_le2 : (segment_crossing_graph L).vertexCoverNum ≤ 2
  · exact triangle_free_blocking_ge_vertex_cover_of_le_two L h_tf h_le2
  · have h_eq3 : (segment_crossing_graph L).vertexCoverNum = 3 := by
      have htop : (segment_crossing_graph L).vertexCoverNum ≠ ⊤ := by
        intro htop_eq
        rw [htop_eq] at h_vc
        revert h_vc
        decide
      rw [← ENat.natCast_toNat htop] at h_vc h_le2 ⊢
      norm_cast at h_vc h_le2 ⊢
      omega
    obtain ⟨a₁, a₂, b₁, b₂, c₁, c₂, d₁, d₂, e₁, e₂, f₁, f₂, A, B, C,
      ha, hb, hc, hd, he, hf, hab, hcd, hef,
      hA₁, hA₂, hB₁, hB₂, hC₁, hC₂, hAB, hBC, hCA⟩ :=
      three_crossing_points_of_vertex_cover_three L h_tf h_eq3
    obtain ⟨P, hP_block, hP_card⟩ :=
      blocking_card_three_of_three_crossing_points L h_tf
        a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ A B C
        ha hb hc hd he hf hab hcd hef
        hA₁ hA₂ hB₁ hB₂ hC₁ hC₂ hAB hBC hCA
    refine ⟨P, hP_block, ?_⟩
    rw [h_eq3, hP_card]
    decide
