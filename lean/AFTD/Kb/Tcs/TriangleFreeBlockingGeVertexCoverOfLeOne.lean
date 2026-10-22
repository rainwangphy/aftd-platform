import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentsBlockPointsOfCardLeOne
import AFTD.Kb.Tcs.SegmentsBlockPoints
import AFTD.Kb.Tcs.SegmentCrossingGraph

/-!
# triangle_free_blocking_ge_vertex_cover_of_le_one

Topic: combinatorics   Node: a49ac85bc1ad

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover

For every finite family of line segments L whose crossing graph has vertex cover number at most 1, there exists a point set P blocked by L with cardinality at least the vertex cover number.
-/

/-- The triangle-free blocking lower bound holds when the crossing graph has vertex cover number at most 1. -/
theorem triangle_free_blocking_ge_vertex_cover_of_le_one
    (L : Finset (Sym2 (ℝ × ℝ)))
    (h_vc : (segment_crossing_graph L).vertexCoverNum ≤ 1) :
    ∃ P : Finset (ℝ × ℝ), segments_block_points L P ∧
      (segment_crossing_graph L).vertexCoverNum ≤ P.card := by
  refine ⟨{(0, 0)}, segments_block_points_of_card_le_one L (by simp), by simp [h_vc]⟩
