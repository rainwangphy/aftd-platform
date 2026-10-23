import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentCrossing

/-!
# segment_crossing_of_mem_openSegments

Topic: combinatorics   Node: 2b14e97f7b37

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover

If a point x lies in the open segment uv and also in the open segment ab, then the segment uv crosses the segment ab.
-/

/-- If a point x lies in the open segment uv and also in the open segment ab, then the segment uv crosses the segment ab. -/
theorem segment_crossing_of_mem_openSegments
    (u v a b x : ℝ × ℝ)
    (huv : x ∈ openSegment ℝ u v) (hab : x ∈ openSegment ℝ a b) :
    segment_crossing s(u, v) s(a, b) := ⟨x, huv, hab⟩
