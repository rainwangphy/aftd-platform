import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentCrossing

/-!
# segment_crossing_symm

Topic: combinatorics   Node: 1cac1de4d347

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover

The segment crossing relation between two segments in ℝ² is symmetric.
-/

/-- The segment crossing relation between two segments in ℝ² is symmetric. -/
theorem segment_crossing_symm (e₁ e₂ : Sym2 (ℝ × ℝ)) :
    segment_crossing e₁ e₂ ↔ segment_crossing e₂ e₁ := by
  unfold segment_crossing
  rw [Set.inter_comm]
