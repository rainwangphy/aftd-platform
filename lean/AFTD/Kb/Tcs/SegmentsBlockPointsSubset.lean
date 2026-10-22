import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentsBlockPoints

/-!
# segments_block_points_subset

Topic: combinatorics   Node: 667a489a5038

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover

If a segment family L blocks a point set Q under the triangle-free crossing property, then L also blocks any subset P ⊆ Q.
-/

/-- If L blocks a point set Q under the triangle-free crossing property, it blocks any subset P ⊆ Q. -/
theorem segments_block_points_subset {L : Finset (Sym2 (ℝ × ℝ))} {P Q : Finset (ℝ × ℝ)}
    (hsub : P ⊆ Q) (hQ : segments_block_points L Q) :
    segments_block_points L P := by
  intro u v hu hv huv
  exact hQ (hsub hu) (hsub hv) huv
