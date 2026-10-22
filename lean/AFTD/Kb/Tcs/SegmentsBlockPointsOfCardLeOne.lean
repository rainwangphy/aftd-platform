import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentsBlockPoints
import AFTD.Kb.Tcs.SegmentCrossingGraph

/-!
# segments_block_points_of_card_le_one

Topic: combinatorics   Node: 62055d91e936

Provenance: helper lemma. step towards triangle_free_blocking_ge_vertex_cover

Any finite point set in ℝ² of cardinality at most 1 is vacuously blocked by any finite family of segments L under the triangle-free crossing property.
-/

/-- Any finite point set of cardinality at most 1 is vacuously blocked under the triangle-free crossing property. -/
theorem segments_block_points_of_card_le_one (L : Finset (Sym2 (ℝ × ℝ))) {P : Finset (ℝ × ℝ)}
    (hP : P.card ≤ 1) : segments_block_points L P := by
  intro u v hu hv hne
  exact (hne (Finset.card_le_one_iff.mp hP hu hv)).elim
